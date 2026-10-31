import math
import os
import shutil
import struct
import subprocess
import tempfile
import unittest
import wave
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG", shutil.which("ffmpeg") or "ffmpeg")
STRACE = shutil.which("strace")
ISO_ENV = {"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"}
LAG = 1024


def run(*args, env=None):
    return subprocess.run([str(a) for a in args], check=True, capture_output=True, env=env)


def ffmpeg_available():
    try:
        out = run(FFMPEG, "-version").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return out.startswith("ffmpeg version ")


def tone(sr, nch, seconds, freqs, step_at=None):
    n = int(sr * seconds)
    chans = [[] for _ in range(nch)]
    for i in range(n):
        t = i / sr
        for c in range(nch):
            if step_at is not None:
                amp = 0.70 if t >= step_at else 0.0
                x = amp * (
                    math.sin(2.0 * math.pi * freqs[c] * t)
                    + 0.25 * math.sin(2.0 * math.pi * (freqs[c] * 3.0) * t)
                )
            else:
                x = 0.55 * math.sin(2.0 * math.pi * freqs[c] * t)
            chans[c].append(max(-1.0, min(1.0, x)))
    return chans


def write_wav(path, sr, chans):
    n = len(chans[0])
    interleaved = []
    for i in range(n):
        for c in chans:
            interleaved.append(int(max(-32768, min(32767, round(c[i] * 32767.0)))))
    with wave.open(str(path), "wb") as wf:
        wf.setnchannels(len(chans))
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(struct.pack("<" + "h" * len(interleaved), *interleaved))


def read_wav_pcm(path):
    with wave.open(str(path), "rb") as wf:
        nch = wf.getnchannels()
        raw = wf.readframes(wf.getnframes())
    vals = struct.unpack("<" + "h" * (len(raw) // 2), raw)
    return [[vals[i] for i in range(c, len(vals), nch)] for c in range(nch)]


def read_pcm(path, nch):
    raw = path.read_bytes()
    vals = struct.unpack("<" + "h" * (len(raw) // 2), raw)
    return [[vals[i] for i in range(c, len(vals), nch)] for c in range(nch)]


def snr_db(ref, got, lag):
    n = min(len(ref), len(got)) - lag
    if n <= 256:
        return -999.0
    sig = err = 0.0
    for i in range(n):
        a = float(ref[i])
        b = float(got[i + lag])
        sig += a * a
        d = a - b
        err += d * d
    if sig <= 0.0:
        return -999.0
    if err <= 0.0:
        return 200.0
    return 10.0 * math.log10(sig / err)


@unittest.skipUnless(LFFMPEG.exists(), "lffmpeg is not built")
@unittest.skipUnless(ffmpeg_available(), "reference ffmpeg is unavailable")
class AacLcDifferentialTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def _bidir(self, sr, nch, freqs, step_at=None, min_snr=75.0):
        chans = tone(sr, nch, 0.35, freqs, step_at)
        wav = self.dir / f"in_{sr}_{nch}_{int(min_snr)}.wav"
        write_wav(wav, sr, chans)
        lean = self.dir / f"lean_{sr}_{nch}.aac"
        ff = self.dir / f"ff_{sr}_{nch}.aac"
        ff_nopns = self.dir / f"ff_nopns_{sr}_{nch}.aac"
        run(LFFMPEG, "-y", "-i", wav, "-c:a", "aac", "-b:a", "128k", lean, env=ISO_ENV)
        run(FFMPEG, "-y", "-v", "error", "-i", wav, "-c:a", "aac", "-b:a", "128k", "-f", "adts", ff)
        run(FFMPEG, "-y", "-v", "error", "-i", wav, "-c:a", "aac", "-aac_pns", "0", "-b:a", "128k", "-f", "adts", ff_nopns)
        lean_pcm = self.dir / f"lean_dec_{sr}_{nch}.pcm"
        ff_ref_pcm = self.dir / f"ff_ref_dec_{sr}_{nch}.pcm"
        ff_lean_wav = self.dir / f"ff_lean_dec_{sr}_{nch}.wav"
        ff_lean_wav2 = self.dir / f"ff_lean_dec2_{sr}_{nch}.wav"
        ff_nopns_pcm = self.dir / f"ff_nopns_dec_{sr}_{nch}.pcm"
        ff_nopns_wav = self.dir / f"ff_nopns_lean_{sr}_{nch}.wav"
        run(FFMPEG, "-y", "-v", "error", "-i", lean, "-f", "s16le", "-ac", str(nch), lean_pcm)
        run(FFMPEG, "-y", "-v", "error", "-i", ff, "-f", "s16le", "-ac", str(nch), ff_ref_pcm)
        run(LFFMPEG, "-y", "-i", ff, ff_lean_wav, env=ISO_ENV)
        run(LFFMPEG, "-y", "-i", ff, ff_lean_wav2, env=ISO_ENV)
        run(FFMPEG, "-y", "-v", "error", "-i", ff_nopns, "-f", "s16le", "-ac", str(nch), ff_nopns_pcm)
        run(LFFMPEG, "-y", "-i", ff_nopns, ff_nopns_wav, env=ISO_ENV)
        self.assertEqual(ff_lean_wav.read_bytes(), ff_lean_wav2.read_bytes())
        ref = read_wav_pcm(wav)
        ours = read_pcm(lean_pcm, nch)
        ff_oracle = read_pcm(ff_ref_pcm, nch)
        theirs = read_wav_pcm(ff_lean_wav)
        nopns_oracle = read_pcm(ff_nopns_pcm, nch)
        nopns_theirs = read_wav_pcm(ff_nopns_wav)
        for c in range(nch):
            self.assertGreater(snr_db(ref[c], ours[c], LAG), min_snr)
            self.assertGreater(snr_db(nopns_oracle[c], nopns_theirs[c], 0), min_snr)
            self.assertGreater(snr_db(ff_oracle[c], theirs[c], 0), 50.0)
        self.assertGreater(lean.stat().st_size, 7)
        self.assertGreater(ff.stat().st_size, 7)

    def test_bidirectional_tone_48k_and_44100(self):
        self._bidir(48000, 2, (440.0, 1000.0))
        self._bidir(44100, 2, (440.0, 1000.0))

    def test_bidirectional_transient_48k_and_44100(self):
        self._bidir(48000, 2, (440.0, 880.0), step_at=0.10, min_snr=50.0)
        self._bidir(44100, 2, (440.0, 880.0), step_at=0.10, min_snr=50.0)
        self._bidir(24000, 2, (440.0, 880.0), step_at=0.10, min_snr=50.0)
        self._bidir(48000, 1, (660.0,), step_at=0.10, min_snr=50.0)

    def test_pulse_data_matches_ffmpeg_decode(self):
        bits = []

        def w(val, n):
            for i in range(n - 1, -1, -1):
                bits.append((val >> i) & 1)

        w(0, 3); w(0, 4); w(168, 8); w(0, 1); w(0, 2); w(0, 1); w(1, 6); w(0, 1)
        w(3, 4); w(1, 5); w(0, 1)
        w(1, 1); w(0, 2); w(0, 6); w(0, 5); w(7, 4)
        w(0, 1); w(0, 1)
        w(0x8, 4); w(0, 1)
        w(7, 3)
        while len(bits) % 8 != 0:
            bits.append(0)
        raw = bytes(int("".join(str(x) for x in bits[i:i + 8]), 2) for i in range(0, len(bits), 8))
        fl = 7 + len(raw)
        hdr = bytes([
            0xFF, 0xF1, (1 << 6) | (3 << 2), (1 << 6) | ((fl >> 11) & 3), (fl >> 3) & 0xFF,
            ((fl & 7) << 5) | 0x1F, 0xFC,
        ])
        adts = self.dir / "pulse.aac"
        adts.write_bytes((hdr + raw) * 2)
        ff_pcm = self.dir / "pulse_ff.pcm"
        lean_wav = self.dir / "pulse_lean.wav"
        run(FFMPEG, "-y", "-v", "error", "-i", adts, "-f", "s16le", "-ac", "1", ff_pcm)
        run(LFFMPEG, "-y", "-i", adts, lean_wav, env=ISO_ENV)
        oracle = read_pcm(ff_pcm, 1)
        ours = read_wav_pcm(lean_wav)
        self.assertGreater(max(abs(x) for x in oracle[0]), 1000)
        self.assertGreater(snr_db(oracle[0], ours[0], 0), 75.0)

    def test_ffmpeg_pns_disabled_matches_lean_decode(self):
        wav = self.dir / "pns.wav"
        write_wav(wav, 48000, tone(48000, 2, 0.20, (440.0, 1000.0)))
        ff = self.dir / "pns_off.aac"
        run(FFMPEG, "-y", "-v", "error", "-i", wav, "-c:a", "aac", "-aac_pns", "0", "-b:a", "128k", "-f", "adts", ff)
        ff_pcm = self.dir / "pns_off_ff.pcm"
        lean_wav = self.dir / "pns_off_lean.wav"
        run(FFMPEG, "-y", "-v", "error", "-i", ff, "-f", "s16le", "-ac", "2", ff_pcm)
        run(LFFMPEG, "-y", "-i", ff, lean_wav, env=ISO_ENV)
        oracle = read_pcm(ff_pcm, 2)
        ours = read_wav_pcm(lean_wav)
        for c in range(2):
            self.assertGreater(snr_db(oracle[c], ours[c], 0), 75.0)

    def test_flac_to_adts_to_flac_and_plan_routing(self):
        wav = self.dir / "src.wav"
        write_wav(wav, 48000, tone(48000, 2, 0.15, (500.0, 1200.0)))
        flac_in = self.dir / "src.flac"
        adts = self.dir / "mid.adts"
        flac_out = self.dir / "dst.flac"
        wav_out = self.dir / "dst.wav"
        run(LFFMPEG, "-y", "-i", wav, flac_in, env=ISO_ENV)
        run(LFFMPEG, "-y", "-i", flac_in, "-b:a", "128k", adts, env=ISO_ENV)
        run(LFFMPEG, "-y", "-i", adts, flac_out, env=ISO_ENV)
        run(LFFMPEG, "-y", "-i", flac_out, wav_out, env=ISO_ENV)
        ref = read_wav_pcm(wav)
        got = read_wav_pcm(wav_out)
        for c in range(2):
            self.assertGreater(snr_db(ref[c], got[c], LAG), 30.0)
        plan_ok = run(LFFMPEG, "plan", "-y", "-i", "in.wav", "-c:a", "aac", "out.aac", env=ISO_ENV)
        self.assertIn(b'"independent_verified"', plan_ok.stdout)
        plan_fx = run(LFFMPEG, "plan", "-y", "-i", "in.wav", "-c:a", "aac_fixed", "out.aac", env=ISO_ENV)
        self.assertIn(b'"delegated_faithful"', plan_fx.stdout)

    def test_corrupt_crc_and_truncation_fail_closed(self):
        wav = self.dir / "crc.wav"
        write_wav(wav, 48000, tone(48000, 1, 0.08, (440.0,)))
        good = self.dir / "crc.aac"
        run(LFFMPEG, "-y", "-i", wav, "-c:a", "aac", good, env=ISO_ENV)
        raw = bytearray(good.read_bytes())
        self.assertGreaterEqual(len(raw), 7)
        fl = ((raw[3] & 0x03) << 11) | (raw[4] << 3) | ((raw[5] >> 5) & 0x07)
        payload = bytearray(raw[7:fl])
        fl_crc = len(payload) + 9
        crc_hdr = bytearray([
            0xFF,
            (raw[1] & 0xFE),
            raw[2],
            (raw[3] & 0xFC) | ((fl_crc >> 11) & 0x03),
            (fl_crc >> 3) & 0xFF,
            ((fl_crc & 0x07) << 5) | (raw[5] & 0x1F),
            raw[6],
        ])
        crc = 0xFFFF
        for b in payload:
            crc ^= b << 8
            for _ in range(8):
                crc = ((crc << 1) ^ 0x8005) & 0xFFFF if crc & 0x8000 else (crc << 1) & 0xFFFF
        crc ^= 0xFFFF
        crc_hdr.extend([(crc >> 8) & 0xFF, crc & 0xFF])
        valid_crc_aac = self.dir / "valid_crc.aac"
        valid_crc_aac.write_bytes(bytes(crc_hdr + payload))
        run(LFFMPEG, "-y", "-i", valid_crc_aac, self.dir / "valid_crc.wav", env=ISO_ENV)
        payload[0] ^= 0x01
        cases = {
            "sync.aac": bytes([0xFE]) + bytes(raw[1:]),
            "trunc.aac": bytes(raw[: max(4, len(raw) // 2)]),
            "crc_corrupt.aac": bytes(crc_hdr + payload),
        }
        for name, data in cases.items():
            path = self.dir / name
            path.write_bytes(data)
            res = subprocess.run(
                [str(LFFMPEG), "-y", "-i", str(path), str(self.dir / f"{name}.wav")],
                env=ISO_ENV, capture_output=True,
            )
            self.assertNotEqual(res.returncode, 0, name)

    def test_strace_execve_zero_children(self):
        wav = self.dir / "iso.wav"
        write_wav(wav, 48000, tone(48000, 2, 0.05, (440.0, 1000.0)))
        out = self.dir / "iso.aac"
        run(LFFMPEG, "-y", "-i", wav, "-c:a", "aac", out, env=ISO_ENV)
        if STRACE is None:
            return
        for cmd in (
            [STRACE, "-f", "-e", "trace=execve", LFFMPEG, "-y", "-i", wav, "-c:a", "aac", self.dir / "iso_enc.aac"],
            [STRACE, "-f", "-e", "trace=execve", LFFMPEG, "-y", "-i", out, self.dir / "iso_dec.wav"],
        ):
            proc = run(*cmd, env=ISO_ENV)
            lines = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if "execve(" in ln]
            self.assertEqual(len(lines), 1, lines)
            self.assertIn("lffmpeg", lines[0])


if __name__ == "__main__":
    unittest.main()
