import json
import math
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG", shutil.which("ffmpeg") or "ffmpeg")
FFPROBE = os.environ.get("FFPROBE", shutil.which("ffprobe") or "ffprobe")
STRACE = shutil.which("strace")
ISO_ENV = {
    "PATH": "/nonexistent",
    "LEANAV_FFMPEG_BIN": "/nonexistent",
    "LEANAV_FFPROBE_BIN": "/nonexistent",
}


def run(*args, env=None, check=True):
    return subprocess.run(
        [str(a) for a in args],
        check=check,
        capture_output=True,
        env=env,
    )


def libaom_av1_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return "libaom-av1" in out


def ffprobe_available():
    try:
        out = run(FFPROBE, "-version").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return out.startswith("ffprobe version ")


def synth_yuv420p(w, h, frames):
    buf = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 7 + y * 5 + f * 19 + ((x ^ y) & 15) * 3) & 0xFF
                buf.append(v)
        cw = w // 2
        ch = h // 2
        for y in range(ch):
            for x in range(cw):
                buf.append((88 + x * 3 + y * 2 + f * 11) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                buf.append((164 - x * 2 + y * 3 - f * 7) & 0xFF)
    return bytes(buf)


def psnr_db(ref_bytes, got_bytes):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    mse = sum((a - b) * (a - b) for a, b in zip(ref_bytes, got_bytes)) / len(ref_bytes)
    if mse == 0.0:
        return 99.0
    return 10.0 * math.log10((255.0 * 255.0) / mse)


@unittest.skipUnless(LFFMPEG.exists(), "lffmpeg is not built")
class TestAv1Main(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _ffmpeg_decode_yuv420p(self, in_path):
        out_yuv = self.dir / f"{Path(in_path).name}.ff.yuv"
        run(
            FFMPEG, "-y", "-v", "error",
            "-i", in_path,
            "-f", "rawvideo", "-pix_fmt", "yuv420p", out_yuv,
        )
        return out_yuv.read_bytes()

    def test_libaom_av1_to_lffmpeg_bit_exact_matrix(self):
        if not libaom_av1_available():
            self.skipTest("ffmpeg with libaom-av1 unavailable")
        cases = [
            ("intra_nocdef.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1", "-aom-params", "enable-cdef=0"]),
            ("intra_cdef_cpu8.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1"]),
            ("intra_cdef_cpu4.ivf", 64, 48, 1, "ivf", ["-cpu-used", "4", "-crf", "30", "-g", "1"]),
            ("ip_lag0_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36", "-lag-in-frames", "0"]),
            ("ip_lag0_cpu4.ivf", 96, 80, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-lag-in-frames", "0"]),
            ("ip_altref_def_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36"]),
            ("ip_altref_def_cpu4.ivf", 96, 80, 5, "ivf", ["-cpu-used", "4", "-crf", "34"]),
            ("tiles_2x2_lag0.ivf", 160, 128, 4, "ivf", ["-cpu-used", "8", "-crf", "34", "-lag-in-frames", "0", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("tiles_2x2_altref_cpu4.ivf", 160, 128, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("crop_98x66_cpu8.ivf", 98, 66, 4, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_98x66_cpu4.ivf", 98, 66, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("crop_130x98_cpu8.ivf", 130, 98, 3, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_130x98_cpu4.ivf", 130, 98, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("lossless_intra.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "0", "-g", "1", "-aom-params", "lossless=1"]),
            ("lossless_inter.ivf", 64, 48, 3, "ivf", ["-cpu-used", "8", "-crf", "0", "-lag-in-frames", "0", "-aom-params", "lossless=1"]),
            ("raw_stream.obu", 96, 80, 4, "obu", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_av1c.mp4", 96, 80, 5, "mp4", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_crop_98x66.mp4", 98, 66, 3, "mp4", ["-cpu-used", "8", "-crf", "34"]),
        ]
        for name, w, h, nf, mux_fmt, aom_opts in cases:
            with self.subTest(case=name):
                src_yuv = self.dir / f"src_{name}.yuv"
                raw_src = synth_yuv420p(w, h, nf)
                src_yuv.write_bytes(raw_src)
                stream_path = self.dir / name
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_yuv,
                    "-c:v", "libaom-av1", "-pix_fmt", "yuv420p",
                    *aom_opts,
                ]
                if mux_fmt == "obu":
                    cmd += ["-f", "obu"]
                elif mux_fmt == "ivf":
                    cmd += ["-f", "ivf"]
                cmd.append(stream_path)
                run(*cmd)

                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(LFFMPEG, "av1-decode-raw", stream_path, lean_yuv_path, env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                lean_bytes = lean_yuv_path.read_bytes()
                self.assertEqual(lean_bytes, ref_yuv)
                if "lossless" in name:
                    self.assertEqual(lean_bytes, raw_src)

                probe_proc = run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV)
                probe = json.loads(probe_proc.stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["codec"], "av1")
                self.assertEqual(probe["container"], mux_fmt)
                self.assertEqual(probe["profile"], 0)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["bit_depth"], 8)
                self.assertEqual(probe["chroma_subsampling"], "4:2:0")
                self.assertEqual(probe["frames"], nf)

    def test_lffmpeg_encode_to_ffmpeg_and_ffprobe_parity(self):
        if not libaom_av1_available():
            self.skipTest("ffmpeg unavailable")
        has_ffprobe = ffprobe_available()
        cases = [
            ("enc_lossless_64x48.obu", 64, 48, 2, 0, "obu", 1, 1),
            ("enc_lossless_98x66.ivf", 98, 66, 2, 0, "ivf", 1, 1),
            ("enc_lossless_mp4.mp4", 64, 48, 2, 0, "mp4", 1, 1),
            ("enc_q60_64x48.obu", 64, 48, 3, 60, "obu", 1, 1),
            ("enc_q60_96x80.ivf", 96, 80, 3, 60, "ivf", 1, 1),
            ("enc_q60_96x80.mp4", 96, 80, 3, 60, "mp4", 1, 1),
            ("enc_q60_crop_130x98.ivf", 130, 98, 2, 60, "ivf", 1, 1),
            ("enc_q60_tiles_2x2.obu", 128, 128, 2, 60, "obu", 2, 2),
            ("enc_q60_tiles_2x2.ivf", 128, 128, 3, 60, "ivf", 2, 2),
            ("enc_q60_tiles_2x2.mp4", 128, 128, 2, 60, "mp4", 2, 2),
        ]
        for name, w, h, nf, qidx, fmt, tc, tr in cases:
            with self.subTest(case=name):
                raw_in = synth_yuv420p(w, h, nf)
                in_path = self.dir / f"in_{name}.yuv"
                out_bs = self.dir / name
                lean_dec = self.dir / f"dec_{name}.yuv"
                in_path.write_bytes(raw_in)

                enc_proc = run(
                    LFFMPEG, "av1-encode-raw", w, h, in_path, out_bs, qidx, fmt, tc, tr,
                    env=ISO_ENV,
                )
                enc_meta = json.loads(enc_proc.stdout.decode())
                self.assertTrue(enc_meta["ok"])
                self.assertEqual(enc_meta["frames"], nf)
                self.assertGreater(out_bs.stat().st_size, 0)

                run(LFFMPEG, "av1-decode-raw", out_bs, lean_dec, env=ISO_ENV)
                ff_yuv = self._ffmpeg_decode_yuv420p(out_bs)
                lean_bytes = lean_dec.read_bytes()
                self.assertEqual(lean_bytes, ff_yuv)
                if qidx == 0:
                    self.assertEqual(ff_yuv, raw_in)
                else:
                    self.assertGreater(psnr_db(raw_in, ff_yuv), 30.0)

                probe = json.loads(run(LFFMPEG, "av1-probe", out_bs, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["container"], fmt)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["frames"], nf)
                self.assertEqual(probe["tile_cols"], tc)
                self.assertEqual(probe["tile_rows"], tr)

                if has_ffprobe:
                    fp_proc = run(
                        FFPROBE, "-v", "error", "-select_streams", "v:0",
                        "-count_frames",
                        "-show_entries", "stream=codec_name,profile,pix_fmt,width,height,nb_read_frames",
                        "-of", "json", out_bs,
                    )
                    st = json.loads(fp_proc.stdout.decode())["streams"][0]
                    self.assertEqual(st["codec_name"], "av1")
                    self.assertEqual(st["profile"], "Main")
                    self.assertEqual(st["pix_fmt"], "yuv420p")
                    self.assertEqual(st["width"], w)
                    self.assertEqual(st["height"], h)
                    self.assertEqual(int(st["nb_read_frames"]), nf)

    def test_non_main_and_malformed_inputs_fail_closed(self):
        in_good = self.dir / "good.yuv"
        in_good.write_bytes(synth_yuv420p(64, 48, 1))
        good_obu = self.dir / "good.obu"
        run(LFFMPEG, "av1-encode-raw", 64, 48, in_good, good_obu, 60, "obu", env=ISO_ENV)
        good_raw = good_obu.read_bytes()

        bad_cases = {
            "empty.obu": b"",
            "junk.obu": b"\xff\xff\xff\xff\x00\x01\x02",
            "trunc_seq.obu": good_raw[:6],
            "trunc_frame.obu": good_raw[: max(18, len(good_raw) // 2)],
        }
        for tag, payload in bad_cases.items():
            p = self.dir / tag
            p.write_bytes(payload)
            self.assertNotEqual(
                run(LFFMPEG, "av1-decode-raw", p, "-", env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        for tag in ("empty.obu", "junk.obu", "trunc_seq.obu"):
            p = self.dir / tag
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", p, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        in_odd = self.dir / "odd.yuv"
        in_odd.write_bytes(b"\x80" * (63 * 48 * 3 // 2))
        self.assertNotEqual(
            run(LFFMPEG, "av1-encode-raw", 63, 48, in_odd, self.dir / "odd.obu", env=ISO_ENV, check=False).returncode,
            0,
        )

        if not libaom_av1_available():
            return
        src_yuv = self.dir / "neg_src.yuv"
        src_yuv.write_bytes(synth_yuv420p(64, 48, 1))
        for tag, pix_fmt in (("av1_10bit.ivf", "yuv420p10le"), ("av1_444.ivf", "yuv444p")):
            neg_path = self.dir / tag
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
                "-i", src_yuv,
                "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", pix_fmt,
                "-frames:v", "1", "-f", "ivf", neg_path,
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-decode-raw", neg_path, "-", env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", neg_path, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

    def test_strace_execve_zero_children(self):
        in_path = self.dir / "iso_in.yuv"
        in_path.write_bytes(synth_yuv420p(64, 48, 2))
        bs_path = self.dir / "iso.obu"
        out_yuv = self.dir / "iso_out.yuv"
        run(LFFMPEG, "av1-encode-raw", 64, 48, in_path, bs_path, 60, "obu", 1, 1, env=ISO_ENV)
        run(LFFMPEG, "av1-decode-raw", bs_path, out_yuv, env=ISO_ENV)
        run(LFFMPEG, "av1-probe", bs_path, env=ISO_ENV)
        if STRACE is None:
            return
        for cmd in (
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-probe", bs_path],
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-encode-raw", 64, 48, in_path, self.dir / "s.obu"],
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-decode-raw", bs_path, self.dir / "s.yuv"],
        ):
            proc = run(*cmd, env=ISO_ENV)
            execves = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if "execve(" in ln]
            self.assertEqual(len(execves), 1, execves)
            self.assertIn("lffmpeg", execves[0])


if __name__ == "__main__":
    unittest.main()
