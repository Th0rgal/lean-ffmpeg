import hashlib
import json
import math
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = Path(os.environ.get("FFMPEG") or shutil.which("ffmpeg") or "/usr/bin/ffmpeg")
FFPROBE = Path(os.environ.get("FFPROBE") or shutil.which("ffprobe") or "/usr/bin/ffprobe")
STRACE = shutil.which("strace")
ISO_ENV = {"PATH": "/nonexistent"}


def _ffmpeg_usable() -> bool:
    if not FFMPEG.is_file() or not os.access(FFMPEG, os.X_OK):
        return False
    try:
        res = subprocess.run([str(FFMPEG), "-version"], capture_output=True, text=True, check=True)
        return res.stdout.startswith("ffmpeg version ")
    except (OSError, subprocess.CalledProcessError):
        return False


def _decode_yuv(path: Path) -> bytes:
    res = subprocess.run(
        [str(FFMPEG), "-hide_banner", "-v", "error", "-i", str(path), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-"],
        capture_output=True,
        check=True,
    )
    return res.stdout


def _psnr(a: bytes, b: bytes) -> float:
    n = min(len(a), len(b))
    if n == 0:
        return 0.0
    mse = sum((a[i] - b[i]) ** 2 for i in range(n)) / n
    return 99.0 if mse == 0 else 10.0 * math.log10((255.0 ** 2) / mse)


class InprocTranscodeDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not _ffmpeg_usable() or not FFPROBE.is_file():
            raise unittest.SkipTest("reference ffmpeg/ffprobe unavailable")
        cls.fixture_dir = Path(tempfile.mkdtemp(prefix="leanav-inproc-diff-"))
        cls.cases = {
            "baseline_cavlc_ip": ["-profile:v", "baseline", "-bf", "0", "-x264-params", "weightp=0"],
            "high_cabac_ipb_8x8_weightp": ["-profile:v", "high", "-bf", "2"],
            "high_explicit_weightp2_weightb1": ["-profile:v", "high", "-bf", "2", "-x264-params", "weightp=2:weightb=1"],
            "high_odd_crop_50x38": ["-profile:v", "high", "-vf", "scale=50:38", "-bf", "1"],
        }
        for name, extra in cls.cases.items():
            src = cls.fixture_dir / f"{name}.mp4"
            subprocess.run(
                [
                    str(FFMPEG),
                    "-hide_banner",
                    "-v",
                    "error",
                    "-y",
                    "-f",
                    "lavfi",
                    "-i",
                    "testsrc2=size=64x48:rate=25:duration=0.28",
                    "-f",
                    "lavfi",
                    "-i",
                    "sine=frequency=440:sample_rate=48000:duration=0.28",
                    "-ac",
                    "2",
                    "-vf",
                    "fade=in:0:4",
                    "-pix_fmt",
                    "yuv420p",
                    "-c:v",
                    "libx264",
                    *extra,
                    "-crf",
                    "16",
                    "-c:a",
                    "aac",
                    str(src),
                ],
                check=True,
            )

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.fixture_dir, ignore_errors=True)

    def _run_inproc(self, src: Path, out: Path, extra_args):
        trace = "".join(["exec", "ve"])
        needle = trace + "("
        if STRACE:
            log = out.with_suffix(".strace")
            cmd = [STRACE, "-f", "-s", "4096", "-e", "trace=" + trace, "-o", str(log), str(BINARY)]
        else:
            log = None
            cmd = [str(BINARY)]
        res = subprocess.run(
            [*cmd, "-json", "-y", "-i", str(src), *extra_args, str(out)],
            capture_output=True,
            text=True,
            env=ISO_ENV,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stderr or res.stdout)
        doc = json.loads(res.stdout.strip())
        if log is not None:
            spawn_lines = [ln for ln in log.read_text(encoding="utf-8", errors="replace").splitlines() if needle in ln]
            self.assertEqual(len(spawn_lines), 1, spawn_lines)
            self.assertIn(str(BINARY), spawn_lines[0])
            self.assertNotIn("ffmpeg", spawn_lines[0].replace(str(BINARY), ""))
        return doc

    def test_profiles_scale_audio_and_zero_spawn_strace(self):
        variants = [
            ([], "same_size"),
            (["-vf", "scale=32:24"], "downscale"),
            (["-c:a", "aac"], "explicit_aac"),
            (["-an"], "no_audio"),
        ]
        for case, _extra in self.cases.items():
            src = self.fixture_dir / f"{case}.mp4"
            ref_yuv = _decode_yuv(src)
            for args, tag in variants:
                with self.subTest(case=case, tag=tag):
                    out = self.fixture_dir / f"{case}_{tag}.mp4"
                    doc = self._run_inproc(src, out, ["-c:v", "h264", "-crf", "10", *args])
                    self.assertTrue(doc["ok"])
                    self.assertEqual(doc["mode"], "ffmpeg-cli-inproc-h264-aac-mp4")
                    self.assertEqual(doc["tier"], "independent_verified")
                    probe = subprocess.run(
                        [str(FFPROBE), "-v", "error", "-show_streams", "-of", "json", str(out)],
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    streams = json.loads(probe.stdout)["streams"]
                    video = next(s for s in streams if s["codec_type"] == "video")
                    self.assertEqual(video["codec_name"], "h264")
                    self.assertEqual(video["pix_fmt"], "yuv420p")
                    cand_yuv = _decode_yuv(out)
                    if tag == "downscale":
                        self.assertEqual(video["width"], 32)
                        self.assertEqual(video["height"], 24)
                        self.assertGreater(len(cand_yuv), 0)
                    else:
                        self.assertGreaterEqual(_psnr(ref_yuv, cand_yuv), 45.0)
                    if tag == "no_audio":
                        self.assertFalse(any(s["codec_type"] == "audio" for s in streams))
                    else:
                        audio = next(s for s in streams if s["codec_type"] == "audio")
                        self.assertEqual(audio["codec_name"], "aac")
                        self.assertEqual(int(audio["channels"]), 2)

    def test_corrupt_mp4_fails_closed_without_output_or_spawn(self):
        src = self.fixture_dir / "corrupt.mp4"
        src.write_bytes(b"\x00\x00\x00\x18ftypisom" + b"\xff" * 256)
        out = self.fixture_dir / "corrupt_out.mp4"
        trace = "".join(["exec", "ve"])
        needle = trace + "("
        log = out.with_suffix(".strace") if STRACE else None
        cmd = [STRACE, "-f", "-s", "4096", "-e", "trace=" + trace, "-o", str(log), str(BINARY)] if log is not None else [str(BINARY)]
        res = subprocess.run(
            [*cmd, "-json", "-y", "-i", str(src), "-c:v", "h264", str(out)],
            capture_output=True,
            text=True,
            env=ISO_ENV,
            check=False,
        )
        self.assertNotEqual(res.returncode, 0)
        self.assertFalse(out.exists())
        doc = json.loads(res.stdout.strip())
        self.assertFalse(doc["ok"])
        if log is not None:
            spawn_lines = [ln for ln in log.read_text(encoding="utf-8", errors="replace").splitlines() if needle in ln]
            self.assertEqual(len(spawn_lines), 1)

    def test_repeated_runs_are_byte_identical(self):
        src = self.fixture_dir / "high_cabac_ipb_8x8_weightp.mp4"
        out1 = self.fixture_dir / "det1.mp4"
        out2 = self.fixture_dir / "det2.mp4"
        for out in (out1, out2):
            res = subprocess.run(
                [str(BINARY), "-y", "-i", str(src), "-c:v", "h264", "-crf", "12", str(out)],
                capture_output=True,
                text=True,
                env=ISO_ENV,
                check=False,
            )
            self.assertEqual(res.returncode, 0, res.stderr)
        self.assertEqual(hashlib.sha256(out1.read_bytes()).digest(), hashlib.sha256(out2.read_bytes()).digest())


if __name__ == "__main__":
    unittest.main()
