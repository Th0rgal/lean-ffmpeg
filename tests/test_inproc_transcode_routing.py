import json
import os
import shutil
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = Path(os.environ.get("FFMPEG", shutil.which("ffmpeg") or "/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg"))


def _ffmpeg_usable() -> bool:
    if not FFMPEG.is_file() or not os.access(FFMPEG, os.X_OK):
        return False
    try:
        res = subprocess.run([str(FFMPEG), "-version"], capture_output=True, text=True, check=True)
        return res.stdout.startswith("ffmpeg version ")
    except (OSError, subprocess.CalledProcessError):
        return False


class InprocTranscodeRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        cls.has_ffmpeg = _ffmpeg_usable()
        cls.fixture_dir = Path(tempfile.mkdtemp(prefix="lean-ffmpeg-inproc-unit-"))
        cls.valid_mp4 = cls.fixture_dir / "valid_h264_aac.mp4"
        cls.valid_10bit_mp4 = cls.fixture_dir / "valid_10bit.mp4"
        cls.valid_444_mp4 = cls.fixture_dir / "valid_444.mp4"
        if cls.has_ffmpeg:
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
                    "testsrc=size=32x32:rate=25:duration=0.2",
                    "-f",
                    "lavfi",
                    "-i",
                    "sine=frequency=440:sample_rate=48000:duration=0.2",
                    "-ac",
                    "2",
                    "-c:v",
                    "libx264",
                    "-profile:v",
                    "high",
                    "-pix_fmt",
                    "yuv420p",
                    "-c:a",
                    "aac",
                    str(cls.valid_mp4),
                ],
                check=True,
            )
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
                    "testsrc=size=32x32:rate=25:duration=0.2",
                    "-c:v",
                    "libx264",
                    "-pix_fmt",
                    "yuv420p10le",
                    str(cls.valid_10bit_mp4),
                ],
                check=True,
            )
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
                    "testsrc=size=32x32:rate=25:duration=0.2",
                    "-c:v",
                    "libx264",
                    "-pix_fmt",
                    "yuv444p",
                    str(cls.valid_444_mp4),
                ],
                check=True,
            )

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.fixture_dir, ignore_errors=True)

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory(prefix="lean-ffmpeg-inproc-case-")
        self.root = Path(self.temp_dir.name)
        self.log = self.root / "delegated-argv.json"
        self.stub = self.root / "fake-ffmpeg"
        self.stub.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "with open(os.environ['FAKE_FFMPEG_LOG'], 'w', encoding='utf-8') as f:\n"
            "    json.dump(sys.argv[1:], f)\n"
            "raise SystemExit(91)\n",
            encoding="utf-8",
        )
        self.stub.chmod(self.stub.stat().st_mode | stat.S_IXUSR)

    def tearDown(self):
        self.temp_dir.cleanup()

    def plan(self, args):
        res = subprocess.run([str(BINARY), "plan", *args], capture_output=True, text=True, check=False)
        return res, json.loads(res.stdout)

    def test_placeholder_non_mp4_stays_translated_partial(self):
        placeholder = self.root / "placeholder.mp4"
        placeholder.write_bytes(b"not an mp4 container")
        out = self.root / "out.mp4"
        res, plan = self.plan(["-i", str(placeholder), "-c:v", "h264", "-vf", "scale=32:24", str(out)])
        self.assertEqual(res.returncode, 0, res.stdout)
        self.assertEqual(plan["backend"]["tier"], "translated_partial")
        self.assertEqual(plan["backend"]["reasons"], ["mp4_seek_or_pixel_simd_transcode"])

    def test_valid_mp4_promotes_h264_aac_to_independent_verified(self):
        if not self.has_ffmpeg:
            self.skipTest("ffmpeg unavailable to synthesize valid MP4 fixture")
        out = self.root / "out.mp4"
        for extra in (
            ["-c:v", "h264"],
            ["-c:v", "h264", "-c:a", "aac"],
            ["-c:v", "h264", "-an"],
            ["-c:v", "h264", "-pix_fmt", "yuv420p", "-vf", "scale=24:16", "-crf", "18"],
        ):
            with self.subTest(extra=extra):
                res, plan = self.plan(["-i", str(self.valid_mp4), *extra, str(out)])
                self.assertEqual(res.returncode, 0, res.stdout)
                self.assertEqual(plan["backend"]["tier"], "independent_verified")
                self.assertFalse(plan["backend"]["fallback_allowed"])
                self.assertEqual(plan["backend"]["reasons"], ["inproc_h264_aac_mp4_transcode"])

    def test_hevc_av1_10bit_444_and_aac_fixed_stay_off_inproc_route(self):
        if not self.has_ffmpeg:
            self.skipTest("ffmpeg unavailable to synthesize valid MP4 fixture")
        out = self.root / "out.mp4"
        for codec in ("hevc", "av1"):
            res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", codec, str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
        for pix in ("yuv420p10le", "p010le"):
            res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", "h264", "-pix_fmt", pix, str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
        for src in (self.valid_10bit_mp4, self.valid_444_mp4):
            res, plan = self.plan(["-i", str(src), "-c:v", "h264", str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
        res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", "h264", "-c:a", "aac_fixed", str(out)])
        self.assertEqual(res.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")

    def test_inproc_executes_with_hostile_ffmpeg_env_and_never_touches_stub(self):
        if not self.has_ffmpeg:
            self.skipTest("ffmpeg unavailable to synthesize valid MP4 fixture")
        out = self.root / "inproc_out.mp4"
        env = os.environ.copy()
        env["FAKE_FFMPEG_LOG"] = str(self.log)
        env["LEANAV_FFMPEG_BIN"] = str(self.stub)
        env["LEANAV_FFPROBE_BIN"] = str(self.stub)
        env["PATH"] = "/nonexistent"
        res = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-c:v", "h264", "-c:a", "aac", str(out)],
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stderr or res.stdout)
        doc = json.loads(res.stdout.strip())
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["mode"], "ffmpeg-cli-inproc-h264-aac-mp4")
        self.assertEqual(doc["tier"], "independent_verified")
        self.assertFalse(self.log.exists(), "in-process transcode must never invoke LEANAV_FFMPEG_BIN")
        self.assertTrue(out.is_file() and out.stat().st_size > 64)


if __name__ == "__main__":
    unittest.main()
