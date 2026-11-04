"""In-process H.264 + AAC-LC MP4 routing and zero-delegation standalone tests."""
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
ISO_ENV = {**os.environ, "PATH": "/nonexistent"}


class InprocTranscodeRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        cls.fixture_dir = Path(tempfile.mkdtemp(prefix="lean-ffmpeg-inproc-unit-"))
        cls.valid_mp4 = cls.fixture_dir / "valid_h264_aac.mp4"
        res = subprocess.run(
            [
                str(BINARY),
                "-y",
                "-f",
                "lavfi",
                "-i",
                "testsrc=size=32x32:rate=25:duration=0.2",
                "-f",
                "lavfi",
                "-i",
                "sine=frequency=440:sample_rate=48000:duration=0.2",
                str(cls.valid_mp4),
            ],
            env=ISO_ENV,
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode != 0 or not cls.valid_mp4.is_file():
            raise AssertionError(f"native lavfi MP4 fixture synthesis failed: {res.stderr or res.stdout}")
        raw_mp4 = cls.valid_mp4.read_bytes()
        idx = raw_mp4.find(b"avcC")
        if idx < 0 or idx + 14 > len(raw_mp4):
            raise AssertionError("synthesized MP4 missing avcC box")
        # Patch SPS NALU profile_idc=135 (out-of-scope profile) or SPS nal_unit_type invalid/out-of-scope
        # avcC layout at idx+4: [ver=1][prof][compat][lvl][lenSize][numSps=0xE1][spsLenHi][spsLenLo][spsHdr][spsProfileIdc...]
        sps_prof_off = idx + 13
        mp4_10bit = bytearray(raw_mp4)
        mp4_10bit[idx + 5] = 135
        mp4_10bit[sps_prof_off] = 135
        cls.valid_10bit_mp4 = cls.fixture_dir / "valid_10bit.mp4"
        cls.valid_10bit_mp4.write_bytes(bytes(mp4_10bit))

        # High 4:4:4 Predictive (244) with High-extension SPS syntax (triggers parse/scope rejection vs Baseline SPS)
        mp4_444 = bytearray(raw_mp4)
        mp4_444[idx + 5] = 244
        mp4_444[sps_prof_off] = 244
        cls.valid_444_mp4 = cls.fixture_dir / "valid_444.mp4"
        cls.valid_444_mp4.write_bytes(bytes(mp4_444))

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.fixture_dir, ignore_errors=True)

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory(prefix="lean-ffmpeg-inproc-case-")
        self.root = Path(self.temp_dir.name)
        self.log = self.root / "stub-argv.json"
        self.stub = self.root / "ffmpeg"
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
        res = subprocess.run([str(BINARY), "plan", *args], env=ISO_ENV,
                             capture_output=True, text=True, check=False)
        return res, json.loads(res.stdout)

    def test_placeholder_non_mp4_stays_translated_partial_and_fails_closed_on_run(self):
        placeholder = self.root / "placeholder.mp4"
        placeholder.write_bytes(b"not an mp4 container")
        out = self.root / "out.mp4"
        res, plan = self.plan(["-i", str(placeholder), "-c:v", "h264", "-vf", "scale=32:24", str(out)])
        self.assertEqual(res.returncode, 0, res.stdout)
        self.assertEqual(plan["backend"]["tier"], "translated_partial")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertEqual(plan["backend"]["reasons"], ["mp4_seek_or_pixel_simd_transcode"])
        run_res = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(placeholder), "-c:v", "h264", "-vf", "scale=32:24", str(out)],
            env=ISO_ENV,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertNotEqual(run_res.returncode, 0)
        self.assertFalse(out.exists())

    def test_valid_mp4_promotes_h264_aac_to_independent_verified(self):
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
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])
                self.assertEqual(plan["backend"]["reasons"], ["inproc_h264_aac_mp4_transcode"])

    def test_hevc_av1_10bit_444_and_aac_fixed_stay_off_inproc_route_and_fail_closed(self):
        out = self.root / "out.mp4"
        for codec in ("hevc", "av1"):
            res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", codec, str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
            run_res = subprocess.run(
                [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-c:v", codec, str(out)],
                env=ISO_ENV, capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(run_res.returncode, 0)
            self.assertFalse(out.exists())
        for pix in ("yuv420p10le", "p010le"):
            res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", "h264", "-pix_fmt", pix, str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
            run_res = subprocess.run(
                [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-c:v", "h264", "-pix_fmt", pix, str(out)],
                env=ISO_ENV, capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(run_res.returncode, 0)
            self.assertFalse(out.exists())
        for src in (self.valid_10bit_mp4, self.valid_444_mp4):
            res, plan = self.plan(["-i", str(src), "-c:v", "h264", str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "translated_partial")
            run_res = subprocess.run(
                [str(BINARY), "-json", "-y", "-i", str(src), "-c:v", "h264", str(out)],
                env=ISO_ENV, capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(run_res.returncode, 0)
            self.assertFalse(out.exists())
        res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", "h264", "-c:a", "aac_fixed", str(out)])
        self.assertNotEqual(res.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])

    def test_inproc_executes_with_empty_path_and_never_touches_stub(self):
        out = self.root / "inproc_out.mp4"
        env = os.environ.copy()
        env["FAKE_FFMPEG_LOG"] = str(self.log)
        env["PATH"] = str(self.root)
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
        self.assertFalse(self.log.exists(), "in-process transcode must never invoke any external ffmpeg binary")
        self.assertTrue(out.is_file() and out.stat().st_size > 64)


if __name__ == "__main__":
    unittest.main()
