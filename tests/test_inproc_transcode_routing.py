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
                self.assertEqual(plan["backend"]["reasons"], ["unified_media_pipeline"])

    def test_hevc_av1_promote_while_10bit_444_and_aac_fixed_fail_closed(self):
        out = self.root / "out.mp4"
        for codec in ("hevc", "av1"):
            out.unlink(missing_ok=True)
            res, plan = self.plan(["-i", str(self.valid_mp4), "-c:v", codec, str(out)])
            self.assertEqual(res.returncode, 0)
            self.assertEqual(plan["backend"]["tier"], "independent_verified")
            self.assertEqual(plan["backend"]["reasons"], ["unified_media_pipeline"])
            run_res = subprocess.run(
                [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-c:v", codec, str(out)],
                env=ISO_ENV, capture_output=True, text=True, check=False,
            )
            self.assertEqual(run_res.returncode, 0, run_res.stderr or run_res.stdout)
            doc = json.loads(run_res.stdout.strip())
            self.assertTrue(doc["ok"])
            self.assertEqual(doc["mode"], "ffmpeg-cli-unified-pipeline")
            self.assertTrue(out.is_file() and out.stat().st_size > 64)
            out.unlink()
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
        self.assertEqual(doc["mode"], "ffmpeg-cli-unified-pipeline")
        self.assertEqual(doc["tier"], "independent_verified")
        self.assertFalse(self.log.exists(), "in-process transcode must never invoke any external ffmpeg binary")
        self.assertTrue(out.is_file() and out.stat().st_size > 64)

    def test_multi_input_raw_hstack_is_byte_exact_and_reports_filtered_frame_count(self):
        left = self.root / "left.yuv"
        right = self.root / "right.yuv"
        left.write_bytes(bytes([16, 17, 18, 19, 90, 140]) * 2)
        right.write_bytes(bytes([32, 33, 34, 35, 100, 150]) * 2)
        out = self.root / "stacked.yuv"
        args = [
            "-f", "rawvideo", "-s", "2x2", "-i", str(left),
            "-f", "rawvideo", "-s", "2x2", "-i", str(right),
            "-filter_complex", "[0:v:0][1:v:0]hstack=inputs=2[v]",
            "-map", "[v]", "-frames:v", "1", "-f", "rawvideo", str(out),
        ]
        res = subprocess.run([str(BINARY), "-json", "-y", *args], env=ISO_ENV,
                             capture_output=True, text=True, check=False)
        self.assertEqual(res.returncode, 0, res.stderr or res.stdout)
        doc = json.loads(res.stdout)
        self.assertEqual(doc["frames"], 1)
        self.assertEqual(doc["out_bytes"], 12)
        self.assertEqual(out.read_bytes(), bytes([16, 17, 32, 33, 18, 19, 34, 35, 90, 100, 140, 150]))

    def test_multi_input_filter_complex_and_new_routes_execute_and_fail_closed_before_overwrite(self):
        out = self.root / "stacked.mp4"
        args = [
            "-i", str(self.valid_mp4),
            "-i", str(self.valid_mp4),
            "-filter_complex", "[0:v][1:v]hstack=inputs=2[v];[0:a][1:a]amix=inputs=2[a]",
            "-map", "[v]", "-map", "[a]",
            "-c:v", "h264", "-c:a", "aac",
            str(out),
        ]
        res, plan = self.plan(args)
        self.assertEqual(res.returncode, 0, res.stdout)
        self.assertEqual(plan["backend"]["tier"], "independent_verified")
        self.assertEqual(plan["backend"]["reasons"], ["unified_media_pipeline"])
        run_res = subprocess.run([str(BINARY), "-json", "-y", *args], env=ISO_ENV,
                                 capture_output=True, text=True, check=False)
        self.assertEqual(run_res.returncode, 0, run_res.stderr or run_res.stdout)
        doc = json.loads(run_res.stdout.strip())
        self.assertEqual(doc["mode"], "ffmpeg-cli-unified-pipeline")
        self.assertTrue(out.is_file() and out.stat().st_size > 64)

        ogg = self.root / "audio.ogg"
        prores = self.root / "video_prores.mov"
        ts = self.root / "program.ts"
        for target, extra in (
            (ogg, ["-vn", "-af", "volume=volume=0", "-c:a", "opus"]),
            (prores, ["-an", "-c:v", "prores"]),
            (ts, ["-c:v", "h264", "-c:a", "aac"]),
        ):
            r = subprocess.run([str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), *extra, str(target)],
                               env=ISO_ENV, capture_output=True, text=True, check=False)
            self.assertEqual(r.returncode, 0, r.stderr or r.stdout)
            rt = self.root / f"rt_{target.stem}.mp4"
            extra_rt = ["-c:a", "aac"] if target == ogg else ["-c:v", "h264"]
            r2 = subprocess.run([str(BINARY), "-json", "-y", "-i", str(target), *extra_rt, str(rt)],
                                env=ISO_ENV, capture_output=True, text=True, check=False)
            self.assertEqual(r2.returncode, 0, r2.stderr or r2.stdout)
            self.assertTrue(rt.is_file() and rt.stat().st_size > 64)

        nonsilent_ogg = self.root / "nonsilent.ogg"
        r_ns = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-vn", "-c:a", "opus", str(nonsilent_ogg)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertNotEqual(r_ns.returncode, 0, r_ns.stdout)
        self.assertFalse(nonsilent_ogg.exists())

        sentinel = self.root / "existing.mp4"
        sentinel.write_bytes(b"SENTINEL")
        for bad in (
            ["-i", str(self.valid_mp4), "-filter_complex", "[0:v]split=2[v1][v2]", "-map", "[v1]", "-map", "[v2]", "-c:v", "h264", str(sentinel)],
            ["-i", str(self.valid_mp4), "-filter_complex", "[0:v]null[v]", "-map", "[missing]", "-c:v", "h264", str(sentinel)],
            ["-i", str(self.valid_mp4), "-filter_complex", "[0:v][0:v:0]hstack=inputs=2[v]", "-map", "[v]", "-c:v", "h264", str(sentinel)],
        ):
            bad_res = subprocess.run([str(BINARY), *bad], env=ISO_ENV,
                                     capture_output=True, text=True, check=False)
            self.assertNotEqual(bad_res.returncode, 0, (bad, bad_res.stdout, bad_res.stderr))
            self.assertNotIn("Not overwriting", bad_res.stderr + bad_res.stdout)
            self.assertEqual(sentinel.read_bytes(), b"SENTINEL")
        res_s, plan_s = self.plan(["-i", str(self.valid_mp4), "-s", "32x32", "-c:v", "h264", str(out)])
        self.assertEqual(res_s.returncode, 0)
        self.assertNotEqual(plan_s["backend"]["reasons"], ["unified_media_pipeline"])

    def test_vf_fps_ts_timestamps_and_32bit_wav_preservation(self):
        fps50_mp4 = self.root / "fps50.mp4"
        r_fps = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(self.valid_mp4), "-an", "-vf", "fps=50", "-c:v", "h264", str(fps50_mp4)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_fps.returncode, 0, r_fps.stderr or r_fps.stdout)
        fps_doc = json.loads(r_fps.stdout.strip())
        self.assertEqual(fps_doc["frames"], 10)
        mp4_bytes = fps50_mp4.read_bytes()
        mdhd_idx = mp4_bytes.find(b"mdhd")
        self.assertGreater(mdhd_idx, 0)
        timescale = int.from_bytes(mp4_bytes[mdhd_idx + 16:mdhd_idx + 20], "big")
        duration = int.from_bytes(mp4_bytes[mdhd_idx + 20:mdhd_idx + 24], "big")
        self.assertEqual(timescale, 50000)
        self.assertEqual(duration, 10000)

        mp4_30 = self.root / "src30.mp4"
        r_30 = subprocess.run(
            [str(BINARY), "-y", "-f", "lavfi", "-i", "testsrc=size=32x32:rate=30:duration=0.2", str(mp4_30)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_30.returncode, 0, r_30.stderr or r_30.stdout)
        ts_30 = self.root / "src30.ts"
        r_ts = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(mp4_30), "-an", "-c:v", "h264", str(ts_30)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_ts.returncode, 0, r_ts.stderr or r_ts.stdout)
        rt_30 = self.root / "rt30.mp4"
        r_rt30 = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(ts_30), "-c:v", "h264", str(rt_30)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_rt30.returncode, 0, r_rt30.stderr or r_rt30.stdout)
        rt30_bytes = rt_30.read_bytes()
        rt_mdhd = rt30_bytes.find(b"mdhd")
        self.assertGreater(rt_mdhd, 0)
        self.assertEqual(int.from_bytes(rt30_bytes[rt_mdhd + 16:rt_mdhd + 20], "big"), 30000)
        self.assertEqual(int.from_bytes(rt30_bytes[rt_mdhd + 20:rt_mdhd + 24], "big"), 6000)

        s32_raw = self.root / "in.s32"
        samples = [0x12345678, -0x12345678, 0x7FFFFFFF, -0x80000000] * 16
        s32_bytes = b"".join(int(x).to_bytes(4, "little", signed=True) for x in samples)
        s32_raw.write_bytes(s32_bytes)
        wav32 = self.root / "out32.wav"
        r_w32 = subprocess.run(
            [str(BINARY), "-json", "-y", "-f", "s32le", "-ar", "48000", "-ac", "1", "-i", str(s32_raw), str(wav32)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_w32.returncode, 0, r_w32.stderr or r_w32.stdout)
        s32_rt = self.root / "rt.s32"
        r_s32 = subprocess.run(
            [str(BINARY), "-json", "-y", "-i", str(wav32), "-f", "s32le", str(s32_rt)],
            env=ISO_ENV, capture_output=True, text=True, check=False,
        )
        self.assertEqual(r_s32.returncode, 0, r_s32.stderr or r_s32.stdout)
        self.assertEqual(s32_rt.read_bytes(), s32_bytes)


if __name__ == "__main__":
    unittest.main()
