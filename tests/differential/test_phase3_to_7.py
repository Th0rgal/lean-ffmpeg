import concurrent.futures
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
REFERENCE = Path("/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg")
FFPROBE = Path("/tmp/opencode/ffmpeg-runtime-full/bin/ffprobe")
FIXTURE_AV = ROOT / "tests" / "differential" / "fixtures" / "input-av.mp4"


def runtime_env():
    env = os.environ.copy()
    lib_dirs = [
        "/tmp/opencode/ffmpeg-runtime-full/lib",
        "/tmp/opencode/ffmpeg-runtime-full/lib/x86_64-linux-gnu",
    ]
    existing_ld = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = ":".join(lib_dirs + ([existing_ld] if existing_ld else []))
    env["PATH"] = f"/tmp/opencode/ffmpeg-runtime-full/bin:{env.get('PATH', '')}"
    return env


class Phase3To7Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not REFERENCE.is_file() or not os.access(REFERENCE, os.X_OK):
            raise unittest.SkipTest("reference FFmpeg is unavailable")
        if not FFPROBE.is_file() or not os.access(FFPROBE, os.X_OK):
            raise unittest.SkipTest("reference FFprobe is unavailable")
        if not FIXTURE_AV.is_file():
            raise unittest.SkipTest("input-av.mp4 fixture is unavailable")

    def run_cmd(self, argv):
        return subprocess.run(
            [str(x) for x in argv],
            capture_output=True,
            text=True,
            check=False,
            env=runtime_env(),
        )

    def probe_json(self, media_path: Path):
        res = self.run_cmd([
            FFPROBE,
            "-v", "error",
            "-show_format",
            "-show_streams",
            "-of", "json",
            media_path,
        ])
        self.assertEqual(res.returncode, 0, res.stderr)
        return json.loads(res.stdout)

    # -------------------------------------------------------------------------
    # Phase 3 (Wave D): Typed MediaPlanIR Inspection, Validation & Round-Trip
    # -------------------------------------------------------------------------
    def test_phase3_plan_ir_serialization_and_validation(self):
        res_valid = self.run_cmd([
            BINARY, "plan",
            "-y", "-i", str(FIXTURE_AV),
            "-map", "0:v:0", "-map", "0:a:0?",
            "-metadata", "title=LeanAV_IR_Test",
            "-bsf:v", "null",
            "-c:v", "copy", "-c:a", "copy",
            "out.mkv",
        ])
        self.assertEqual(res_valid.returncode, 0, res_valid.stderr)
        doc = json.loads(res_valid.stdout.strip())
        self.assertEqual(doc["kind"], "MediaPlanIR")
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["backend"]["tier"], "delegated_faithful")
        self.assertTrue(doc["backend"]["delegated_container"])
        self.assertEqual(doc["maps"], ["0:v:0", "0:a:0?"])
        self.assertEqual(doc["metadata"]["entries"], [{"key": "title", "value": "LeanAV_IR_Test"}])
        self.assertEqual(doc["graphs"]["bitstream_filters"], [{"stream": "v", "filter": "null"}])

        # Also verify `-dump-plan` via direct CLI invocation
        res_dump = self.run_cmd([
            BINARY, "-dump-plan",
            "-y", "-i", str(FIXTURE_AV), "-c", "copy", "out.mp4",
        ])
        self.assertEqual(res_dump.returncode, 0, res_dump.stderr)
        doc_dump = json.loads(res_dump.stdout.strip())
        self.assertEqual(doc_dump["kind"], "MediaPlanIR")
        self.assertTrue(doc_dump["ok"])

        # Pre-execution validation fails closed on invalid plans
        invalid_cases = [
            ["-y", "-i", str(FIXTURE_AV), "-c", "copy", "-vf", "hflip", "out.mp4"],
            ["-y", "-i", str(FIXTURE_AV), "-map", "invalid_map", "-c", "copy", "out.mp4"],
            ["-y", "-i", "http://evil.example/stream.mp4", "-c", "copy", "out.mp4"],
            ["-y", "-ss", "4294968", "-i", str(FIXTURE_AV), "-c", "copy", "out.mp4"],
        ]
        for args in invalid_cases:
            with self.subTest(args=args):
                res_bad = self.run_cmd([BINARY, "plan", *args])
                self.assertNotEqual(res_bad.returncode, 0)
                bad_doc = json.loads(res_bad.stdout.strip())
                self.assertFalse(bad_doc["ok"])

    # -------------------------------------------------------------------------
    # Phase 4 (Waves E & F): Delegated Containers, Maps, Metadata, BSF & Security
    # -------------------------------------------------------------------------
    def test_phase4_delegated_containers_maps_metadata_differential_parity(self):
        with tempfile.TemporaryDirectory(prefix="phase4-delegated-") as tmp:
            root = Path(tmp)

            # 1. Matroska (.mkv) remux with -map, -metadata, -bsf:v null
            ref_mkv = root / "ref.mkv"
            cand_mkv = root / "cand.mkv"
            common_mkv_args = [
                "-y", "-i", str(FIXTURE_AV),
                "-map", "0:v:0", "-map", "0:a:0?",
                "-metadata", "title=MaxwellPhase4",
                "-bsf:v", "null",
                "-c:v", "copy", "-c:a", "copy",
            ]
            r_ref = self.run_cmd([REFERENCE, "-v", "error", *common_mkv_args, str(ref_mkv)])
            r_cand = self.run_cmd([BINARY, "-json", *common_mkv_args, str(cand_mkv)])
            self.assertEqual(r_ref.returncode, 0, r_ref.stderr)
            self.assertEqual(r_cand.returncode, 0, r_cand.stderr)
            cand_doc = json.loads(r_cand.stdout.strip())
            self.assertTrue(cand_doc["ok"])
            self.assertEqual(cand_doc["tier"], "delegated_faithful")
            self.assertEqual(r_cand.stderr, "")

            probe_ref = self.probe_json(ref_mkv)
            probe_cand = self.probe_json(cand_mkv)
            self.assertEqual(len(probe_ref["streams"]), len(probe_cand["streams"]))
            self.assertEqual(
                [s["codec_name"] for s in probe_ref["streams"]],
                [s["codec_name"] for s in probe_cand["streams"]],
            )
            self.assertEqual(
                probe_cand["format"].get("tags", {}).get("TITLE")
                or probe_cand["format"].get("tags", {}).get("title"),
                "MaxwellPhase4",
            )

            # 2. WAV (.wav) and FLAC (.flac) audio extraction
            for ext, codec in (("wav", "pcm_s16le"), ("flac", "flac")):
                with self.subTest(container=ext):
                    ref_aud = root / f"ref.{ext}"
                    cand_aud = root / f"cand.{ext}"
                    aud_args = ["-y", "-i", str(FIXTURE_AV), "-vn", "-c:a", codec]
                    self.assertEqual(self.run_cmd([REFERENCE, "-v", "error", *aud_args, str(ref_aud)]).returncode, 0)
                    r_ca = self.run_cmd([BINARY, "-json", *aud_args, str(cand_aud)])
                    self.assertEqual(r_ca.returncode, 0, r_ca.stderr)
                    p_ref = self.probe_json(ref_aud)
                    p_cand = self.probe_json(cand_aud)
                    self.assertEqual(p_ref["streams"][0]["codec_name"], p_cand["streams"][0]["codec_name"])
                    self.assertEqual(p_ref["streams"][0]["sample_rate"], p_cand["streams"][0]["sample_rate"])
                    self.assertEqual(p_ref["streams"][0]["channels"], p_cand["streams"][0]["channels"])

            # 3. Null muxer (`-f null -`)
            r_null = self.run_cmd([BINARY, "-json", "-y", "-i", str(FIXTURE_AV), "-f", "null", "-"])
            self.assertEqual(r_null.returncode, 0, r_null.stderr)
            self.assertTrue(json.loads(r_null.stdout.strip())["ok"])

    def test_phase4_protocol_allowlist_and_mutant_flags_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="phase4-security-") as tmp:
            out_path = Path(tmp) / "out.mp4"
            unsafe_inputs = [
                "http://127.0.0.1:8080/video.mp4",
                "https://example.com/video.mp4",
                "rtsp://10.0.0.1/live",
                "tcp://127.0.0.1:9000",
                "/dev/video0",
                "lavfi:testsrc",
                "../outside_traversal.mp4",
            ]
            for unsafe_in in unsafe_inputs:
                with self.subTest(unsafe_input=unsafe_in):
                    res = self.run_cmd([BINARY, "-json", "-y", "-i", unsafe_in, "-c", "copy", str(out_path)])
                    self.assertNotEqual(res.returncode, 0)
                    doc = json.loads(res.stdout.strip())
                    self.assertFalse(doc["ok"])
                    self.assertEqual(res.stderr, "")
                    self.assertFalse(out_path.exists())

            mutant_flags = [
                ["-map", "0:x:0"],
                ["-map"],
                ["-metadata", "=missing_key"],
                ["-metadata", "no_equals"],
                ["-bsf:v", "nonexistent_bsf"],
                ["-c:s", "nonexistent_sub_codec"],
            ]
            for mflags in mutant_flags:
                with self.subTest(mutant=mflags):
                    res = self.run_cmd([
                        BINARY, "-json", "-y", "-i", str(FIXTURE_AV), *mflags, "-c", "copy", str(out_path)
                    ])
                    self.assertNotEqual(res.returncode, 0)
                    doc = json.loads(res.stdout.strip())
                    self.assertFalse(doc["ok"])
                    self.assertEqual(res.stderr, "")
                    self.assertFalse(out_path.exists())

    # -------------------------------------------------------------------------
    # Phase 5 (Wave G): Pinned C-ABI FFI Facade & Multi-Process Concurrency
    # -------------------------------------------------------------------------
    def test_phase5_ffi_abi_verification_and_concurrency(self):
        res = self.run_cmd([BINARY, "verify-ffi", str(FIXTURE_AV)])
        self.assertEqual(res.returncode, 0, res.stderr)
        doc = json.loads(res.stdout.strip())
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["phase"], 5)
        self.assertEqual(doc["abi_version"], "0x00010005")
        self.assertTrue(doc["abi_ok"])
        self.assertTrue(doc["cancel_gate_ok"])
        self.assertTrue(doc["corrupt_rejected"])
        self.assertTrue(doc["mp4_probe_ok"])
        self.assertGreater(doc["mp4_width"], 0)
        self.assertGreater(doc["mp4_height"], 0)
        self.assertTrue(doc["plane_ffi_contract_ok"])

        # Concurrent multi-worker stress test (4 parallel transcode/remux jobs)
        with tempfile.TemporaryDirectory(prefix="phase5-concurrent-") as tmp:
            root = Path(tmp)

            def worker(idx: int):
                out_file = root / f"worker-{idx}.mp4"
                r = self.run_cmd([BINARY, "-json", "-y", "-i", str(FIXTURE_AV), "-c", "copy", str(out_file)])
                return r.returncode, out_file.is_file() and out_file.stat().st_size > 0

            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                results = list(pool.map(worker, range(4)))
            for rc, exists_nonempty in results:
                self.assertEqual(rc, 0)
                self.assertTrue(exists_nonempty)

    # -------------------------------------------------------------------------
    # Phase 6 (Wave H): Bounded Independent Verified Kernels & Fallback
    # -------------------------------------------------------------------------
    def test_phase6_independent_verified_kernels(self):
        res = self.run_cmd([BINARY, "verify-kernels"])
        self.assertEqual(res.returncode, 0, res.stderr)
        doc = json.loads(res.stdout.strip())
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["phase"], 6)
        self.assertTrue(doc["rescale_kernel_ok"])
        self.assertTrue(doc["scale2x2_kernel_ok"])
        self.assertTrue(doc["ivf_demux_kernel_ok"])
        self.assertGreaterEqual(doc["bench_us"], 0)

    # -------------------------------------------------------------------------
    # Phase 7 & §11: Contracts & Campaign Closure Dossier Completeness
    # -------------------------------------------------------------------------
    def test_phase7_contracts_and_closure_dossier_present(self):
        contracts_dir = ROOT / "docs" / "contracts"
        expected_contracts = [
            "platform-qualification.json",
            "quorum-wave-a.json",
            "timing-seek.json",
            "phase3-ir-schema.json",
            "phase4-delegated-coverage.json",
            "phase5-ffi-abi-boundary.json",
            "phase6-independent-kernels.json",
            "phase7-promotion-and-rollback.json",
        ]
        for name in expected_contracts:
            with self.subTest(contract=name):
                path = contracts_dir / name
                self.assertTrue(path.is_file(), f"Missing contract: {path}")
                payload = json.loads(path.read_text(encoding="utf-8"))
                self.assertIn("schema_version", payload)

        dossier = ROOT / "docs" / "CAMPAIGN_CLOSURE_DOSSIER.md"
        self.assertTrue(dossier.is_file(), "Missing docs/CAMPAIGN_CLOSURE_DOSSIER.md")
        text = dossier.read_text(encoding="utf-8")
        for section in ("Phase 0", "Phase 1", "Phase 2", "Phase 3", "Phase 4", "Phase 5", "Phase 6", "Phase 7"):
            self.assertIn(section, text)

    # -------------------------------------------------------------------------
    # 3-Model Quorum Audit Regressions (Claude Fable 5.1, GPT-6 Astra, Gemini 4 Argon)
    # -------------------------------------------------------------------------
    def test_quorum_ffmpeg_parity_and_security_hardening(self):
        with tempfile.TemporaryDirectory(prefix="quorum-parity-") as tmp:
            root = Path(tmp)

            # 1. Mixed video filter + audio copy (-vf scale=160:90 -c:v h264 -c:a copy)
            mixed_out = root / "mixed_vf_acopy.mp4"
            r_mixed = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(FIXTURE_AV),
                "-vf", "scale=160:90", "-c:v", "h264", "-c:a", "copy", str(mixed_out),
            ])
            self.assertEqual(r_mixed.returncode, 0, r_mixed.stderr)
            mixed_probe = self.probe_json(mixed_out)
            v_streams = [s for s in mixed_probe["streams"] if s["codec_type"] == "video"]
            a_streams = [s for s in mixed_probe["streams"] if s["codec_type"] == "audio"]
            self.assertEqual((v_streams[0]["width"], v_streams[0]["height"]), (160, 90))
            self.assertEqual(len(a_streams), 1)

            # 2. Mixed video copy + audio re-encode (-c:v copy -c:a aac)
            vcopy_aenc = root / "vcopy_aenc.mp4"
            r_vcopy = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(FIXTURE_AV),
                "-c:v", "copy", "-c:a", "aac", str(vcopy_aenc),
            ])
            self.assertEqual(r_vcopy.returncode, 0, r_vcopy.stderr)

            # 3. Fractional leading zeros in duration (-t 0.0050 -> "0.005", matching ffmpeg packet count)
            ref_frac = root / "ref_frac.mkv"
            cand_frac = root / "cand_frac.mkv"
            r_ref_frac = self.run_cmd([
                REFERENCE, "-v", "error", "-y", "-i", str(FIXTURE_AV),
                "-t", "0.0050", "-c", "copy", str(ref_frac),
            ])
            r_cand_frac = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(FIXTURE_AV),
                "-t", "0.0050", "-c", "copy", str(cand_frac),
            ])
            self.assertEqual(r_ref_frac.returncode, 0, r_ref_frac.stderr)
            self.assertEqual(r_cand_frac.returncode, 0, r_cand_frac.stderr)
            self.assertEqual(ref_frac.stat().st_size, cand_frac.stat().st_size)

            # 4. Sexagesimal and millisecond time syntax (-ss 00:00:00.5 -t 500ms)
            time_out = root / "time_syntax.mp4"
            r_time = self.run_cmd([
                BINARY, "-json", "-y", "-ss", "00:00:00.5", "-t", "500ms",
                "-i", str(FIXTURE_AV), "-c:v", "h264", "-c:a", "aac", str(time_out),
            ])
            self.assertEqual(r_time.returncode, 0, r_time.stderr)

            # 5. Stream mapping (-map 0 and -map 0:1) and .mov container output
            mov_out = root / "mapped.mov"
            r_mov = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(FIXTURE_AV),
                "-map", "0", "-c", "copy", str(mov_out),
            ])
            self.assertEqual(r_mov.returncode, 0, r_mov.stderr)
            self.assertEqual(len(self.probe_json(mov_out)["streams"]), 2)

            # 6. MP4 stream copy size parity (no 256 KB moov bloat)
            copy_mp4 = root / "copy.mp4"
            r_copy = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(FIXTURE_AV), "-c", "copy", str(copy_mp4),
            ])
            self.assertEqual(r_copy.returncode, 0, r_copy.stderr)
            self.assertLess(copy_mp4.stat().st_size, FIXTURE_AV.stat().st_size * 2)

            # 7. Clean JSON error on missing input file (no uncaught exception on stderr)
            missing_in = root / "does_not_exist.mp4"
            missing_out = root / "missing_out.mp4"
            r_missing = self.run_cmd([
                BINARY, "-json", "-y", "-i", str(missing_in), "-c:v", "h264", str(missing_out),
            ])
            self.assertNotEqual(r_missing.returncode, 0)
            self.assertEqual(r_missing.stderr.strip(), "")
            missing_doc = json.loads(r_missing.stdout.strip())
            self.assertFalse(missing_doc["ok"])

            # 8. Protocol/device path hardening (//dev/null, file:///..., pipe:0, data:...)
            for unsafe_path in ("//dev/null", "file:///etc/passwd", "pipe:0", "data:text/plain;base64,AA=="):
                with self.subTest(unsafe_path=unsafe_path):
                    r_unsafe = self.run_cmd([
                        BINARY, "-json", "-y", "-i", unsafe_path, "-c", "copy", str(root / "bad.mp4"),
                    ])
                    self.assertNotEqual(r_unsafe.returncode, 0)
                    unsafe_doc = json.loads(r_unsafe.stdout.strip())
                    self.assertFalse(unsafe_doc["ok"])


if __name__ == "__main__":
    unittest.main()
