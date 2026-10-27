import importlib.util
import unittest
import hashlib
import tempfile
from unittest.mock import patch
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "scripts" / "paired_benchmark.py"
spec = importlib.util.spec_from_file_location("paired_benchmark", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class PairedBenchmarkTests(unittest.TestCase):
    def test_trial_order_alternates_and_has_five_pairs(self):
        order = mod.trial_order(5)
        self.assertEqual([x[0] for x in order], ["reference", "candidate", "reference", "candidate", "reference"])
        self.assertEqual([x[1] for x in order], list(range(5)))

    def test_too_few_samples_rejected(self):
        with self.assertRaises(ValueError):
            mod.stats([0.1, 0.2, 0.3, 0.4])
        with self.assertRaises(ValueError):
            mod.trial_order(4)

    def test_both_fail_quality_is_blocked(self):
        failed = {"status": "error", "output": {"exists": False}, "decoded": {"status": "error"}, "probe": {"status": "error"}}
        self.assertEqual(mod.quality_check(failed, failed, "lossless")["reason"], "command_failure")

    def test_missing_output_quality_is_blocked(self):
        missing = {"status": "ok", "output": {"exists": False}, "decoded": {"status": "error"}, "probe": {"status": "error"}}
        self.assertEqual(mod.quality_check(missing, missing, "lossless")["reason"], "missing_output")

    def test_corrupt_decoded_output_is_blocked(self):
        base = {"status": "ok", "output": {"exists": True, "size": 1, "sha256": "a"},
                "decoded": {"status": "ok", "streams": [{"sha256": "decoded-a", "bytes": 1}]},
                "probe": {"status": "ok", "signature": {"duration": "1"}}}
        corrupt = {**base, "decoded": {"status": "ok", "streams": [{"sha256": "decoded-b", "bytes": 1}]}}
        self.assertEqual(mod.quality_check(base, corrupt, "lossless")["reason"], "decoded_digest_mismatch")

    def test_exact_mode_requires_output_digest(self):
        base = {"status": "ok", "output": {"exists": True, "size": 1, "sha256": "a"},
                "decoded": {"status": "ok", "streams": [{"sha256": "decoded", "bytes": 1}]},
                "probe": {"status": "ok", "signature": {"duration": "1"}}}
        different = {**base, "output": {"exists": True, "size": 1, "sha256": "b"}}
        self.assertEqual(mod.quality_check(base, different, "exact")["reason"], "exact_output_digest_mismatch")

    def test_manifest_rejects_incomplete_lossy_and_missing_media(self):
        root = Path("/tmp")
        with self.assertRaises(ValueError):
            mod.validate_manifest({"complete": False, "cases": []}, root, 2, 5)
        with self.assertRaises(ValueError):
            mod.validate_manifest({"complete": True, "cases": [{"id": "x", "mode": "lossy", "input": "missing", "args": ["{INPUT}", "{OUTPUT}"], "delegation_backend": "delegated_ffmpeg", "input_sha256": "0" * 64}]}, root, 2, 5)


    def test_real_execution_loop_alternates_and_pins_threads(self):
        calls = []
        events = []
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); (root / "input.nut").write_bytes(b"input")
            case = {"id": "tiny", "mode": "exact", "input": "input.nut", "input_format": "nut", "input_sha256": hashlib.sha256((root / "input.nut").read_bytes()).hexdigest(), "output_suffix": ".nut",
                    "args": ["-i", "{INPUT}", "-c", "copy", "{OUTPUT}"], "delegation_backend": "delegated_ffmpeg"}
            def command(argv, cwd, env, timeout):
                calls.append(argv)
                events.append("run")
                Path(argv[-1]).write_bytes(b"valid")
                return {"status": "ok", "elapsed_s": 1.0, "returncode": 0, "stdout": b"", "stderr": b""}
            def probe(*args):
                events.append("probe")
                return {"status": "ok", "signature": {"streams": []}}
            with patch.object(mod, "bounded_run", side_effect=command), \
                 patch.object(mod, "normalized_probe", side_effect=probe), \
                 patch.object(mod, "decoded_digest", return_value={"status": "ok", "streams": [{"sha256": "digest", "bytes": 1}]}):
                report = mod.run_case(case, root, "reference", "candidate", "ffprobe", "decoder",
                                      {"OMP_NUM_THREADS": "2"}, 2, 5, 10)
            self.assertEqual([x[0] for x in calls], ["reference", "candidate"] * 2 +
                             ["reference", "candidate", "candidate", "reference", "reference", "candidate",
                              "candidate", "reference", "reference", "candidate"])
            self.assertEqual(len(report["warmups"]), 2)
            self.assertEqual(len(report["trials"]), 5)
            self.assertTrue(all(len(v) == 5 for v in report["raw_times_s"].values()))
            self.assertTrue(all(cmd.count("-threads") == 2 for cmd in calls))
            self.assertTrue(all(cmd.count("-filter_threads") == cmd.count("-filter_complex_threads") == 1 for cmd in calls))
            self.assertTrue(all(cmd[cmd.index("-i") - 2:cmd.index("-i")] == ["-f", "nut"] for cmd in calls))
            self.assertEqual(events, ["run", "run", "probe", "probe"] * 7)
            self.assertFalse(report["gain_above_noise"])  # equality is not a measured speedup

    def test_manifest_rejects_missing_input_and_insufficient_warmups(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            case = {"id": "x", "mode": "lossless", "input": "missing.nut", "input_format": "nut", "output_suffix": ".nut",
                    "args": ["-i", "{INPUT}", "{OUTPUT}"], "delegation_backend": "delegated_ffmpeg", "input_sha256": "0" * 64}
            manifest = {"complete": True, "cases": [case]}
            with self.assertRaisesRegex(ValueError, "input unavailable"):
                mod.validate_manifest(manifest, root, 2, 5)
            with self.assertRaisesRegex(ValueError, "warmups"):
                mod.validate_manifest(manifest, root, 1, 5)

    def test_probe_duration_or_frame_mutant_rejected(self):
        base = {"status": "ok", "output": {"exists": True, "size": 1, "sha256": "same"},
                "decoded": {"status": "ok", "streams": [{"sha256": "same", "bytes": 1}]},
                "probe": {"status": "ok", "signature": {"duration": "2", "nb_read_frames": "60"}}}
        changed = {**base, "probe": {"status": "ok", "signature": {"duration": "1", "nb_read_frames": "30"}}}
        self.assertFalse(mod.quality_check(base, changed, "lossless")["ok"])

    def test_manifest_rejects_auxiliary_input_and_thread_override(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); media = root / "input.nut"; media.write_bytes(b"x")
            base = {"complete": True, "cases": [{"id": "x", "mode": "lossless", "input": "input.nut", "input_format": "nut",
                    "input_sha256": hashlib.sha256(media.read_bytes()).hexdigest(), "output_suffix": ".nut",
                    "args": ["-i", "{INPUT}", "-i", "other.nut", "{OUTPUT}"], "delegation_backend": "delegated_ffmpeg"}]}
            with self.assertRaisesRegex(ValueError, "exactly one"):
                mod.validate_manifest(base, root, 2, 5)
            base["cases"][0]["args"] = ["-i", "{INPUT}", "-c", "copy", "-threads", "2", "{OUTPUT}"]
            with self.assertRaisesRegex(ValueError, "thread"):
                mod.validate_manifest(base, root, 2, 5)

    def test_readfile_filters_and_literal_outputs_rejected(self):
        for args in (["-i", "{INPUT}", "-c", "copy", "-vf", "movie=other.mp4", "{OUTPUT}"],
                     ["-i", "{INPUT}", "-c", "copy", "-filter_complex_script", "graph.txt", "{OUTPUT}"],
                     ["-i", "{INPUT}", "-c", "copy", "extra.nut", "{OUTPUT}"],
                     ["-i", "literal.nut", "{OUTPUT}"]):
            with self.subTest(args=args), self.assertRaises(ValueError):
                mod.validate_args(args, "nut")

    def test_expected_input_hash_required_and_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); media = root / "input.nut"; media.write_bytes(b"pinned")
            case = {"id": "x", "mode": "lossless", "input": "input.nut", "input_format": "nut", "output_suffix": ".nut",
                    "args": ["-i", "{INPUT}", "{OUTPUT}"], "delegation_backend": "delegated_ffmpeg"}
            with self.assertRaisesRegex(ValueError, "input_sha256"):
                mod.validate_manifest({"complete": True, "cases": [case]}, root, 2, 5)
            case["input_sha256"] = hashlib.sha256(b"different").hexdigest()
            with self.assertRaisesRegex(ValueError, "input hash mismatch"):
                mod.validate_manifest({"complete": True, "cases": [case]}, root, 2, 5)

    def test_playlist_and_unknown_input_format_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); media = root / "playlist.m3u8"; media.write_bytes(b"#EXTM3U\nother.ts\n")
            case = {"id": "x", "mode": "exact", "input": media.name, "input_format": "hls",
                    "input_sha256": hashlib.sha256(media.read_bytes()).hexdigest(), "output_suffix": ".nut",
                    "args": ["-i", "{INPUT}", "-c", "copy", "{OUTPUT}"], "delegation_backend": "reference_control"}
            with self.assertRaisesRegex(ValueError, "input_format"):
                mod.validate_manifest({"complete": True, "cases": [case]}, root, 2, 5)
            case["input_format"] = "nut"
            with self.assertRaisesRegex(ValueError, "extension"):
                mod.validate_manifest({"complete": True, "cases": [case]}, root, 2, 5)

    def test_implicit_lossy_or_misordered_codecs_rejected(self):
        for args in (["-i", "{INPUT}", "{OUTPUT}"],
                     ["-i", "{INPUT}", "-c:v", "ffv1", "{OUTPUT}"],
                     ["-i", "{INPUT}", "-c:v", "ffv1", "-c", "copy", "{OUTPUT}"],
                     ["-i", "{INPUT}", "-c", "copy", "-c:v", "libx264", "{OUTPUT}"],
                     ["-f", "hls", "-i", "{INPUT}", "-c", "copy", "{OUTPUT}"]):
            with self.subTest(args=args), self.assertRaises(ValueError):
                mod.validate_args(args, "nut")
        mod.validate_args(["-i", "{INPUT}", "-c", "copy", "-c:v", "rawvideo", "{OUTPUT}"], "nut")


if __name__ == "__main__":
    unittest.main()
