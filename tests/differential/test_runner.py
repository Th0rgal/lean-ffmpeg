import json
import os
import stat
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import runner


class RunnerTests(unittest.TestCase):
    def make_executable(self, directory, name, body):
        path = Path(directory) / name
        path.write_text("#!/usr/bin/env python3\n" + body, encoding="utf-8")
        path.chmod(path.stat().st_mode | stat.S_IXUSR)
        return path

    def make_fixture(
        self,
        directory,
        args=None,
        output="result.bin",
        inputs=None,
        probe_packets=False,
        probe_frames=False,
        probe_decoded_video=False,
        probe_decoded_audio=False,
    ):
        path = Path(directory) / "fixture.json"
        case = {
            "name": "sample",
            "args": args or [],
            "output": output,
            "probe_packets": probe_packets,
            "probe_frames": probe_frames,
            "probe_decoded_video": probe_decoded_video,
            "probe_decoded_audio": probe_decoded_audio,
        }
        if inputs is not None:
            case["inputs"] = inputs
        path.write_text(json.dumps({"cases": [case]}), encoding="utf-8")
        return path

    def run_capture(self, reference_body, candidate_body, args=None, output="result.bin", inputs=None, **kwargs):
        with tempfile.TemporaryDirectory() as directory:
            reference = self.make_executable(directory, "reference", reference_body)
            candidate = self.make_executable(directory, "candidate", candidate_body)
            if inputs:
                for input_name in inputs:
                    input_path = Path(directory) / input_name
                    input_path.parent.mkdir(parents=True, exist_ok=True)
                    input_path.write_bytes(b"fixture")
            fixture = self.make_fixture(directory, args, output, inputs)
            destination = Path(directory) / "captured"
            result_path = runner.run_fixture(str(reference), str(candidate), None, fixture, destination, **kwargs)
            return json.loads(result_path.read_text(encoding="utf-8"))

    def test_rational_parsing(self):
        self.assertEqual(runner.parse_rational("30000/1001"), {"numerator": 30000, "denominator": 1001})
        self.assertEqual(runner.parse_rational("4/2"), {"numerator": 2, "denominator": 1})
        self.assertIsNone(runner.parse_rational("N/A"))
        self.assertIsNone(runner.parse_rational("not-a-rational"))

    def test_normalized_probe_keeps_absent_nb_frames_as_none(self):
        normalized = runner.normalized_probe({
            "format": {"duration": "1.500000", "start_time": "-0.250000"},
            "streams": [{
                "index": "0",
                "codec_type": "video",
                 "duration": "1.500000",
                 "duration_ts": "135000",
                 "sample_rate": "48000",
                 "channels": "1",
                 "r_frame_rate": "30000/1001",
                "avg_frame_rate": "25/1",
                "time_base": "1/90000",
                "start_time": "-22500",
                "color_space": "bt709",
                "color_range": "tv",
            }],
        })
        stream = normalized["streams"][0]
        self.assertEqual(normalized["format"], {"duration": 1.5, "start_time": -0.25})
        self.assertEqual(stream["time_base"], {"numerator": 1, "denominator": 90000})
        self.assertEqual(stream["r_frame_rate"], {"numerator": 30000, "denominator": 1001})
        self.assertIsNone(stream["nb_frames"])
        self.assertEqual(stream["color_space"], "bt709")
        self.assertEqual(stream["color_range"], "tv")

    def test_normalized_timestamp_summary(self):
        summary = runner.normalized_timestamp_summary({
            "packets": [
                {"pts_time": "0.100", "dts_time": "0.000", "duration_time": "0.040"},
                {"pts_time": "0.140", "dts_time": "0.040", "duration_time": "0.040"},
            ]
        })
        self.assertEqual(summary, {
            "count": 2,
            "first_pts_time": 0.1,
            "last_pts_time": 0.14,
            "first_dts_time": 0.0,
            "last_dts_time": 0.04,
            "duration_time": 0.08,
        })

    def test_normalized_timestamp_summary_consumes_mixed_packets_and_frames(self):
        document = {
            "packets_and_frames": [
                {"type": "packet", "pts_time": "0.100", "dts_time": "0.000", "duration_time": "0.040"},
                {"type": "frame", "best_effort_timestamp_time": "0.100", "duration_time": "0.040"},
                {"type": "packet", "pts_time": "0.140", "dts_time": "0.040", "duration_time": "0.040"},
                {"type": "frame", "pts_time": "0.140", "dts_time": "0.040", "duration_time": "0.040"},
            ]
        }
        self.assertEqual(runner.normalized_timestamp_summary(document, "packet"), {
            "count": 2,
            "first_pts_time": 0.1,
            "last_pts_time": 0.14,
            "first_dts_time": 0.0,
            "last_dts_time": 0.04,
            "duration_time": 0.08,
        })
        self.assertEqual(runner.normalized_timestamp_summary(document, "frame"), {
            "count": 2,
            "first_pts_time": 0.1,
            "last_pts_time": 0.14,
            "first_dts_time": None,
            "last_dts_time": 0.04,
            "duration_time": 0.08,
        })

    def test_timestamp_probe_unavailable_is_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            output = {"exists": False, "path": str(Path(directory) / "missing.mp4")}
            record = runner.probe_timestamps("ffprobe", output, directory, 1, 16, "packets")
            self.assertEqual(record, {"status": "unavailable", "reason": "output does not exist"})

    def test_decoded_probe_unavailable_is_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            output = {"exists": False, "path": str(Path(directory) / "missing.mp4")}
            record = runner.decoded_probe("ffmpeg", output, None, directory, 1, 16, "video", True)
            self.assertEqual(record, {"status": "unavailable", "reason": "output does not exist"})

    def test_decoded_probe_is_diagnostic_only(self):
        comparison = runner.compare_decoded_buffers(
            {"status": "success", "byte_count": 2, "_data": b"ab"},
            {"status": "success", "byte_count": 2, "_data": b"ad"},
        )
        self.assertEqual(comparison["status"], "diagnostic")
        self.assertEqual(comparison["max_absolute_byte_difference"], 2)

    def test_timing_comparator_passes_and_reports_non_timing_diagnostics(self):
        reference = runner.normalized_probe({
            "format": {"duration": "1.000000", "start_time": "0"},
            "streams": [{
                "index": "0",
                "codec_type": "video",
                "duration": "1.000000",
                "r_frame_rate": "30000/1001",
                "avg_frame_rate": "30000/1001",
                "nb_frames": "30",
                "time_base": "1/90000",
                "start_time": "0",
                "color_space": "bt709",
            }],
        })
        candidate = runner.normalized_probe({
            "format": {"duration": "1.000500", "start_time": "0.100000"},
            "streams": [{
                "index": "0",
                "codec_type": "video",
                "duration": "1.000500",
                "r_frame_rate": "30000/1001",
                "avg_frame_rate": "30000/1001",
                "nb_frames": "30",
                "time_base": "1/90000",
                "start_time": "0.100000",
                "color_space": "bt2020",
            }],
        })
        comparison = runner.compare_timing_probes(reference, candidate)
        self.assertEqual(comparison["status"], "pass")
        self.assertEqual(comparison["diagnostics"]["start_time"][0]["field"], "format.start_time")
        self.assertEqual(comparison["diagnostics"]["color"][0]["field"], "stream[0:video].color_space")

    def test_timing_comparator_duration_tolerance(self):
        reference = runner.normalized_probe({"format": {"duration": "2.0"}, "streams": []})
        candidate = runner.normalized_probe({"format": {"duration": "2.0005"}, "streams": []})
        comparison = runner.compare_timing_probes(reference, candidate, duration_tolerance=0.001)
        self.assertEqual(comparison["status"], "pass")
        self.assertEqual(comparison["fields"]["format.duration"]["status"], "pass")

    def test_timing_comparator_missing_data_does_not_fail(self):
        reference = runner.normalized_probe({"format": {}, "streams": [{"index": "0", "codec_type": "video"}]})
        candidate = runner.normalized_probe({"format": {}, "streams": [{"index": "0", "codec_type": "video"}]})
        comparison = runner.compare_timing_probes(reference, candidate)
        self.assertEqual(comparison["status"], "pass")
        self.assertEqual(comparison["fields"]["stream[0:video].nb_frames"]["status"], "missing")

    def test_timing_comparator_frame_count_failure(self):
        reference = runner.normalized_probe({
            "format": {},
            "streams": [{"index": "0", "codec_type": "video", "nb_frames": "30"}],
        })
        candidate = runner.normalized_probe({
            "format": {},
            "streams": [{"index": "0", "codec_type": "video", "nb_frames": "29"}],
        })
        comparison = runner.compare_timing_probes(reference, candidate)
        self.assertEqual(comparison["status"], "fail")
        self.assertEqual(comparison["failures"], ["stream[0:video].nb_frames"])

    def test_success_and_json_persistence(self):
        data = self.run_capture(
            "import pathlib, sys; pathlib.Path(sys.argv[1]).write_bytes(b'ok'); print('ready')",
            "import pathlib, sys; pathlib.Path(sys.argv[1]).write_bytes(b'ok'); print('ready')",
            args=["result.bin"],
        )
        self.assertTrue(data["capture_only"])
        self.assertFalse(data["media_equivalence_claim"])
        self.assertEqual(data["environment_policy"]["locale"], "C")
        self.assertEqual(len(data["records"]), 2)
        self.assertEqual(data["records"][0]["status"], "success")
        self.assertEqual(data["records"][0]["output"]["size"], 2)
        self.assertEqual(data["records"][0]["output"]["sha256"], data["records"][1]["output"]["sha256"])
        self.assertEqual(data["records"][0]["probe"]["status"], "unavailable")
        self.assertEqual(data["records"][0]["timestamp_probe"]["status"], "disabled")

    def test_failure_is_captured(self):
        data = self.run_capture("import sys; print('bad', file=sys.stderr); sys.exit(7)", "print('ok')")
        record = data["records"][0]
        self.assertEqual(record["status"], "failed")
        self.assertEqual(record["exit_status"], 7)
        self.assertEqual(record["stderr"], "bad\n")

    def test_tool_specific_args_are_captured(self):
        with tempfile.TemporaryDirectory() as directory:
            reference = self.make_executable(directory, "reference", "print('reference')")
            candidate = self.make_executable(directory, "candidate", "print('candidate')")
            fixture = Path(directory) / "fixture.json"
            fixture.write_text(json.dumps({
                "cases": [{
                    "name": "specific",
                    "args": [],
                    "reference_args": ["reference-only"],
                    "candidate_args": ["candidate-only"],
                }]
            }), encoding="utf-8")
            data = json.loads(runner.run_fixture(
                str(reference), str(candidate), None, fixture, Path(directory) / "captured"
            ).read_text(encoding="utf-8"))
        self.assertEqual(data["records"][0]["command"][1:], ["reference-only"])
        self.assertEqual(data["records"][1]["command"][1:], ["candidate-only"])

    def test_candidate_cannot_reuse_reference_output(self):
        data = self.run_capture(
            "import pathlib, sys; pathlib.Path(sys.argv[1]).write_bytes(b'reference')",
            "import pathlib, sys; output = pathlib.Path(sys.argv[1]); output.write_bytes(output.read_bytes() if output.exists() else b'candidate')",
            args=["result.bin"],
        )
        reference, candidate = data["records"]
        self.assertEqual(reference["output"]["size"], 9)
        self.assertEqual(candidate["output"]["size"], 9)
        self.assertNotEqual(reference["output"]["sha256"], candidate["output"]["sha256"])
        self.assertNotEqual(reference["output"]["path"], candidate["output"]["path"])

    def test_timeout_is_captured(self):
        data = self.run_capture("import time; time.sleep(1)", "print('ok')", timeout=0.05)
        self.assertEqual(data["records"][0]["status"], "timeout")

    def test_output_limit_is_captured_and_bounded(self):
        data = self.run_capture("print('x' * 100)", "print('ok')", output_limit=16)
        record = data["records"][0]
        self.assertEqual(record["status"], "output_limit")
        self.assertLessEqual(len(record["stdout"].encode()), 16)

    def test_timeout_kills_descendant_process_group(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "child.pid"
            after = Path(directory) / "child.after"
            reference = self.make_executable(
                directory,
                "reference",
                "import os, pathlib, sys, time; child = os.fork(); pathlib.Path(sys.argv[1]).write_text(str(child)); time.sleep(0.4); pathlib.Path(sys.argv[2]).write_text('alive')",
            )
            candidate = self.make_executable(directory, "candidate", "print('ok')")
            fixture = self.make_fixture(directory, args=[str(marker), str(after)])
            data = json.loads(runner.run_fixture(str(reference), str(candidate), None, fixture, Path(directory) / "captured", timeout=0.1).read_text(encoding="utf-8"))
            self.assertEqual(data["records"][0]["status"], "timeout")
            time.sleep(0.6)
            self.assertFalse(after.exists())

    def test_stderr_output_limit_is_bounded_without_artifact(self):
        data = self.run_capture("import sys; sys.stderr.write('x' * 100)", "print('ok')", output_limit=16)
        record = data["records"][0]
        self.assertEqual(record["status"], "output_limit")
        self.assertLessEqual(len(record["stderr"].encode()), 16)
        self.assertFalse(record["output"]["exists"])

    def test_cpu_limit_is_applied(self):
        data = self.run_capture("while True: pass", "print('ok')", timeout=2, cpu_seconds=1)
        self.assertNotEqual(data["records"][0]["status"], "success")
        self.assertFalse(data["records"][0]["output"]["exists"])

    def test_address_space_limit_is_applied(self):
        data = self.run_capture("x = bytearray(64 * 1024 * 1024)", "print('ok')", address_space_bytes=32 * 1024 * 1024)
        self.assertNotEqual(data["records"][0]["status"], "success")
        self.assertFalse(data["records"][0]["output"]["exists"])

    def test_structured_command_uses_isolated_cwd(self):
        data = self.run_capture("import os; print(os.getcwd())", "print('ok')")
        record = data["records"][0]
        self.assertEqual(record["command"][1:], [])
        self.assertIn("/differential-", record["stdout"].strip())
        self.assertIsNotNone(record["executable"]["sha256"])

    def test_output_path_rejects_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            case_dir = Path(directory) / "case"
            case_dir.mkdir()
            for output in ("../outside.bin", "/tmp/outside.bin"):
                with self.assertRaisesRegex(ValueError, "relative path|case directory"):
                    runner.fixture_output_path(case_dir, output)

    def test_declared_input_is_copied_and_rewritten(self):
        data = self.run_capture(
            "import pathlib, sys; pathlib.Path(sys.argv[1]).write_bytes(pathlib.Path(sys.argv[2]).read_bytes())",
            "import pathlib, sys; pathlib.Path(sys.argv[1]).write_bytes(pathlib.Path(sys.argv[2]).read_bytes())",
            args=["result.bin", "fixtures/input.bin"],
            inputs=["fixtures/input.bin"],
        )
        reference, candidate = data["records"]
        self.assertEqual(reference["status"], "success")
        self.assertEqual(reference["output"]["size"], 7)
        self.assertEqual(reference["output"]["sha256"], candidate["output"]["sha256"])
        self.assertTrue(reference["command"][2].endswith("/input.bin"))
        self.assertNotIn("fixtures/input.bin", reference["command"])

    def test_declared_input_rejects_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.make_fixture(directory, args=[], inputs=["../outside.bin"])
            with self.assertRaisesRegex(ValueError, "relative path|fixture directory"):
                runner.run_fixture("true", "true", None, fixture, Path(directory) / "captured")

    def test_child_environment_is_deterministic(self):
        data = self.run_capture(
            "import os; print(sorted(k for k in os.environ if k != '__CF_USER_TEXT_ENCODING'))",
            "import os; print(sorted(k for k in os.environ if k != '__CF_USER_TEXT_ENCODING'))",
        )
        self.assertEqual(data["records"][0]["stdout"], data["records"][1]["stdout"])
        self.assertEqual(
            data["records"][0]["stdout"].strip(),
            "['LANG', 'LC_ALL', 'PATH']" if "LD_LIBRARY_PATH" not in os.environ else "['LANG', 'LC_ALL', 'LD_LIBRARY_PATH', 'PATH']",
        )

    def test_cli_requires_all_explicit_paths(self):
        with self.assertRaises(SystemExit):
            runner.build_parser().parse_args([])


if __name__ == "__main__":
    unittest.main()
