"""Portable side-data routing checks using a backend that does not read media.

These tests check one-token passthrough and backend status propagation, not
FFmpeg's semantic interpretation of side-data flag expressions.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))
NAMED_VALUES = ("mvs", "prft", "venc_params", "film_grain", "enhancements")
EXPRESSION_VALUES = ("0", "1", "31", "0x4", "-1", "none", "all", "+mvs",
                     "-mvs", "mvs+venc_params", "all-mvs", "2*2")


class ExportSideDataRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise AssertionError(f"reviewed executable required: {BINARY}")

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root / "input with spaces.mp4"
        self.source.write_bytes(b"routing placeholder; not media")
        self.output = self.root / "output with spaces.mp4"
        self.log = self.root / "argv.json"
        shim = self.root / "backend.py"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "args = sys.argv[1:]\n"
            "with open(os.environ['SIDE_DATA_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump({'argv': args, 'argv_hex': [os.fsencode(a).hex() for a in args]}, stream)\n"
            "sys.exit(int(os.environ['SIDE_DATA_ROUTING_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        SIDE_DATA_ROUTING_LOG=str(self.log), SIDE_DATA_ROUTING_EXIT="0")

    def arguments(self, value, before_input=False, flag="-export_side_data"):
        option = [flag, value]
        tail = ["-c:v", "h264", "-vf", "scale=64:48", str(self.output)]
        return (option + ["-i", str(self.source)] + tail if before_input else
                ["-i", str(self.source)] + option + tail)

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, SIDE_DATA_ROUTING_EXIT=str(code)))
        return result, argv

    def assert_exact_argv(self, argv):
        record = json.loads(self.log.read_text())
        self.assertEqual(record["argv"], argv)
        self.assertEqual(record["argv_hex"], [os.fsencode(a).hex() for a in argv])

    def assert_delegated(self, args, code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        self.assertEqual(plan["outputs"][0]["format"], "mp4")
        actual, argv = self.invoke(args, code)
        self.assertEqual(actual.returncode, code, actual.stderr)
        self.assert_exact_argv(argv)
        self.assertEqual(actual.stdout, "")
        self.assertFalse(self.output.exists())

    def assert_rejected(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertGreater(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_all_named_values_delegate_before_and_after_input(self):
        for value in NAMED_VALUES:
            for before_input in (True, False):
                with self.subTest(value=value, before_input=before_input):
                    self.assert_delegated(self.arguments(value, before_input))

    def test_numeric_signed_and_expression_values_remain_single_tokens(self):
        for value in EXPRESSION_VALUES:
            for before_input in (True, False):
                with self.subTest(value=value, before_input=before_input):
                    self.assert_delegated(self.arguments(value, before_input))

    def test_repeated_values_preserve_order_and_neighboring_options(self):
        args = ["-export_side_data", "mvs", "-i", str(self.source),
                "-export_side_data", "none", "-c:v", "h264", "-vf", "scale=64:48",
                "-export_side_data", "+venc_params", str(self.output)]
        self.assert_delegated(args)

    def test_backend_failure_status_is_preserved_in_both_positions(self):
        for code in (1, 73):
            for before_input in (True, False):
                with self.subTest(code=code, before_input=before_input):
                    self.assert_delegated(self.arguments("venc_params", before_input), code)

    def test_missing_and_empty_values_fail_before_backend(self):
        self.assert_rejected(["-i", str(self.source), str(self.output),
                              "-export_side_data"])
        for before_input in (True, False):
            with self.subTest(before_input=before_input):
                self.assert_rejected(self.arguments("", before_input))

    def test_stream_specifier_forms_delegate_before_and_after_input(self):
        for flag in ("-export_side_data:v", "-export_side_data:v:0", "-export_side_data:0"):
            for before_input in (True, False):
                with self.subTest(flag=flag, before_input=before_input):
                    self.assert_delegated(self.arguments("venc_params", before_input, flag))

    def test_stream_specifier_missing_and_empty_values_fail_before_backend(self):
        for flag in ("-export_side_data:v", "-export_side_data:v:0", "-export_side_data:0"):
            with self.subTest(flag=flag):
                self.assert_rejected(["-i", str(self.source), str(self.output), flag])
                self.assert_rejected(self.arguments("", flag=flag))

    def test_malformed_stream_specifier_remains_literal_and_backend_failure_propagates(self):
        marker = self.root / "suffix-shell-marker"
        for flag in ("-export_side_data:bogus", f"-export_side_data:v;touch {marker}"):
            for before_input in (True, False):
                with self.subTest(flag=flag, before_input=before_input):
                    self.assert_delegated(self.arguments("venc_params", before_input, flag), 73)
                    self.assertFalse(marker.exists())

    def test_unknown_and_malformed_flags_fail_before_backend(self):
        for flag in ("-export_side_datax", "--export_side_data", "-EXPORT_SIDE_DATA",
                     "-export_side_data=venc_params", "-export_side_data "):
            for before_input in (True, False):
                with self.subTest(flag=flag, before_input=before_input):
                    self.assert_rejected(self.arguments("venc_params", before_input, flag))

    def test_invalid_values_reach_backend_as_literals_without_shell_effects(self):
        marker = self.root / "shell-marker"
        values = ("unknown_side_data", "venc_params -i extra.mp4", "venc_params,unknown",
                  f"venc_params;touch {marker}", f"$(touch {marker})",
                  f"`touch {marker}`")
        for value in values:
            for before_input in (True, False):
                with self.subTest(value=value, before_input=before_input):
                    # The shim's nonzero status models backend semantic rejection.
                    self.assert_delegated(self.arguments(value, before_input), 1)
                    self.assertFalse(marker.exists())

    def test_shell_like_flag_names_fail_without_side_effects(self):
        marker = self.root / "shell-marker"
        for flag in (f"-export_side_data;touch {marker}",
                     f"-export_side_data$(touch {marker})"):
            with self.subTest(flag=flag):
                self.assert_rejected(self.arguments("venc_params", flag=flag))
                self.assertFalse(marker.exists())

    def test_unsafe_input_and_output_paths_fail_before_backend(self):
        for unsafe in ("https://invalid.example/input", "file:input", "pipe:0",
                       "/dev/video0", "/proc/self/mem", "fixtures/../outside.mp4"):
            for position in ("input", "output"):
                with self.subTest(unsafe=unsafe, position=position):
                    args = (["-export_side_data", "venc_params", "-i", unsafe,
                             "-c:v", "h264", str(self.output)] if position == "input" else
                            ["-i", str(self.source), "-export_side_data", "venc_params",
                             "-c:v", "h264", unsafe])
                    result, plan = self.plan(args)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("unsafe_protocol_or_path_traversal",
                                  plan["backend"]["reasons"])
                    actual, _ = self.invoke(args)
                    self.assertNotEqual(actual.returncode, 0)
                    self.assertFalse(self.log.exists())
                    self.assertFalse(self.output.exists())

    def test_filtergraph_file_option_remains_rejected(self):
        graph = self.root / "graph.txt"
        graph.write_text("null")
        self.assert_rejected(["-i", str(self.source), "-export_side_data", "venc_params",
                              "-/filter_complex", str(graph), str(self.output)])

    def test_native_plan_without_side_data_remains_unchanged(self):
        # Plan only: the placeholder must never be sent through the native route.
        for codec in ("h264", "hevc", "av1"):
            with self.subTest(codec=codec):
                result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                          "-vf", "scale=64:48", str(self.output)])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
                self.assertFalse(self.log.exists())


if __name__ == "__main__":
    unittest.main()
