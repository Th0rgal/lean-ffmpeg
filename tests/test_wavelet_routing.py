"""Bounded VC-2 wavelet option routing tests.

These tests prove exact delegated argv handling and fail-closed local grammar.
They do not claim native VC-2 encoding or media correctness; that evidence is
the separate six-target FATE wave.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/lffmpeg"


class WaveletRoutingTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "input.mp4"
        self.source.write_bytes(b"routing-only fixture; not media")
        self.output = self.root / "output.mp4"
        self.log = self.root / "backend-argv.json"
        self.shim = self.root / "backend.py"
        self.shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['WAVELET_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "code = int(os.environ['WAVELET_ROUTING_EXIT'])\n"
            "sys.exit(code)\n"
        )
        self.shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(self.shim),
                        WAVELET_ROUTING_LOG=str(self.log), WAVELET_ROUTING_EXIT="0")

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-n", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, WAVELET_ROUTING_EXIT=str(code)))
        return result, argv

    def assert_delegated(self, args):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        actual, argv = self.invoke(args)
        self.assertEqual(actual.returncode, 0, actual.stderr)
        self.assertEqual(json.loads(self.log.read_text()), argv)
        self.assertFalse(self.output.exists())

    def assert_rejected_before_backend(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(plan["ok"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_four_documented_values_preserve_exact_argv_and_positions(self):
        for value in ("9_7", "5_3", "haar", "haar_noshift"):
            for position in ("before_input", "after_input"):
                args = (["-f", "rawvideo", "-wavelet_type", value, "-i",
                         str(self.source), "-f", "mov", str(self.output)]
                        if position == "before_input" else
                        ["-f", "rawvideo", "-i", str(self.source),
                         "-wavelet_type", value, "-f", "mov", str(self.output)])
                with self.subTest(value=value, position=position):
                    self.assert_delegated(args)

    def test_repeated_values_remain_literal_and_ordered(self):
        self.assert_delegated(["-i", str(self.source), "-wavelet_type", "5_3",
                               "-wavelet_type", "haar", "-f", "mov", str(self.output)])

    def test_unknown_numeric_expression_and_shell_values_fail_closed(self):
        marker = self.root / "shell-marker"
        for value in ("", "0", "2", "7", "9_7+5_3", "vc2", f"$(touch {marker})"):
            with self.subTest(value=value):
                self.assert_rejected_before_backend(["-i", str(self.source),
                                                     "-wavelet_type", value,
                                                     "-f", "mov", str(self.output)])
                self.assertFalse(marker.exists())

    def test_exact_token_and_stream_qualified_variants_are_not_whitelisted(self):
        for token in ("-wavelet_typex", "-wavelet_type:0", "-wavelet_type:v:0"):
            with self.subTest(token=token):
                self.assert_rejected_before_backend(["-i", str(self.source), token,
                                                     "5_3", str(self.output)])

    def test_missing_value_fails_before_backend(self):
        self.assert_rejected_before_backend(["-i", str(self.source), str(self.output),
                                             "-wavelet_type"])

    def test_ordinary_native_routes_remain_separate_from_wavelet_option(self):
        for codec in ("h264", "hevc", "av1"):
            with self.subTest(codec=codec):
                result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                          "-vf", "scale=64:48", str(self.root / "native.mp4")])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
        self.assert_delegated(["-i", str(self.source), "-c:v", "vc2",
                               "-wavelet_type", "5_3", str(self.output)])

    def test_backend_failure_and_unsafe_paths_are_propagated_or_rejected(self):
        args = ["-i", str(self.source), "-wavelet_type", "haar", "-f", "mov",
                str(self.output)]
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        actual, argv = self.invoke(args, code=73)
        self.assertEqual(actual.returncode, 73)
        self.assertEqual(json.loads(self.log.read_text()), argv)
        for unsafe in ("https://invalid.example/input", "/dev/video0", "/proc/self/mem",
                       "fixtures/../outside.yuv"):
            with self.subTest(unsafe=unsafe):
                self.assert_rejected_before_backend(["-i", unsafe, "-wavelet_type",
                                                     "5_3", str(self.output)])
                self.assert_rejected_before_backend(["-i", str(self.source), "-wavelet_type",
                                                     "5_3", "-f", "mov", unsafe])


if __name__ == "__main__":
    unittest.main()
