"""Signed output timestamp routing: fake backend only, no codec/media claim."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", ROOT / ".lake/build/bin/lffmpeg"))


class OutputTimestampOffsetTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root / "input with spaces.mkv"
        self.source.write_bytes(b"routing placeholder, not media")
        self.output = self.root / "output with spaces.mkv"
        self.log = self.root / "argv.json"
        backend = self.root / "backend.py"
        backend.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['OFFSET_LOG'], 'w') as f: json.dump(sys.argv[1:], f)\n"
            "print('offset-backend-diagnostic', file=sys.stderr)\n"
            "sys.exit(int(os.environ['OFFSET_EXIT']))\n"
        )
        backend.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(backend),
                        OFFSET_LOG=str(self.log), OFFSET_EXIT="0")

    def args(self, value, flag="-output_ts_offset"):
        return ["-i", str(self.source), "-c", "copy", flag, value, str(self.output)]

    def plan(self, args):
        result = subprocess.run([str(BINARY), "--dump-plan", *args], env=self.env,
                                capture_output=True, text=True, timeout=10)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv],
                                env=dict(self.env, OFFSET_EXIT=str(code)),
                                capture_output=True, text=True, timeout=10)
        return result, argv

    def delegated(self, args, code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        result, argv = self.invoke(args, code)
        self.assertEqual(result.returncode, code, result.stderr)
        self.assertEqual(json.loads(self.log.read_text()), argv)
        self.assertIn("offset-backend-diagnostic", result.stderr)
        self.assertFalse(self.output.exists())

    def rejected(self, args):
        result, _ = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        result, _ = self.invoke(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_signed_units_and_colon_values_preserve_exact_arguments(self):
        for value in ("-60ms", "60ms", "0", "-0", "-0.060", "-60000us",
                      "-2.5s", "01:02.5", "-00:00:00.060"):
            with self.subTest(value=value):
                self.delegated(self.args(value))

    def test_repeated_options_and_before_input_position_preserve_order(self):
        self.delegated(["-output_ts_offset", "-60ms", "-i", str(self.source),
                        "-c", "copy", "-output_ts_offset", "0", str(self.output)])

    def test_historical_matroska_option_shape_and_backend_failure(self):
        args = ["-f", "mpegts", "-i", str(self.source), "-c", "copy", "-ss", "1.09",
                "-output_ts_offset", "-60ms", "-f", "matroska", str(self.output)]
        self.delegated(args)
        self.delegated(args, 73)

    def test_missing_empty_and_malformed_values_fail_before_backend(self):
        self.rejected(["-i", str(self.source), str(self.output), "-output_ts_offset"])
        for value in ("", "-", "--60ms", "60msjunk", "1:60", "unknown", "1 2"):
            with self.subTest(value=value):
                self.rejected(self.args(value))

    def test_unknown_spelling_and_bare_negative_value_remain_errors(self):
        for flag in ("-output_ts_offset:v", "-output_ts_offsetx", "--output_ts_offset"):
            with self.subTest(flag=flag):
                self.rejected(self.args("-60ms", flag))
        self.rejected(["-i", str(self.source), "-60ms", str(self.output)])

    def test_shell_values_and_unsafe_media_paths_remain_rejected(self):
        marker = self.root / "must-not-exist"
        for value in (f"-60ms;touch {marker}", f"$(touch {marker})", f"`touch {marker}`"):
            with self.subTest(value=value):
                self.rejected(self.args(value))
                self.assertFalse(marker.exists())
        for path in ("https://example.invalid/media", "../unsafe.mkv", "/dev/zero"):
            with self.subTest(path=path):
                self.rejected(["-i", path, "-output_ts_offset", "-60ms", str(self.output)])
                self.rejected(["-i", str(self.source), "-output_ts_offset", "-60ms", path])

    def test_existing_signed_time_and_translated_plan_are_unchanged(self):
        for flag in ("-itsoffset", "-sseof"):
            with self.subTest(flag=flag):
                self.delegated(self.args("-60ms", flag))
        result, plan = self.plan(["-i", "input.mp4", "-c:v", "h264",
                                  "-vf", "scale=64:48", "output.mp4"])
        self.assertEqual(result.returncode, 0)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "translated_partial")


if __name__ == "__main__":
    unittest.main()
