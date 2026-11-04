"""Portable SPDIF CLI grammar and fail-closed zero-delegation checks."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))


class SpdifRoutingTests(unittest.TestCase):
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
        shim = self.root / "ffmpeg"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['SPDIF_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "sys.exit(0)\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, PATH="/nonexistent",
                        SPDIF_ROUTING_LOG=str(self.log))

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, argv

    def assert_parsed_unsupported_fail_closed(self, args, output_format):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertFalse(plan["ok"])
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertFalse(plan["backend"]["fallback_allowed"])
        self.assertEqual(plan["outputs"][0]["format"], output_format)
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())
        if args[-1] != "-":
            self.assertFalse(Path(args[-1]).exists())

    def assert_rejected(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertGreater(plan["error_count"], 0)
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_explicit_output_format_parses_and_fails_closed_for_file_and_stdout(self):
        for output in (str(self.output), str(self.root / "output.spdif"),
                       str(self.root / "output.bin"), "-"):
            with self.subTest(output=output):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-c", "copy", "-f", "spdif", output],
                    "spdif")

    def test_format_token_before_input_parses_and_fails_closed(self):
        cases = [
            (["-f", "spdif", "-i", str(self.source), "-c", "copy",
              str(self.output)], "mp4"),
            (["-f", "spdif", "-i", str(self.source), "-c", "copy",
              "-f", "framecrc", "-"], "framecrc"),
            (["-f", "aac", "-i", str(self.source), "-c", "copy",
              "-f", "spdif", str(self.output)], "spdif"),
        ]
        for args, output_format in cases:
            with self.subTest(args=args):
                self.assert_parsed_unsupported_fail_closed(args, output_format)

    def test_repeated_formats_preserve_final_output_format_and_fail_closed(self):
        for first, second in (("wav", "spdif"), ("spdif", "wav")):
            with self.subTest(first=first, second=second):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-c", "copy",
                     "-f", first, "-f", second, str(self.output)], second)

    def test_json_fail_closed_diagnostics_for_input_and_output_formats(self):
        cases = [
            ["-f", "spdif", "-i", str(self.source), "-c", "copy", str(self.output)],
            ["-i", str(self.source), "-c", "copy", "-f", "spdif", str(self.output)],
        ]
        for args in cases:
            with self.subTest(args=args):
                actual = subprocess.run([str(BINARY), "-json", "-y", *args],
                                        capture_output=True, text=True,
                                        timeout=10, env=self.env)
                self.assertNotEqual(actual.returncode, 0)
                doc = json.loads(actual.stdout.strip())
                self.assertFalse(doc["ok"])
                self.assertEqual(doc["tier"], "unsupported")
                self.assertFalse(self.log.exists())
                self.assertFalse(self.output.exists())

    def test_missing_empty_unknown_and_malformed_formats_fail_parse(self):
        self.assert_rejected(["-i", str(self.source), str(self.output), "-f"])
        for value in ("", "SPDIF", "spdifx", "iec61937", " spdif", "spdif ",
                      "spdif,ac3", "spdif -i extra.mp4"):
            for position in ("input", "output"):
                with self.subTest(value=value, position=position):
                    args = (["-f", value, "-i", str(self.source), str(self.output)]
                            if position == "input" else
                            ["-i", str(self.source), "-f", value, str(self.output)])
                    self.assert_rejected(args)

    def test_shell_like_format_tokens_are_rejected_without_side_effects(self):
        marker = self.root / "shell-marker"
        for value in (f"spdif;touch {marker}", f"$(touch {marker})",
                      f"spdif`touch {marker}`"):
            with self.subTest(value=value):
                self.assert_rejected(["-i", str(self.source), "-f", value,
                                      str(self.output)])
                self.assertFalse(marker.exists())

    def test_unsafe_input_and_output_paths_fail_closed(self):
        for unsafe in ("https://invalid.example/input", "file:input", "pipe:0",
                       "/dev/audio", "/proc/self/mem", "fixtures/../outside"):
            for position in ("input", "output"):
                with self.subTest(unsafe=unsafe, position=position):
                    args = (["-f", "spdif", "-i", unsafe, str(self.output)]
                            if position == "input" else
                            ["-i", str(self.source), "-f", "spdif", unsafe])
                    result, plan = self.plan(args)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("unsafe_protocol_or_path_traversal",
                                  plan["backend"]["reasons"])
                    actual, _ = self.invoke(args)
                    self.assertNotEqual(actual.returncode, 0)
                    self.assertFalse(self.log.exists())
                    self.assertFalse(self.output.exists())

    def test_implicit_spdif_output_extension_remains_unknown_in_plan(self):
        result, plan = self.plan(["-i", str(self.source),
                                  str(self.root / "output.spdif")])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrecognized_output_container_format",
                      plan["backend"]["reasons"])

    def test_spdif_flags_and_dtshd_rate_parse_and_unknown_flag_rejected(self):
        for flag, value in (("-spdif_flags", "+be"), ("-dtshd_rate", "192000"),
                            ("-dtshd_rate", "96000")):
            with self.subTest(flag=flag, value=value):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-c", "copy", flag, value,
                     "-f", "spdif", str(self.output)], "spdif")
        self.assert_rejected(["-i", str(self.source), "-c", "copy",
                              "-spdif_unknown_flag", "1", "-f", "spdif", str(self.output)])

    def test_native_plan_without_explicit_spdif_remains_unchanged(self):
        for codec in ("h264", "hevc", "av1"):
            with self.subTest(codec=codec):
                result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                          "-vf", "scale=64:48", str(self.output)])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(self.log.exists())


if __name__ == "__main__":
    unittest.main()
