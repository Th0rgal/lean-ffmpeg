"""Portable VVC CLI grammar and fail-closed zero-delegation checks."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/lffmpeg"


class VvcRoutingTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "input.mp4"
        self.source.write_bytes(b"routing-only fixture; not media")
        self.output = self.root / "output.mp4"
        self.log = self.root / "backend-argv.json"
        self.shim = self.root / "ffmpeg"
        self.shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['VVC_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "sys.exit(0)\n"
        )
        self.shim.chmod(0o755)
        self.env = dict(os.environ, PATH="/nonexistent",
                        VVC_ROUTING_LOG=str(self.log))

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

    def assert_parsed_unsupported_fail_closed(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertFalse(plan["ok"])
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertFalse(plan["backend"]["fallback_allowed"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def assert_rejected_parse(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertGreater(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_vvc_codec_input_and_output_selector_spellings_parse_and_fail_closed(self):
        for flag in ("-c:v", "-vcodec", "-codec:v"):
            for position in ("input", "output"):
                with self.subTest(flag=flag, position=position):
                    args = ([flag, "vvc", "-i", str(self.source), str(self.output)]
                            if position == "input" else
                            ["-i", str(self.source), flag, "vvc", str(self.output)])
                    self.assert_parsed_unsupported_fail_closed(args)

    def test_vvc_format_input_and_output_positions_parse_and_fail_closed(self):
        for args in (["-f", "vvc", "-i", str(self.source), "-c", "copy", str(self.output)],
                     ["-i", str(self.source), "-c", "copy", "-f", "vvc", str(self.output)]):
            with self.subTest(args=args):
                self.assert_parsed_unsupported_fail_closed(args)

    def test_vvc_metadata_parameters_and_filter_chains_parse_and_fail_closed(self):
        for value in ("vvc_metadata", "vvc_metadata=aud=pass", "vvc_metadata=aud=insert",
                      "vvc_metadata=aud=remove", "null,vvc_metadata=aud=pass",
                      "vvc_metadata,"):
            for flag in ("-bsf:v", "-bsf:v:0"):
                with self.subTest(flag=flag, value=value):
                    self.assert_parsed_unsupported_fail_closed(
                        ["-i", str(self.source), "-c:v", "copy",
                         flag, value, "-f", "vvc", str(self.output)])

    def test_json_fail_closed_diagnostics_without_claiming_media_success(self):
        cases = [["-i", str(self.source), "-c:v", "vvc", str(self.output)],
                 ["-i", str(self.source), "-c:v", "copy", "-f", "vvc", str(self.output)],
                 ["-i", str(self.source), "-c:v", "copy", "-bsf:v",
                  "vvc_metadata=not_an_option=1", "-f", "vvc", str(self.output)]]
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

    def test_unknown_missing_empty_and_malformed_values_fail_locally(self):
        for flag, values in (("-c:v", ("vvcc", "h266", "libvvenc", "")),
                             ("-f", ("vvcc", "vvcx", "")),
                             ("-bsf:v", ("vvcc_metadata", "vvc_mp4toannexb", "",
                                         "vvc_metadata,,", ",vvc_metadata",
                                         "vvc_metadata,unknown_bsf"))):
            self.assert_rejected_parse(["-i", str(self.source), str(self.output), flag])
            for value in values:
                with self.subTest(flag=flag, value=value):
                    self.assert_rejected_parse(
                        ["-i", str(self.source), flag, value, str(self.output)])

    def test_shell_like_values_are_not_executed_or_split_into_options(self):
        marker = self.root / "shell-marker"
        for flag, value in (("-c:v", f"vvc;touch {marker}"),
                            ("-f", f"$(touch {marker})"),
                            ("-bsf:v", "vvc_metadata -i extra.mp4")):
            with self.subTest(flag=flag):
                self.assert_rejected_parse(
                    ["-i", str(self.source), flag, value, str(self.output)])
                self.assertFalse(marker.exists())
        value = f"vvc_metadata=aud=$(touch {marker})"
        self.assert_parsed_unsupported_fail_closed(
            ["-i", str(self.source), "-c:v", "copy",
             "-bsf:v", value, "-f", "vvc", str(self.output)])
        self.assertFalse(marker.exists())
        self.assertFalse(self.output.exists())

    def test_unsafe_input_and_output_paths_fail_closed(self):
        prefixes = [["-c:v", "vvc"], ["-f", "vvc"], ["-bsf:v", "vvc_metadata"]]
        for unsafe in ("https://invalid.example/input", "/dev/video0", "/proc/self/mem",
                       "fixtures/../outside.mp4"):
            for flags in prefixes:
                for position in ("input", "output"):
                    with self.subTest(unsafe=unsafe, flags=flags, position=position):
                        args = ([*flags, "-i", unsafe, str(self.output)]
                                if position == "input" else
                                ["-i", str(self.source), *flags, unsafe])
                        result, plan = self.plan(args)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unsafe_protocol_or_path_traversal", plan["backend"]["reasons"])
                        actual, _ = self.invoke(args)
                        self.assertNotEqual(actual.returncode, 0)
                        self.assertFalse(self.log.exists())

    def test_input_format_does_not_supply_output_format_or_extension_inference(self):
        for suffix in (".unrecognized", ".vvc", ".h266", ".266"):
            with self.subTest(suffix=suffix):
                result, plan = self.plan(["-f", "vvc", "-i", str(self.source),
                                          str(self.root / ("output" + suffix))])
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unrecognized_output_container_format", plan["backend"]["reasons"])
        self.assert_rejected_parse(["-f", "vvc", "-i", str(self.source),
                                    "-f", "not_a_format", str(self.output)])

    def test_existing_native_route_remains_distinct_from_vvc(self):
        for codec in ("h264", "hevc", "av1"):
            with self.subTest(codec=codec):
                result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                          "-vf", "scale=64:48", str(self.output)])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
                self.assertFalse(plan["backend"]["delegated_container"])
        for value in ("null", "h264_metadata", "hevc_metadata"):
            result, plan = self.plan(["-i", str(self.source), "-c:v", "copy",
                                      "-bsf:v", value, str(self.output)])
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(plan["backend"]["tier"], "unsupported")
            self.assertFalse(plan["backend"]["delegated_container"])


if __name__ == "__main__":
    unittest.main()
