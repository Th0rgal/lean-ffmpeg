"""Portable aac_fixed CLI grammar and fail-closed zero-delegation checks."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/lffmpeg"
SELECTORS = ("-c", "-codec", "-c:a", "-acodec", "-codec:a",
             "-c:a:0", "-codec:a:0")


class AacFixedRoutingTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "input.mp4"
        self.source.write_bytes(b"routing-only placeholder; not media")
        self.output = self.root / "output.mp4"
        self.log = self.root / "backend-argv.json"
        self.shim = self.root / "ffmpeg"
        self.shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['AAC_FIXED_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "sys.exit(0)\n"
        )
        self.shim.chmod(0o755)
        self.env = dict(os.environ, PATH="/nonexistent",
                        AAC_FIXED_ROUTING_LOG=str(self.log))

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
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_input_decoder_selector_spellings_parse_and_fail_closed(self):
        for flag in SELECTORS:
            with self.subTest(flag=flag):
                self.assert_parsed_unsupported_fail_closed(
                    [flag, "aac_fixed", "-i", str(self.source),
                     "-c:a", "pcm_s16le", str(self.output)])

    def test_output_selector_spellings_parse_and_fail_closed(self):
        for flag in SELECTORS:
            with self.subTest(flag=flag):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), flag, "aac_fixed", str(self.output)])

    def test_input_output_and_repeated_selectors_parse_and_fail_closed(self):
        cases = [
            ["-acodec", "aac_fixed", "-i", str(self.source), "-codec:a", "aac",
             str(self.output)],
            ["-c:a", "aac", "-c:a", "aac_fixed", "-i", str(self.source),
             "-c:a", "pcm_s16le", str(self.output)],
            ["-c:a", "aac_fixed", "-i", str(self.source), "-c:a", "aac_fixed",
             "-c:a", "aac", str(self.output)],
            ["-codec:a:0", "aac_fixed", "-i", str(self.source), "-c:v", "copy",
             "-c:a", "aac", str(self.output)],
        ]
        for args in cases:
            with self.subTest(args=args):
                self.assert_parsed_unsupported_fail_closed(args)

    def test_json_fail_closed_diagnostic_for_decoder_and_output_encoder_requests(self):
        for flag in SELECTORS:
            for position in ("input", "output"):
                with self.subTest(flag=flag, position=position):
                    args = ([flag, "aac_fixed", "-i", str(self.source), str(self.output)]
                            if position == "input" else
                            ["-i", str(self.source), flag, "aac_fixed", str(self.output)])
                    result, plan = self.plan(args)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertEqual(plan["backend"]["tier"], "unsupported")
                    self.assertFalse(plan["backend"]["delegated_container"])
                    actual = subprocess.run([str(BINARY), "-json", "-y", *args],
                                            capture_output=True, text=True,
                                            timeout=10, env=self.env)
                    self.assertNotEqual(actual.returncode, 0)
                    doc = json.loads(actual.stdout.strip())
                    self.assertFalse(doc["ok"])
                    self.assertEqual(doc["tier"], "unsupported")
                    self.assertFalse(self.log.exists())
                    self.assertFalse(self.output.exists())

    def test_unknown_empty_missing_and_malformed_codec_values_fail_locally(self):
        for flag in SELECTORS:
            with self.subTest(flag=flag, missing=True):
                self.assert_rejected_parse(
                    ["-i", str(self.source), str(self.output), flag])
            for value in ("", "aac_fixedx", "xaac_fixed", "AAC_FIXED", "aac-fixed",
                          "aac_fixed ", " aac_fixed", "aac_fixed=1", "aac_fixed,copy", "0"):
                for position in ("input", "output"):
                    with self.subTest(flag=flag, value=value, position=position):
                        args = ([flag, value, "-i", str(self.source), str(self.output)]
                                if position == "input" else
                                ["-i", str(self.source), flag, value, str(self.output)])
                        self.assert_rejected_parse(args)
        for flag in ("-acodec_fixed", "-aac_fixed", "-codec_fixed"):
            with self.subTest(flag=flag):
                self.assert_rejected_parse(
                    ["-i", str(self.source), flag, "aac_fixed", str(self.output)])

    def test_shell_like_codec_values_are_rejected_without_side_effects(self):
        marker = self.root / "shell-marker"
        for flag in ("-c", "-c:a", "-acodec", "-c:a:0"):
            for value in (f"aac_fixed;touch {marker}", f"$(touch {marker})",
                          f"aac_fixed`touch {marker}`", "aac_fixed -i extra.mp4",
                          "aac_fixed\n-i extra.mp4"):
                with self.subTest(flag=flag, value=value):
                    self.assert_rejected_parse(
                        [flag, value, "-i", str(self.source), str(self.output)])
                    self.assertFalse(marker.exists())

    def test_unsafe_input_and_output_paths_fail_closed(self):
        for unsafe in ("https://invalid.example/input.mp4", "/dev/video0",
                       "/proc/self/mem", "fixtures/../outside.mp4"):
            for flag in ("-c", "-c:a", "-acodec", "-c:a:0"):
                for position in ("input", "output"):
                    with self.subTest(unsafe=unsafe, flag=flag, position=position):
                        args = ([flag, "aac_fixed", "-i", unsafe, str(self.output)]
                                if position == "input" else
                                ["-i", str(self.source), flag, "aac_fixed", unsafe])
                        result, plan = self.plan(args)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unsafe_protocol_or_path_traversal",
                                      plan["backend"]["reasons"])
                        actual, _ = self.invoke(args)
                        self.assertNotEqual(actual.returncode, 0)
                        self.assertFalse(self.log.exists())
                        self.assertFalse(self.output.exists())

    def test_ordinary_aac_and_native_video_routes_remain_distinct(self):
        for video in ("h264", "hevc", "av1"):
            for audio in (None, "aac"):
                with self.subTest(video=video, audio=audio):
                    args = ["-i", str(self.source), "-c:v", video,
                            "-vf", "scale=64:48"]
                    if audio is not None:
                        args += ["-c:a", audio]
                    result, plan = self.plan([*args, str(self.output)])
                    self.assertEqual(result.returncode, 0, result.stdout)
                    self.assertEqual(plan["backend"]["tier"], "translated_partial")
                    self.assertFalse(plan["backend"]["delegated_container"])
            result, plan = self.plan(["-i", str(self.source), "-c:v", video,
                                      "-vf", "scale=64:48", "-c:a", "aac_fixed",
                                      str(self.output)])
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(plan["backend"]["tier"], "unsupported")
            self.assertFalse(plan["backend"]["delegated_container"])


if __name__ == "__main__":
    unittest.main()
