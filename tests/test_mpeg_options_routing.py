"""Portable production CLI checks using a synthetic backend; no media decoding.

Author-prepared and not executed during staging. After independent review and a
separately authorized build, install under tests/ or set LFFMPEG_BINARY to the
reviewed candidate. The shim records argv and returns the requested status.
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
ATOMS = ("skip_rd", "strict_gop", "qp_rd", "cbp_rd", "naq", "mv0")
FLAGS = ("-mpv_flags", "-intra_vlc", "-data_partitioning")


class MpegOptionsRoutingTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "input.mp4"
        self.source.write_bytes(b"routing-only placeholder; not media")
        self.output = self.root / "output.mp4"
        self.log = self.root / "backend-argv.json"
        shim = self.root / "backend.py"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['MPEG_OPTIONS_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "sys.exit(int(os.environ['MPEG_OPTIONS_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        MPEG_OPTIONS_LOG=str(self.log), MPEG_OPTIONS_EXIT="0")

    def args(self, options):
        return ["-i", str(self.source), "-c:v", "h264", *options, str(self.output)]

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, MPEG_OPTIONS_EXIT=str(code)))
        return result, argv

    def assert_delegated(self, args, pairs):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        self.assertTrue(plan["backend"]["delegated_container"])
        self.assertEqual(plan["mpeg_options"],
                         [{"flag": flag, "value": value} for flag, value in pairs])
        result, argv = self.invoke(args)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(self.log.read_text()), argv)
        self.assertFalse(self.output.exists())

    def assert_rejected(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        result, _ = self.invoke(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_all_atoms_signs_zero_and_combinations(self):
        values = ["0", *ATOMS, *("+" + a for a in ATOMS),
                  *("-" + a for a in ATOMS), "+qp_rd+mv0", "skip_rd-strict_gop+naq",
                  "-cbp_rd+qp_rd-mv0", "+" + "+".join(ATOMS), "mv0+mv0"]
        for value in values:
            with self.subTest(value=value):
                self.assert_delegated(self.args(["-mpv_flags", value]),
                                      [("-mpv_flags", value)])

    def test_both_boolean_values_force_delegation(self):
        for flag in FLAGS[1:]:
            for value in ("0", "1"):
                with self.subTest(flag=flag, value=value):
                    self.assert_delegated(self.args([flag, value]), [(flag, value)])

    def test_repeated_interleaved_options_preserve_exact_argv_and_plan_order(self):
        pairs = [("-mpv_flags", "+qp_rd"), ("-intra_vlc", "0"),
                 ("-mpv_flags", "-qp_rd+mv0"), ("-data_partitioning", "1"),
                 ("-intra_vlc", "1"), ("-mpv_flags", "0"),
                 ("-data_partitioning", "0")]
        options = [token for pair in pairs for token in pair]
        self.assert_delegated(self.args(options), pairs)
        # Original CLI order, including placement around -i and other options.
        args = [*options[:4], "-i", str(self.source), *options[4:8],
                "-c:v", "mpeg4", *options[8:], str(self.output)]
        self.assert_delegated(args, pairs)

    def test_backend_nonzero_propagates(self):
        for flag, value in (("-mpv_flags", "+mv0"), ("-intra_vlc", "1"),
                            ("-data_partitioning", "0")):
            for code in (1, 73):
                with self.subTest(flag=flag, code=code):
                    result, argv = self.invoke(self.args([flag, value]), code)
                    self.assertEqual(result.returncode, code, result.stderr)
                    self.assertEqual(json.loads(self.log.read_text()), argv)
                    self.assertIn("Delegated conversion failed!", result.stderr)
                    self.assertFalse(self.output.exists())

    def test_native_routes_without_options(self):
        for codec in ("h264", "hevc", "av1"):
            with self.subTest(codec=codec):
                result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                          "-vf", "scale=64:48", str(self.output)])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertEqual(plan["mpeg_options"], [])

    def test_mpv_invalid_values_fail_before_backend(self):
        values = ("", "unknown", "MV0", "all", "none", "default", "1", "32", "63",
                  "0x20", "00", "+0", "-0", "0+mv0", "mv0+0", "1<<5", "2*16",
                  "+", "-", "++mv0", "--mv0", "+-mv0", "-+mv0", "mv0++naq",
                  "mv0--naq", "mv0+-naq", "mv0-+naq", "mv0+", "mv0-",
                  "mv0|naq", "mv0,naq", "mv0=1", "mv0/naq", " mv0", "mv0 ",
                  "mv0\t", "mv0\n", "mv0\r", "mv0 naq", "mv0\u00a0", "＋mv0")
        for value in values:
            with self.subTest(value=value):
                self.assert_rejected(self.args(["-mpv_flags", value]))

    def test_boolean_invalid_values_fail_before_backend(self):
        for flag in FLAGS[1:]:
            for value in ("", "true", "false", "yes", "no", "on", "off", "2", "-1",
                          "01", "00", "+1", "1.0", "0x1", "1+0", " 1", "1 ", "1\n"):
                with self.subTest(flag=flag, value=value):
                    self.assert_rejected(self.args([flag, value]))

    def test_missing_values_and_malformed_option_spellings(self):
        for flag in FLAGS:
            with self.subTest(flag=flag):
                self.assert_rejected([*self.args([]), flag])
                self.assert_rejected(self.args([flag, "-intra_vlc", "1"]))
            for spelling in (flag + "=1", flag + ":v", flag + ":0", "-" + flag,
                             flag + "x"):
                with self.subTest(spelling=spelling):
                    self.assert_rejected(self.args([spelling, "1"]))

    def test_shell_strings_are_rejected_without_side_effects(self):
        marker = self.root / "shell-marker"
        for flag in FLAGS:
            for value in (f"mv0;touch {marker}", f"$(touch {marker})",
                          f"`touch {marker}`", f"1 && touch {marker}",
                          f"mv0|touch {marker}", "mv0 -i extra.mp4", "mv0\n-i extra.mp4"):
                with self.subTest(flag=flag, value=value):
                    self.assert_rejected(self.args([flag, value]))
                    self.assertFalse(marker.exists())

    def test_unsafe_paths_still_fail_before_backend(self):
        for flag, value in (("-mpv_flags", "mv0"), ("-intra_vlc", "0"),
                            ("-data_partitioning", "1")):
            for unsafe in ("https://invalid.example/a.mp4", "/dev/video0",
                           "/proc/self/mem", "fixtures/../outside.mp4"):
                for is_input in (True, False):
                    with self.subTest(flag=flag, unsafe=unsafe, is_input=is_input):
                        args = ["-i", unsafe if is_input else str(self.source),
                                flag, value, str(self.output) if is_input else unsafe]
                        self.assert_rejected(args)
                        _, plan = self.plan(args)
                        self.assertIn("unsafe_protocol_or_path_traversal",
                                      plan["backend"]["reasons"])


if __name__ == "__main__":
    unittest.main()
