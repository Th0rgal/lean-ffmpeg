"""Production CLI routing for extended pixel formats; the shim reads no media."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))
FORMATS = (
    'ayuv', 'gbrap14be', 'gbrap14le', 'gbrapf32be', 'gbrapf32le',
    'gbrp10msbbe', 'gbrp10msble', 'gbrp12msbbe', 'gbrp12msble', 'gbrpf32be',
    'gbrpf32le', 'grayf32be', 'grayf32le', 'nv20be', 'nv20le',
    'p012be', 'p012le', 'p210be', 'p210le', 'p212be',
    'p212le', 'p216be', 'p216le', 'uyva', 'v30xle',
    'vuya', 'vuyx', 'vyu444', 'x2bgr10le', 'x2rgb10le',
    'xv30le', 'xv36be', 'xv36le', 'xv48be', 'xv48le',
    'y210le', 'y212le', 'y216le', 'yuv440p10be', 'yuv440p10le',
    'yuv440p12be', 'yuv440p12le', 'yuv444p10msbbe', 'yuv444p10msble', 'yuv444p12msbbe',
    'yuv444p12msble', 'yuva420p10be', 'yuva420p10le', 'yuva420p16be', 'yuva420p16le',
    'yuva420p9be', 'yuva420p9le', 'yuva422p10be', 'yuva422p10le', 'yuva422p12be',
    'yuva422p12le', 'yuva422p16be', 'yuva422p16le', 'yuva422p9be', 'yuva422p9le',
    'yuva444p10be', 'yuva444p10le', 'yuva444p12be', 'yuva444p12le', 'yuva444p16be',
    'yuva444p16le', 'yuva444p9be', 'yuva444p9le',
)
FLAGS = ("-pix_fmt", "-pixel_format")


class ExtendedPixelFormatRoutingTests(unittest.TestCase):
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
            "with open(os.environ['PIXEL_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump({'argv': args, 'argv_hex': [os.fsencode(a).hex() for a in args]}, stream)\n"
            "sys.exit(int(os.environ['PIXEL_ROUTING_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        PIXEL_ROUTING_LOG=str(self.log), PIXEL_ROUTING_EXIT="0")

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, PIXEL_ROUTING_EXIT=str(code)))
        return result, argv

    def args_for(self, value, flag, position):
        if position == "input":
            return [flag, value, "-i", str(self.source), "-c:v", "h264", str(self.output)]
        return ["-i", str(self.source), "-c:v", "h264", flag, value, str(self.output)]

    def assert_exact_argv(self, argv):
        record = json.loads(self.log.read_text())
        self.assertEqual(record["argv"], argv)
        self.assertEqual(record["argv_hex"], [os.fsencode(a).hex() for a in argv])

    def assert_delegated(self, args, code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        actual, argv = self.invoke(args, code)
        self.assertEqual(actual.returncode, code, actual.stderr)
        self.assert_exact_argv(argv)
        self.assertEqual(actual.stdout, "")
        self.assertFalse(self.output.exists())

    def assert_rejected(self, args, reason=None):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        if reason is not None:
            self.assertIn(reason, plan["backend"]["reasons"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_all_formats_both_flags_and_positions_preserve_exact_argv(self):
        for value in FORMATS:
            for flag in FLAGS:
                for position in ("input", "output"):
                    with self.subTest(value=value, flag=flag, position=position):
                        self.assert_delegated(self.args_for(value, flag, position))

    def test_mixed_input_output_formats_and_alias_spellings_preserve_order(self):
        for first, second in (("yuv440p10be", "yuv440p12le"),
                              ("yuva444p16le", "yuva420p9be"),
                              ("gbrapf32be", "grayf32le"), ("xv48be", "p012le")):
            for input_flag in FLAGS:
                for output_flag in FLAGS:
                    with self.subTest(first=first, second=second,
                                      input_flag=input_flag, output_flag=output_flag):
                        self.assert_delegated([input_flag, first, "-i", str(self.source),
                                               "-c:v", "h264", output_flag, second,
                                               str(self.output)])

    def test_repeated_pixel_formats_preserve_order(self):
        for first, second in (("yuv420p", "ayuv"), ("ayuv", "yuv440p10be"),
                              ("gbrap14be", "gbrap14le")):
            for flag in FLAGS:
                with self.subTest(first=first, second=second, flag=flag):
                    self.assert_delegated(["-i", str(self.source), "-c:v", "h264",
                                           flag, first, flag, second, str(self.output)])

    def test_backend_failure_propagates_for_both_flags_and_positions(self):
        for value in ("yuv440p10be", "gbrapf32le", "yuva444p16be", "p212le"):
            for flag in FLAGS:
                for position in ("input", "output"):
                    for code in (1, 73):
                        with self.subTest(value=value, flag=flag, position=position, code=code):
                            self.assert_delegated(self.args_for(value, flag, position), code)

    def test_missing_empty_and_malformed_values_fail_before_backend(self):
        for flag in FLAGS:
            self.assert_rejected(["-i", str(self.source), str(self.output), flag])
            for value in ("", "AYUV", " yuv440p10le", "yuv440p10le ", "yuv440p10",
                          "yuv440p10xx", "yuva420p11le", "gbrapf64be", "p012xx",
                          "xv48be,ayuv", "ayuv -i extra.mp4"):
                for position in ("input", "output"):
                    with self.subTest(value=value, flag=flag, position=position):
                        self.assert_rejected(self.args_for(value, flag, position))

    def test_near_miss_for_every_added_format_is_rejected(self):
        for value in FORMATS:
            with self.subTest(value=value):
                self.assert_rejected(self.args_for(value + "x", "-pix_fmt", "output"))

    def test_shell_like_pixel_format_tokens_have_no_side_effects(self):
        marker = self.root / "shell-marker"
        for value in (f"ayuv;touch {marker}", f"$(touch {marker})",
                      f"yuv440p10le`touch {marker}`"):
            for flag in FLAGS:
                with self.subTest(value=value, flag=flag):
                    self.assert_rejected(self.args_for(value, flag, "output"))
                    self.assertFalse(marker.exists())

    def test_unsafe_input_and_output_paths_remain_rejected(self):
        for value in ("ayuv", "yuv440p12be", "yuva444p16le", "gbrapf32be", "p212le"):
            for unsafe in ("https://invalid.example/input", "file:input", "pipe:0",
                           "/dev/video0", "/proc/self/mem", "fixtures/../outside"):
                for position in ("input", "output"):
                    with self.subTest(value=value, unsafe=unsafe, position=position):
                        args = (["-pix_fmt", value, "-i", unsafe, str(self.output)]
                                if position == "input" else
                                ["-i", str(self.source), "-pix_fmt", value, unsafe])
                        self.assert_rejected(args, "unsafe_protocol_or_path_traversal")

    def test_unknown_option_spellings_remain_rejected(self):
        for flag in ("-pix_fmt:bogus", "-pixel_format:bogus", "-pix_fmtt", "-pixel_formats"):
            with self.subTest(flag=flag):
                self.assert_rejected(self.args_for("ayuv", flag, "output"))

    def test_native_pixel_format_boundary_is_unchanged(self):
        # Plan-only: never send a placeholder input through the native pipeline.
        for value in ("yuv420p", "yuv420p10le", "p010le"):
            for codec in ("h264", "hevc", "av1"):
                with self.subTest(value=value, codec=codec):
                    result, plan = self.plan(["-i", str(self.source), "-c:v", codec,
                                              "-pix_fmt", value, str(self.output)])
                    self.assertEqual(result.returncode, 0, result.stdout)
                    self.assertEqual(plan["error_count"], 0)
                    self.assertEqual(plan["backend"]["tier"], "translated_partial")
                    self.assertFalse(self.log.exists())
                    self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
