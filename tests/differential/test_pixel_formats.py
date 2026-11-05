"""Extended P416 / YUV422P10 / P410 / P412 pixel formats parse cleanly and fail closed."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FORMATS = ("p416le", "p416be", "yuv422p10")
ISOLATED = {"PATH": "/nonexistent"}


class PixelFormatRoutingTests(unittest.TestCase):
    def plan(self, args):
        result = subprocess.run(
            [str(BINARY), "plan", *args],
            capture_output=True, text=True, timeout=10, env=ISOLATED,
        )
        return result, json.loads(result.stdout)

    def test_extended_formats_fail_closed_in_both_positions_and_option_spellings(self):
        for pixel_format in (*FORMATS, "yuv422p10le", "yuv422p10be",
                             "p410le", "p410be", "p412le", "p412be"):
            for flag in ("-pix_fmt", "-pixel_format"):
                for position in ("input", "output"):
                    with self.subTest(format=pixel_format, flag=flag, position=position):
                        args = ([flag, pixel_format, "-i", "input.mp4", "-c:v", "h264",
                                 "output.mp4"] if position == "input" else
                                ["-i", "input.mp4", "-c:v", "h264", flag, pixel_format,
                                 "output.mp4"])
                        result, plan = self.plan(args)
                        self.assertNotEqual(result.returncode, 0, result.stdout)
                        self.assertEqual(plan["error_count"], 0)
                        self.assertFalse(plan["ok"])
                        self.assertEqual(plan["backend"]["tier"], "unsupported")
                        self.assertFalse(plan["backend"]["delegated_container"])
                        self.assertFalse(plan["backend"]["fallback_allowed"])
                        exec_res = subprocess.run(
                            [str(BINARY), "-y", *args],
                            capture_output=True, timeout=10, env=ISOLATED,
                        )
                        self.assertNotEqual(exec_res.returncode, 0)

    def test_native_pixel_format_boundary_is_unchanged(self):
        for pixel_format in ("yuv420p", "yuv420p10le", "p010le"):
            with self.subTest(format=pixel_format):
                result, plan = self.plan(["-i", "input.mp4", "-c:v", "h264",
                                          "-pix_fmt", pixel_format, "output.mp4"])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])

    def test_missing_empty_unknown_and_shell_like_values_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "shell-marker"
            for flag in ("-pix_fmt", "-pixel_format"):
                result, _ = self.plan(["-i", "input.mp4", "output.mp4", flag])
                self.assertNotEqual(result.returncode, 0)
                for value in ("", "p416xx", "p414le", "yuv422p10xx", "bogus_pix_fmt",
                              "p416le -i other.raw", f"$(touch {marker})"):
                    for before_input in (True, False):
                        with self.subTest(flag=flag, value=value, input=before_input):
                            args = ([flag, value, "-i", "input.mp4", "output.mp4"]
                                    if before_input else
                                    ["-i", "input.mp4", flag, value, "output.mp4"])
                            result, _ = self.plan(args)
                            self.assertNotEqual(result.returncode, 0)
                            self.assertFalse(marker.exists())

    def test_new_formats_do_not_bypass_input_or_output_path_checks(self):
        for pixel_format in FORMATS:
            for unsafe in ("https://invalid.example/media", "/dev/video0",
                           "/proc/self/mem", "fixtures/../outside.mp4"):
                for position in ("input", "output"):
                    with self.subTest(format=pixel_format, unsafe=unsafe, position=position):
                        args = (["-pix_fmt", pixel_format, "-i", unsafe, "output.mp4"]
                                if position == "input" else
                                ["-i", "input.mp4", "-pix_fmt", pixel_format, unsafe])
                        result, plan = self.plan(args)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unsafe_protocol_or_path_traversal",
                                      plan["backend"]["reasons"])


if __name__ == "__main__":
    unittest.main()
