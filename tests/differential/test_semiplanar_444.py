"""10/12-bit semiplanar 4:4:4 pixel formats fail closed."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FORMATS = ("p410le", "p410be", "p412le", "p412be")
ISOLATED = {"PATH": "/nonexistent"}


class Semiplanar444Tests(unittest.TestCase):
    def test_formats_fail_closed_even_for_mp4(self):
        for pixel_format in FORMATS:
            with self.subTest(pixel_format=pixel_format):
                result = subprocess.run(
                    [str(BINARY), "plan", "-i", "input.mp4", "-c:v", "h264",
                     "-pix_fmt", pixel_format, "output.mp4"],
                    capture_output=True, text=True, timeout=10, env=ISOLATED,
                )
                plan = json.loads(result.stdout)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["error_count"], 0)
                self.assertFalse(plan["ok"])
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])
                actual = subprocess.run(
                    [str(BINARY), "-y", "-i", "input.mp4", "-c:v", "h264",
                     "-pix_fmt", pixel_format, "output.mp4"],
                    capture_output=True, timeout=10, env=ISOLATED,
                )
                self.assertNotEqual(actual.returncode, 0)

    def test_unknown_formats_and_unsafe_inputs_still_fail(self):
        for pixel_format in ("p410xx", "p414le", ""):
            with self.subTest(pixel_format=pixel_format):
                result = subprocess.run(
                    [str(BINARY), "plan", "-i", "input.mp4", "-pix_fmt", pixel_format, "output.mp4"],
                    capture_output=True, timeout=10, env=ISOLATED,
                )
                self.assertNotEqual(result.returncode, 0)
        result = subprocess.run(
            [str(BINARY), "plan", "-i", "https://invalid.example/in", "-pix_fmt", "p410le", "output.mp4"],
            capture_output=True, timeout=10, env=ISOLATED,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
