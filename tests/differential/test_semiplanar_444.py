"""Delegated CLI parity for 10/12-bit semiplanar 4:4:4 pixel formats."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake/build/bin/lffmpeg"
FORMATS = ("p410le", "p410be", "p412le", "p412be")


class Semiplanar444Tests(unittest.TestCase):
    def test_formats_require_delegation_even_for_mp4(self):
        for pixel_format in FORMATS:
            with self.subTest(pixel_format=pixel_format):
                result = subprocess.run([str(BINARY), "plan", "-i", "input.mp4",
                                         "-c:v", "h264", "-pix_fmt", pixel_format,
                                         "output.mp4"], capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout)
                plan = json.loads(result.stdout)
                self.assertEqual(plan["error_count"], 0)
                self.assertEqual(plan["backend"]["tier"], "delegated_faithful")

    def test_input_and_output_bytes_match_reference(self):
        reference = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not reference:
            self.skipTest("reference FFmpeg unavailable")
        reference = str(Path(reference).resolve())
        env = dict(os.environ, LEANAV_FFMPEG_BIN=reference)
        listing = subprocess.run([reference, "-pix_fmts"], capture_output=True,
                                 check=True, timeout=30).stdout.decode()
        supported = {line.split()[1] for line in listing.splitlines()
                     if len(line.split()) >= 2 and len(line.split()[0]) == 5}
        with tempfile.TemporaryDirectory() as directory:
            source = str(Path(directory) / "input.nut")
            subprocess.run([reference, "-v", "error", "-f", "lavfi", "-i",
                            "testsrc2=size=32x32:rate=5", "-frames:v", "2",
                            "-c:v", "rawvideo", source], check=True,
                           capture_output=True, timeout=30)
            for pixel_format in FORMATS:
                with self.subTest(pixel_format=pixel_format):
                    if pixel_format not in supported:
                        self.skipTest(f"reference lacks {pixel_format}")
                    encode = ["-v", "error", "-i", source, "-c:v", "rawvideo",
                              "-pix_fmt", pixel_format, "-f", "rawvideo", "-"]
                    expected = subprocess.run([reference, *encode], check=True,
                                              capture_output=True, timeout=30, env=env)
                    actual = subprocess.run([str(BINARY), *encode],
                                            capture_output=True, timeout=30, env=env)
                    self.assertEqual(actual.returncode, 0, actual.stderr)
                    self.assertEqual(len(expected.stdout), 2 * 32 * 32 * 6)
                    self.assertEqual(actual.stdout, expected.stdout)
                    raw = Path(directory) / (pixel_format + ".raw")
                    raw.write_bytes(expected.stdout)
                    decode = ["-v", "error", "-f", "rawvideo", "-s", "32x32",
                              "-pixel_format", pixel_format, "-i", str(raw),
                              "-c:v", "rawvideo", "-pix_fmt", "rgb24",
                              "-f", "rawvideo", "-"]
                    expected = subprocess.run([reference, *decode], check=True,
                                              capture_output=True, timeout=30, env=env)
                    actual = subprocess.run([str(BINARY), *decode],
                                            capture_output=True, timeout=30, env=env)
                    self.assertEqual(actual.returncode, 0, actual.stderr)
                    self.assertEqual(len(expected.stdout), 2 * 32 * 32 * 3)
                    self.assertEqual(actual.stdout, expected.stdout)

    def test_unknown_formats_and_unsafe_inputs_still_fail(self):
        for pixel_format in ("p410xx", "p414le", ""):
            with self.subTest(pixel_format=pixel_format):
                result = subprocess.run([str(BINARY), "plan", "-i", "input.mp4",
                                         "-pix_fmt", pixel_format, "output.mp4"],
                                        capture_output=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
        result = subprocess.run([str(BINARY), "plan", "-i", "https://invalid.example/in",
                                 "-pix_fmt", "p410le", "output.mp4"],
                                capture_output=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
