"""CLI parity for the streamhash muxer, using decoded video checksums."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake/build/bin/lffmpeg"


class StreamHashTests(unittest.TestCase):
    def test_decoded_stream_checksum_matches_reference(self):
        reference = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not reference:
            self.skipTest("reference FFmpeg is unavailable")
        reference = str(Path(reference).resolve())
        env = dict(os.environ, LEANAV_FFMPEG_BIN=reference)
        with tempfile.TemporaryDirectory() as directory:
            source = str(Path(directory) / "input.nut")
            subprocess.run([reference, "-nostdin", "-v", "error", "-f", "lavfi",
                            "-i", "testsrc2=size=32x32:rate=5", "-frames:v", "2",
                            "-c:v", "rawvideo", source], check=True, timeout=30,
                           capture_output=True, env=env)
            args = ["-nostdin", "-hide_banner", "-loglevel", "error", "-i", source,
                    "-c:v", "rawvideo", "-f", "streamhash", "-"]
            expected = subprocess.run([reference, *args], check=True, env=env,
                                      capture_output=True, timeout=30)
            actual = subprocess.run([str(BINARY), *args], env=env,
                                    capture_output=True, timeout=30)
            self.assertEqual(actual.returncode, 0, actual.stderr.decode(errors="replace"))
            self.assertTrue(expected.stdout.strip())
            self.assertEqual(actual.stdout, expected.stdout)

    def test_streamhash_does_not_bypass_unsafe_input_policy(self):
        result = subprocess.run([str(BINARY), "plan", "-i", "https://invalid.example/input",
                                 "-f", "streamhash", "-"], capture_output=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
