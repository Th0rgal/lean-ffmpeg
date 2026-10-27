"""CLI parity for the streamhash muxer, using decoded video checksums."""
import os
import json
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
            for algorithm in (None, "md5", "sHa256", "SHA512/224"):
                with self.subTest(algorithm=algorithm):
                    command = args[:-1] + (["-hash", algorithm] if algorithm else []) + ["-"]
                    expected = subprocess.run([reference, *command], check=True, env=env,
                                              capture_output=True, timeout=30)
                    actual = subprocess.run([str(BINARY), *command], env=env,
                                            capture_output=True, timeout=30)
                    self.assertEqual(actual.returncode, 0, actual.stderr.decode(errors="replace"))
                    self.assertTrue(expected.stdout.strip())
                    self.assertEqual(actual.stdout, expected.stdout)

    def test_channel_order_uses_validated_delegated_route(self):
        for order in ("default", "coded", "0", "1"):
            with self.subTest(order=order):
                result = subprocess.run([str(BINARY), "plan", "-channel_order", order,
                                         "-i", "input.dts", "-f", "streamhash", "-"],
                                        capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout)
                plan = json.loads(result.stdout)
                self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
                self.assertEqual(plan["error_count"], 0)

    def test_invalid_or_missing_hash_and_channel_order_fail_closed(self):
        for flag, value in (("-hash", "not-a-hash"), ("-channel_order", "2"),
                            ("-hash", ""), ("-channel_order", "")):
            with self.subTest(flag=flag, value=value):
                result = subprocess.run([str(BINARY), "plan", "-i", "input.dts",
                                         "-f", "streamhash", "-", flag, value],
                                        capture_output=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
        for flag in ("-hash", "-channel_order"):
            with self.subTest(missing=flag):
                result = subprocess.run([str(BINARY), "plan", "-i", "input.dts",
                                         "-f", "streamhash", "-", flag],
                                        capture_output=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)

    def test_streamhash_does_not_bypass_unsafe_input_policy(self):
        result = subprocess.run([str(BINARY), "plan", "-i", "https://invalid.example/input",
                                 "-f", "streamhash", "-"], capture_output=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
