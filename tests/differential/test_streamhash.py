"""streamhash is outside the native muxer set and fails closed."""
import json
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
ISOLATED = {"PATH": "/nonexistent"}


class StreamHashTests(unittest.TestCase):
    def _plan(self, args):
        result = subprocess.run(
            [str(BINARY), "plan", *args],
            capture_output=True, text=True, timeout=10, env=ISOLATED,
        )
        return result, json.loads(result.stdout)

    def test_decoded_stream_checksum_fails_closed(self):
        if not BINARY.is_file():
            self.fail("lffmpeg binary is unavailable")
        for algorithm in (None, "md5", "sHa256", "SHA512/224"):
            with self.subTest(algorithm=algorithm):
                args = ["-nostdin", "-hide_banner", "-loglevel", "error", "-i", "input.nut",
                        "-c:v", "rawvideo", "-f", "streamhash"]
                if algorithm:
                    args += ["-hash", algorithm]
                args.append("-")
                result, plan = self._plan(args[3:])
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertFalse(plan["ok"])
                self.assertEqual(plan["error_count"], 0)
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])
                actual = subprocess.run([str(BINARY), *args], capture_output=True, timeout=10, env=ISOLATED)
                self.assertNotEqual(actual.returncode, 0)

    def test_channel_order_is_unsupported(self):
        for order in ("default", "coded", "0", "1"):
            with self.subTest(order=order):
                result, plan = self._plan(["-channel_order", order, "-i", "input.dts", "-f", "streamhash", "-"])
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["error_count"], 0)
                self.assertFalse(plan["ok"])
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])

    def test_invalid_or_missing_hash_and_channel_order_fail_closed(self):
        for flag, value in (("-hash", "not-a-hash"), ("-channel_order", "2"),
                            ("-hash", ""), ("-channel_order", "")):
            with self.subTest(flag=flag, value=value):
                result, _plan = self._plan(["-i", "input.dts", "-f", "streamhash", "-", flag, value])
                self.assertNotEqual(result.returncode, 0)
        for flag in ("-hash", "-channel_order"):
            with self.subTest(missing=flag):
                result = subprocess.run(
                    [str(BINARY), "plan", "-i", "input.dts", "-f", "streamhash", "-", flag],
                    capture_output=True, timeout=10, env=ISOLATED,
                )
                self.assertNotEqual(result.returncode, 0)

    def test_streamhash_does_not_bypass_unsafe_input_policy(self):
        result, plan = self._plan(["-i", "https://invalid.example/input", "-f", "streamhash", "-"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
