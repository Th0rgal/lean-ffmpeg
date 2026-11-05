"""Ogg serial_offset keeps option arity and fails closed."""
import json
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
ISOLATED = {"PATH": "/nonexistent"}


class OggSerialOffset(unittest.TestCase):
    def test_option_value_does_not_become_output_path(self):
        result = subprocess.run(
            [str(CANDIDATE), "--dump-plan", "-i", "input.ogg", "-c", "copy",
             "-serial_offset", "67574", "-f", "ogg", "output.ogg"],
            capture_output=True, text=True, env=ISOLATED,
        )
        self.assertEqual(result.returncode, 1, result.stderr)
        plan = json.loads(result.stdout)
        self.assertFalse(plan["ok"])
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertFalse(plan["backend"]["fallback_allowed"])
        self.assertEqual([item["path"] for item in plan["outputs"]], ["output.ogg"])

    def test_missing_value_is_rejected(self):
        result = subprocess.run(
            [str(CANDIDATE), "--dump-plan", "-i", "input.ogg", "output.ogg", "-serial_offset"],
            capture_output=True, text=True, env=ISOLATED,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(json.loads(result.stdout)["ok"])

    def test_mux_fails_closed_for_every_serial_value(self):
        for value in ("0", "67574", "2147483647", "-2", "2147483648", "bad"):
            with self.subTest(value=value):
                result = subprocess.run(
                    [str(CANDIDATE), "-nostdin", "-v", "error", "-y", "-i", "input.ogg",
                     "-c", "copy", "-fflags", "+bitexact", "-serial_offset", value,
                     "-f", "ogg", "output.ogg"],
                    capture_output=True, env=ISOLATED,
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(os.path.exists("output.ogg"))


if __name__ == "__main__":
    unittest.main()
