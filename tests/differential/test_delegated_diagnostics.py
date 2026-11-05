"""-af hdcd is outside the native filter set and fails closed."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
ISOLATED = {"PATH": "/nonexistent"}


class DelegatedDiagnostics(unittest.TestCase):
    def run_audio(self, options, output):
        return subprocess.run(
            [str(CANDIDATE), "-nostdin", "-y", *options, "-i", "source.flac",
             "-af", "hdcd", "-f", "s24le", str(output)],
            capture_output=True, env=ISOLATED,
        )

    def test_hdcd_plan_and_exec_fail_closed(self):
        for options in ([], ["-nostats"], ["-nostats", "-v", "quiet"], ["-nostats", "-json"]):
            with self.subTest(options=options):
                plan = subprocess.run(
                    [str(CANDIDATE), "plan", *options, "-i", "source.flac", "-af", "hdcd",
                     "-f", "s24le", "out.raw"],
                    capture_output=True, text=True, env=ISOLATED, timeout=10,
                )
                body = json.loads(plan.stdout)
                self.assertNotEqual(plan.returncode, 0, plan.stdout)
                self.assertFalse(body["ok"])
                self.assertEqual(body["error_count"], 0)
                self.assertEqual(body["backend"]["tier"], "unsupported")
                self.assertFalse(body["backend"]["delegated_container"])
                self.assertFalse(body["backend"]["fallback_allowed"])
                result = self.run_audio(options, "out.raw")
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(Path("out.raw").exists())

    def test_explicit_pipe_protocol_keeps_existing_security_rejection(self):
        result = self.run_audio(["-nostats"], "pipe:1")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")


if __name__ == "__main__":
    unittest.main()
