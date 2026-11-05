"""AC-3/DTS decoder flags (-flags2, -downmix) parse cleanly and fail closed."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
ISOLATED = {"PATH": "/nonexistent"}


class DecoderOptionsTests(unittest.TestCase):
    def _plan(self, args):
        res = subprocess.run(
            [str(BINARY), "plan", *args],
            capture_output=True, text=True, timeout=10, env=ISOLATED,
        )
        return res, json.loads(res.stdout)

    def test_flags2_and_downmix_fail_closed_with_zero_parse_errors(self):
        for value in ("skip_manual", "+skip_manual", "0", "0x20000000",
                      "none+skip_manual", "+skip_manual-skip_manual", "2*2"):
            with self.subTest(flags2=value):
                res, plan = self._plan(["-flags2", value, "-i", "six-channels.ac3",
                                        "-c:a", "pcm_s16le", "-f", "s16le", "-"])
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertEqual(plan["error_count"], 0)
                self.assertFalse(plan["ok"])
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])
        for layout in ("mono", "stereo", "0x3", "FL+FR"):
            with self.subTest(downmix=layout):
                res, plan = self._plan(["-downmix", layout, "-flags2", "skip_manual",
                                        "-i", "six-channels.ac3", "-c:a", "pcm_s16le",
                                        "-f", "s16le", "-"])
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertEqual(plan["error_count"], 0)
                self.assertFalse(plan["ok"])
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])

    def test_execution_and_shell_like_values_fail_without_output_or_shell(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "shell-marker"
            for flag, value in (("-flags2", "skip_manual"), ("-flags2", "not_a_flag"),
                                ("-downmix", "stereo"), ("-downmix", "not_a_layout"),
                                ("-flags2", f"$(touch {marker})")):
                with self.subTest(flag=flag, value=value):
                    output = Path(directory) / "candidate.raw"
                    result = subprocess.run(
                        [str(BINARY), "-nostdin", "-v", "error", flag, value,
                         "-i", "six-channels.ac3", "-c:a", "pcm_s16le", "-f", "s16le",
                         str(output)],
                        capture_output=True, timeout=10, env=ISOLATED,
                    )
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output.exists())
                    self.assertFalse(marker.exists())

    def test_dtshd_container_demux_fails_closed(self):
        args = ["-v", "error", "-f", "dtshd", "-flags2", "skip_manual",
                "-downmix", "stereo", "-i", "wrapped.dtshd",
                "-c:a", "pcm_s16le", "-f", "s16le", "-"]
        actual = subprocess.run([str(BINARY), *args], capture_output=True, timeout=10, env=ISOLATED)
        self.assertNotEqual(actual.returncode, 0)
        self.assertEqual(actual.stdout, b"")

    def test_routing_missing_values_and_unsafe_inputs(self):
        for flag, value in (("-flags2", "+skip_manual"), ("-downmix", "stereo")):
            with self.subTest(flag=flag):
                res, plan = self._plan(["-i", "input.mp4", flag, value, "out.mp4"])
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])
                for tail in ([flag], [flag, ""]):
                    missing = subprocess.run(
                        [str(BINARY), "plan", "-i", "input.mp4", "out.mp4", *tail],
                        capture_output=True, timeout=10, env=ISOLATED,
                    )
                    self.assertNotEqual(missing.returncode, 0)
                unsafe = subprocess.run(
                    [str(BINARY), "plan", "-i", "https://invalid.example/input", flag, value, "out.mp4"],
                    capture_output=True, timeout=10, env=ISOLATED,
                )
                self.assertNotEqual(unsafe.returncode, 0)
                self.assertIn(b"unsafe_protocol", unsafe.stdout)


if __name__ == "__main__":
    unittest.main()
