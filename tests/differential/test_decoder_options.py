"""Decoder option parity; semantic value validation belongs to the backend."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake/build/bin/lffmpeg"


class DecoderOptionsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        reference = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not reference:
            raise unittest.SkipTest("reference FFmpeg unavailable")
        cls.reference = str(Path(reference).resolve())
        cls.env = dict(os.environ, LEANAV_FFMPEG_BIN=cls.reference)
        cls.directory = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.directory.cleanup)
        cls.source = str(Path(cls.directory.name) / "six-channels.ac3")
        tones = "|".join(f"0.1*sin(2*PI*{frequency}*t)"
                         for frequency in (220, 330, 440, 55, 660, 880))
        subprocess.run([cls.reference, "-v", "error", "-f", "lavfi", "-i",
                        f"aevalsrc={tones}:s=48000:d=0.1:c=5.1",
                        "-c:a", "ac3", cls.source], check=True,
                       capture_output=True, timeout=30, env=cls.env)

    def run_decode(self, binary, options, output="-"):
        return subprocess.run([binary, "-nostdin", "-v", "error", *options,
                               "-i", self.source, "-c:a", "pcm_s16le",
                               "-f", "s16le", output], capture_output=True,
                              timeout=30, env=self.env)

    def test_flags2_preserves_numeric_and_signed_expression_semantics(self):
        for value in ("skip_manual", "+skip_manual", "0", "0x20000000",
                      "none+skip_manual", "+skip_manual-skip_manual", "2*2"):
            with self.subTest(value=value):
                expected = self.run_decode(self.reference, ["-flags2", value])
                actual = self.run_decode(str(BINARY), ["-flags2", value])
                self.assertEqual(expected.returncode, 0, expected.stderr)
                self.assertEqual(actual.returncode, 0, actual.stderr)
                self.assertTrue(expected.stdout)
                self.assertEqual(actual.stdout, expected.stdout)

    def test_downmix_names_masks_and_channel_expressions(self):
        outputs = {}
        for layout in ("mono", "stereo", "0x3", "FL+FR"):
            with self.subTest(layout=layout):
                options = ["-downmix", layout, "-flags2", "skip_manual"]
                expected = self.run_decode(self.reference, options)
                actual = self.run_decode(str(BINARY), options)
                self.assertEqual(expected.returncode, 0, expected.stderr)
                self.assertEqual(actual.returncode, 0, actual.stderr)
                self.assertTrue(any(expected.stdout))
                self.assertEqual(actual.stdout, expected.stdout)
                outputs[layout] = actual.stdout
        self.assertEqual(set(outputs), {"mono", "stereo", "0x3", "FL+FR"})
        self.assertEqual(len(outputs["stereo"]), 2 * len(outputs["mono"]))
        self.assertEqual(outputs["stereo"], outputs["0x3"])
        self.assertEqual(outputs["stereo"], outputs["FL+FR"])

    def test_invalid_values_fail_at_execution_without_output_or_shell(self):
        marker = Path(self.directory.name) / "shell-marker"
        for flag, value in (("-flags2", "not_a_flag"), ("-downmix", "not_a_layout"),
                            ("-flags2", f"$(touch {marker})")):
            for label, binary in (("reference", self.reference), ("candidate", str(BINARY))):
                with self.subTest(flag=flag, value=value, binary=label):
                    output = Path(self.directory.name) / f"{label}.raw"
                    result = self.run_decode(binary, [flag, value], str(output))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output.exists())
                    self.assertFalse(marker.exists())

    def test_dtshd_container_demux_matches_reference(self):
        core = Path(self.directory.name) / "core.dts"
        subprocess.run([self.reference, "-v", "error", "-i", self.source,
                        "-ac", "2", "-c:a", "dca", "-strict", "-2", str(core)],
                       check=True, capture_output=True, timeout=30, env=self.env)
        payload = core.read_bytes()
        self.assertTrue(payload)
        # DTS-HD's chunk envelope contains a generated DTS core stream. No
        # external samples or proprietary encoder are needed for this fixture.
        source = Path(self.directory.name) / "wrapped.dtshd"
        source.write_bytes(b"DTSHDHDR" + (4).to_bytes(8, "big") + bytes(4) +
                           b"STRMDATA" + len(payload).to_bytes(8, "big") + payload)
        args = ["-v", "error", "-f", "dtshd", "-flags2", "skip_manual",
                "-downmix", "stereo", "-i", str(source),
                "-c:a", "pcm_s16le", "-f", "s16le", "-"]
        expected = subprocess.run([self.reference, *args], capture_output=True,
                                  timeout=30, env=self.env)
        actual = subprocess.run([str(BINARY), *args], capture_output=True,
                                timeout=30, env=self.env)
        self.assertEqual(expected.returncode, 0, expected.stderr)
        self.assertTrue(any(expected.stdout))
        self.assertEqual(actual.returncode, 0, actual.stderr)
        self.assertEqual(actual.stdout, expected.stdout)

    def test_routing_missing_values_and_unsafe_inputs(self):
        for flag, value in (("-flags2", "+skip_manual"), ("-downmix", "stereo")):
            with self.subTest(flag=flag):
                args = [str(BINARY), "plan", "-i", "input.mp4", flag, value, "out.mp4"]
                result = subprocess.run(args, capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(json.loads(result.stdout)["backend"]["tier"], "delegated_faithful")
                for tail in ([flag], [flag, ""]):
                    result = subprocess.run([str(BINARY), "plan", "-i", "input.mp4",
                                             "out.mp4", *tail], capture_output=True, timeout=10)
                    self.assertNotEqual(result.returncode, 0)
                args[3] = "https://invalid.example/input"
                result = subprocess.run(args, capture_output=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b"unsafe_protocol", result.stdout)


if __name__ == "__main__":
    unittest.main()
