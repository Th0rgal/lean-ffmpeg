"""Ogg serial_offset option arity and delegated muxer compatibility."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / ".lake/build/bin/lffmpeg"
REFERENCE = os.environ.get("LEANAV_FFMPEG_BIN", "ffmpeg")


class OggSerialOffset(unittest.TestCase):
    def test_option_value_does_not_become_output_path(self):
        result = subprocess.run([str(CANDIDATE), "--dump-plan", "-i", "input.ogg",
                                 "-c", "copy", "-serial_offset", "67574",
                                 "-f", "ogg", "output.ogg"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(result.stdout)
        self.assertTrue(plan["ok"])
        self.assertEqual([o["path"] for o in plan["outputs"]], ["output.ogg"])

    def test_missing_value_is_rejected(self):
        result = subprocess.run([str(CANDIDATE), "--dump-plan", "-i", "input.ogg",
                                 "output.ogg", "-serial_offset"], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(json.loads(result.stdout)["ok"])

    def test_muxed_bytes_and_invalid_values_match_reference(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            source = directory / "input.ogg"
            subprocess.run([REFERENCE, "-nostdin", "-v", "error", "-f", "lavfi",
                            "-i", "sine=frequency=440:duration=0.05", "-c:a", "flac",
                            "-fflags", "+bitexact", "-serial_offset", "0", str(source)],
                           check=True, capture_output=True)
            for value in ("0", "67574", "2147483647", "-2", "2147483648", "bad"):
                with self.subTest(value=value):
                    outputs = [directory / "reference.ogg", directory / "candidate.ogg"]
                    results = []
                    for binary, output in zip((REFERENCE, str(CANDIDATE)), outputs):
                        results.append(subprocess.run(
                            [binary, "-nostdin", "-v", "error", "-y", "-i", str(source),
                             "-c", "copy", "-fflags", "+bitexact", "-serial_offset", value,
                             "-f", "ogg", str(output)], capture_output=True))
                    self.assertEqual(results[0].returncode == 0, results[1].returncode == 0,
                                     results[1].stderr)
                    if value in ("0", "67574", "2147483647"):
                        self.assertEqual(results[0].returncode, 0, results[0].stderr)
                        self.assertEqual(outputs[0].read_bytes(), outputs[1].read_bytes())
                    else:
                        self.assertNotEqual(results[0].returncode, 0)
