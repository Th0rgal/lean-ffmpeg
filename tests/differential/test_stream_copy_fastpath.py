"""Regression coverage for probe reuse and copy without the Lean metadata probe."""
import json
import tempfile
import unittest
from pathlib import Path

from test_phase3_to_7 import BINARY, FIXTURE_AV, REFERENCE
import test_phase3_to_7 as phase_tests

class StreamCopyFastpathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        phase_tests.Phase3To7Tests.setUpClass()

    run_cmd = phase_tests.Phase3To7Tests.run_cmd
    probe_json = phase_tests.Phase3To7Tests.probe_json

    def test_invalid_copy_rejected_without_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, payload in [
                ("corrupt", b"not an mp4" * 100),
                ("truncated", b"\x00\x00\x00\x18ftypisom\x00\x00\x02\x00isomiso2"
                              b"\x00\x01\x00\x00moov\x00\x00"),
            ]:
                source = root / (name + ".mp4")
                source.write_bytes(payload)
                for json_args in [[], ["-json"]]:
                    out = root / "output.mp4"
                    result = self.run_cmd([BINARY, *json_args, "-y", "-i", source, "-c", "copy", out])
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertFalse(out.exists())

    def test_front_and_end_moov_copy_and_scale(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for layout in ["front", "end", "wide-mdat"]:
                source = root / (layout + ".mp4")
                flags = ["-movflags", "+faststart"] if layout == "front" else []
                result = self.run_cmd([REFERENCE, "-v", "error", "-y", "-i", FIXTURE_AV,
                                       "-c", "copy", *flags, source])
                self.assertEqual(result.returncode, 0, result.stderr)
                if layout == "wide-mdat":
                    import struct
                    data = source.read_bytes()
                    pos = 0
                    while data[pos + 4:pos + 8] != b"mdat":
                        pos += int.from_bytes(data[pos:pos + 4], "big")
                    size = int.from_bytes(data[pos:pos + 4], "big")
                    # Consume the preceding 8-byte free box to preserve all chunk offsets.
                    self.assertEqual(data[pos - 4:pos], b"free")
                    data = data[:pos - 8] + struct.pack(">I4sQ", 1, b"mdat", size + 8) + data[pos + 8:]
                    source.write_bytes(data)
                for mode, flags in [
                    ("copy", ["-c", "copy"]),
                    ("json-copy", ["-json", "-c", "copy"]),
                    ("scale", ["-json", "-vf", "scale=16:16"]),
                ]:
                    out = root / (layout + "-" + mode + ".mp4")
                    result = self.run_cmd([BINARY, "-y", "-i", source, *flags, out])
                    self.assertEqual(result.returncode, 0, result.stderr)
                    if "-json" in flags:
                        self.assertTrue(json.loads(result.stdout)["ok"])
                    video = next(s for s in self.probe_json(out)["streams"] if s["codec_type"] == "video")
                    self.assertEqual(video["width"], 16 if mode == "scale" else 32)
