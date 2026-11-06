"""Pure moov HDR/fps probe: no external process, malformed boxes stay closed."""
from pathlib import Path
import os
import shutil
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


def lean_runner():
    lean = shutil.which("lean") or "lean"
    lean_path = os.pathsep.join([
        str(ROOT / ".lake" / "build" / "lib" / "lean"),
        str(ROOT.parent / "lean-sys" / ".lake" / "build" / "lib" / "lean"),
    ])
    return lean, {"PATH": "/nonexistent", "LEAN_PATH": lean_path}


def box(kind, payload):
    return struct.pack(">I", len(payload) + 8) + kind.encode() + payload


def moov(color, fps):
    colr = b"" if color is None else box("colr", b"nclx" + struct.pack(">HHH", *color) + b"\0")
    entry = box("avc1", bytes(78) + colr)
    stsd = box("stsd", bytes(4) + struct.pack(">I", 1) + entry)
    stts = box("stts", struct.pack(">IIII", 0, 1, 10, 1001)) if fps else b""
    mdhd = box("mdhd", bytes(12) + struct.pack(">II", 30000, 10010))
    hdlr = box("hdlr", bytes(8) + b"vide" + bytes(12))
    return box("moov", box("trak", box("mdia", mdhd + hdlr + box("minf", box("stbl", stsd + stts)))))


class CombinedProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean, cls.env = lean_runner()

    def test_probe_results_come_from_the_moov_only(self):
        cases = [
            (None, False, True, "0,24000,1001"),
            (None, True, True, "0,30000,1001"),
            ((1, 1, 1), False, True, "0,24000,1001"),
            ((1, 1, 1), True, True, "0,30000,1001"),
            ((9, 16, 9), True, True, "1,30000,1001"),
            (None, True, False, "0,30000,1001"),
            (None, False, False, "0,24000,1001"),
        ]
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            tmp = Path(directory)
            marker = tmp / "must-not-run"
            marker.write_text("#!/bin/sh\nexit 99\n")
            marker.chmod(0o755)
            for color, fps, need_hdr, expected in cases:
                with self.subTest(color=color, fps=fps, need_hdr=need_hdr):
                    source = tmp / "moov"
                    source.write_bytes(moov(color, fps))
                    result = subprocess.run(
                        [self.lean, "--run", "tests/differential/combined_probe.lean",
                         str(source), str(need_hdr).lower()],
                        cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=60,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                    self.assertEqual(result.stdout.strip(), expected)

    def test_malformed_and_empty_boxes_fail_closed(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            tmp = Path(directory)
            for name, payload in (("empty", b""), ("truncated", b"\x00\x00\x00\x01"), ("text", b"not a box")):
                source = tmp / name
                source.write_bytes(payload)
                result = subprocess.run(
                    [self.lean, "--run", "tests/differential/combined_probe.lean",
                     str(source), "true"],
                    cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=60,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                hdr, num, den = result.stdout.strip().split(",")
                self.assertEqual(hdr, "0")
                self.assertTrue(num.isdigit() and den.isdigit())


if __name__ == "__main__":
    unittest.main()
