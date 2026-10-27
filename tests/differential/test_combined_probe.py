"""Exercise the real Lean IO helper with synthetic moov boxes and a counted ffprobe."""
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


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
    def test_probe_results_and_process_counts(self):
        # Both misses, either miss, both hits, disabled HDR, malformed and empty output.
        cases = [
            (None, False, True, "hlg", "2,60000,1001", "both"),
            (None, True, True, "hlg", "2,30000,1001", "hdr"),
            ((1, 1, 1), False, True, "hlg", "0,60000,1001", "fps"),
            ((1, 1, 1), True, True, "hlg", "0,30000,1001", None),
            ((9, 16, 9), True, True, "hlg", "1,30000,1001", None),
            (None, True, False, "hlg", "0,30000,1001", None),
            (None, False, False, "hlg", "0,60000,1001", "fps"),
            (None, False, True, "bad", "1,24000,1001", "both"),
            (None, False, True, "empty", "0,24000,1001", "both"),
        ]
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            tmp = Path(directory)
            mock = tmp / "ffprobe"
            mock.write_text('''#!/usr/bin/python3
import json, os, sys
with open(os.environ["PROBE_LOG"], "a") as log:
    log.write(json.dumps(sys.argv[1:]) + "\\n")
query = sys.argv[sys.argv.index("-show_entries") + 1]
mode = os.environ["PROBE_MODE"]
if mode == "empty": sys.exit(1)
if mode == "bad":
    print("color_transfer=smpte2084\\nr_frame_rate=0/0")
elif query == "stream=r_frame_rate": print("60000/1001")
elif query.endswith(",r_frame_rate"):
    print("r_frame_rate=60000/1001\\ncolor_space=bt2020nc\\ncolor_transfer=arib-std-b67\\ncolor_primaries=bt2020")
else: print("bt2020\\narib-std-b67\\nbt2020nc")
''')
            mock.chmod(0o755)
            for color, fps, need_hdr, mode, expected, query in cases:
                with self.subTest(color=color, fps=fps, need_hdr=need_hdr, mode=mode):
                    source, log = tmp / "moov", tmp / "calls"
                    source.write_bytes(moov(color, fps))
                    log.write_text("")
                    env = dict(os.environ, LEANAV_FFPROBE_BIN=str(mock),
                               PROBE_LOG=str(log), PROBE_MODE=mode)
                    result = subprocess.run(
                        ["lake", "env", "lean", "--run", "tests/differential/combined_probe.lean",
                         str(source), str(need_hdr).lower()], cwd=ROOT, env=env,
                        capture_output=True, text=True, timeout=60)
                    self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                    self.assertEqual(result.stdout.strip(), expected)
                    calls = [json.loads(line) for line in log.read_text().splitlines()]
                    self.assertEqual(len(calls), int(query is not None))
                    if calls:
                        entries = calls[0][calls[0].index("-show_entries") + 1]
                        self.assertEqual(entries, {
                            "hdr": "stream=color_primaries,color_transfer,color_space",
                            "fps": "stream=r_frame_rate",
                            "both": "stream=color_primaries,color_transfer,color_space,r_frame_rate",
                        }[query])
                        if query == "both":
                            self.assertIn("default=noprint_wrappers=1:nokey=0", calls[0])
