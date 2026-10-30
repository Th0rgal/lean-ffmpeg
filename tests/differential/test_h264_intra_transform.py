import json
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"


def filt3(a, b, c):
    return (a + 2 * b + c + 2) // 4


def avg2(a, b):
    return (a + b + 1) // 2


def clip1(v):
    return 0 if v < 0 else 255 if v > 255 else v


def asr(x, n):
    return x // (1 << n)


def idct4_1d(d0, d1, d2, d3):
    e0, e1 = d0 + d2, d0 - d2
    e2, e3 = asr(d1, 1) - d3, d1 + asr(d3, 1)
    return (e0 + e3, e1 + e2, e1 - e2, e0 - e3)


def idct8_1d(d):
    d0, d1, d2, d3, d4, d5, d6, d7 = d
    a0, a2, a4, a6 = d0 + d4, d0 - d4, asr(d2, 1) - d6, d2 + asr(d6, 1)
    b0, b2, b4, b6 = a0 + a6, a2 + a4, a2 - a4, a0 - a6
    a1 = -d3 + d5 - d7 - asr(d7, 1)
    a3 = d1 + d7 - d3 - asr(d3, 1)
    a5 = -d1 + d7 + d5 + asr(d5, 1)
    a7 = d3 + d5 + d1 + asr(d1, 1)
    b1, b7 = a1 + asr(a7, 2), -asr(a1, 2) + a7
    b3, b5 = a3 + asr(a5, 2), asr(a3, 2) - a5
    return (b0 + b7, b2 + b5, b4 + b3, b6 + b1, b6 - b1, b4 - b3, b2 - b5, b0 - b7)


def idct4(levels, qp, dc_override=None):
    q = qp // 6
    v = [10, 16, 13] if qp % 6 == 0 else [11, 18, 14] if qp % 6 == 1 else [13, 20, 16] if qp % 6 == 2 else [14, 23, 18] if qp % 6 == 3 else [16, 25, 20] if qp % 6 == 4 else [18, 29, 23]
    scaled = [0] * 16
    for i in range(4):
        for j in range(4):
            cls = 0 if i % 2 == 0 and j % 2 == 0 else 1 if i % 2 == 1 and j % 2 == 1 else 2
            c, ls = levels[i * 4 + j], 16 * v[cls]
            scaled[i * 4 + j] = (c * ls) << (q - 4) if qp >= 24 else (c * ls + (1 << (3 - q))) >> (4 - q)
    if dc_override is not None:
        scaled[0] = dc_override
    rows = [idct4_1d(*scaled[r * 4:(r + 1) * 4]) for r in range(4)]
    cols = [idct4_1d(*(rows[r][c] for r in range(4))) for c in range(4)]
    return [asr(cols[c][r] + 32, 6) for r in range(4) for c in range(4)]


class H264IntraTransformTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not (BINARY.stat().st_mode & 0o111):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not shutil.which("ffmpeg"):
            raise unittest.SkipTest("reference FFmpeg is unavailable")

    def probe(self, *args):
        res = subprocess.run([str(BINARY), "h264-intra-probe", *args], capture_output=True, text=True, timeout=60)
        self.assertEqual(res.returncode, 0, res.stderr)
        return [int(x) for x in res.stdout.strip().split(",") if x != ""]

    def test_itu_idct4x4_positions_and_thresholds(self):
        for qp in (10, 30):
            for pos in range(16):
                levels = [1 if i == pos else 0 for i in range(16)]
                got = self.probe("idct4x4", str(qp), "none", *[str(v) for v in levels])
                self.assertEqual(got, idct4(levels, qp))
        got_dc = self.probe("idct4x4", "10", "128", *["0"] * 16)
        self.assertEqual(got_dc, idct4([0] * 16, 10, 128))

    def test_itu_idct8x8_dc_and_zero(self):
        zero = self.probe("idct8x8", "10", *["0"] * 64)
        self.assertEqual(zero, [0] * 64)
        v8 = {0: [20, 18, 32, 19, 25, 24], 1: [22, 19, 35, 21, 28, 26], 2: [26, 23, 42, 24, 33, 31],
              3: [28, 25, 45, 26, 36, 33], 4: [32, 28, 51, 30, 40, 38], 5: [36, 32, 58, 34, 46, 43]}
        for qp in (10, 27, 38):
            for pos in range(64):
                i, j = divmod(pos, 8)
                im, jm = i % 4, j % 4
                cls = (0 if im == 0 and jm == 0 else 1 if i % 2 == 1 and j % 2 == 1 else
                       2 if im == 2 and jm == 2 else 3 if (im == 0 and j % 2 == 1) or (i % 2 == 1 and jm == 0) else
                       4 if (im == 0 and jm == 2) or (im == 2 and jm == 0) else 5)
                q, ls = qp // 6, 16 * v8[qp % 6][cls]
                scaled = [0] * 64
                scaled[pos] = (1 * ls) << (q - 6) if qp >= 36 else (1 * ls + (1 << (5 - q))) >> (6 - q)
                rows = [idct8_1d(scaled[r * 8:(r + 1) * 8]) for r in range(8)]
                cols = [idct8_1d([rows[r][c] for r in range(8)]) for c in range(8)]
                expect = [asr(cols[c][r] + 32, 6) for r in range(8) for c in range(8)]
                levels = ["1" if k == pos else "0" for k in range(64)]
                self.assertEqual(self.probe("idct8x8", str(qp), *levels), expect)

    def test_chroma_dc_threshold30_no_rounding(self):
        for qpc, expect in ((18, 40), (26, 104), (30, 160), (39, 448), (0, 5)):
            got = self.probe("chroma-dc", str(qpc), "1", "0", "0", "0")
            self.assertEqual(got, [expect] * 4)

    def test_luma_dc_threshold36(self):
        for qp, expect in ((10, 8), (36, 160), (40, 256)):
            got = self.probe("luma-dc", str(qp), "1", *["0"] * 15)
            self.assertEqual(got[0], expect)

    def test_intra_modes_and_boundary(self):
        left = [str(40 + i * 11) for i in range(8)]
        top = [str(90 + i * 9) for i in range(8)]
        tr = [str(170 + i * 3) for i in range(8)]
        for mode in range(9):
            p4 = self.probe("pred4x4", str(mode), "1", "1", "1", "1", "33", *left[:4], *top[:4], *tr[:4])
            self.assertEqual(len(p4), 16)
            self.assertTrue(all(0 <= v <= 255 for v in p4))
            p8 = self.probe("pred8x8", str(mode), "1", "1", "1", "1", "33", *left, *top, *tr)
            self.assertEqual(len(p8), 64)
        bounded = self.probe("pred8x8", "3", "0", "1", "0", "0", "0", *["128"] * 24)
        self.assertEqual(len(bounded), 64)
        chroma = self.probe("pred-chroma", "0", "0", "1", "120", *[str(100 + i) for i in range(16)])
        self.assertEqual(len(chroma), 64)

    def test_lossless_and_lossy_mb_and_ffmpeg_iframe(self):
        for part, modes in (("0", ["0", "1", "2", "3", "4", "5", "6", "7", "8", "0", "1", "2", "3", "4", "5", "6"]),
                            ("1", ["0", "1", "2"]), ("2", ["3"])):
            res = subprocess.run(
                [str(BINARY), "h264-intra-probe", "lossless-mb-roundtrip", part, "2", *modes],
                capture_output=True, text=True, timeout=120)
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertTrue(json.loads(res.stdout)["ok"])
        lossy = subprocess.run(
            [str(BINARY), "h264-intra-probe", "lossy-mb", "1", "12", "0"],
            capture_output=True, text=True, timeout=180)
        self.assertEqual(lossy.returncode, 0, lossy.stderr)
        body = json.loads(lossy.stdout)
        self.assertTrue(body["ok"])
        self.assertLessEqual(body["err_y"], 8)
        frame = subprocess.run([
            "ffmpeg", "-hide_banner", "-loglevel", "error", "-f", "lavfi",
            "-i", "color=c=gray:s=16x16", "-frames:v", "1", "-c:v", "libx264",
            "-qp", "12", "-profile:v", "high", "-f", "h264", "-"], capture_output=True, timeout=30)
        self.assertEqual(frame.returncode, 0, frame.stderr.decode(errors="replace"))
        self.assertGreater(len(frame.stdout), 32)


if __name__ == "__main__":
    unittest.main()
