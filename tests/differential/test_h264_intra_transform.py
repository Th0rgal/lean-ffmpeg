import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = os.environ.get("FFMPEG") or shutil.which("ffmpeg")


class _BitWriter:
    def __init__(self):
        self.bits = []

    def u(self, n, val):
        for i in range(n - 1, -1, -1):
            self.bits.append((val >> i) & 1)

    def bit(self, b):
        self.bits.append(b & 1)

    def ue(self, val):
        code = val + 1
        k = code.bit_length() - 1
        for _ in range(k):
            self.bits.append(0)
        self.u(k + 1, code)

    def se(self, val):
        self.ue(-2 * val if val <= 0 else 2 * val - 1)

    def align(self):
        while len(self.bits) % 8 != 0:
            self.bits.append(0)

    def raw_bytes(self, bs):
        self.align()
        for b in bs:
            self.u(8, b)

    def rbsp(self):
        self.bit(1)
        self.align()
        out = bytearray()
        for i in range(0, len(self.bits), 8):
            v = 0
            for j in range(8):
                v = (v << 1) | self.bits[i + j]
            out.append(v)
        return bytes(out)


def _annexb_nal(hdr, rbsp):
    ebsp = bytearray()
    zr = 0
    for b in rbsp:
        if zr >= 2 and b <= 3:
            ebsp.append(3)
            zr = 0
        ebsp.append(b)
        zr = zr + 1 if b == 0 else 0
    return b"\x00\x00\x00\x01" + bytes([hdr]) + bytes(ebsp)


def _make_sps(w_mbs, h_mbs, high_profile=False):
    w = _BitWriter()
    if high_profile:
        w.u(8, 100)
        w.u(8, 0x00)
        w.u(8, 10)
        w.ue(0)
        w.ue(1)
        w.ue(0)
        w.ue(0)
        w.bit(0)
        w.bit(0)
    else:
        w.u(8, 66)
        w.u(8, 0xC0)
        w.u(8, 10)
        w.ue(0)
    w.ue(0)
    w.ue(2)
    w.ue(0)
    w.bit(0)
    w.ue(w_mbs - 1)
    w.ue(h_mbs - 1)
    w.bit(1)
    w.bit(1)
    w.bit(0)
    w.bit(0)
    return _annexb_nal(0x67, w.rbsp())


def _make_pps(transform_8x8=False):
    w = _BitWriter()
    w.ue(0)
    w.ue(0)
    w.bit(0)
    w.bit(0)
    w.ue(0)
    w.ue(0)
    w.ue(0)
    w.bit(0)
    w.u(2, 0)
    w.se(0)
    w.se(0)
    w.se(0)
    w.bit(1)
    w.bit(0)
    w.bit(0)
    if transform_8x8:
        w.bit(1)
        w.bit(0)
        w.se(0)
    return _annexb_nal(0x68, w.rbsp())


def _start_idr_slice(qp=26):
    w = _BitWriter()
    w.ue(0)
    w.ue(7)
    w.ue(0)
    w.u(4, 0)
    w.ue(0)
    w.bit(0)
    w.bit(0)
    w.se(qp - 26)
    w.ue(1)
    return w


def _write_intra_pred_mode(w, mode, pred_mode=2):
    if mode == pred_mode:
        w.bit(1)
    else:
        w.bit(0)
        w.u(3, mode if mode < pred_mode else mode - 1)


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
        if not FFMPEG:
            raise unittest.SkipTest("reference FFmpeg is unavailable")

    def probe(self, *args):
        res = subprocess.run(
            [str(BINARY), "h264-intra-probe", *(str(a) for a in args)],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(res.returncode, 0, res.stderr)
        return [int(x) for x in res.stdout.strip().split(",") if x != ""]

    def decode_ffmpeg_yuv420p(self, stream, w_px, h_px):
        res = subprocess.run(
            [FFMPEG, "-hide_banner", "-loglevel", "error", "-f", "h264", "-i", "pipe:0",
             "-f", "rawvideo", "-pix_fmt", "yuv420p", "pipe:1"],
            input=stream, capture_output=True, timeout=30)
        self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace"))
        self.assertEqual(len(res.stdout), w_px * h_px * 3 // 2)
        return res.stdout

    @staticmethod
    def extract_mb(frame, w_px, h_px, mb_x, mb_y):
        y_sz = w_px * h_px
        uv_w, uv_h = w_px // 2, h_px // 2
        uv_sz = uv_w * uv_h
        y_p, u_p, v_p = frame[:y_sz], frame[y_sz:y_sz + uv_sz], frame[y_sz + uv_sz:]
        y_mb = [y_p[(mb_y * 16 + r) * w_px + mb_x * 16 + c] for r in range(16) for c in range(16)]
        u_mb = [u_p[(mb_y * 8 + r) * uv_w + mb_x * 8 + c] for r in range(8) for c in range(8)]
        v_mb = [v_p[(mb_y * 8 + r) * uv_w + mb_x * 8 + c] for r in range(8) for c in range(8)]
        return y_mb, u_mb, v_mb

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
                            ("1", ["0", "1", "2"]), ("2", ["3"]), ("3", [])):
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
            FFMPEG, "-hide_banner", "-loglevel", "error", "-f", "lavfi",
            "-i", "color=c=gray:s=16x16", "-frames:v", "1", "-c:v", "libx264",
            "-qp", "12", "-profile:v", "high", "-f", "h264", "-"], capture_output=True, timeout=30)
        self.assertEqual(frame.returncode, 0, frame.stderr.decode(errors="replace"))
        self.assertGreater(len(frame.stdout), 32)
        for pad in ("0", "3", "7"):
            ipcm = subprocess.run(
                [str(BINARY), "h264-intra-probe", "ipcm-roundtrip", pad],
                capture_output=True, text=True, timeout=60)
            self.assertEqual(ipcm.returncode, 0, ipcm.stderr)
            ipcm_body = json.loads(ipcm.stdout)
            self.assertTrue(ipcm_body["ok"])
            self.assertEqual(ipcm_body["pcm_bytes"], 384)
            self.assertEqual(ipcm_body["mb_type"], 25)
            self.assertEqual(ipcm_body["nz"], 16)

    def test_ipcm_annexb_ffmpeg_pixel_equality(self):
        with tempfile.TemporaryDirectory() as td:
            td = Path(td)
            raw = bytes(((i * 29 + (i // 16) * 13 + 7) % 256) for i in range(256))
            raw += bytes(((110 + i * 7) % 256) for i in range(64))
            raw += bytes(((140 + i * 5) % 256) for i in range(64))
            raw = bytearray(raw)
            raw[10:13] = b"\x00\x00\x00"
            raw[13] = 1
            raw[20:22] = b"\x00\x00"
            raw[22] = 3
            raw_path = td / "ipcm.yuv"
            h264_path = td / "ipcm.h264"
            decoded_path = td / "decoded.yuv"
            raw_path.write_bytes(bytes(raw))
            enc = subprocess.run(
                [str(BINARY), "h264-intra-probe", "ipcm-encode-annexb", str(raw_path), str(h264_path)],
                capture_output=True, timeout=60)
            self.assertEqual(enc.returncode, 0, enc.stderr)
            ffmpeg_dec = subprocess.run([
                FFMPEG, "-hide_banner", "-loglevel", "error", "-f", "h264",
                "-i", str(h264_path), "-f", "rawvideo", "-pix_fmt", "yuv420p", str(decoded_path)],
                capture_output=True, timeout=60)
            self.assertEqual(ffmpeg_dec.returncode, 0, ffmpeg_dec.stderr.decode(errors="replace"))
            self.assertEqual(decoded_path.read_bytes(), bytes(raw))
            lean_dec = subprocess.run(
                [str(BINARY), "h264-intra-probe", "ipcm-decode-annexb", str(h264_path), str(td / "lean.yuv")],
                capture_output=True, timeout=60)
            self.assertEqual(lean_dec.returncode, 0, lean_dec.stderr)
            self.assertEqual((td / "lean.yuv").read_bytes(), bytes(raw))

    def test_ffmpeg_pixel_equality_pred_and_idct(self):
        mb00_y = [(i * 19 + 23) & 0xFF for i in range(256)]
        mb10_y = [(i * 29 + 41) & 0xFF for i in range(256)]
        mb01_y = [(i * 31 + 67) & 0xFF for i in range(256)]
        mb00_u = [(i * 13 + 77) & 0xFF for i in range(64)]
        mb10_u = [(i * 7 + 105) & 0xFF for i in range(64)]
        mb01_u = [(i * 23 + 53) & 0xFF for i in range(64)]
        uv_fill = [128] * 128
        pcm00 = bytes(mb00_y + mb00_u + [(i * 17 + 91) & 0xFF for i in range(64)])
        pcm10 = bytes(mb10_y + mb10_u + [(i * 11 + 149) & 0xFF for i in range(64)])
        pcm01 = bytes(mb01_y + mb01_u + [(i * 19 + 173) & 0xFF for i in range(64)])
        tl_y = mb00_y[15 * 16 + 15]
        top_y = [mb10_y[15 * 16 + c] for c in range(16)]
        left_y = [mb01_y[r * 16 + 15] for r in range(16)]
        tl_u = mb00_u[7 * 8 + 7]
        top_u = [mb10_u[7 * 8 + c] for c in range(8)]
        left_u = [mb01_u[r * 8 + 7] for r in range(8)]
        for m16 in range(4):
            for cm in range(4):
                w = _start_idr_slice(26)
                for pcm in (pcm00, pcm10, pcm01):
                    w.ue(25)
                    w.raw_bytes(pcm)
                w.ue(1 + m16)
                w.ue(cm)
                w.se(0)
                w.u(6, 0b000011)
                frame = self.decode_ffmpeg_yuv420p(
                    _make_sps(2, 2) + _make_pps() + _annexb_nal(0x65, w.rbsp()), 32, 32)
                y_ff, u_ff, _ = self.extract_mb(frame, 32, 32, 1, 1)
                self.assertEqual(y_ff, self.probe("pred16x16", m16, 1, 1, tl_y, *left_y, *top_y))
                self.assertEqual(u_ff, self.probe("pred-chroma", cm, 1, 1, tl_u, *left_u, *top_u))
        for m4 in range(9):
            w = _start_idr_slice(26)
            for pcm in (pcm00, pcm10, pcm01):
                w.ue(25)
                w.raw_bytes(pcm)
            w.ue(0)
            _write_intra_pred_mode(w, m4, 2)
            for _ in range(15):
                w.bit(1)
            w.ue(0)
            w.ue(3)
            frame = self.decode_ffmpeg_yuv420p(
                _make_sps(2, 2) + _make_pps() + _annexb_nal(0x65, w.rbsp()), 32, 32)
            y_ff, _, _ = self.extract_mb(frame, 32, 32, 1, 1)
            blk0_ff = [y_ff[r * 16 + c] for r in range(4) for c in range(4)]
            self.assertEqual(
                blk0_ff, self.probe("pred4x4", m4, 1, 1, 1, 1, tl_y, *left_y[:4], *top_y[:4], *top_y[4:8]))
        pcm00_8 = bytes(mb00_y + uv_fill)
        pcm10_8 = bytes(mb10_y + uv_fill)
        pcm01_8 = bytes(mb01_y + uv_fill)
        for m8 in range(9):
            w = _start_idr_slice(26)
            for pcm in (pcm00_8, pcm10_8, pcm01_8):
                w.ue(25)
                w.raw_bytes(pcm)
            w.ue(0)
            w.bit(1)
            _write_intra_pred_mode(w, m8, 2)
            _write_intra_pred_mode(w, m8, min(m8, 2))
            w.bit(1)
            w.bit(1)
            w.ue(0)
            w.ue(3)
            frame = self.decode_ffmpeg_yuv420p(
                _make_sps(2, 2, True) + _make_pps(True) + _annexb_nal(0x65, w.rbsp()), 32, 32)
            y_ff, _, _ = self.extract_mb(frame, 32, 32, 1, 1)
            blk0_ff = [y_ff[r * 16 + c] for r in range(8) for c in range(8)]
            self.assertEqual(
                blk0_ff,
                self.probe("pred8x8", m8, 1, 1, 1, 1, tl_y, *left_y[:8], *top_y[:8], *top_y[8:16]))
            blk1_left = [blk0_ff[r * 8 + 7] for r in range(8)]
            blk1_ff = [y_ff[r * 16 + (8 + c)] for r in range(8) for c in range(8)]
            self.assertEqual(
                blk1_ff,
                self.probe("pred8x8", m8, 1, 1, 0, 1, top_y[7], *blk1_left, *top_y[8:16], *([0] * 8)))
        tz_tc1 = {
            0: (1, 0b1), 1: (3, 0b011), 2: (3, 0b010), 3: (4, 0b0011),
            4: (4, 0b0010), 5: (5, 0b00011), 6: (5, 0b00010), 7: (6, 0b000011),
            8: (6, 0b000010), 9: (7, 0b0000011), 10: (7, 0b0000010), 11: (8, 0b00000011),
            12: (8, 0b00000010), 13: (9, 0b000000011), 14: (9, 0b000000010), 15: (9, 0b000000001),
        }
        zigzag4 = [
            (0, 0), (0, 1), (1, 0), (2, 0), (1, 1), (0, 2), (0, 3), (1, 2),
            (2, 1), (3, 0), (3, 1), (2, 2), (1, 3), (2, 3), (3, 2), (3, 3),
        ]
        for qp in (12, 30):
            for zpos in range(16):
                for sign_val in (1, -1):
                    w = _start_idr_slice(qp)
                    w.ue(0)
                    for _ in range(16):
                        w.bit(1)
                    w.ue(0)
                    w.ue(29)
                    w.se(0)
                    w.u(2, 0b01)
                    w.bit(0 if sign_val == 1 else 1)
                    nb, vc = tz_tc1[zpos]
                    w.u(nb, vc)
                    w.bit(1)
                    w.bit(1)
                    w.bit(1)
                    frame = self.decode_ffmpeg_yuv420p(
                        _make_sps(1, 1) + _make_pps() + _annexb_nal(0x65, w.rbsp()), 16, 16)
                    y_ff, _, _ = self.extract_mb(frame, 16, 16, 0, 0)
                    blk0_ff = [y_ff[r * 16 + c] for r in range(4) for c in range(4)]
                    r_idx, c_idx = zigzag4[zpos]
                    levels = [0] * 16
                    levels[r_idx * 4 + c_idx] = sign_val
                    res_lean = self.probe("idct4x4", qp, "none", *levels)
                    self.assertEqual(blk0_ff, [max(0, min(255, 128 + v)) for v in res_lean])


if __name__ == "__main__":
    unittest.main()
