import hashlib
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"


def _make_yuv420p(w: int, h: int, frames: int) -> bytes:
    out = bytearray()
    cw, ch = w // 2, h // 2
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 17 + y * 31 + f * 53 + ((x * y) & 0x3F)) & 0xFF
                out.append(v)
        for y in range(ch):
            for x in range(cw):
                out.append((128 + ((x * 11 - y * 13 + f * 29) & 0x7F) - 64) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                out.append((128 + ((y * 19 - x * 7 - f * 23) & 0x7F) - 64) & 0xFF)
    return bytes(out)


def _make_gray8(w: int, h: int, frames: int) -> bytes:
    out = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                out.append((x * 23 + y * 41 + f * 67 + (x ^ (y * 3))) & 0xFF)
    return bytes(out)


def _make_yuv420p10le(w: int, h: int, frames: int) -> bytes:
    out = bytearray()
    cw, ch = w // 2, h // 2
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 73 + y * 139 + f * 211 + ((x ^ y) * 19)) & 0x3FF
                out += v.to_bytes(2, "little")
        for y in range(ch):
            for x in range(cw):
                v = (512 + ((x * 43 - y * 59 + f * 97) % 401) - 200) & 0x3FF
                out += v.to_bytes(2, "little")
        for y in range(ch):
            for x in range(cw):
                v = (512 + ((y * 61 - x * 37 - f * 83) % 401) - 200) & 0x3FF
                out += v.to_bytes(2, "little")
    return bytes(out)


class H264EntropyDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not (BINARY.stat().st_mode & 0o111):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        ref = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not ref:
            raise unittest.SkipTest("reference FFmpeg is unavailable")
        cls.ffmpeg = str(Path(ref).resolve())
        enc_check = subprocess.run(
            [cls.ffmpeg, "-hide_banner", "-encoders"],
            capture_output=True,
            text=True,
            timeout=15,
        )
        cls.has_libx264 = "libx264" in enc_check.stdout
        cls.isolated_env = {
            "PATH": "/nonexistent",
            "LEANAV_FFMPEG_BIN": "/nonexistent/ffmpeg",
            "LEANAV_FFPROBE_BIN": "/nonexistent/ffprobe",
            "LANG": "C",
            "LC_ALL": "C",
        }

    def run_isolated(self, *args: str):
        return subprocess.run(
            [str(BINARY), *args],
            env=self.isolated_env,
            capture_output=True,
            timeout=60,
        )

    def run_ref(self, *args: str):
        return subprocess.run(
            [self.ffmpeg, "-nostdin", "-hide_banner", "-loglevel", "error", *args],
            capture_output=True,
            timeout=60,
        )

    def decode_raw(self, h264_path: Path, pix_fmt: str) -> bytes:
        res = self.run_ref("-i", str(h264_path), "-f", "rawvideo", "-pix_fmt", pix_fmt, "-")
        self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace"))
        return res.stdout

    def encode_h264(
        self,
        raw_path: Path,
        out_path: Path,
        w: int,
        h: int,
        src_pix_fmt: str,
        dst_pix_fmt: str,
        profile: str,
        qp: int,
        x264_params: str,
    ):
        res = self.run_ref(
            "-y",
            "-f",
            "rawvideo",
            "-pix_fmt",
            src_pix_fmt,
            "-video_size",
            f"{w}x{h}",
            "-framerate",
            "25",
            "-i",
            str(raw_path),
            "-c:v",
            "libx264",
            "-pix_fmt",
            dst_pix_fmt,
            "-profile:v",
            profile,
            "-qp",
            str(qp),
            "-x264-params",
            x264_params,
            "-f",
            "h264",
            str(out_path),
        )
        self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace"))

    def assert_all_modes_pixel_exact(self, src_264: Path, pix_fmt: str, workdir: Path, tag: str):
        ref_pixels = self.decode_raw(src_264, pix_fmt)
        self.assertGreater(len(ref_pixels), 0)
        ref_sha = hashlib.sha256(ref_pixels).hexdigest()

        out_preserve = workdir / f"{tag}_preserve.264"
        out_cavlc = workdir / f"{tag}_cavlc.264"
        out_cabac = workdir / f"{tag}_cabac.264"
        out_roundtrip_cavlc = workdir / f"{tag}_cabac_to_cavlc.264"
        out_roundtrip_cabac = workdir / f"{tag}_cavlc_to_cabac.264"

        for mode, dst in (
            ("preserve", out_preserve),
            ("cavlc", out_cavlc),
            ("cabac", out_cabac),
        ):
            r = self.run_isolated("h264-entropy", "transcode", mode, str(src_264), str(dst))
            self.assertEqual(r.returncode, 0, f"{tag} {mode}: {r.stderr.decode(errors='replace')}")
            dec = self.decode_raw(dst, pix_fmt)
            self.assertEqual(hashlib.sha256(dec).hexdigest(), ref_sha, f"{tag} {mode} pixel mismatch")

        r1 = self.run_isolated("h264-entropy", "transcode", "cavlc", str(out_cabac), str(out_roundtrip_cavlc))
        self.assertEqual(r1.returncode, 0, r1.stderr.decode(errors="replace"))
        self.assertEqual(hashlib.sha256(self.decode_raw(out_roundtrip_cavlc, pix_fmt)).hexdigest(), ref_sha)

        r2 = self.run_isolated("h264-entropy", "transcode", "cabac", str(out_cavlc), str(out_roundtrip_cabac))
        self.assertEqual(r2.returncode, 0, r2.stderr.decode(errors="replace"))
        self.assertEqual(hashlib.sha256(self.decode_raw(out_roundtrip_cabac, pix_fmt)).hexdigest(), ref_sha)

    def test_baseline_main_high_ipb_bpyramid_matrix(self):
        if not self.has_libx264:
            self.skipTest("libx264 encoder unavailable in reference FFmpeg")
        with tempfile.TemporaryDirectory(prefix="leanav-h264-entropy-") as tmp:
            root = Path(tmp)
            w, h, frames = 96, 64, 8
            raw_path = root / "src_420.yuv"
            raw_path.write_bytes(_make_yuv420p(w, h, frames))

            cases = [
                ("baseline_ip_cavlc", "baseline", 22, "cabac=0:ref=2:bframes=0:subme=6:trellis=0:annexb=1"),
                ("main_ipb_cabac", "main", 24, "cabac=1:ref=3:bframes=2:b-pyramid=none:weightp=2:weightb=1:annexb=1"),
                ("main_ipb_cavlc", "main", 24, "cabac=0:ref=3:bframes=2:b-pyramid=none:weightp=2:weightb=1:annexb=1"),
                ("high_8x8_bpyramid_cabac", "high", 20, "cabac=1:8x8dct=1:ref=4:bframes=3:b-pyramid=normal:weightp=2:weightb=1:aq-mode=2:annexb=1"),
                ("high_8x8_bpyramid_cavlc", "high", 20, "cabac=0:8x8dct=1:ref=4:bframes=3:b-pyramid=normal:weightp=2:weightb=1:aq-mode=2:annexb=1"),
                ("high_multislicemb_cabac", "high", 26, "cabac=1:8x8dct=1:bframes=2:slice-max-mbs=12:annexb=1"),
                ("high_multislicemb_cavlc", "high", 26, "cabac=0:8x8dct=1:bframes=2:slice-max-mbs=12:annexb=1"),
            ]
            for tag, profile, qp, params in cases:
                with self.subTest(case=tag):
                    src_264 = root / f"{tag}.264"
                    self.encode_h264(raw_path, src_264, w, h, "yuv420p", "yuv420p", profile, qp, params)
                    self.assert_all_modes_pixel_exact(src_264, "yuv420p", root, tag)

    def test_high10_10bit_large_escape_levels_pixel_exact(self):
        if not self.has_libx264:
            self.skipTest("libx264 encoder unavailable in reference FFmpeg")
        with tempfile.TemporaryDirectory(prefix="leanav-h264-hi10-") as tmp:
            root = Path(tmp)
            w, h, frames = 64, 48, 5
            raw10 = root / "src_420p10le.yuv"
            raw10.write_bytes(_make_yuv420p10le(w, h, frames))

            for tag, cabac_flag in (("hi10_qp2_cavlc", 0), ("hi10_qp2_cabac", 1)):
                with self.subTest(case=tag):
                    src_264 = root / f"{tag}.264"
                    self.encode_h264(
                        raw10,
                        src_264,
                        w,
                        h,
                        "yuv420p10le",
                        "yuv420p10le",
                        "high10",
                        2,
                        f"cabac={cabac_flag}:8x8dct=1:ref=2:bframes=2:b-pyramid=normal:annexb=1",
                    )
                    self.assert_all_modes_pixel_exact(src_264, "yuv420p10le", root, tag)

    def test_monochrome_high_profile_pixel_exact(self):
        if not self.has_libx264:
            self.skipTest("libx264 encoder unavailable in reference FFmpeg")
        with tempfile.TemporaryDirectory(prefix="leanav-h264-gray-") as tmp:
            root = Path(tmp)
            w, h, frames = 64, 48, 4
            raw_gray = root / "src_gray.yuv"
            raw_gray.write_bytes(_make_gray8(w, h, frames))

            for tag, cabac_flag in (("gray_cavlc", 0), ("gray_cabac", 1)):
                with self.subTest(case=tag):
                    src_264 = root / f"{tag}.264"
                    self.encode_h264(
                        raw_gray,
                        src_264,
                        w,
                        h,
                        "gray",
                        "gray",
                        "high",
                        18,
                        f"cabac={cabac_flag}:8x8dct=1:ref=2:bframes=1:annexb=1",
                    )
                    self.assert_all_modes_pixel_exact(src_264, "gray", root, tag)

    def test_cli_usage_and_fail_closed_rejections(self):
        with tempfile.TemporaryDirectory(prefix="leanav-h264-neg-") as tmp:
            root = Path(tmp)
            empty_in = root / "empty.264"
            empty_in.write_bytes(b"")
            dpa_in = root / "dpa.264"
            dpa_in.write_bytes(b"\x00\x00\x00\x01\x62\xAA\xBB")
            bad_sps = root / "badsps.264"
            bad_sps.write_bytes(b"\x00\x00\x00\x01\x67\x42")
            out_path = root / "out.264"

            r_mode = self.run_isolated("h264-entropy", "transcode", "bogus", str(empty_in), str(out_path))
            self.assertEqual(r_mode.returncode, 2)
            self.assertFalse(out_path.exists())

            r_usage = self.run_isolated("h264-entropy")
            self.assertEqual(r_usage.returncode, 2)

            for bad_file in (empty_in, dpa_in, bad_sps):
                r_bad = self.run_isolated("h264-entropy", "transcode", "preserve", str(bad_file), str(out_path))
                self.assertEqual(r_bad.returncode, 1)
                self.assertFalse(out_path.exists())

    def test_cavlc_8x8_unequal_subblock_totalcoeff_nc_vs_ffmpeg(self):
        if not self.has_libx264:
            self.skipTest("libx264 encoder unavailable in reference FFmpeg")
        with tempfile.TemporaryDirectory(prefix="leanav-h264-8x8-nc-") as tmp:
            root = Path(tmp)
            w, h = 64, 48
            out = bytearray()
            for f in range(2):
                for y in range(h):
                    for x in range(w):
                        base = ((x * 29 + y * 47) ^ ((x * y) & 0x3F)) & 0xFF
                        if f == 0:
                            v = base
                        else:
                            delta = ((x * 19 ^ y * 37) % 23) - 11 if ((x + y) % 3 == 0) else 0
                            v = max(0, min(255, base + delta * 3))
                        out.append(v)
                out.extend([128] * (2 * (w // 2) * (h // 2)))
            raw_path = root / "unequal_8x8.yuv"
            raw_path.write_bytes(bytes(out))

            for tag, cabac_flag in (("unequal_8x8_cavlc", 0), ("unequal_8x8_cabac", 1)):
                with self.subTest(case=tag):
                    src_264 = root / f"{tag}.264"
                    self.encode_h264(
                        raw_path,
                        src_264,
                        w,
                        h,
                        "yuv420p",
                        "yuv420p",
                        "high",
                        28,
                        f"cabac={cabac_flag}:8x8dct=1:bframes=0:ref=1:aq-mode=0:trellis=0:annexb=1",
                    )
                    self.assert_all_modes_pixel_exact(src_264, "yuv420p", root, tag)

    def test_ipcm_multi_mb_midbyte_cabac_cavlc_roundtrip(self):
        def pack_nal(nal_hdr: int, bits: list[int]) -> bytes:
            padded = list(bits) + [1]
            while len(padded) % 8 != 0:
                padded.append(0)
            rbsp = bytearray()
            for i in range(0, len(padded), 8):
                v = 0
                for b in padded[i : i + 8]:
                    v = (v << 1) | b
                rbsp.append(v)
            out = bytearray([0, 0, 0, 1, nal_hdr])
            zeros = 0
            for b in rbsp:
                if zeros == 2 and b <= 3:
                    out.append(3)
                    zeros = 0
                out.append(b)
                zeros = zeros + 1 if b == 0 else 0
            return bytes(out)

        def put_u(bits: list[int], val: int, n: int):
            for i in range(n - 1, -1, -1):
                bits.append((val >> i) & 1)

        def put_ue(bits: list[int], val: int):
            x = val + 1
            k = x.bit_length() - 1
            put_u(bits, 0, k)
            put_u(bits, x, k + 1)

        def put_se(bits: list[int], val: int):
            put_ue(bits, 0 if val == 0 else (2 * val - 1 if val > 0 else -2 * val))

        def put_pcm(bits: list[int], pcm: bytes):
            while len(bits) % 8 != 0:
                bits.append(0)
            for b in pcm:
                put_u(bits, b, 8)

        sps: list[int] = []
        put_u(sps, 66, 8); put_u(sps, 0xC0, 8); put_u(sps, 30, 8)
        put_ue(sps, 0); put_ue(sps, 0); put_ue(sps, 2); put_ue(sps, 0); put_u(sps, 0, 1)
        put_ue(sps, 1); put_ue(sps, 1); put_u(sps, 1, 1); put_u(sps, 1, 1); put_u(sps, 0, 1); put_u(sps, 0, 1)

        pps: list[int] = []
        put_ue(pps, 0); put_ue(pps, 0); put_u(pps, 0, 1); put_u(pps, 0, 1)
        put_ue(pps, 0); put_ue(pps, 0); put_ue(pps, 0); put_u(pps, 0, 1); put_u(pps, 0, 2)
        put_se(pps, 0); put_se(pps, 0); put_se(pps, 0); put_u(pps, 1, 1); put_u(pps, 0, 1); put_u(pps, 0, 1)

        pcm1 = bytes(((0x17 + i * 37 + (i >> 3) * 11) & 0xFF) or 1 for i in range(384))
        pcm3 = bytes(((0x2B + i * 53 + (i >> 2) * 7) & 0xFF) or 2 for i in range(384))
        sl: list[int] = []
        put_ue(sl, 0); put_ue(sl, 7); put_ue(sl, 0); put_u(sl, 0, 4); put_ue(sl, 0)
        put_u(sl, 0, 1); put_u(sl, 0, 1); put_se(sl, 0); put_ue(sl, 1)
        put_ue(sl, 3); put_ue(sl, 0); put_se(sl, 0); put_u(sl, 1, 1)
        put_ue(sl, 25); put_pcm(sl, pcm1)
        put_ue(sl, 1); put_ue(sl, 0); put_se(sl, 0); put_u(sl, 1, 1)
        put_ue(sl, 25); put_pcm(sl, pcm3)

        with tempfile.TemporaryDirectory(prefix="leanav-h264-ipcm-") as tmp:
            root = Path(tmp)
            src_264 = root / "ipcm_mixed_cavlc.264"
            src_264.write_bytes(pack_nal(0x67, sps) + pack_nal(0x68, pps) + pack_nal(0x65, sl))
            r_src = self.run_ref("-i", str(src_264), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-")
            self.assertEqual(r_src.returncode, 0, r_src.stderr.decode(errors="replace"))
            self.assertEqual(r_src.stderr, b"")
            ref_sha = hashlib.sha256(r_src.stdout).hexdigest()

            out_cabac = root / "ipcm_cabac.264"
            out_cabac_pres = root / "ipcm_cabac_preserve.264"
            out_rt_cavlc = root / "ipcm_cabac_to_cavlc.264"
            for mode, inp, dst in (
                ("cabac", src_264, out_cabac),
                ("preserve", out_cabac, out_cabac_pres),
                ("cavlc", out_cabac, out_rt_cavlc),
            ):
                rt = self.run_isolated("h264-entropy", "transcode", mode, str(inp), str(dst))
                self.assertEqual(rt.returncode, 0, rt.stderr.decode(errors="replace"))
                rd = self.run_ref("-i", str(dst), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-")
                self.assertEqual(rd.returncode, 0, rd.stderr.decode(errors="replace"))
                self.assertEqual(rd.stderr, b"")
                self.assertEqual(hashlib.sha256(rd.stdout).hexdigest(), ref_sha, f"ipcm {mode} mismatch")


if __name__ == "__main__":
    unittest.main()
