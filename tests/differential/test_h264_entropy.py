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


if __name__ == "__main__":
    unittest.main()
