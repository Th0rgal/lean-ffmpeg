#!/usr/bin/env python3
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG_BIN = shutil.which("ffmpeg")
FFPROBE_BIN = shutil.which("ffprobe")


def _run_lffmpeg(argv: list[str], timeout: int = 90) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(BINARY), *argv],
        cwd=ROOT,
        env={"PATH": "/nonexistent"},
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _ffprobe_json(path: Path) -> dict:
    proc = subprocess.run(
        [
            FFPROBE_BIN,
            "-v",
            "error",
            "-show_format",
            "-show_streams",
            "-show_frames",
            "-of",
            "json",
            str(path),
        ],
        capture_output=True,
        text=True,
        timeout=60,
        check=True,
    )
    return json.loads(proc.stdout)


def _make_raw_10bit_yuv420p(w: int, h: int, frames: int = 2) -> bytes:
    buf = bytearray()
    cw, ch = w // 2, h // 2
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                val = min(1023, 128 + ((x * 23 + y * 19 + f * 37) % 700))
                buf += int(val).to_bytes(2, "little")
        for y in range(ch):
            for x in range(cw):
                u = min(1023, 480 + ((x * 7 + y * 11 + f * 5) % 64))
                buf += int(u).to_bytes(2, "little")
        for y in range(ch):
            for x in range(cw):
                v = min(1023, 520 + ((x * 9 + y * 13 + f * 7) % 64))
                buf += int(v).to_bytes(2, "little")
    return bytes(buf)


def _make_raw_12bit_yuv444p(w: int, h: int, frames: int = 1) -> bytes:
    buf = bytearray()
    for f in range(frames):
        for p in range(3):
            for y in range(h):
                for x in range(w):
                    val = min(4095, 256 + ((x * 41 + y * 29 + p * 113 + f * 53) % 3200))
                    buf += int(val).to_bytes(2, "little")
    return bytes(buf)


class TestP11E2EPipeline(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        assert BINARY.exists(), f"Missing {BINARY}"
        assert FFMPEG_BIN is not None, "Missing ffmpeg oracle on PATH"
        assert FFPROBE_BIN is not None, "Missing ffprobe oracle on PATH"
        cls.tmp = tempfile.TemporaryDirectory(prefix="leanav-p11-e2e-")
        cls.work = Path(cls.tmp.name)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tmp.cleanup()

    def test_01_raw_10bit_to_hevc_hdr10_mp4_and_mkv_cross_remux(self) -> None:
        raw_in = self.work / "in_10b.yuv"
        raw_in.write_bytes(_make_raw_10bit_yuv420p(16, 16, frames=2))
        mp4_out = self.work / "hevc_hdr10.mp4"
        mkv_out = self.work / "hevc_hdr10_remux.mkv"
        mp4_roundtrip = self.work / "hevc_hdr10_roundtrip.mp4"

        res = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "25",
                "-i",
                str(raw_in),
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "smpte2084",
                "-colorspace",
                "bt2020nc",
                "-x265-params",
                "qp=0:master-display=G(13250,34500)B(7500,3000)R(34000,16000)WP(15635,16450)L(10000000,50):max-cll=1000,400",
                "-y",
                str(mp4_out),
            ]
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        probe_mp4 = _ffprobe_json(mp4_out)
        vstream = probe_mp4["streams"][0]
        self.assertEqual(vstream["codec_name"], "hevc")
        self.assertEqual(vstream["width"], 16)
        self.assertEqual(vstream["height"], 16)
        self.assertEqual(vstream.get("color_primaries"), "bt2020")
        self.assertEqual(vstream.get("color_transfer"), "smpte2084")

        r_mkv = _run_lffmpeg(["-i", str(mp4_out), "-c", "copy", "-y", str(mkv_out)])
        self.assertEqual(r_mkv.returncode, 0, r_mkv.stdout + r_mkv.stderr)
        probe_mkv = _ffprobe_json(mkv_out)
        self.assertEqual(probe_mkv["streams"][0]["codec_name"], "hevc")
        self.assertEqual(probe_mkv["streams"][0].get("color_primaries"), "bt2020")
        self.assertEqual(probe_mkv["streams"][0].get("color_transfer"), "smpte2084")

        r_back = _run_lffmpeg(["-i", str(mkv_out), "-c", "copy", "-y", str(mp4_roundtrip)])
        self.assertEqual(r_back.returncode, 0, r_back.stdout + r_back.stderr)
        probe_back = _ffprobe_json(mp4_roundtrip)
        self.assertEqual(probe_back["streams"][0]["codec_name"], "hevc")
        self.assertEqual(probe_back["streams"][0].get("color_primaries"), "bt2020")
        self.assertEqual(probe_back["streams"][0].get("color_transfer"), "smpte2084")

    def test_02_hevc_hdr10_tonemap_to_8bit_bt709_h264_mp4(self) -> None:
        raw_in = self.work / "in_hdr_src.yuv"
        raw_in.write_bytes(_make_raw_10bit_yuv420p(16, 16, frames=2))
        hdr_mp4 = self.work / "hdr_src.mp4"
        sdr_mp4 = self.work / "sdr_tonemapped.mp4"

        res_hdr = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "25",
                "-i",
                str(raw_in),
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "smpte2084",
                "-colorspace",
                "bt2020nc",
                "-y",
                str(hdr_mp4),
            ]
        )
        self.assertEqual(res_hdr.returncode, 0, res_hdr.stdout + res_hdr.stderr)

        res_sdr = _run_lffmpeg(
            [
                "-i",
                str(hdr_mp4),
                "-vf",
                "colorspace=all=bt709,tonemap=hable,format=yuv420p",
                "-c:v",
                "h264",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(sdr_mp4),
            ]
        )
        self.assertEqual(res_sdr.returncode, 0, res_sdr.stdout + res_sdr.stderr)
        probe_sdr = _ffprobe_json(sdr_mp4)
        self.assertEqual(probe_sdr["streams"][0]["codec_name"], "h264")
        self.assertEqual(probe_sdr["streams"][0]["pix_fmt"], "yuv420p")
        self.assertEqual(len(probe_sdr["frames"]), 2)

    def test_03_h264_high444p_12bit_lossless_roundtrip(self) -> None:
        raw_12b = _make_raw_12bit_yuv444p(16, 16, frames=1)
        raw_in = self.work / "in_444_12b.yuv"
        raw_in.write_bytes(raw_12b)
        mp4_out = self.work / "h264_hi444_12b.mp4"
        raw_back = self.work / "out_444_12b.yuv"

        res_enc = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv444p12le",
                "-s",
                "16x16",
                "-r",
                "25",
                "-i",
                str(raw_in),
                "-c:v",
                "h264",
                "-pix_fmt",
                "yuv444p12le",
                "-qp",
                "0",
                "-y",
                str(mp4_out),
            ]
        )
        self.assertEqual(res_enc.returncode, 0, res_enc.stdout + res_enc.stderr)
        probe = _ffprobe_json(mp4_out)
        self.assertEqual(probe["streams"][0]["codec_name"], "h264")
        self.assertEqual(probe["streams"][0]["pix_fmt"], "yuv444p12le")

        res_dec = _run_lffmpeg(
            [
                "-i",
                str(mp4_out),
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv444p12le",
                "-y",
                str(raw_back),
            ]
        )
        self.assertEqual(res_dec.returncode, 0, res_dec.stdout + res_dec.stderr)
        self.assertEqual(raw_back.read_bytes(), raw_12b)

    def test_04_av1_10bit_film_grain_mp4_and_webm(self) -> None:
        raw_in = self.work / "in_av1_10b.yuv"
        raw_in.write_bytes(_make_raw_10bit_yuv420p(16, 16, frames=1))
        mp4_out = self.work / "av1_10b_fg.mp4"
        webm_out = self.work / "av1_10b_fg.webm"

        res_mp4 = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "25",
                "-i",
                str(raw_in),
                "-c:v",
                "av1",
                "-pix_fmt",
                "yuv420p10le",
                "-svtav1-params",
                "film-grain=12",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "arib-std-b67",
                "-colorspace",
                "bt2020nc",
                "-y",
                str(mp4_out),
            ]
        )
        self.assertEqual(res_mp4.returncode, 0, res_mp4.stdout + res_mp4.stderr)
        probe_mp4 = _ffprobe_json(mp4_out)
        self.assertEqual(probe_mp4["streams"][0]["codec_name"], "av1")
        self.assertEqual(probe_mp4["streams"][0]["width"], 16)
        self.assertEqual(probe_mp4["streams"][0]["height"], 16)

        res_webm = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "25",
                "-i",
                str(raw_in),
                "-c:v",
                "av1",
                "-pix_fmt",
                "yuv420p10le",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "arib-std-b67",
                "-colorspace",
                "bt2020nc",
                "-y",
                str(webm_out),
            ]
        )
        self.assertEqual(res_webm.returncode, 0, res_webm.stdout + res_webm.stderr)
        probe_webm = _ffprobe_json(webm_out)
        self.assertEqual(probe_webm["streams"][0]["codec_name"], "av1")

    def test_05_p010le_and_bayer_dither_filter_pipeline(self) -> None:
        raw_10b = _make_raw_10bit_yuv420p(16, 16, frames=1)
        raw_in = self.work / "in_dither_10b.yuv"
        raw_in.write_bytes(raw_10b)
        p010_out = self.work / "out_p010.raw"
        u8_out = self.work / "out_dither_8b.yuv"

        r_p010 = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-i",
                str(raw_in),
                "-vf",
                "format=p010le",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "p010le",
                "-y",
                str(p010_out),
            ]
        )
        self.assertEqual(r_p010.returncode, 0, r_p010.stdout + r_p010.stderr)
        self.assertEqual(len(p010_out.read_bytes()), 16 * 16 * 3)

        r_dither = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "p010le",
                "-s",
                "16x16",
                "-i",
                str(p010_out),
                "-vf",
                "scale=16:16:sws_dither=bayer,format=yuv420p",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(u8_out),
            ]
        )
        self.assertEqual(r_dither.returncode, 0, r_dither.stdout + r_dither.stderr)
        self.assertEqual(len(u8_out.read_bytes()), 16 * 16 * 3 // 2)


if __name__ == "__main__":
    unittest.main()
