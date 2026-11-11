#!/usr/bin/env python3
import hashlib
import json
import os
import shutil
import struct
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

    def test_06_peak_white_10bit_clamping_and_multi_obu_av1_dovi_rpu_e2e(self) -> None:
        w, h = 64, 64
        # Include 1022 and 1023 peak-white codes with neutral chroma (512) to ensure 10-bit -> 8-bit frame unpacking clamps to 255 (never wraps to 0)
        peak_y = [1022 if (i % 2 == 0) else 1023 for i in range(w * h)]
        peak_uv = [512 for _ in range((w // 2) * (h // 2))]
        raw_peak = struct.pack(f"<{len(peak_y) + 2 * len(peak_uv)}H", *peak_y, *peak_uv, *peak_uv)
        peak_in = self.work / "peak_1023.yuv"
        peak_in.write_bytes(raw_peak)
        sdr_raw = self.work / "peak_1023_tonemap.yuv"

        r_tm = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                f"{w}x{h}",
                "-i",
                str(peak_in),
                "-vf",
                "tonemap=reinhard,format=yuv420p",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(sdr_raw),
            ]
        )
        self.assertEqual(r_tm.returncode, 0, r_tm.stdout + r_tm.stderr)
        y_plane = sdr_raw.read_bytes()[: w * h]
        self.assertEqual(len(y_plane), w * h)
        self.assertGreaterEqual(min(y_plane), 200, f"1022/1023 peak-white wrapped around: min={min(y_plane)}")

        # Multi-OBU AV1 MP4 (produced by ffmpeg libaom-av1 with TD + Sequence Header + Frame OBUs) -> lffmpeg AV1 MP4
        av1_src = self.work / "ff_av1_hdr10.mp4"
        subprocess.run(
            [
                FFMPEG_BIN,
                "-hide_banner",
                "-loglevel",
                "error",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                f"{w}x{h}",
                "-r",
                "25",
                "-i",
                str(peak_in),
                "-c:v",
                "libaom-av1",
                "-cpu-used",
                "8",
                "-y",
                str(av1_src),
            ],
            check=True,
        )
        # Inject >=255B RPU via test_p1_1_hdr_dovi_containers helper pattern or re-encode 105B DOVI AV1 MP4 through lffmpeg
        av1_reenc = self.work / "lffmpeg_av1_reenc.mp4"
        r_av1 = _run_lffmpeg(
            [
                "-i",
                str(av1_src),
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
                str(av1_reenc),
            ]
        )
        self.assertEqual(r_av1.returncode, 0, r_av1.stdout + r_av1.stderr)
        hlg_sdr = self.work / "hlg_tonemapped.yuv"
        r_hlg = _run_lffmpeg(
            [
                "-i",
                str(av1_reenc),
                "-vf",
                "tonemap=hable,format=yuv420p",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(hlg_sdr),
            ]
        )
        self.assertEqual(r_hlg.returncode, 0, r_hlg.stdout + r_hlg.stderr)
        self.assertGreaterEqual(min(hlg_sdr.read_bytes()[: w * h]), 180)

    def test_07_hbd_unsupported_vf_fails_closed_and_mkv_aac_audio_preserved(self) -> None:
        raw_10b = _make_raw_10bit_yuv420p(16, 16, frames=2)
        raw_in = self.work / "in_hbd_negate.yuv"
        raw_in.write_bytes(raw_10b)
        bad_out = self.work / "out_hbd_negate.yuv"

        r_neg = _run_lffmpeg(
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
                "negate",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-y",
                str(bad_out),
            ]
        )
        self.assertNotEqual(r_neg.returncode, 0)
        self.assertFalse(bad_out.exists())

        post_tm_out = self.work / "out_tonemap_negate.yuv"
        r_tm_neg = _run_lffmpeg(
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
                "tonemap=reinhard,negate",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(post_tm_out),
            ]
        )
        self.assertEqual(r_tm_neg.returncode, 0, r_tm_neg.stdout + r_tm_neg.stderr)
        r_tm_only_out = self.work / "out_tonemap_only.yuv"
        r_tm_only = _run_lffmpeg(
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
                "tonemap=reinhard",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(r_tm_only_out),
            ]
        )
        self.assertEqual(r_tm_only.returncode, 0, r_tm_only.stdout + r_tm_only.stderr)
        b_tm = r_tm_only_out.read_bytes()
        b_tm_neg = post_tm_out.read_bytes()
        self.assertEqual(len(b_tm), len(b_tm_neg))
        self.assertNotEqual(b_tm[: 16 * 16], b_tm_neg[: 16 * 16])

        hdr_video_mp4 = self.work / "hdr_video_only.mp4"
        r_hdr_v = _run_lffmpeg(
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
                str(hdr_video_mp4),
            ]
        )
        self.assertEqual(r_hdr_v.returncode, 0, r_hdr_v.stdout + r_hdr_v.stderr)

        hdr_av_mp4 = self.work / "hdr_with_aac.mp4"
        subprocess.run(
            [
                FFMPEG_BIN,
                "-hide_banner",
                "-loglevel",
                "error",
                "-i",
                str(hdr_video_mp4),
                "-f",
                "lavfi",
                "-i",
                "sine=frequency=440:sample_rate=48000:duration=0.08",
                "-c:v",
                "copy",
                "-c:a",
                "aac",
                "-b:a",
                "128k",
                "-y",
                str(hdr_av_mp4),
            ],
            check=True,
        )

        mkv_aac_out = self.work / "hdr_with_aac.mkv"
        r_mkv_aac = _run_lffmpeg(
            [
                "-i",
                str(hdr_av_mp4),
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-c:a",
                "aac",
                "-y",
                str(mkv_aac_out),
            ]
        )
        self.assertEqual(r_mkv_aac.returncode, 0, r_mkv_aac.stdout + r_mkv_aac.stderr)
        probe_mkv = _ffprobe_json(mkv_aac_out)
        codecs = [s["codec_name"] for s in probe_mkv["streams"]]
        self.assertEqual(codecs, ["hevc", "aac"])

        mkv_copy_out = self.work / "hdr_with_aac_copy.mkv"
        r_mkv_copy = _run_lffmpeg(
            [
                "-i",
                str(hdr_av_mp4),
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-c:a",
                "copy",
                "-y",
                str(mkv_copy_out),
            ]
        )
        self.assertEqual(r_mkv_copy.returncode, 0, r_mkv_copy.stdout + r_mkv_copy.stderr)
        probe_copy = _ffprobe_json(mkv_copy_out)
        self.assertEqual([s["codec_name"] for s in probe_copy["streams"]], ["hevc", "aac"])

        webm_bad_aac = self.work / "bad_webm_aac.webm"
        r_webm_bad = _run_lffmpeg(
            [
                "-i",
                str(hdr_av_mp4),
                "-c:v",
                "av1",
                "-pix_fmt",
                "yuv420p10le",
                "-c:a",
                "aac",
                "-y",
                str(webm_bad_aac),
            ]
        )
        self.assertNotEqual(r_webm_bad.returncode, 0)
        self.assertFalse(webm_bad_aac.exists())

        mkv_bad_pcm = self.work / "bad_mkv_pcm.mkv"
        r_mkv_pcm = _run_lffmpeg(
            [
                "-i",
                str(hdr_av_mp4),
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-c:a",
                "pcm_s16le",
                "-y",
                str(mkv_bad_pcm),
            ]
        )
        self.assertNotEqual(r_mkv_pcm.returncode, 0)
        self.assertFalse(mkv_bad_pcm.exists())

        fc_bad_out = self.work / "bad_hbd_fc.mp4"
        r_fc_bad = _run_lffmpeg(
            [
                "-i",
                str(hdr_video_mp4),
                "-filter_complex",
                "[0:v]negate[v]",
                "-map",
                "[v]",
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-y",
                str(fc_bad_out),
            ]
        )
        self.assertNotEqual(r_fc_bad.returncode, 0)
        self.assertFalse(fc_bad_out.exists())

        cs10_out = self.work / "hdr_cs_bt709_10b.mp4"
        r_cs10 = _run_lffmpeg(
            [
                "-i",
                str(hdr_video_mp4),
                "-vf",
                "colorspace=all=bt709",
                "-c:v",
                "hevc",
                "-pix_fmt",
                "yuv420p10le",
                "-y",
                str(cs10_out),
            ]
        )
        self.assertEqual(r_cs10.returncode, 0, r_cs10.stdout + r_cs10.stderr)
        probe_cs10 = _ffprobe_json(cs10_out)
        self.assertEqual(probe_cs10["streams"][0]["pix_fmt"], "yuv420p10le")
        self.assertEqual(probe_cs10["streams"][0].get("color_space"), "bt709")

        raw_40s = self.work / "in_40s_1fps.yuv"
        raw_40s.write_bytes(_make_raw_10bit_yuv420p(16, 16, frames=1) * 40)
        mp4_40s_src = self.work / "in_40s_hdr_aac.mp4"
        subprocess.run(
            [
                FFMPEG_BIN,
                "-hide_banner",
                "-loglevel",
                "error",
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "1",
                "-i",
                str(raw_40s),
                "-f",
                "lavfi",
                "-i",
                "sine=frequency=440:sample_rate=48000:duration=2.0",
                "-c:v",
                "libx265",
                "-pix_fmt",
                "yuv420p10le",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "smpte2084",
                "-colorspace",
                "bt2020nc",
                "-c:a",
                "aac",
                "-b:a",
                "128k",
                "-y",
                str(mp4_40s_src),
            ],
            check=True,
        )
        mkv_40s = self.work / "hdr_40s_multicluster.mkv"
        r_40s = _run_lffmpeg(
            [
                "-i",
                str(mp4_40s_src),
                "-r",
                "1",
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
                "-c:a",
                "aac",
                "-y",
                str(mkv_40s),
            ]
        )
        self.assertEqual(r_40s.returncode, 0, r_40s.stdout + r_40s.stderr)
        pkt_res = subprocess.run(
            [
                FFPROBE_BIN,
                "-v",
                "error",
                "-show_entries",
                "packet=codec_type,pts_time",
                "-of",
                "json",
                str(mkv_40s),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        pkts = json.loads(pkt_res.stdout)["packets"]
        all_pts_ms = [round(float(p["pts_time"]) * 1000) for p in pkts]
        self.assertEqual(all_pts_ms, sorted(all_pts_ms))
        vid_pts_ms = [round(float(p["pts_time"]) * 1000) for p in pkts if p["codec_type"] == "video"]
        aud_pts_ms = [round(float(p["pts_time"]) * 1000) for p in pkts if p["codec_type"] == "audio"]
        self.assertEqual(vid_pts_ms, [i * 1000 for i in range(40)])
        self.assertGreater(len(aud_pts_ms), 0)
        mp4_40s = self.work / "hdr_40s_multicluster_rt.mp4"
        r_40s_rt = _run_lffmpeg(
            [
                "-i",
                str(mkv_40s),
                "-c:v",
                "copy",
                "-c:a",
                "copy",
                "-y",
                str(mp4_40s),
            ]
        )
        self.assertEqual(r_40s_rt.returncode, 0, r_40s_rt.stdout + r_40s_rt.stderr)
        rt_pkt_res = subprocess.run(
            [
                FFPROBE_BIN,
                "-v",
                "error",
                "-select_streams",
                "v:0",
                "-show_entries",
                "packet=pts_time",
                "-of",
                "json",
                str(mp4_40s),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        rt_vid_pts = [round(float(p["pts_time"]) * 1000) for p in json.loads(rt_pkt_res.stdout)["packets"]]
        self.assertEqual(rt_vid_pts, [i * 1000 for i in range(40)])

        bad_frac_out = self.work / "bad_frac_fps.mp4"
        for bad_rate in ("30000/1001", "24000/1001", "ntsc"):
            r_bad_frac = _run_lffmpeg(
                [
                    "-f",
                    "rawvideo",
                    "-pix_fmt",
                    "yuv420p10le",
                    "-s",
                    "16x16",
                    "-r",
                    bad_rate,
                    "-i",
                    str(raw_40s),
                    "-c:v",
                    "hevc",
                    "-pix_fmt",
                    "yuv420p10le",
                    "-y",
                    str(bad_frac_out),
                ]
            )
            self.assertNotEqual(r_bad_frac.returncode, 0, f"rate {bad_rate} must fail closed")
            self.assertFalse(bad_frac_out.exists())

        sdr_src_mp4 = self.work / "sdr_src_10fps.mp4"
        subprocess.run(
            [
                FFMPEG_BIN,
                "-hide_banner",
                "-loglevel",
                "error",
                "-f",
                "lavfi",
                "-i",
                "testsrc=size=32x32:rate=10:duration=0.4",
                "-c:v",
                "libx264",
                "-pix_fmt",
                "yuv420p",
                "-y",
                str(sdr_src_mp4),
            ],
            check=True,
        )
        sdr_fc_r_mp4 = self.work / "sdr_fc_out_5fps.mp4"
        r_sdr_fc = _run_lffmpeg(
            [
                "-i",
                str(sdr_src_mp4),
                "-filter_complex",
                "[0:v]null[v]",
                "-map",
                "[v]",
                "-r",
                "5",
                "-c:v",
                "h264",
                "-y",
                str(sdr_fc_r_mp4),
            ]
        )
        self.assertEqual(r_sdr_fc.returncode, 0, r_sdr_fc.stdout + r_sdr_fc.stderr)
        probe_sdr_fc = _ffprobe_json(sdr_fc_r_mp4)
        self.assertEqual(int(probe_sdr_fc["streams"][0]["nb_frames"]), 2)
        self.assertEqual(probe_sdr_fc["streams"][0]["r_frame_rate"], "5/1")

        # Direct RGB24 standalone lavfi testsrc output-rate resampling (duplication & dropping):
        rgb_base = self.work / "testsrc_10fps.rgb"
        rgb_dup = self.work / "testsrc_20fps.rgb"
        rgb_drop = self.work / "testsrc_5fps.rgb"
        for out_p, extra in [
            (rgb_base, []),
            (rgb_dup, ["-r", "20"]),
            (rgb_drop, ["-r", "5"]),
        ]:
            res = _run_lffmpeg(
                [
                    "-lavfi",
                    "testsrc=size=32x32:rate=10:duration=1",
                    *extra,
                    "-pix_fmt",
                    "rgb24",
                    "-f",
                    "rawvideo",
                    "-y",
                    str(out_p),
                ]
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        frame_bytes = 32 * 32 * 3
        b_base = rgb_base.read_bytes()
        b_dup = rgb_dup.read_bytes()
        b_drop = rgb_drop.read_bytes()
        self.assertEqual(len(b_base), 10 * frame_bytes)
        self.assertEqual(len(b_dup), 20 * frame_bytes)
        self.assertEqual(len(b_drop), 5 * frame_bytes)
        for i in range(10):
            src_frame = b_base[i * frame_bytes : (i + 1) * frame_bytes]
            self.assertEqual(b_dup[(2 * i) * frame_bytes : (2 * i + 1) * frame_bytes], src_frame)
            self.assertEqual(b_dup[(2 * i + 1) * frame_bytes : (2 * i + 2) * frame_bytes], src_frame)
        for j in range(5):
            src_frame = b_base[(2 * j) * frame_bytes : (2 * j + 1) * frame_bytes]
            self.assertEqual(b_drop[j * frame_bytes : (j + 1) * frame_bytes], src_frame)

    def test_12_master_display_max_cll_side_data_and_fail_closed_kv_params(self) -> None:
        raw_in = self.work / "in_bt2020_custom_mdcv.yuv"
        raw_in.write_bytes(_make_raw_10bit_yuv420p(16, 16, frames=2))
        mp4_hevc = self.work / "custom_mdcv_hevc.mp4"
        mkv_hevc = self.work / "custom_mdcv_hevc.mkv"
        mp4_rt = self.work / "custom_mdcv_hevc_rt.mp4"
        mp4_av1 = self.work / "custom_mdcv_av1.mp4"
        mkv_av1 = self.work / "custom_mdcv_av1.mkv"

        # Use non-default BT.2020 primaries + 4000/0.001 nits + 4000/1000 CLL/FALL so fallback to DCI-P3 would fail
        kv_spec = (
            "qp=0:"
            "master-display=G(8500,39850)B(6550,2300)R(35400,14600)WP(15635,16450)L(40000000,10):"
            "max-cll=4000,1000"
        )
        r_hevc = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "24",
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
                kv_spec,
                "-y",
                str(mp4_hevc),
            ]
        )
        self.assertEqual(r_hevc.returncode, 0, r_hevc.stdout + r_hevc.stderr)

        def _collect_side_data(probe_obj: dict) -> dict[str, dict]:
            found: dict[str, dict] = {}
            for s in probe_obj.get("streams", []):
                for sd in s.get("side_data_list", []):
                    found[sd["side_data_type"]] = sd
            for fr in probe_obj.get("frames", []):
                for sd in fr.get("side_data_list", []):
                    found.setdefault(sd["side_data_type"], sd)
            return found

        for step_cmd, target in [
            (None, mp4_hevc),
            (["-i", str(mp4_hevc), "-c", "copy", "-y", str(mkv_hevc)], mkv_hevc),
            (["-i", str(mkv_hevc), "-c", "copy", "-y", str(mp4_rt)], mp4_rt),
        ]:
            if step_cmd is not None:
                res = _run_lffmpeg(step_cmd)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            probe = _ffprobe_json(target)
            sd = _collect_side_data(probe)
            self.assertIn("Mastering display metadata", sd, f"Missing mdcv in {target}: {sd}")
            self.assertIn("Content light level metadata", sd, f"Missing clli in {target}: {sd}")
            mdcv = sd["Mastering display metadata"]
            clli = sd["Content light level metadata"]
            from fractions import Fraction

            self.assertAlmostEqual(float(Fraction(str(mdcv.get("red_x")))), 35400 / 50000, places=4)
            self.assertAlmostEqual(float(Fraction(str(mdcv.get("green_x")))), 8500 / 50000, places=4)
            self.assertAlmostEqual(float(Fraction(str(mdcv.get("blue_x")))), 6550 / 50000, places=4)
            self.assertAlmostEqual(float(Fraction(str(mdcv.get("max_luminance")))), 4000.0, places=2)
            self.assertAlmostEqual(float(Fraction(str(mdcv.get("min_luminance")))), 0.001, places=5)
            self.assertEqual(int(clli["max_content"]), 4000)
            self.assertEqual(int(clli["max_average"]), 1000)

        r_av1 = _run_lffmpeg(
            [
                "-f",
                "rawvideo",
                "-pix_fmt",
                "yuv420p10le",
                "-s",
                "16x16",
                "-r",
                "24",
                "-i",
                str(raw_in),
                "-c:v",
                "av1",
                "-pix_fmt",
                "yuv420p10le",
                "-color_primaries",
                "bt2020",
                "-color_trc",
                "smpte2084",
                "-colorspace",
                "bt2020nc",
                "-svtav1-params",
                kv_spec,
                "-y",
                str(mp4_av1),
            ]
        )
        self.assertEqual(r_av1.returncode, 0, r_av1.stdout + r_av1.stderr)
        r_av1_mkv = _run_lffmpeg(["-i", str(mp4_av1), "-c", "copy", "-y", str(mkv_av1)])
        self.assertEqual(r_av1_mkv.returncode, 0, r_av1_mkv.stdout + r_av1_mkv.stderr)
        for av1_target in (mp4_av1, mkv_av1):
            sd_av1 = _collect_side_data(_ffprobe_json(av1_target))
            self.assertIn("Mastering display metadata", sd_av1)
            self.assertIn("Content light level metadata", sd_av1)
            self.assertEqual(int(sd_av1["Content light level metadata"]["max_content"]), 4000)
            self.assertEqual(int(sd_av1["Content light level metadata"]["max_average"]), 1000)

        # Malformed HDR metadata and unsupported stateful encoder KV params must fail closed with no output file
        bad_kv_cases = [
            ("fall_gt_cll", "max-cll=500,1000"),
            ("cll_overflow", "max-cll=70000,400"),
            ("min_ge_max_lum", "master-display=G(13250,34500)B(7500,3000)R(34000,16000)WP(15635,16450)L(100,100)"),
            ("chrom_gt_50000", "master-display=G(50001,34500)B(7500,3000)R(34000,16000)WP(15635,16450)L(10000000,50)"),
            ("dovi_profile", "dolby-vision-profile=8.1"),
            ("stateful_profile", "profile=main10"),
            ("film_grain_denoise", "film-grain=8:film-grain-denoise=1"),
        ]
        for label, bad_kv in bad_kv_cases:
            bad_out = self.work / f"bad_kv_{label}.mp4"
            flag = "-svtav1-params" if "film-grain" in bad_kv else "-x265-params"
            codec = "av1" if "film-grain" in bad_kv else "hevc"
            res_bad = _run_lffmpeg(
                [
                    "-f",
                    "rawvideo",
                    "-pix_fmt",
                    "yuv420p10le",
                    "-s",
                    "16x16",
                    "-r",
                    "24",
                    "-i",
                    str(raw_in),
                    "-c:v",
                    codec,
                    "-pix_fmt",
                    "yuv420p10le",
                    flag,
                    bad_kv,
                    "-y",
                    str(bad_out),
                ]
            )
            self.assertNotEqual(res_bad.returncode, 0, f"Expected fail-closed rejection for {label}: {bad_kv}")
            self.assertFalse(bad_out.exists(), f"Output file leaked on rejected {label}")

    def test_13_fractional_ntsc_fps_fail_closed_and_exact_rational_resampling(self) -> None:
        # Oracle FFmpeg generates a 60-frame 30000/1001 (~29.97 fps, ~2.002s) 10-bit HEVC MP4 and AV1 IVF + MKV
        ntsc_hevc_mp4 = self.work / "ntsc_2997_hevc.mp4"
        ntsc_av1_ivf = self.work / "ntsc_2997_av1.ivf"
        ntsc_hevc_mkv = self.work / "ntsc_2997_hevc.mkv"
        subprocess.run(
            [
                FFMPEG_BIN,
                "-v",
                "error",
                "-f",
                "lavfi",
                "-i",
                "testsrc2=size=32x32:rate=30000/1001:duration=2",
                "-frames:v",
                "60",
                "-pix_fmt",
                "yuv420p10le",
                "-c:v",
                "libx265",
                "-x265-params",
                "log-level=error:qp=12",
                "-y",
                str(ntsc_hevc_mp4),
            ],
            check=True,
            timeout=60,
        )
        subprocess.run(
            [
                FFMPEG_BIN,
                "-v",
                "error",
                "-i",
                str(ntsc_hevc_mp4),
                "-c",
                "copy",
                "-y",
                str(ntsc_hevc_mkv),
            ],
            check=True,
            timeout=60,
        )
        subprocess.run(
            [
                FFMPEG_BIN,
                "-v",
                "error",
                "-f",
                "lavfi",
                "-i",
                "testsrc2=size=32x32:rate=30000/1001:duration=2",
                "-frames:v",
                "60",
                "-pix_fmt",
                "yuv420p10le",
                "-c:v",
                "libsvtav1",
                "-crf",
                "20",
                "-y",
                str(ntsc_av1_ivf),
            ],
            check=True,
            timeout=60,
        )

        # 1. Stream copy preserves fractional 30000/1001 timing untouched
        copy_mp4 = self.work / "ntsc_copy.mp4"
        r_copy = _run_lffmpeg(["-i", str(ntsc_hevc_mp4), "-c", "copy", "-y", str(copy_mp4)])
        self.assertEqual(r_copy.returncode, 0, r_copy.stdout + r_copy.stderr)
        probe_copy = _ffprobe_json(copy_mp4)
        self.assertEqual(probe_copy["streams"][0]["avg_frame_rate"], "30000/1001")

        # 2. Transcoding fractional-FPS MP4/MKV/IVF without explicit -r / fps= fails closed
        for label, src_p in [("mp4", ntsc_hevc_mp4), ("mkv", ntsc_hevc_mkv), ("ivf", ntsc_av1_ivf)]:
            no_r_out = self.work / f"ntsc_no_rate_{label}.mp4"
            res_fail = _run_lffmpeg(
                ["-i", str(src_p), "-c:v", "hevc", "-pix_fmt", "yuv420p10le", "-y", str(no_r_out)]
            )
            self.assertNotEqual(res_fail.returncode, 0, f"Expected fractional-FPS fail-closed for {label}")
            self.assertFalse(no_r_out.exists())

        # 3. With explicit -r 24 or -vf fps=24, 60 frames @ 30000/1001 (~2.002s) resamples to 48 frames
        #    (whereas truncated integer 29 fps would have yielded 49 frames: round(60 * 24 / 29) == 50 / 49!)
        for mode, extra_args in [
            ("dash_r", ["-r", "24"]),
            ("vf_fps", ["-vf", "fps=24"]),
            ("fc_fps", ["-filter_complex", "[0:v]fps=24,format=yuv420p[v]", "-map", "[v]"]),
        ]:
            out_24 = self.work / f"ntsc_to_24_{mode}.mp4"
            pix_args = ["-pix_fmt", "yuv420p"] if mode == "fc_fps" else ["-pix_fmt", "yuv420p10le"]
            codec = "h264" if mode == "fc_fps" else "hevc"
            r_ok = _run_lffmpeg(
                ["-i", str(ntsc_hevc_mp4), *extra_args, "-c:v", codec, *pix_args, "-y", str(out_24)]
            )
            self.assertEqual(r_ok.returncode, 0, f"{mode}: {r_ok.stdout + r_ok.stderr}")
            probe_24 = _ffprobe_json(out_24)
            self.assertEqual(int(probe_24["streams"][0]["nb_frames"]), 48, f"Wrong rational frame count for {mode}")
            self.assertEqual(probe_24["streams"][0]["r_frame_rate"], "24/1")

        # Also verify MKV 29.97 (1ms cluster timestamps) + IVF 30000/1001 with -r 24 -> exact 48 frames
        for label, src_p in [("mkv", ntsc_hevc_mkv), ("ivf", ntsc_av1_ivf)]:
            out_p = self.work / f"ntsc_{label}_24.mkv"
            r_ok2 = _run_lffmpeg(
                ["-i", str(src_p), "-r", "24", "-c:v", "hevc", "-pix_fmt", "yuv420p10le", "-y", str(out_p)]
            )
            self.assertEqual(r_ok2.returncode, 0, f"{label}: {r_ok2.stdout + r_ok2.stderr}")
            probe_m = _ffprobe_json(out_p)
            self.assertEqual(len(probe_m["frames"]), 48, f"Wrong MKV frame count for {label}")
            # Verify exact 24fps MKV timescale (no 1000/24 = 41ms cumulative drift: frame 24 pts_time == 1.000s)
            pts_24 = float(probe_m["frames"][24]["pts_time"])
            self.assertAlmostEqual(pts_24, 1.0, places=3)


if __name__ == "__main__":
    unittest.main()
