import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"


class H264SyntaxDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not (BINARY.stat().st_mode & 0o111):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        ffmpeg_bin = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        ffprobe_bin = os.environ.get("LEANAV_TEST_FFPROBE") or shutil.which("ffprobe")
        if not ffmpeg_bin or not ffprobe_bin:
            raise unittest.SkipTest("reference ffmpeg/ffprobe is unavailable")
        cls.ffmpeg = str(Path(ffmpeg_bin).resolve())
        cls.ffprobe = str(Path(ffprobe_bin).resolve())
        cls.isolated_env = {
            "PATH": "/nonexistent",
            "LEANAV_FFMPEG_BIN": "/nonexistent/ffmpeg",
            "LANG": "C",
            "LC_ALL": "C",
        }

    def run_probe(self, path: Path) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(BINARY), "h264-probe", str(path)],
            env=self.isolated_env,
            capture_output=True,
            text=True,
            timeout=30,
        )

    def encode_sample(self, out_path: Path, *extra_args: str) -> None:
        subprocess.run(
            [
                self.ffmpeg,
                "-y",
                "-nostdin",
                "-hide_banner",
                "-loglevel",
                "error",
                "-f",
                "lavfi",
                "-i",
                "testsrc=size=320x240:rate=30:duration=0.2",
                *extra_args,
                str(out_path),
            ],
            check=True,
            timeout=30,
        )

    def ffprobe_stream_and_frames(self, path: Path) -> tuple[dict, list[dict]]:
        s_res = subprocess.run(
            [
                self.ffprobe,
                "-v",
                "error",
                "-select_streams",
                "v:0",
                "-show_streams",
                "-of",
                "json",
                str(path),
            ],
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        )
        f_res = subprocess.run(
            [
                self.ffprobe,
                "-v",
                "error",
                "-select_streams",
                "v:0",
                "-show_frames",
                "-of",
                "json",
                str(path),
            ],
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        )
        stream = json.loads(s_res.stdout)["streams"][0]
        frames = json.loads(f_res.stdout)["frames"]
        return stream, frames

    def test_baseline_annexb_cavlc_poc_type2_matches_ffprobe(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "baseline.h264"
            self.encode_sample(
                p,
                "-c:v",
                "libx264",
                "-profile:v",
                "baseline",
                "-pix_fmt",
                "yuv420p",
                "-x264-params",
                "keyint=30:bframes=0",
            )
            res = self.run_probe(p)
            self.assertEqual(res.returncode, 0, res.stderr)
            got = json.loads(res.stdout)
            stream, frames = self.ffprobe_stream_and_frames(p)

            self.assertTrue(got["ok"])
            self.assertEqual(got["profile_idc"], 66)
            self.assertEqual(got["width"], stream["width"])
            self.assertEqual(got["height"], stream["height"])
            self.assertFalse(got["cabac"])
            self.assertFalse(got["transform_8x8"])
            self.assertTrue(got["framing_roundtrip_ok"])
            self.assertTrue(got["slice_header_roundtrip_ok"])
            self.assertTrue(got["slice_header_bit_offset_ok"])
            self.assertEqual(len(got["frames"]), len(frames))
            self.assertTrue(all(f["data_bit_offset"] >= 8 for f in got["frames"]))
            self.assertEqual(
                [f["pict_type"] for f in got["frames"]],
                [f["pict_type"] for f in frames],
            )
            pocs = [f["poc"] for f in got["frames"]]
            self.assertEqual(pocs, [2 * i for i in range(len(frames))])

    def test_main_cabac_bframes_poc_type0_and_mp4_avcc_match_ffprobe(self):
        with tempfile.TemporaryDirectory() as td:
            mp4 = Path(td) / "main_bframes.mp4"
            annexb = Path(td) / "main_bframes.h264"
            self.encode_sample(
                mp4,
                "-c:v",
                "libx264",
                "-profile:v",
                "main",
                "-pix_fmt",
                "yuv420p",
                "-bf",
                "2",
                "-x264-params",
                "b-adapt=0:weightp=2:weightb=1",
            )
            subprocess.run(
                [
                    self.ffmpeg,
                    "-y",
                    "-nostdin",
                    "-hide_banner",
                    "-loglevel",
                    "error",
                    "-i",
                    str(mp4),
                    "-c:v",
                    "copy",
                    "-bsf:v",
                    "h264_mp4toannexb",
                    str(annexb),
                ],
                check=True,
                timeout=30,
            )

            res_mp4 = self.run_probe(mp4)
            res_b = self.run_probe(annexb)
            self.assertEqual(res_mp4.returncode, 0, res_mp4.stderr)
            self.assertEqual(res_b.returncode, 0, res_b.stderr)
            got_mp4 = json.loads(res_mp4.stdout)
            got_b = json.loads(res_b.stdout)
            stream, frames = self.ffprobe_stream_and_frames(mp4)

            for got in (got_mp4, got_b):
                self.assertTrue(got["ok"])
                self.assertEqual(got["profile_idc"], 77)
                self.assertEqual(got["width"], stream["width"])
                self.assertEqual(got["height"], stream["height"])
                self.assertEqual(got["poc_type"], 0)
                self.assertTrue(got["cabac"])
                self.assertTrue(got["weighted_pred"])
                self.assertEqual(got["weighted_bipred_idc"], 2)
                self.assertTrue(got["avcc_roundtrip_ok"])
                self.assertTrue(got["framing_roundtrip_ok"])
                self.assertTrue(got["slice_header_roundtrip_ok"])
                self.assertTrue(got["slice_header_bit_offset_ok"])
                self.assertTrue(got["cabac_prefix_rbsp_exact_ok"])
                self.assertEqual(len(got["frames"]), len(frames))
                self.assertTrue(all(f["data_bit_offset"] % 8 == 0 and f["data_bit_offset"] >= 16 for f in got["frames"]))

            self.assertEqual(got_mp4["frames"], got_b["frames"])
            display_sorted = sorted(got_mp4["frames"], key=lambda x: x["poc"])
            self.assertEqual(
                [f["pict_type"] for f in display_sorted],
                [f["pict_type"] for f in frames],
            )
            self.assertEqual([f["poc"] for f in display_sorted], [2 * i for i in range(len(frames))])

    def test_high_1080p_jvt_scaling_and_8x8dct_mp4_roundtrip(self):
        with tempfile.TemporaryDirectory() as td:
            mp4 = Path(td) / "high1080_jvt.mp4"
            subprocess.run(
                [
                    self.ffmpeg,
                    "-y",
                    "-nostdin",
                    "-hide_banner",
                    "-loglevel",
                    "error",
                    "-f",
                    "lavfi",
                    "-i",
                    "testsrc=size=1920x1080:rate=25:duration=0.12",
                    "-c:v",
                    "libx264",
                    "-profile:v",
                    "high",
                    "-pix_fmt",
                    "yuv420p",
                    "-x264-params",
                    "8x8dct=1:cqm=jvt:bframes=1",
                    str(mp4),
                ],
                check=True,
                timeout=30,
            )
            res = self.run_probe(mp4)
            self.assertEqual(res.returncode, 0, res.stderr)
            got = json.loads(res.stdout)
            stream, frames = self.ffprobe_stream_and_frames(mp4)

            self.assertTrue(got["ok"])
            self.assertEqual(got["profile_idc"], 100)
            self.assertEqual(got["width"], 1920)
            self.assertEqual(got["height"], 1080)
            self.assertEqual(got["width"], stream["width"])
            self.assertEqual(got["height"], stream["height"])
            self.assertTrue(got["transform_8x8"])
            self.assertTrue(got["seq_scaling_matrix"] or got["pic_scaling_matrix"])
            self.assertTrue(got["avcc_roundtrip_ok"])
            self.assertTrue(got["framing_roundtrip_ok"])
            self.assertTrue(got["slice_header_roundtrip_ok"])
            self.assertTrue(got["slice_header_bit_offset_ok"])
            self.assertTrue(got["cabac_prefix_rbsp_exact_ok"])
            self.assertEqual(len(got["frames"]), len(frames))
            self.assertTrue(all(f["data_bit_offset"] % 8 == 0 for f in got["frames"]))

    def test_high444_qpprime_lossless_mp4_and_annexb_match_ffprobe(self):
        with tempfile.TemporaryDirectory() as td:
            mp4 = Path(td) / "high444_lossless.mp4"
            subprocess.run(
                [
                    self.ffmpeg,
                    "-y",
                    "-nostdin",
                    "-hide_banner",
                    "-loglevel",
                    "error",
                    "-f",
                    "lavfi",
                    "-i",
                    "testsrc=size=128x96:rate=25:duration=0.16",
                    "-c:v",
                    "libx264",
                    "-profile:v",
                    "high444",
                    "-pix_fmt",
                    "yuv444p",
                    "-qp",
                    "0",
                    str(mp4),
                ],
                check=True,
                timeout=30,
            )
            res = self.run_probe(mp4)
            self.assertEqual(res.returncode, 0, res.stderr)
            got = json.loads(res.stdout)
            stream, frames = self.ffprobe_stream_and_frames(mp4)

            self.assertTrue(got["ok"])
            self.assertEqual(got["profile_idc"], 244)
            self.assertEqual(got["chroma_format_idc"], 3)
            self.assertTrue(got["qpprime_bypass"])
            self.assertEqual(got["width"], stream["width"])
            self.assertEqual(got["height"], stream["height"])
            self.assertTrue(got["avcc_roundtrip_ok"])
            self.assertTrue(got["framing_roundtrip_ok"])
            self.assertTrue(got["slice_header_roundtrip_ok"])
            self.assertTrue(got["slice_header_bit_offset_ok"])
            self.assertTrue(got["cabac_prefix_rbsp_exact_ok"])
            self.assertEqual(len(got["frames"]), len(frames))
            self.assertTrue(all(f["data_bit_offset"] % 8 == 0 for f in got["frames"]))

    def test_cabac_idr_and_nonidr_pslice_exact_byte_aligned_prefixes_without_spurious_stop_byte(self):
        with tempfile.TemporaryDirectory() as td:
            annexb = Path(td) / "cabac_ip.h264"
            subprocess.run(
                [
                    self.ffmpeg,
                    "-y",
                    "-nostdin",
                    "-hide_banner",
                    "-loglevel",
                    "error",
                    "-f",
                    "lavfi",
                    "-i",
                    "testsrc=size=128x96:rate=25:duration=0.2",
                    "-c:v",
                    "libx264",
                    "-profile:v",
                    "main",
                    "-pix_fmt",
                    "yuv420p",
                    "-coder",
                    "1",
                    "-bf",
                    "0",
                    "-x264-params",
                    "keyint=30:weightp=2",
                    str(annexb),
                ],
                check=True,
                timeout=30,
            )
            res = self.run_probe(annexb)
            self.assertEqual(res.returncode, 0, res.stderr)
            got = json.loads(res.stdout)
            self.assertTrue(got["ok"])
            self.assertTrue(got["cabac"])
            self.assertTrue(got["slice_header_roundtrip_ok"])
            self.assertTrue(got["slice_header_bit_offset_ok"])
            self.assertTrue(got["cabac_prefix_rbsp_exact_ok"])
            pict_types = [f["pict_type"] for f in got["frames"]]
            self.assertIn("I", pict_types)
            self.assertIn("P", pict_types)
            for f in got["frames"]:
                self.assertEqual(f["data_bit_offset"] % 8, 0)
                self.assertGreaterEqual(f["data_bit_offset"], 32)

    def test_corrupt_or_truncated_streams_fail_closed(self):
        with tempfile.TemporaryDirectory() as td:
            empty = Path(td) / "empty.h264"
            empty.write_bytes(b"")
            self.assertNotEqual(self.run_probe(empty).returncode, 0)

            bad_avcc = Path(td) / "bad_avcc.bin"
            bad_avcc.write_bytes(bytes([0x02, 0x64, 0x00, 0x2A, 0xFF, 0xE1, 0x00, 0x02, 0x67, 0x64]))
            self.assertNotEqual(self.run_probe(bad_avcc).returncode, 0)

            trunc_sps = Path(td) / "trunc_sps.h264"
            trunc_sps.write_bytes(b"\x00\x00\x00\x01\x67\x64\x00")
            self.assertNotEqual(self.run_probe(trunc_sps).returncode, 0)


if __name__ == "__main__":
    unittest.main()
