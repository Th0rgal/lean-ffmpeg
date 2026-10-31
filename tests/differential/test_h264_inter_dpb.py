import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"


def _clip3(lo: int, hi: int, x: int) -> int:
    return lo if x < lo else (hi if x > hi else x)


def _clip1y(x: int) -> int:
    return _clip3(0, 255, x)


def _sample_ext(grid: list[list[int]], x: int, y: int) -> int:
    h = len(grid)
    w = len(grid[0])
    cx = _clip3(0, w - 1, x)
    cy = _clip3(0, h - 1, y)
    return grid[cy][cx]


def _tap6(e: int, f: int, g: int, h: int, i: int, j: int) -> int:
    return e - 5 * f + 20 * g + 20 * h - 5 * i + j


def _h264_luma_qpel_16_oracle(grid: list[list[int]], x0: int, y0: int) -> list[int]:
    def horiz_b1(xi: int, yi: int) -> int:
        return _tap6(
            _sample_ext(grid, xi - 2, yi),
            _sample_ext(grid, xi - 1, yi),
            _sample_ext(grid, xi, yi),
            _sample_ext(grid, xi + 1, yi),
            _sample_ext(grid, xi + 2, yi),
            _sample_ext(grid, xi + 3, yi),
        )

    def vert_h1(xi: int, yi: int) -> int:
        return _tap6(
            _sample_ext(grid, xi, yi - 2),
            _sample_ext(grid, xi, yi - 1),
            _sample_ext(grid, xi, yi),
            _sample_ext(grid, xi, yi + 1),
            _sample_ext(grid, xi, yi + 2),
            _sample_ext(grid, xi, yi + 3),
        )

    g = _sample_ext(grid, x0, y0)
    m = _sample_ext(grid, x0 + 1, y0)
    s0 = _sample_ext(grid, x0, y0 + 1)
    b = _clip1y((horiz_b1(x0, y0) + 16) >> 5)
    s = _clip1y((horiz_b1(x0, y0 + 1) + 16) >> 5)
    h = _clip1y((vert_h1(x0, y0) + 16) >> 5)
    mv = _clip1y((vert_h1(x0 + 1, y0) + 16) >> 5)
    j1 = _tap6(
        horiz_b1(x0, y0 - 2),
        horiz_b1(x0, y0 - 1),
        horiz_b1(x0, y0),
        horiz_b1(x0, y0 + 1),
        horiz_b1(x0, y0 + 2),
        horiz_b1(x0, y0 + 3),
    )
    j = _clip1y((j1 + 512) >> 10)
    avg = lambda u, v: (u + v + 1) >> 1
    table = [
        [g, avg(g, b), b, avg(b, m)],
        [avg(g, h), avg(b, h), avg(b, j), avg(b, mv)],
        [h, avg(h, j), j, avg(j, mv)],
        [avg(h, s0), avg(h, s), avg(j, s), avg(s, mv)],
    ]
    return [table[yf][xf] for yf in range(4) for xf in range(4)]


def _h264_chroma_opel_64_oracle(grid: list[list[int]], x0: int, y0: int) -> list[int]:
    a = grid[y0][x0]
    b = grid[y0][x0 + 1]
    c = grid[y0 + 1][x0]
    d = grid[y0 + 1][x0 + 1]
    out: list[int] = []
    for yf in range(8):
        for xf in range(8):
            val = (
                (8 - xf) * (8 - yf) * a
                + xf * (8 - yf) * b
                + (8 - xf) * yf * c
                + xf * yf * d
                + 32
            ) >> 6
            out.append(_clip1y(val))
    return out


def _ue_bits(v: int) -> str:
    b = bin(v + 1)[2:]
    return "0" * (len(b) - 1) + b


def _se_bits(v: int) -> str:
    return _ue_bits((-2 * v) if v <= 0 else (2 * v - 1))


def _rbsp_to_annexb_nalu(hdr_byte: int, bitstr: str, pcm_bytes: bytes = b"") -> bytes:
    bits = bitstr
    if pcm_bytes:
        while len(bits) % 8 != 0:
            bits += "0"
        body = (
            bytes(int(bits[i : i + 8], 2) for i in range(0, len(bits), 8))
            + pcm_bytes
            + b"\x80"
        )
    else:
        bits += "1"
        while len(bits) % 8 != 0:
            bits += "0"
        body = bytes(int(bits[i : i + 8], 2) for i in range(0, len(bits), 8))
    out = bytearray([hdr_byte])
    zeros = 0
    for b in body:
        if zeros >= 2 and b <= 3:
            out.append(0x03)
            zeros = 0
        out.append(b)
        zeros = zeros + 1 if b == 0 else 0
    return b"\x00\x00\x00\x01" + bytes(out)


class H264InterDeblockDpbTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not (BINARY.stat().st_mode & 0o111):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        ref = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not ref:
            raise unittest.SkipTest("reference FFmpeg is unavailable")
        cls.ffmpeg = str(Path(ref).resolve())
        ffprobe_cand = Path(cls.ffmpeg).with_name("ffprobe")
        cls.ffprobe = (
            str(ffprobe_cand)
            if ffprobe_cand.is_file()
            else (shutil.which("ffprobe") or "")
        )
        cls.isolated_env = {
            "PATH": "/nonexistent",
            "LEANAV_FFMPEG_BIN": "/nonexistent/ffmpeg",
            "LANG": "C",
            "LC_ALL": "C",
        }

    def run_isolated(self, *args: str):
        return subprocess.run(
            [str(BINARY), *args],
            env=self.isolated_env,
            capture_output=True,
            text=True,
            timeout=30,
        )

    def run_ffmpeg(self, *args: str):
        return subprocess.run(
            [self.ffmpeg, "-nostdin", "-hide_banner", *args],
            capture_output=True,
            text=True,
            timeout=30,
        )

    def _parse_trace_headers_slices(self, h264_path: Path) -> list[dict[str, int]]:
        tr = self.run_ffmpeg(
            "-i",
            str(h264_path),
            "-c",
            "copy",
            "-bsf:v",
            "trace_headers",
            "-f",
            "null",
            "-",
        )
        self.assertEqual(tr.returncode, 0, tr.stderr)
        slices: list[dict[str, int]] = []
        cur: dict[str, int] | None = None
        for ln in tr.stderr.splitlines():
            if "Slice Header" in ln:
                if cur is not None:
                    slices.append(cur)
                cur = {}
            elif cur is not None:
                m = re.search(
                    r"\]\s+\d+\s+([a-zA-Z0-9_]+)\s+[01]+\s*=\s*(-?\d+)", ln
                )
                if m and m.group(1) not in cur:
                    cur[m.group(1)] = int(m.group(2))
        if cur is not None:
            slices.append(cur)
        return slices

    def test_kernel_vectors_itu_t_h264_exact(self):
        res = self.run_isolated("h264-inter-dpb-vectors")
        self.assertEqual(res.returncode, 0, res.stderr)
        vec = json.loads(res.stdout)
        self.assertTrue(vec["ok"])

        luma_grid = [
            [(17 * r + 31 * c + 5 * r * c + 23) % 256 for c in range(8)]
            for r in range(8)
        ]
        self.assertEqual(vec["qpel16"], _h264_luma_qpel_16_oracle(luma_grid, 3, 3))

        chroma_grid = [
            [40, 120, 200, 90],
            [60, 140, 180, 110],
            [80, 160, 150, 130],
            [50, 100, 170, 70],
        ]
        self.assertEqual(vec["chroma64"], _h264_chroma_opel_64_oracle(chroma_grid, 1, 1))

        self.assertEqual(vec["deblock_strong"], [100, 100, 100, 102, 106, 108, 108, 108])
        self.assertEqual(vec["deblock_normal"], [90, 96, 99, 103, 105, 109, 114, 120])
        self.assertEqual(vec["deblock_chroma"], [102, 106])
        self.assertEqual(vec["implicit_weights_2_0_6"], [43, 21])
        self.assertEqual(vec["implicit_bipred_px"], 99)
        self.assertEqual(vec["explicit_bipred_px"], 99)
        self.assertEqual(vec["mvp_16x8_top"], [12, 16])
        self.assertEqual(vec["pskip_zero_mv"], [0, 0])
        self.assertEqual(vec["bdirect_temporal"], [8, -4, -8, 4])
        self.assertEqual(vec["subpel_me_mv"], [-1, 2, 0])

    def test_libx264_dpb_profiles_rplm_mmco_and_poc_parity(self):
        cases = (
            (
                "baseline_ip_wrap",
                "baseline",
                "ref=2:keyint=8:min-keyint=8:scenecut=0",
                [],
                12,
            ),
            (
                "main_b2_wp1",
                "main",
                "bframes=2:b-pyramid=none:ref=3:weightp=1:keyint=8:min-keyint=8:scenecut=0",
                [],
                12,
            ),
            (
                "high_bpyramid_wp2_mmco",
                "high",
                "bframes=3:b-pyramid=normal:ref=4:weightp=2:weightb=1:keyint=8:min-keyint=8:scenecut=0",
                [],
                12,
            ),
            (
                "high_deblock_disabled",
                "high",
                "bframes=2:b-pyramid=strict:ref=3:deblock=0:keyint=10:min-keyint=10:scenecut=0",
                ["-flags", "-loop"],
                12,
            ),
            (
                "high_long_gop_framenum_wrap",
                "high",
                "bframes=2:b-pyramid=normal:ref=4:keyint=24:min-keyint=24:scenecut=0",
                [],
                20,
            ),
            (
                "high_ref8_bpyramid_dpb_full_nonref",
                "high",
                "bframes=3:b-pyramid=normal:ref=8:keyint=30:min-keyint=30:scenecut=0",
                [],
                20,
            ),
        )
        slice_char = {0: "P", 1: "B", 2: "I"}
        with tempfile.TemporaryDirectory(prefix="lean-h264-dpb-") as tmp:
            root = Path(tmp)
            for name, profile, x264_params, extra_flags, nframes in cases:
                with self.subTest(case=name):
                    h264_path = root / f"{name}.264"
                    enc = self.run_ffmpeg(
                        "-y",
                        "-loglevel",
                        "error",
                        "-f",
                        "lavfi",
                        "-i",
                        "testsrc2=size=64x48:rate=25",
                        "-frames:v",
                        str(nframes),
                        "-pix_fmt",
                        "yuv420p",
                        "-c:v",
                        "libx264",
                        "-profile:v",
                        profile,
                        *extra_flags,
                        "-x264-params",
                        x264_params,
                        "-f",
                        "h264",
                        str(h264_path),
                    )
                    self.assertEqual(enc.returncode, 0, enc.stderr)

                    probe = self.run_isolated("h264-inter-dpb-probe", str(h264_path))
                    self.assertEqual(probe.returncode, 0, probe.stderr)
                    rep = json.loads(probe.stdout)
                    self.assertTrue(rep["ok"])
                    self.assertTrue(rep["poc_monotone"])
                    self.assertTrue(rep["capacity_all_ok"])
                    self.assertEqual(rep["frames_decoded"], nframes)
                    self.assertEqual(len(rep["output_poc_order"]), nframes)

                    ff_slices = self._parse_trace_headers_slices(h264_path)
                    self.assertEqual(len(ff_slices), len(rep["traces"]))
                    for fs, lt in zip(ff_slices, rep["traces"]):
                        self.assertEqual(fs["slice_type"] % 5, lt["slice_type"])
                        self.assertEqual(fs["nal_unit_type"] == 5, lt["is_idr"])
                        self.assertEqual(fs["nal_ref_idc"] != 0, lt["is_ref"])
                        self.assertEqual(fs["frame_num"], lt["frame_num"])
                        self.assertEqual(
                            fs.get("disable_deblocking_filter_idc", 0),
                            lt["disable_dbf"],
                        )
                        if lt["slice_type"] == 0:
                            self.assertGreaterEqual(len(lt["ref_l0_pocs"]), 1)
                            self.assertEqual(lt["ref_l1_pocs"], [])
                        elif lt["slice_type"] == 1:
                            self.assertGreaterEqual(len(lt["ref_l0_pocs"]), 1)
                            self.assertGreaterEqual(len(lt["ref_l1_pocs"]), 1)

                    if self.ffprobe:
                        ffp = subprocess.run(
                            [
                                self.ffprobe,
                                "-v",
                                "error",
                                "-select_streams",
                                "v:0",
                                "-show_frames",
                                "-show_entries",
                                "frame=pict_type,key_frame",
                                "-of",
                                "json",
                                str(h264_path),
                            ],
                            capture_output=True,
                            text=True,
                            check=True,
                        )
                        ff_frames = json.loads(ffp.stdout)["frames"]
                        self.assertEqual(len(ff_frames), nframes)

                        cvs_groups: list[list[dict]] = []
                        cur_grp: list[dict] = []
                        for tr_item in rep["traces"]:
                            if tr_item["is_idr"] and cur_grp:
                                cvs_groups.append(cur_grp)
                                cur_grp = []
                            cur_grp.append(tr_item)
                        if cur_grp:
                            cvs_groups.append(cur_grp)

                        lean_display: list[dict] = []
                        lean_expected_pocs: list[int] = []
                        for grp in cvs_groups:
                            ordered = sorted(grp, key=lambda t: t["poc"])
                            lean_display.extend(ordered)
                            lean_expected_pocs.extend(t["poc"] for t in ordered)

                        self.assertEqual(rep["output_poc_order"], lean_expected_pocs)
                        for lf, ff in zip(lean_display, ff_frames):
                            self.assertEqual(
                                slice_char[lf["slice_type"]], ff["pict_type"]
                            )
                            self.assertEqual(lf["is_idr"], bool(ff["key_frame"]))

    def test_qpel_16_positions_ffmpeg_decoded_pixels_bit_exact(self):
        res = self.run_isolated("h264-inter-dpb-vectors")
        self.assertEqual(res.returncode, 0, res.stderr)
        vec = json.loads(res.stdout)
        sps_bits = (
            f"{66:08b}{0:08b}{30:08b}"
            + _ue_bits(0) + _ue_bits(0) + _ue_bits(0) + _ue_bits(0)
            + _ue_bits(1) + "0" + _ue_bits(0) + _ue_bits(0) + "1100"
        )
        pps_bits = (
            _ue_bits(0) + _ue_bits(0) + "00" + _ue_bits(0) + _ue_bits(0)
            + _ue_bits(0) + "0" + "00" + _se_bits(0) + _se_bits(0)
            + _se_bits(0) + "100"
        )
        idr_sh = (
            _ue_bits(0) + _ue_bits(2) + _ue_bits(0) + "0000" + _ue_bits(0)
            + "0000" + "00" + _se_bits(0) + _ue_bits(1) + _ue_bits(25)
        )
        luma_16x16 = bytearray(
            (17 * min(r, 7) + 31 * min(c, 7) + 5 * min(r, 7) * min(c, 7) + 23) % 256
            for r in range(16)
            for c in range(16)
        )
        sps_nal = _rbsp_to_annexb_nalu(0x67, sps_bits)
        pps_nal = _rbsp_to_annexb_nalu(0x68, pps_bits)
        idr_nal = _rbsp_to_annexb_nalu(0x65, idr_sh, bytes(luma_16x16) + bytes([128] * 128))
        ff_pixels: list[int] = []
        with tempfile.TemporaryDirectory(prefix="lean-h264-qpel-") as tmp:
            root = Path(tmp)
            for yf in range(4):
                for xf in range(4):
                    p_bits = (
                        _ue_bits(0) + _ue_bits(0) + _ue_bits(0) + "0001" + "0010"
                        + "000" + _se_bits(0) + _ue_bits(1)
                        + _ue_bits(0) + _ue_bits(0) + _se_bits(xf) + _se_bits(yf) + _ue_bits(0)
                    )
                    p264 = root / f"q_{yf}_{xf}.264"
                    pyuv = root / f"q_{yf}_{xf}.yuv"
                    p264.write_bytes(sps_nal + pps_nal + idr_nal + _rbsp_to_annexb_nalu(0x41, p_bits))
                    dec = self.run_ffmpeg(
                        "-y", "-loglevel", "error", "-i", str(p264),
                        "-f", "rawvideo", "-pix_fmt", "yuv420p", str(pyuv),
                    )
                    self.assertEqual(dec.returncode, 0, dec.stderr)
                    ff_pixels.append(pyuv.read_bytes()[384 + 3 * 16 + 3])
        self.assertEqual(vec["qpel16"], ff_pixels)
        self.assertEqual(vec["qpel16"][3 * 4 + 2], 133)

    def test_sps_scaling_matrix_poc_type1_and_mmco5_reset_parity(self):
        pcm = bytes([128] * 384)
        pps0 = (
            _ue_bits(0) + _ue_bits(0) + "00" + _ue_bits(0) + _ue_bits(0)
            + _ue_bits(0) + "0" + "00" + _se_bits(0) + _se_bits(0)
            + _se_bits(0) + "100"
        )
        sps_scale = (
            f"{100:08b}{0:08b}{30:08b}"
            + _ue_bits(0) + _ue_bits(1) + _ue_bits(0) + _ue_bits(0) + "0" + "1"
            + ("1" + _se_bits(-8)) + "00000" + ("1" + _se_bits(2) + _se_bits(-10)) + "0"
            + _ue_bits(0) + _ue_bits(0) + _ue_bits(0) + _ue_bits(2) + "0"
            + _ue_bits(0) + _ue_bits(0) + "1100"
        )
        idr0 = _ue_bits(0) + _ue_bits(7) + _ue_bits(0) + "0000" + _ue_bits(0) + "0000" + "00" + _se_bits(0) + _ue_bits(1) + _ue_bits(25)
        p0_1 = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0001" + "0010" + "000" + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        sps1 = (
            f"{66:08b}{0:08b}{30:08b}"
            + _ue_bits(0) + _ue_bits(0) + _ue_bits(1) + "0" + _se_bits(-2)
            + _se_bits(0) + _ue_bits(2) + _se_bits(4) + _se_bits(6) + _ue_bits(2)
            + "0" + _ue_bits(0) + _ue_bits(0) + "1100"
        )
        idr1 = _ue_bits(0) + _ue_bits(7) + _ue_bits(0) + "0000" + _ue_bits(0) + _se_bits(0) + "00" + _se_bits(0) + _ue_bits(1) + _ue_bits(25)
        p1 = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0001" + _se_bits(0) + "000" + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        p2_nr = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0010" + _se_bits(-1) + "00" + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        p3_r = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0010" + _se_bits(2) + "000" + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        sps2 = f"{66:08b}{0:08b}{30:08b}" + _ue_bits(0) + _ue_bits(0) + _ue_bits(2) + _ue_bits(2) + "0" + _ue_bits(0) + _ue_bits(0) + "1100"
        idr2 = _ue_bits(0) + _ue_bits(7) + _ue_bits(0) + "0000" + _ue_bits(0) + "00" + _se_bits(0) + _ue_bits(1) + _ue_bits(25)
        p_fn1 = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0001" + "000" + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        p_mmco5 = _ue_bits(0) + _ue_bits(5) + _ue_bits(0) + "0010" + "00" + "1" + _ue_bits(5) + _ue_bits(0) + _se_bits(0) + _ue_bits(1) + _ue_bits(1)
        with tempfile.TemporaryDirectory(prefix="lean-h264-syn-") as tmp:
            root = Path(tmp)
            p_sc = root / "scale_sps.264"
            p_sc.write_bytes(_rbsp_to_annexb_nalu(0x67, sps_scale) + _rbsp_to_annexb_nalu(0x68, pps0) + _rbsp_to_annexb_nalu(0x65, idr0, pcm) + _rbsp_to_annexb_nalu(0x41, p0_1))
            p_t1 = root / "poc_type1.264"
            p_t1.write_bytes(_rbsp_to_annexb_nalu(0x67, sps1) + _rbsp_to_annexb_nalu(0x68, pps0) + _rbsp_to_annexb_nalu(0x65, idr1, pcm) + _rbsp_to_annexb_nalu(0x41, p1) + _rbsp_to_annexb_nalu(0x01, p2_nr) + _rbsp_to_annexb_nalu(0x41, p3_r))
            p_m5 = root / "mmco5_poc2.264"
            p_m5.write_bytes(_rbsp_to_annexb_nalu(0x67, sps2) + _rbsp_to_annexb_nalu(0x68, pps0) + _rbsp_to_annexb_nalu(0x65, idr2, pcm) + _rbsp_to_annexb_nalu(0x41, p_fn1) + _rbsp_to_annexb_nalu(0x41, p_mmco5) + _rbsp_to_annexb_nalu(0x41, p_fn1))
            for f in (p_sc, p_t1, p_m5):
                dec = self.run_ffmpeg("-v", "error", "-i", str(f), "-f", "null", "-")
                self.assertEqual(dec.returncode, 0, dec.stderr)
            r_sc = json.loads(self.run_isolated("h264-inter-dpb-probe", str(p_sc)).stdout)
            self.assertTrue(r_sc["ok"])
            self.assertEqual(r_sc["output_poc_order"], [0, 2])
            r_t1 = json.loads(self.run_isolated("h264-inter-dpb-probe", str(p_t1)).stdout)
            self.assertTrue(r_t1["ok"])
            self.assertEqual([t["poc"] for t in r_t1["traces"]], [0, 4, 1, 12])
            self.assertEqual(r_t1["output_poc_order"], [0, 1, 4, 12])
            if self.ffprobe:
                ffp = subprocess.run([self.ffprobe, "-v", "error", "-show_frames", "-show_entries", "frame=coded_picture_number", "-of", "json", str(p_t1)], capture_output=True, text=True, check=True)
                self.assertEqual([fr["coded_picture_number"] for fr in json.loads(ffp.stdout)["frames"]], [0, 2, 1, 3])
            r_m5 = json.loads(self.run_isolated("h264-inter-dpb-probe", str(p_m5)).stdout)
            self.assertTrue(r_m5["ok"])
            self.assertEqual([t["poc"] for t in r_m5["traces"]], [0, 2, 0, 2])
            self.assertEqual([t["frame_num"] for t in r_m5["traces"]], [0, 1, 0, 1])

    def test_empty_or_non_h264_annexb_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="lean-h264-bad-") as tmp:
            bad = Path(tmp) / "garbage.264"
            bad.write_bytes(b"\x00\x00\x00\x01\x06\x05\x04deadbeef")
            res = self.run_isolated("h264-inter-dpb-probe", str(bad))
            self.assertNotEqual(res.returncode, 0)
            rep = json.loads(res.stdout)
            self.assertFalse(rep["ok"])
            self.assertEqual(rep["frames_decoded"], 0)


if __name__ == "__main__":
    unittest.main()
