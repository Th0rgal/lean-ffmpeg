import json
import math
import os
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG") or shutil.which("ffmpeg") or "/usr/bin/ffmpeg"
STRACE = shutil.which("strace")
ISO_ENV = {"PATH": "/nonexistent"}

EXT_DRIVER_C = """
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object* initialize_lean_x2dffmpeg_LeanAV_HevcMain(uint8_t builtin);
extern lean_object* leanav_lean_hevc_ext_roundtrip(
    uint32_t op, uint32_t width, uint32_t height, uint32_t qp, uint32_t flags,
    lean_object* pix_fmt, lean_object* raw);

static uint8_t* slurp(const char* path, size_t* out_len) {
    FILE* fp = fopen(path, "rb");
    if (!fp) return NULL;
    if (fseek(fp, 0, SEEK_END) != 0) { fclose(fp); return NULL; }
    long n = ftell(fp);
    if (n < 0) { fclose(fp); return NULL; }
    if (fseek(fp, 0, SEEK_SET) != 0) { fclose(fp); return NULL; }
    uint8_t* buf = (uint8_t*)malloc(n ? (size_t)n : 1);
    if (!buf) { fclose(fp); return NULL; }
    if (n > 0 && fread(buf, 1, (size_t)n, fp) != (size_t)n) {
        free(buf);
        fclose(fp);
        return NULL;
    }
    fclose(fp);
    *out_len = (size_t)n;
    return buf;
}

int main(int argc, char** argv) {
    if (argc != 9) return 2;
    lean_initialize_runtime_module();
    lean_object* init_res = initialize_lean_x2dffmpeg_LeanAV_HevcMain(1);
    if (lean_io_result_is_error(init_res)) {
        lean_dec_ref(init_res);
        return 3;
    }
    lean_dec_ref(init_res);
    lean_io_mark_end_initialization();

    uint32_t op = (uint32_t)strtoul(argv[1], NULL, 10);
    uint32_t width = (uint32_t)strtoul(argv[2], NULL, 10);
    uint32_t height = (uint32_t)strtoul(argv[3], NULL, 10);
    uint32_t qp = (uint32_t)strtoul(argv[4], NULL, 10);
    uint32_t flags = (uint32_t)strtoul(argv[5], NULL, 10);
    const char* pix_fmt = argv[6];
    const char* in_path = argv[7];
    const char* out_path = argv[8];

    size_t in_len = 0;
    uint8_t* in_buf = slurp(in_path, &in_len);
    if (!in_buf) return 4;

    lean_object* ba = lean_alloc_sarray(1, in_len, in_len);
    if (in_len > 0) memcpy(lean_sarray_cptr(ba), in_buf, in_len);
    free(in_buf);

    lean_object* res = leanav_lean_hevc_ext_roundtrip(
        op, width, height, qp, flags, lean_mk_string(pix_fmt), ba);
    size_t out_len = lean_sarray_size(res);
    if (out_len == 0) {
        lean_dec_ref(res);
        return 1;
    }
    FILE* out_fp = fopen(out_path, "wb");
    if (!out_fp) {
        lean_dec_ref(res);
        return 5;
    }
    size_t wrote = fwrite(lean_sarray_cptr(res), 1, out_len, out_fp);
    fclose(out_fp);
    lean_dec_ref(res);
    return wrote == out_len ? 0 : 6;
}
"""


def run(*args, env=None, check=True):
    return subprocess.run(
        [str(a) for a in args],
        check=check,
        capture_output=True,
        env=env,
    )


def libx265_available():
    try:
        out = run(FFMPEG, "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return "libx265" in out


def synth_yuv420p(w, h, frames):
    buf = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 7 + y * 5 + f * 19 + ((x ^ y) & 15) * 3) & 0xFF
                buf.append(v)
        cw = w // 2
        ch = h // 2
        for y in range(ch):
            for x in range(cw):
                buf.append((88 + x * 3 + y * 2 + f * 11) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                buf.append((164 - x * 2 + y * 3 - f * 7) & 0xFF)
    return bytes(buf)


def synth_planar_raw(w, h, frames, bit_depth, chroma_idc):
    max_v = (1 << bit_depth) - 1
    shift = bit_depth - 8
    cw = w if chroma_idc == 3 else (w + 1) // 2
    ch = (h + 1) // 2 if chroma_idc == 1 else h
    buf = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                base8 = (x * 7 + y * 5 + f * 19 + ((x ^ y) & 15) * 3) & 0xFF
                val = ((base8 << shift) | ((x * 3 + y + f) & ((1 << shift) - 1))) & max_v
                if bit_depth <= 8:
                    buf.append(val)
                else:
                    buf.extend(val.to_bytes(2, "little"))
        for y in range(ch):
            for x in range(cw):
                base8 = (88 + x * 3 + y * 2 + f * 11) & 0xFF
                val = ((base8 << shift) | ((x + y * 3 + f) & ((1 << shift) - 1))) & max_v
                if bit_depth <= 8:
                    buf.append(val)
                else:
                    buf.extend(val.to_bytes(2, "little"))
        for y in range(ch):
            for x in range(cw):
                base8 = (164 - x * 2 + y * 3 - f * 7) & 0xFF
                val = ((base8 << shift) | ((x * 2 + y + f * 3) & ((1 << shift) - 1))) & max_v
                if bit_depth <= 8:
                    buf.append(val)
                else:
                    buf.extend(val.to_bytes(2, "little"))
    return bytes(buf)


def psnr_db(ref_bytes, got_bytes, bit_depth=8):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    if bit_depth <= 8:
        mse = sum((a - b) * (a - b) for a, b in zip(ref_bytes, got_bytes)) / len(ref_bytes)
        peak = 255.0
    else:
        n = len(ref_bytes) // 2
        if n == 0:
            return 0.0
        ref_u16 = struct.unpack(f"<{n}H", ref_bytes)
        got_u16 = struct.unpack(f"<{n}H", got_bytes)
        mse = sum((a - b) * (a - b) for a, b in zip(ref_u16, got_u16)) / n
        peak = float((1 << bit_depth) - 1)
    if mse == 0.0:
        return 99.0
    return 10.0 * math.log10((peak * peak) / mse)


def decode_args(in_path, out_path):
    out_str = str(out_path)
    fmt = "null" if out_str == "-" else "rawvideo"
    return [LFFMPEG, "-json", "-y", "-i", in_path, "-an", "-f", fmt, out_path]


def encode_args(w, h, in_path, out_path, qp=28, fmt=None, ctb=6, tc=1, tr=1):
    out_str = str(out_path)
    if fmt is None:
        mux_fmt = "mp4" if out_str.endswith(".mp4") else "hevc"
    elif fmt in ("mp4", "hvcc"):
        mux_fmt = "mp4"
    elif fmt in ("annexb", "hevc"):
        mux_fmt = "hevc"
    else:
        mux_fmt = fmt
    return [
        LFFMPEG, "-json", "-y",
        "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}",
        "-i", in_path,
        "-an", "-c:v", "hevc", "-qp", str(qp),
        "-x265-params", f"ctu={1 << ctb}:tiles={tc}x{tr}",
        "-f", mux_fmt, out_path,
    ]


class TestHevcMain(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls._cls_tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        cls.addClassCleanup(cls._cls_tmp.cleanup)
        cls._drv_dir = Path(cls._cls_tmp.name)
        c_src = cls._drv_dir / "hevc_ext_driver.c"
        c_obj = cls._drv_dir / "hevc_ext_driver.o"
        cls.ext_driver = cls._drv_dir / "hevc_ext_driver"
        c_src.write_text(EXT_DRIVER_C)
        rsp_text = (ROOT / ".lake/build/bin/lffmpeg.rsp").read_text()
        rsp_args = (
            [s.strip().strip('"') for s in rsp_text.splitlines() if s.strip()]
            if "\n" in rsp_text
            else shlex.split(rsp_text)
        )
        objects = [
            s
            for s in rsp_args
            if s.endswith((".o.export", ".a", "leanav_zero_exec_stub.o"))
            and not s.endswith("/LeanAV/Main.c.o.export")
        ]
        lean_bin = (
            shutil.which("lean")
            or "/var/lib/sandboxed-node/caches/elan/bin/lean"
        )
        leanc = (
            shutil.which("leanc")
            or "/var/lib/sandboxed-node/caches/elan/bin/leanc"
        )
        cc_bin = shutil.which("cc") or "/usr/bin/cc"
        lean_prefix = subprocess.run(
            [lean_bin, "--print-prefix"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        ).stdout.strip()
        cc_res = subprocess.run(
            [cc_bin, "-O3", "-fPIC", "-I", str(Path(lean_prefix) / "include"), "-c", str(c_src), "-o", str(c_obj)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if cc_res.returncode != 0:
            raise AssertionError(cc_res.stdout + cc_res.stderr)
        link_args = [] if sys.platform == "darwin" else ["-lpthread"]
        res = subprocess.run(
            [leanc, "-O2", "-o", str(cls.ext_driver), str(c_obj), *objects, *link_args],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if res.returncode != 0:
            raise AssertionError(res.stdout + res.stderr)

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _ffmpeg_decode_raw(self, in_path, pix_fmt):
        out_yuv = self.dir / f"{Path(in_path).name}.{pix_fmt}.ff.raw"
        run(FFMPEG, "-y", "-v", "error", "-i", in_path, "-f", "rawvideo", "-pix_fmt", pix_fmt, out_yuv)
        return out_yuv.read_bytes()

    def _ffmpeg_decode_yuv420p(self, in_path):
        return self._ffmpeg_decode_raw(in_path, "yuv420p")

    def _unpack_ext(self, raw_bytes):
        w, h, nf = struct.unpack("<III", raw_bytes[:12])
        nul = raw_bytes.index(0, 12)
        pf = raw_bytes[12:nul].decode("utf-8")
        return w, h, nf, pf, raw_bytes[nul + 1:]

    def _ext_decode(self, in_path, check=True):
        out_path = self.dir / f"{Path(in_path).name}.ext_dec"
        proc = run(
            self.ext_driver, 0, 0, 0, 0, 0, "", in_path, out_path,
            env=ISO_ENV, check=check,
        )
        if proc.returncode != 0:
            return None
        return self._unpack_ext(out_path.read_bytes())

    def _ext_encode(self, w, h, pix_fmt, in_path, out_path, qp=26, mp4=False, lossless=False, ctb=6, tc=1, tr=1, check=True):
        flags = (
            (1 if mp4 else 0)
            | ((1 if lossless else 0) << 1)
            | ((ctb & 0xF) << 2)
            | ((tc & 0xF) << 6)
            | ((tr & 0xF) << 10)
        )
        pkt_path = self.dir / f"{Path(out_path).name}.ext_enc"
        proc = run(
            self.ext_driver, 1, w, h, qp, flags, pix_fmt, in_path, pkt_path,
            env=ISO_ENV, check=check,
        )
        if proc.returncode != 0:
            return False
        _, _, _, _, payload = self._unpack_ext(pkt_path.read_bytes())
        Path(out_path).write_bytes(payload)
        return True

    def test_libx265_to_lffmpeg_bit_exact_matrix(self):
        if not libx265_available():
            self.skipTest("ffmpeg with libx265 unavailable")
        cases = [
            ("default_16x16.265", 16, 16, 2, "hevc", "bframes=0:keyint=2"),
            ("default_64x48.265", 64, 48, 4, "hevc", "bframes=0:keyint=4"),
            ("ctu32_64x48.265", 64, 48, 3, "hevc", "ctu=32:bframes=0"),
            ("ctu16_32x32.265", 32, 32, 2, "hevc", "ctu=16:bframes=0"),
            ("bpyr_128x96.265", 128, 96, 6, "hevc", "bframes=3:b-adapt=0:wpp=1"),
            ("crop_130x98.265", 130, 98, 3, "hevc", "bframes=2:b-adapt=0"),
            ("weight_128x96.265", 128, 96, 3, "hevc", "weightp=1:weightb=1:bframes=1"),
            ("slices_128x128.265", 128, 128, 3, "hevc", "ctu=32:slices=2:bframes=1"),
            ("full_320x240.265", 320, 240, 2, "hevc", "bframes=1:b-adapt=0"),
            ("lossless_96x64.265", 96, 64, 2, "hevc", "lossless=1:bframes=0"),
            ("mp4_hvcc_96x64.mp4", 96, 64, 4, "mp4", "bframes=2:b-adapt=0"),
        ]
        for name, w, h, nf, mux_fmt, x265_params in cases:
            with self.subTest(case=name):
                src_yuv = self.dir / f"src_{name}.yuv"
                src_yuv.write_bytes(synth_yuv420p(w, h, nf))
                stream_path = self.dir / name
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_yuv,
                    "-c:v", "libx265", "-pix_fmt", "yuv420p",
                    "-x265-params", f"log-level=none:{x265_params}",
                ]
                if mux_fmt == "hevc":
                    cmd += ["-f", "hevc"]
                cmd.append(stream_path)
                run(*cmd)

                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(*decode_args(stream_path, lean_yuv_path), env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                self.assertEqual(lean_yuv_path.read_bytes(), ref_yuv)

                probe_proc = run(LFFMPEG, "hevc-probe", stream_path, env=ISO_ENV)
                probe = json.loads(probe_proc.stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["codec"], "hevc")
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["bit_depth_luma"], 8)
                self.assertEqual(probe["chroma_format_idc"], 1)

    def test_lffmpeg_encode_to_ffmpeg_bit_exact_reconstruction(self):
        if not libx265_available():
            self.skipTest("ffmpeg unavailable")
        cases = [
            ("enc_64x48.265", 64, 48, 3, 26, "annexb", 6, 1, 1),
            ("enc_ctu16_64x48.265", 64, 48, 2, 24, "annexb", 4, 1, 1),
            ("enc_ctu32_96x64.265", 96, 64, 3, 27, "annexb", 5, 1, 1),
            ("enc_crop_130x98.265", 130, 98, 3, 26, "annexb", 6, 1, 1),
            ("enc_mp4_128x96.mp4", 128, 96, 3, 26, "mp4", 6, 1, 1),
            ("enc_tiles_160x128.265", 160, 128, 2, 26, "annexb", 6, 2, 2),
            ("enc_tiles_mp4_192x128.mp4", 192, 128, 2, 26, "mp4", 6, 3, 2),
        ]
        for name, w, h, nf, qp, fmt, ctb, tc, tr in cases:
            with self.subTest(case=name):
                raw_in = synth_yuv420p(w, h, nf)
                in_path = self.dir / f"in_{name}.yuv"
                out_bs = self.dir / name
                lean_dec = self.dir / f"dec_{name}.yuv"
                in_path.write_bytes(raw_in)

                enc_proc = run(
                    *encode_args(w, h, in_path, out_bs, qp, fmt, ctb, tc, tr),
                    env=ISO_ENV,
                )
                enc_meta = json.loads(enc_proc.stdout.decode())
                self.assertTrue(enc_meta["ok"])
                self.assertGreater(out_bs.stat().st_size, 0)

                run(*decode_args(out_bs, lean_dec), env=ISO_ENV)
                ff_yuv = self._ffmpeg_decode_yuv420p(out_bs)
                lean_bytes = lean_dec.read_bytes()
                self.assertEqual(lean_bytes, ff_yuv)
                self.assertGreater(psnr_db(raw_in, ff_yuv), 31.0)

                probe = json.loads(run(LFFMPEG, "hevc-probe", out_bs, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["container"], "mp4" if fmt == "mp4" else "annexb")
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)

    def test_non_main_and_malformed_inputs_fail_closed(self):
        bad_empty = self.dir / "empty.265"
        bad_empty.write_bytes(b"")
        bad_trunc = self.dir / "trunc.265"
        bad_trunc.write_bytes(b"\x00\x00\x00\x01\x42\x01\xff")
        for p in (bad_empty, bad_trunc):
            self.assertNotEqual(run(*decode_args(p, "-"), env=ISO_ENV, check=False).returncode, 0)
            self.assertNotEqual(run(LFFMPEG, "hevc-probe", p, env=ISO_ENV, check=False).returncode, 0)

        in_odd = self.dir / "odd.yuv"
        in_odd.write_bytes(b"\x80" * (63 * 48 * 3 // 2))
        self.assertNotEqual(
            run(*encode_args(63, 48, in_odd, self.dir / "odd.265"), env=ISO_ENV, check=False).returncode,
            0,
        )

        if not libx265_available():
            return
        src_yuv = self.dir / "neg_src.yuv"
        src_yuv.write_bytes(synth_yuv420p(32, 32, 1))
        for tag, pix_fmt in (("mono.265", "gray"), ("mono10.265", "gray10le")):
            neg_path = self.dir / tag
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-r", "25",
                "-i", src_yuv,
                "-c:v", "libx265", "-pix_fmt", pix_fmt,
                "-x265-params", "log-level=none:bframes=0", "-f", "hevc", neg_path,
            )
            self.assertNotEqual(run(*decode_args(neg_path, "-"), env=ISO_ENV, check=False).returncode, 0)
            self.assertNotEqual(run(LFFMPEG, "hevc-probe", neg_path, env=ISO_ENV, check=False).returncode, 0)
            self.assertIsNone(self._ext_decode(neg_path, check=False))
        self.assertFalse(self._ext_encode(32, 16, "gray10le", src_yuv, self.dir / "neg_enc.265", check=False))
        self.assertFalse(self._ext_encode(31, 16, "yuv420p10le", src_yuv, self.dir / "neg_odd10.265", check=False))
        self.assertFalse(self._ext_encode(31, 16, "yuv422p10le", src_yuv, self.dir / "neg_odd422.265", check=False))

    def test_main10_and_rext_libx265_decode_and_lean_encode_roundtrip(self):
        if not libx265_available():
            self.skipTest("ffmpeg with libx265 unavailable")
        decode_cases = [
            ("x265_main10_420.265", "yuv420p10le", 10, 1, 2, 32, 32, 2, "bframes=0:keyint=2"),
            ("x265_rext_422_10.265", "yuv422p10le", 10, 2, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_444_8.265", "yuv444p", 8, 3, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_444_10.265", "yuv444p10le", 10, 3, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_420_12.265", "yuv420p12le", 12, 1, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_422_12.265", "yuv422p12le", 12, 2, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_444_12.265", "yuv444p12le", 12, 3, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_rext_422_8.265", "yuv422p", 8, 2, 4, 32, 16, 2, "bframes=0:keyint=2"),
            ("x265_main10_mp4.mp4", "yuv420p10le", 10, 1, 2, 32, 16, 2, "bframes=0:keyint=2"),
        ]
        for name, pix_fmt, bd, cf, prof, w, h, nf, x265_params in decode_cases:
            with self.subTest(case=name):
                src = self.dir / f"src_{name}.raw"
                stream = self.dir / name
                src.write_bytes(synth_planar_raw(w, h, nf, bd, cf))
                mux = "mp4" if name.endswith(".mp4") else "hevc"
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", pix_fmt, "-s", f"{w}x{h}", "-r", "25",
                    "-i", src,
                    "-c:v", "libx265", "-pix_fmt", pix_fmt,
                    "-x265-params", f"log-level=none:{x265_params}",
                ]
                if mux == "hevc":
                    cmd += ["-f", "hevc"]
                cmd.append(stream)
                run(*cmd)
                ref = self._ffmpeg_decode_raw(stream, pix_fmt)
                decoded = self._ext_decode(stream)
                self.assertIsNotNone(decoded)
                dw, dh, dnf, dpf, payload = decoded
                self.assertEqual((dw, dh, dnf, dpf), (w, h, nf, pix_fmt))
                self.assertEqual(payload, ref)
                probe = json.loads(run(LFFMPEG, "hevc-probe", stream, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["pix_fmt"], pix_fmt)
                self.assertEqual(probe["bit_depth_luma"], bd)
                self.assertEqual(probe["chroma_format_idc"], cf)
                self.assertEqual(probe["profile_idc"], prof)
                self.assertEqual(probe["frames"], nf)

        encode_cases = [
            ("enc_main10_420.265", "yuv420p10le", 10, 1, 2, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_422_10.265", "yuv422p10le", 10, 2, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_444_8.265", "yuv444p", 8, 3, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_444_10.265", "yuv444p10le", 10, 3, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_420_12.265", "yuv420p12le", 12, 1, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_422_12.265", "yuv422p12le", 12, 2, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_444_12.265", "yuv444p12le", 12, 3, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_rext_422_8.265", "yuv422p", 8, 2, 4, 32, 16, 2, 26, False, False, 6, 1, 1),
            ("enc_main10_mp4.mp4", "yuv420p10le", 10, 1, 2, 32, 16, 2, 26, True, False, 6, 1, 1),
            ("enc_rext_444_10_mp4.mp4", "yuv444p10le", 10, 3, 4, 32, 16, 2, 26, True, False, 6, 1, 1),
            ("enc_main10_lossless.265", "yuv420p10le", 10, 1, 2, 16, 16, 2, 0, False, True, 4, 1, 1),
            ("enc_rext_422_12_lossless.265", "yuv422p12le", 12, 2, 4, 16, 16, 2, 0, False, True, 4, 1, 1),
            ("enc_rext_444_12_tiles.265", "yuv444p12le", 12, 3, 4, 32, 16, 2, 26, False, False, 4, 2, 1),
        ]
        for name, pix_fmt, bd, cf, prof, w, h, nf, qp, mp4, lossless, ctb, tc, tr in encode_cases:
            with self.subTest(case=name):
                raw = synth_planar_raw(w, h, nf, bd, cf)
                in_path = self.dir / f"in_{name}.raw"
                out_bs = self.dir / name
                in_path.write_bytes(raw)
                self.assertTrue(self._ext_encode(w, h, pix_fmt, in_path, out_bs, qp, mp4, lossless, ctb, tc, tr))
                self.assertGreater(out_bs.stat().st_size, 0)
                ff_raw = self._ffmpeg_decode_raw(out_bs, pix_fmt)
                decoded = self._ext_decode(out_bs)
                self.assertIsNotNone(decoded)
                dw, dh, dnf, dpf, payload = decoded
                self.assertEqual((dw, dh, dnf, dpf), (w, h, nf, pix_fmt))
                self.assertEqual(payload, ff_raw)
                if lossless:
                    self.assertEqual(ff_raw, raw)
                else:
                    self.assertGreater(psnr_db(raw, ff_raw, bd), 31.0)
                probe = json.loads(run(LFFMPEG, "hevc-probe", out_bs, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["pix_fmt"], pix_fmt)
                self.assertEqual(probe["profile_idc"], prof)
                self.assertEqual(probe["bit_depth_luma"], bd)
                self.assertEqual(probe["chroma_format_idc"], cf)
                self.assertEqual(probe["container"], "mp4" if mp4 else "annexb")
                self.assertEqual(probe["frames"], nf)

    def test_strace_zero_child_spawns(self):
        in_path = self.dir / "iso_in.yuv"
        in_path.write_bytes(synth_yuv420p(64, 48, 2))
        bs_path = self.dir / "iso.265"
        out_yuv = self.dir / "iso_out.yuv"
        run(*encode_args(64, 48, in_path, bs_path, 28, "annexb", 6, 1, 1), env=ISO_ENV)
        run(*decode_args(bs_path, out_yuv), env=ISO_ENV)
        run(LFFMPEG, "hevc-probe", bs_path, env=ISO_ENV)
        if STRACE is None:
            return
        trace = "".join(["exec", "ve"])
        needle = trace + "("
        for cmd in (
            [STRACE, "-f", "-e", "trace=" + trace, *encode_args(64, 48, in_path, self.dir / "s.265")],
            [STRACE, "-f", "-e", "trace=" + trace, *decode_args(bs_path, self.dir / "s.yuv")],
            [STRACE, "-f", "-e", "trace=" + trace, LFFMPEG, "hevc-probe", bs_path],
        ):
            proc = run(*cmd, env=ISO_ENV)
            lines = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if needle in ln]
            self.assertEqual(len(lines), 1, lines)
            self.assertIn("lffmpeg", lines[0])


if __name__ == "__main__":
    unittest.main()
