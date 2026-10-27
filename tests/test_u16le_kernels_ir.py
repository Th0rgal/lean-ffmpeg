"""LLVM 18 U16LE runtime parity, unaligned buffers, SIMD tails and both targets."""
import ctypes
import random
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
START = "define weak_odr dso_local void @lean_native_swscale_bilinear_q8_u16le"


class U16LeKernelsIR(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        clang = shutil.which("clang-18")
        if not clang:
            raise unittest.SkipTest("clang-18 unavailable")
        cls.tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        directory = Path(cls.tmp.name)
        kernels = []
        for arch in ("x86_64", "arm64"):
            text = (ROOT / "c" / f"leanav_lnir_{arch}.ll").read_text()
            names = ("lean_native_swscale_bilinear_q8_u16le", "lean_native_luma_stats_u16le",
                     "lean_native_extract_u16le_msb8")
            kernels.append("\n".join(re.search(
                r"define weak_odr dso_local [^\n]*@" + name + r"\([^\n]*\n.*?\n}",
                text, re.S).group() for name in names))
        if kernels[0] != kernels[1]:
            raise AssertionError("architecture U16LE implementations differ")
        ir = directory / "u16.ll"
        ir.write_text("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)\n" +
                      kernels[0].replace(" #0 {", " {").replace(", !llvm.loop !0", ""))
        so = directory / "u16.so"
        subprocess.run([clang, "-O3", "-shared", "-fPIC", str(ir), "-o", str(so)],
                       check=True, capture_output=True)
        subprocess.run([clang, "-target", "aarch64-linux-gnu", "-O3", "-c", str(ir),
                        "-o", str(directory / "u16-arm.o")], check=True, capture_output=True)
        cls.lib = ctypes.CDLL(str(so))
        cls.scale = cls.lib.lean_native_swscale_bilinear_q8_u16le
        cls.scale.argtypes = [ctypes.c_void_p] * 2 + [ctypes.c_uint64] * 4
        cls.scale.restype = None
        cls.extract = cls.lib.lean_native_extract_u16le_msb8
        cls.extract.argtypes = [ctypes.c_void_p] * 2 + [ctypes.c_uint64]
        cls.extract.restype = None
        cls.stats = cls.lib.lean_native_luma_stats_u16le
        cls.stats.argtypes = [ctypes.c_void_p] + [ctypes.c_uint64] * 2
        cls.stats.restype = ctypes.c_uint64

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def check_scale(self, sw, sh, dw, dh, values):
        expected = []
        for y in range(dh):
            for x in range(dw):
                if (sw, sh) == (dw, dh):
                    v = values[y * sw + x]
                elif (sw, sh) in ((dw * 2, dh * 2), (dw * 3, dh * 3)):
                    k = sw // dw
                    s = sum(values[(y * k + yy) * sw + x * k + xx]
                            for yy in range(k) for xx in range(k))
                    v = (s + 2) >> 2 if k == 2 else ((s + 4) * 7282) >> 16
                else:
                    xq, yq = x * sw * 256 // dw, y * sh * 256 // dh
                    x0, y0, fx, fy = xq >> 8, yq >> 8, xq & 255, yq & 255
                    x1, y1 = min(x0 + 1, sw - 1), min(y0 + 1, sh - 1)
                    top = (256 - fx) * values[y0 * sw + x0] + fx * values[y0 * sw + x1]
                    bot = (256 - fx) * values[y1 * sw + x0] + fx * values[y1 * sw + x1]
                    v = min(1023, ((256 - fy) * top + fy * bot + 32768) >> 16)
                expected.append(v & 65535)
        raw = b"".join(v.to_bytes(2, "little") for v in values)
        src = ctypes.create_string_buffer(b"\xa5" + raw + b"\xa5")
        dst = ctypes.create_string_buffer(b"\x5a" * (dw * dh * 2 + 2))
        self.scale(ctypes.byref(src, 1), ctypes.byref(dst, 1), sw, sh, dw, dh)
        want = b"".join(v.to_bytes(2, "little") for v in expected)
        self.assertEqual(dst.raw[:-1], b"\x5a" + want + b"\x5a", (sw, sh, dw, dh))
        self.assertEqual(src.raw[:-1], b"\xa5" + raw + b"\xa5")

    def test_scaling_paths_and_tails(self):
        rng = random.Random(20261027)
        for dw in range(1, 18):
            for k in (1, 2, 3):
                sw, sh, dh = dw * k, 5 * k, 5
                for cap in (1023, 65535):
                    self.check_scale(sw, sh, dw, dh, [rng.randrange(cap + 1) for _ in range(sw * sh)])
                    self.check_scale(sw, sh, dw, dh, [cap] * (sw * sh))
        for _ in range(80):
            sw, sh, dw, dh = [rng.randrange(1, 30) for _ in range(4)]
            self.check_scale(sw, sh, dw, dh, [rng.randrange(65536) for _ in range(sw * sh)])
        for dims in ((0, 3, 2, 2), (3, 0, 2, 2), (3, 3, 0, 2), (3, 3, 2, 0)):
            self.scale(None, None, *dims)

    def test_all_u16_values_and_stats_steps(self):
        values = list(range(65536))
        raw = b"".join(v.to_bytes(2, "little") for v in values)
        src = ctypes.create_string_buffer(b"\xa5" + raw + b"\xa5")
        for n in (0, 1, 15, 16, 17, 31, 32, 33, 65535, 65536):
            dst = ctypes.create_string_buffer(b"\x5a" * (n + 2))
            self.extract(ctypes.byref(src, 1), ctypes.byref(dst, 1), n)
            self.assertEqual(dst.raw[:-1], b"\x5a" + bytes((v >> 2) & 255 for v in values[:n]) + b"\x5a")
            for step in (0, 1, 2, 16, 17, n + 1, 2**64 - 1):
                sampled = [v >> 2 for v in values[:n:step]] if step else []
                mean = sum(sampled) // len(sampled) if sampled else 0
                var = max(0, sum(v * v for v in sampled) // len(sampled) - mean * mean) if sampled else 0
                self.assertEqual(self.stats(ctypes.byref(src, 1), n, step), (var << 32) | mean)
