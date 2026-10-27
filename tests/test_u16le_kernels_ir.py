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
            names = ("lean_native_swscale_bilinear_q8_u16le", "lean_native_luma_stats_u16le", "lean_native_luma_stats_u8",
                     "lean_native_extract_u16le_msb8", "lean_native_luma_acceptance_16x16_u8",
                     "lean_native_luma_acceptance_16x16_u16le", "lean_native_stencil2d_box3x3_u8")
            kernels.append("\n".join(re.search(
                r"define weak_odr dso_local [^\n]*@" + name + r"\([^\n]*\n.*?\n}",
                text, re.S).group() for name in names))
        if kernels[0] != kernels[1]:
            raise AssertionError("architecture U16LE implementations differ")
        ir = directory / "u16.ll"
        host = subprocess.check_output([clang, "-dumpmachine"], text=True).strip()
        ir.write_text(f'target triple = "{host}"\n' +
                      "declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>)\n" +
                      "declare i32 @llvm.vector.reduce.add.v16i32(<16 x i32>)\n" +
                      "declare <4 x i32> @llvm.umin.v4i32(<4 x i32>, <4 x i32>)\n" +
                      "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)\n" +
                      kernels[0].replace(" #0 {", " {").replace(", !llvm.loop !0", ""))
        so = directory / "u16.so"
        subprocess.run([clang, "-Werror", "-O3", "-shared", "-fPIC", str(ir), "-o", str(so)],
                       check=True, capture_output=True)
        arm_ir = directory / "u16-arm.ll"
        arm_ir.write_text(ir.read_text().replace(host, "aarch64-unknown-linux-gnu"))
        subprocess.run([clang, "-Werror", "-target", "aarch64-unknown-linux-gnu", "-O3", "-c", str(arm_ir),
                        "-o", str(directory / "u16-arm.o")], check=True, capture_output=True)
        cls.clang = clang
        cls.directory = directory
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
        cls.stats8 = cls.lib.lean_native_luma_stats_u8
        cls.stats8.argtypes = cls.stats.argtypes
        cls.stats8.restype = ctypes.c_uint64

        cls.accept = cls.lib.lean_native_luma_acceptance_16x16_u16le
        cls.accept8 = cls.lib.lean_native_luma_acceptance_16x16_u8
        for fn in (cls.accept, cls.accept8):
            fn.argtypes = [ctypes.c_void_p, ctypes.c_uint64, ctypes.c_uint64,
                           ctypes.c_void_p, ctypes.c_uint64, ctypes.c_uint64, ctypes.c_void_p]
            fn.restype = None

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_box3x3_interior_vectors_and_tails(self):
        stencil = self.lib.lean_native_stencil2d_box3x3_u8
        stencil.argtypes = [ctypes.c_void_p] * 2 + [ctypes.c_uint64] * 2
        stencil.restype = None
        rng = random.Random(13)
        for w in list(range(28)) + [33, 65]:
            for h in [0, 1, 2, 3, 4, 9]:
                for values in ([255] * (w * h), [rng.randrange(256) for _ in range(w * h)]):
                    expected = values.copy()
                    for y in range(1, h - 1):
                        for x in range(1, w - 1):
                            total = sum(values[(y + dy) * w + x + dx]
                                        for dy in (-1, 0, 1) for dx in (-1, 0, 1))
                            expected[y * w + x] = (total + 4) // 9
                    src = ctypes.create_string_buffer(b"\xa5" + bytes(values) + b"\xa5")
                    dst = ctypes.create_string_buffer(b"\x5a" * (w * h + 2))
                    stencil(ctypes.byref(dst, 1), ctypes.byref(src, 1), w, h)
                    self.assertEqual(dst.raw[:-1], b"\x5a" + bytes(expected) + b"\x5a",
                                     (w, h))
                    self.assertEqual(src.raw[:-1], b"\xa5" + bytes(values) + b"\xa5")

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
                    v = (s + 2) >> 2 if k == 2 else (s + 4) // 9
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

    def test_3x3_full_u16_maximum(self):
        # Pure scalar, full vectors, and each possible vector tail.
        for dw in (1, 3, 4, 5, 6, 7, 8, 9):
            with self.subTest(dw=dw):
                src = (ctypes.c_uint16 * (9 * dw))(*([65535] * (9 * dw)))
                dst = (ctypes.c_uint16 * dw)()
                self.scale(src, dst, 3 * dw, 3, dw, 1)
                self.assertEqual(list(dst), [65535] * dw)
                self.check_scale(3 * dw, 3, dw, 1, [65535] * (9 * dw))

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

    def test_general_q8_ratios_and_table_boundary(self):
        rng = random.Random(1102)
        dims = [(1920, 1080, 854, 480), (18, 6, 11, 5),
                (1, 1, 7, 3), (17, 9, 1, 5)]
        dims += [(23, 7, w, 5) for w in (*range(1, 13), 4095, 4096, 4097, 4101)]
        for sw, sh, dw, dh in dims:
            for cap in (1023, 65535):
                with self.subTest(dims=(sw, sh, dw, dh), cap=cap):
                    self.check_scale(sw, sh, dw, dh,
                                     [rng.randrange(cap + 1) for _ in range(sw * sh)])
        # Sweep every UInt16 source value through a fractional-ratio case
        # containing SIMD lanes and a scalar tail; constants catch signed shifts.
        for base in range(0, 65536, 256):
            values = [base + i for i in range(256)]
            self.check_scale(16, 16, 19, 17, values)
        for value in (0, 1, 1022, 1023, 1024, 32767, 32768, 65534, 65535):
            for dw in (11, 4096, 4097):
                self.check_scale(18, 6, dw, 5, [value] * 108)
        self.check_scale(18, 6, 11, 5, [0, 65535] * 54)

    def test_whole_module_has_zero_clang_warnings(self):
        for arch, target in (("x86_64", "x86_64-pc-linux-gnu"),
                             ("arm64", "aarch64-unknown-linux-gnu")):
            result = subprocess.run(
                [self.clang, "-Werror", "-target", target, "-O3", "-c",
                 str(ROOT / f"c/leanav_lnir_{arch}.ll"),
                 "-o", str(self.directory / f"whole-{arch}.o")],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")

    def test_both_stats_vector_paths_and_tails(self):
        rng = random.Random(1202)
        sizes = list(range(130)) + [4095, 4096, 4097, 65535, 65536, 65537]
        for bits, fn in ((8, self.stats8), (16, self.stats)):
            cap = (1 << bits) - 1
            for n in sizes:
                patterns = ([cap] * n, [0, cap] * (n // 2) + [cap] * (n % 2),
                            [rng.randrange(cap + 1) for _ in range(n)])
                for values in patterns:
                    raw = b"".join(v.to_bytes(bits // 8, "little") for v in values)
                    src = ctypes.create_string_buffer(b"S" + raw + b"S")
                    for step in (0, 1, 2, 3, 15, 16, 17, 63, 64, n + 1, 2**64 - 1):
                        sampled = values[::step] if step else []
                        if bits == 16:
                            sampled = [v >> 2 for v in sampled]
                        count = len(sampled)
                        mean = sum(sampled) // count if count else 0
                        var = max(0, sum(v*v for v in sampled) // count - mean*mean) if count else 0
                        self.assertEqual(fn(ctypes.byref(src, 1), n, step),
                                         (var << 32) | mean, (bits, n, step))
                    self.assertEqual(src.raw[:-1], b"S" + raw + b"S")
            self.assertEqual(fn(None, 0, 1), 0)
            self.assertEqual(fn(None, 10, 0), 0)

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

    def check_acceptance(self, sw, sh, dw, dh, src_values, dst_values):
        src8 = bytes((v >> 2) & 255 for v in src_values)
        dst8 = bytes((v >> 2) & 255 for v in dst_values)
        raw_s = b"".join(v.to_bytes(2, "little") for v in src_values)
        raw_d = b"".join(v.to_bytes(2, "little") for v in dst_values)
        # Offset one byte deliberately exercises unaligned i16 loads.
        src = ctypes.create_string_buffer(b"S" + raw_s + b"S")
        dst = ctypes.create_string_buffer(b"D" + raw_d + b"D")
        out = (ctypes.c_uint64 * 6)(123, 99, 99, 99, 99, 456)
        ref = (ctypes.c_uint64 * 4)()
        self.accept(ctypes.byref(src, 1), sw, sh, ctypes.byref(dst, 1), dw, dh,
                    ctypes.byref(out, 8))
        self.accept8(src8, sw, sh, dst8, dw, dh, ref)
        # Independent block-grid oracle, including rounding AFTER per-pixel masking.
        expected = [0, 0, 0, 1]
        for by in range(0, dh - 15, 64 if dh >= 256 else 16):
            for bx in range(0, dw - 15, 64 if dw >= 256 else 16):
                sad = sse = black = refsum = 0
                for y in range(by, by + 16):
                    for x in range(bx, bx + 16):
                        if (sw, sh) == (dw, dh):
                            r = src8[y * sw + x]
                        else:
                            r = (sum(src8[(2*y+yy)*sw+2*x+xx]
                                     for yy in range(2) for xx in range(2)) + 2) >> 2
                        ad = abs(dst8[y * dw + x] - r)
                        sad += ad
                        sse += ad * ad
                        black += abs(r - 16)
                        refsum += r
                expected[0] = max(expected[0], sad)
                expected[1] += sse
                expected[2] += 256
                if refsum >= 24 * 256 and sad >= black:
                    expected[3] = 0
        self.assertEqual(list(out), [123] + expected + [456], (sw, sh, dw, dh))
        self.assertEqual(list(ref), expected)
        self.assertEqual(src.raw[:-1], b"S" + raw_s + b"S")
        self.assertEqual(dst.raw[:-1], b"D" + raw_d + b"D")

    def test_acceptance_grid_full_range_and_black_threshold(self):
        rng = random.Random(20261028)
        for dw, dh in [(0, 0), (1, 1), (15, 19), (16, 16), (17, 19), (31, 33),
                       (32, 48), (255, 257), (256, 256), (257, 259), (513, 263)]:
            for k in (1, 2):
                sw, sh = k * dw, k * dh
                src = [rng.randrange(65536) for _ in range(sw * sh)]
                dst = [rng.randrange(65536) for _ in range(dw * dh)]
                self.check_acceptance(sw, sh, dw, dh, src, dst)
                if k == 1:
                    self.check_acceptance(sw, sh, dw, dh, src, src)
        # Exhaust every UInt16 in both same-size and averaged source loads.
        for base in range(0, 65536, 256):
            src = list(range(base, base + 256))
            self.check_acceptance(16, 16, 16, 16, src, list(reversed(src)))
        for base in range(0, 65536, 1024):
            src = list(range(base, base + 1024))
            self.check_acceptance(32, 32, 16, 16, src, src[:256])
        for s in (0, 63, 64, 95, 96, 1023, 1024, 65535):
            for d in (0, 64, s, 65535):
                self.check_acceptance(32, 32, 16, 16, [s]*1024, [d]*256)
