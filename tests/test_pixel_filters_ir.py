"""Exercise the checked-in LLVM filter independently, including unaligned/in-place buffers."""
import ctypes
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class PixelFiltersIR(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        clang = shutil.which("clang-18")
        if not clang:
            raise unittest.SkipTest("clang-18 unavailable")
        cls.tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        directory = Path(cls.tmp.name)
        kernels = []
        callees = []
        callee_names = ("lnir_px_y_studio_clamp_u8", "lnir_px_bt2020_to_bt709_uv_u8")
        for arch in ("x86_64", "arm64"):
            text = (ROOT / "c" / f"leanav_lnir_{arch}.ll").read_text()
            matches = re.findall(
                r"^define[^\n]*@lean_native_apply_filters_yuv420p_u8\([^\n]*\n.*?^}",
                text, re.M | re.S)
            if len(matches) != 1:
                raise AssertionError("exactly one packed filter definition required")
            for cname in callee_names:
                if f"@{cname}(" not in matches[0]:
                    raise AssertionError(f"{arch}: filter shell must call @{cname}")
            kernels.append(matches[0])
            cdefs = []
            for cname in callee_names:
                cm = re.findall(r"^define dso_local i64 @" + cname + r"\([^\n]*\n.*?^}", text, re.M | re.S)
                if len(cm) != 1:
                    raise AssertionError(f"{arch}: missing @{cname}")
                cdefs.append(cm[0])
            callees.append("\n\n".join(cdefs))
        if kernels[0] != kernels[1]:
            raise AssertionError("architecture filter implementations differ")
        if callees[0] != callees[1]:
            raise AssertionError("architecture filter @lnir_px_* callees differ")
        ir = directory / "filters.ll"
        host = subprocess.check_output([clang, "-dumpmachine"], text=True).strip()
        body = re.sub(r" #[0-9]+ \{", " {", kernels[0] + "\n\n" + callees[0])
        ir.write_text(f'target triple = "{host}"\n'
                      "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)\n\n"
                      + body + "\n")
        so = directory / "filters.so"
        subprocess.run([clang, "-Werror", "-O3", "-shared", "-fPIC", str(ir), "-o", str(so)],
                       check=True, capture_output=True)
        arm_ir = directory / "filters-arm.ll"
        arm_ir.write_text(ir.read_text().replace(host, "aarch64-unknown-linux-gnu"))
        subprocess.run([clang, "-Werror", "-target", "aarch64-unknown-linux-gnu", "-O3", "-c", str(arm_ir),
                        "-o", str(directory / "filters-arm.o")], check=True, capture_output=True)
        cls.lib = ctypes.CDLL(str(so))
        cls.kernel = cls.lib.lean_native_apply_filters_yuv420p_u8
        cls.kernel.argtypes = [ctypes.c_void_p, ctypes.c_void_p,
                               ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64]
        cls.kernel.restype = None

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def check_frame(self, y, u, v, flags, inplace=False):
        src = bytes(y + u + v)
        def clip(n):
            return max(0, min(255, n))
        expected_y = bytes(max(16, min(235, b)) if flags & 2 else b for b in y)
        expected_u = bytes(clip(128 + ((1004 * (a - 128) - 74 * (b - 128) + 512) >> 10))
                           if flags & 1 else a for a, b in zip(u, v))
        expected_v = bytes(clip(128 + ((-42 * (a - 128) + 986 * (b - 128) + 512) >> 10))
                           if flags & 1 else b for a, b in zip(u, v))
        array = ctypes.c_ubyte * (len(src) + 34)
        sb = array(*([0xA5] * 17 + list(src) + [0xA5] * 17))
        db = sb if inplace else array(*([0xA5] * (len(src) + 34)))
        self.kernel(ctypes.byref(sb, 17), ctypes.byref(db, 17), len(y), len(u), flags)
        self.assertEqual(bytes(db)[17:-17], expected_y + expected_u + expected_v)
        sentinel = 0xA5
        self.assertEqual(bytes(db)[:17] + bytes(db)[-17:], bytes([sentinel] * 34))
        if not inplace:
            self.assertEqual(bytes(sb)[17:-17], src)

    def test_all_pairs_and_luma(self):
        u = [i // 256 for i in range(65536)]
        v = [i % 256 for i in range(65536)]
        for flags in (0, 1, 2, 3, 8, 9, 10, 11, 0xFFFFFFFFFFFFFFFC, 0xFFFFFFFFFFFFFFFF):
            for inplace in (False, True):
                with self.subTest(flags=flags, inplace=inplace):
                    self.check_frame(list(range(256)), u, v, flags, inplace)

    def test_tails_and_alias(self):
        for n in (0, 1, 15, 16, 17, 31, 32, 33, 255):
            for flags in (0, 1, 2, 3, 8, 9, 10, 11):
                for inplace in (False, True):
                    self.check_frame([(i * 71) % 256 for i in range(n)],
                                     [(i * 131) % 256 for i in range(n)],
                                     [(255 - i * 17) % 256 for i in range(n)], flags, inplace)

    def test_independent_plane_lengths(self):
        for yn, cn in ((0, 17), (17, 0), (1, 33), (33, 1), (16, 31), (31, 16)):
            for flags in (0, 1, 2, 3, 8, 9, 10, 11):
                for inplace in (False, True):
                    with self.subTest(y_len=yn, uv_len=cn, flags=flags, inplace=inplace):
                        self.check_frame([(i * 71) % 256 for i in range(yn)],
                                         [(i * 131) % 256 for i in range(cn)],
                                         [(255 - i * 17) % 256 for i in range(cn)],
                                         flags, inplace)
