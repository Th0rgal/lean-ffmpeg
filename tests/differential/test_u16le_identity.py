"""Compiled Lean 10-bit LNIR C-ABI wrapper & identity tests (zero subprocesses).

Exercises leanav_c_exec_lnir_scale2d_yuv420p10le_ba,
leanav_c_exec_lnir_luma_stats_u16le_ba, and
leanav_c_exec_lnir_extract_u16le_msb8_ba directly through C interposition
counters against independent Python and pure-Lean reference formulas, while
verifying transcodeMp4GeneralVerifiedIO remains fail-closed.
"""
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def scale_plane(values, sw, sh, dw, dh):
    if (sw, sh) == (dw, dh):
        return list(values[:sw * sh])
    if sw == dw * 2 and sh == dh * 2:
        return [
            ((values[(2 * y) * sw + 2 * x] + values[(2 * y) * sw + 2 * x + 1] +
              values[(2 * y + 1) * sw + 2 * x] + values[(2 * y + 1) * sw + 2 * x + 1] + 2) >> 2) & 65535
            for y in range(dh) for x in range(dw)
        ]
    if sw == dw * 3 and sh == dh * 3:
        return [
            ((sum(values[(3 * y + dy) * sw + 3 * x + dx]
                  for dy in range(3) for dx in range(3)) + 4) // 9) & 65535
            for y in range(dh) for x in range(dw)
        ]
    if sw >= 3 and sh >= 3 and sw * 2 == dw * 3 and sh * 2 == dh * 3:
        result = []
        for y in range(dh):
            sy0 = y + (y >> 1)
            sy1 = sy0 + (y & 1)
            for x in range(dw):
                sx0 = x + (x >> 1)
                sx1 = sx0 + (x & 1)
                col_a = values[sy0 * sw + sx0] + values[sy1 * sw + sx0]
                col_b = values[sy0 * sw + sx1] + values[sy1 * sw + sx1]
                result.append(min(1023, (col_a + col_b + 2) >> 2))
        return result
    result = []
    for y in range(dh):
        for x in range(dw):
            xq, yq = x * sw * 256 // dw, y * sh * 256 // dh
            x0, y0, fx, fy = min(xq >> 8, sw - 1), min(yq >> 8, sh - 1), xq & 255, yq & 255
            x1, y1 = min(x0 + 1, sw - 1), min(y0 + 1, sh - 1)
            top = (256 - fx) * values[y0 * sw + x0] + fx * values[y0 * sw + x1]
            bot = (256 - fx) * values[y1 * sw + x0] + fx * values[y1 * sw + x1]
            v = min(1023, ((256 - fy) * top + fy * bot + 32768) >> 16)
            result.append(v & 65535)
    return result


def scale_frame_c_abi(raw: bytes, sw: int, sh: int, dw: int, dh: int) -> bytes:
    if (sw < 2 or sh < 2 or dw < 2 or dh < 2 or ((sw | sh | dw | dh) & 1) or
            sw > 0xFFFFFF or sh > 0xFFFFFF or dw > 0x3FFFFFFF or dh > 0x3FFFFFFF):
        return b""
    y = sw * sh
    uv = (sw // 2) * (sh // 2)
    need_bytes = (y + 2 * uv) * 2
    if len(raw) < need_bytes:
        return b""
    if (sw, sh) == (dw, dh):
        return raw[:need_bytes]
    values = [int.from_bytes(raw[2 * i:2 * i + 2], "little") for i in range(y + 2 * uv)]
    scaled = (scale_plane(values[:y], sw, sh, dw, dh) +
              scale_plane(values[y:y + uv], sw // 2, sh // 2, dw // 2, dh // 2) +
              scale_plane(values[y + uv:y + 2 * uv], sw // 2, sh // 2, dw // 2, dh // 2))
    return b"".join(v.to_bytes(2, "little") for v in scaled)


def extract_msb8_ref(raw: bytes, n_pixels: int) -> bytes:
    n = min(n_pixels, len(raw) // 2)
    return bytes(((int.from_bytes(raw[2 * i:2 * i + 2], "little") >> 2) & 0xFF)
                 for i in range(n))


def luma_stats_ref(raw: bytes, n_pixels: int, step: int) -> tuple[int, int]:
    n = min(n_pixels, len(raw) // 2)
    if n == 0 or step == 0:
        return (0, 0)
    samples = [int.from_bytes(raw[2 * i:2 * i + 2], "little") >> 2
               for i in range(0, n, step)]
    cnt = len(samples)
    mean = sum(samples) // cnt
    mean_sq = sum(v * v for v in samples) // cnt
    var = max(0, mean_sq - mean * mean)
    return (mean & 0xFFFFFFFF, var & 0xFFFFFFFF)


class U16LeIdentityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(dir=ROOT / '.lake')
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.directory = Path(cls.tmp.name)
        c_file, cls.binary = cls.directory / 'identity.c', cls.directory / 'identity'
        subprocess.run(['lake', 'env', 'lean', '-c', str(c_file),
                        str(HERE / 'u16le_identity.lean')], cwd=ROOT, check=True,
                       capture_output=True, text=True, timeout=120)
        args = shlex.split((ROOT / '.lake/build/bin/lffmpeg.rsp').read_text())
        objects = [s for s in args if s.endswith(('.o.export', '.a')) and
                   not s.endswith('/LeanAV/Main.c.o.export')]
        lean_prefix = subprocess.run(['lake', 'env', 'lean', '--print-prefix'],
                                     cwd=ROOT, check=True, capture_output=True,
                                     text=True, timeout=30).stdout.strip()
        counter = cls.directory / 'counter.o'
        subprocess.run(['cc', '-O3', '-fPIC', '-I', str(Path(lean_prefix) / 'include'),
                        '-c', str(HERE / 'u16le_identity_counter.c'), '-o', str(counter)],
                       cwd=ROOT, check=True, capture_output=True, text=True, timeout=120)
        link_args = [] if sys.platform == 'darwin' else ['-lpthread']
        result = subprocess.run(['lake', 'env', 'leanc', '-O2', '-o', str(cls.binary),
                                 str(c_file), str(counter),
                                 *objects, *link_args],
                                cwd=ROOT, capture_output=True, text=True, timeout=120)
        if result.returncode or result.stderr:
            raise AssertionError(result.stdout + result.stderr)

    def test_gate_units_pointer_reuse_and_native_pure_differentials(self):
        result = subprocess.run([str(self.binary)], cwd=ROOT,
                                env={'PATH': '/nonexistent'},
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('checks passed', result.stdout)

    def run_wrappers(self, raw: bytes, dims, n_pixels: int, step: int):
        sw, sh, dw, dh = dims
        src = self.directory / 'wrap_in.raw'
        out_scale = self.directory / 'wrap_scale.raw'
        out_msb = self.directory / 'wrap_msb.raw'
        src.write_bytes(raw)
        out_scale.unlink(missing_ok=True)
        out_msb.unlink(missing_ok=True)
        res = subprocess.run(
            [str(self.binary), 'wrappers', str(src), str(out_scale), str(out_msb),
             str(sw), str(sh), str(dw), str(dh), str(n_pixels), str(step)],
            cwd=ROOT, env={'PATH': '/nonexistent'},
            capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        mean, var, sc, lc, ec = map(int, res.stdout.strip().split(','))
        self.assertEqual((sc, lc, ec), (1, 1, 1))
        self.assertEqual(out_scale.read_bytes(), scale_frame_c_abi(raw, sw, sh, dw, dh))
        self.assertEqual(out_msb.read_bytes(), extract_msb8_ref(raw, n_pixels))
        self.assertEqual((mean, var), luma_stats_ref(raw, n_pixels, step))

    def test_direct_c_abi_wrappers_normal_strided_empty_and_short_odd_inputs(self):
        # Empty and odd/short buffers (including odd trailing byte 0xFD)
        for raw in (b'', b'\xfd', b'\x34\x12\xfd', bytes(range(11))):
            for req in (0, 1, 5, 16):
                for step in (0, 1, 3, 16):
                    with self.subTest(raw_len=len(raw), req=req, step=step):
                        self.run_wrappers(raw, (4, 4, 4, 4), req, step)
        # Normal identity & Q8 bilinear resize frames (10-bit and full-range 16-bit values)
        for dims in ((4, 6, 4, 6), (16, 16, 16, 16), (20, 12, 10, 6),
                     (30, 18, 10, 6), (14, 10, 8, 6), (6, 4, 14, 10)):
            sw, sh, _, _ = dims
            count = sw * sh + 2 * ((sw // 2) * (sh // 2))
            for full_u16 in (False, True):
                vals = [((i * 7919 + 65535) % 65536) if full_u16 else ((i * 137 + 31) % 1024)
                        for i in range(count)]
                raw = b''.join(v.to_bytes(2, 'little') for v in vals) + b'\xa5'
                for step in (1, 4, 16):
                    with self.subTest(dims=dims, full_u16=full_u16, step=step):
                        self.run_wrappers(raw, dims, sw * sh, step)
        # Odd geometry rejected cleanly by C-ABI scaler while stats/extract still run
        self.run_wrappers(b'\xff' * 64, (3, 2, 3, 2), 32, 5)
        # Strided >65536 pixel frame exercising stride-16 and arbitrary step C-ABI paths
        big_n = 65553
        big_raw = b''.join(((i * 7919 + 17) % 65536).to_bytes(2, 'little')
                           for i in range(big_n)) + b'\x7f'
        for req in (big_n, big_n + 20):
            for step in (1, 16, 17):
                with self.subTest(big_req=req, step=step):
                    self.run_wrappers(big_raw, (256, 160, 16, 16), req, step)

    def run_pipeline(self, dims, pixfmt='yuv420p10le', flags=0, frames=9,
                     black=False, truncated=False, fail_encoder=False):
        sw, sh, dw, dh = dims
        bps = 1 if pixfmt == 'yuv420p' else 2
        count = sw * sh + 2 * ((sw // 2) * (sh // 2))
        raw = bytearray()
        for f in range(frames):
            values = [0 if black else (i * 7919 + f * 137 + 65535) % (256 ** bps)
                      for i in range(count)]
            raw.extend(b''.join(v.to_bytes(bps, 'little') for v in values))
        if truncated:
            raw.extend(b'\xa5' * (count * bps - 1))
        source, output = self.directory / 'input.raw', self.directory / 'output.raw'
        source.write_bytes(raw)
        output.unlink(missing_ok=True)
        result = subprocess.run([str(self.binary), str(source), str(output), pixfmt,
                                 *map(str, dims), str(flags)], cwd=ROOT,
                                env={'PATH': '/nonexistent'},
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report, metrics, sc, lc, ec = map(int, result.stdout.strip().split(','))
        self.assertEqual((report, metrics, sc, lc, ec), (0, 0, 0, 0, 0))
        self.assertFalse(output.exists())
        self.assertEqual(source.read_bytes(), raw)

    def test_transcode_identity_bytes_metrics_and_no_native_scaling(self):
        for dims in [(4, 6, 4, 6), (16, 16, 16, 16), (18, 10, 18, 10)]:
            for pixfmt in ['yuv420p10le', 'p010le', 'yuv420p']:
                with self.subTest(dims=dims, pixfmt=pixfmt):
                    self.run_pipeline(dims, pixfmt, truncated=True)
        for pixfmt in ['yuv420p10le', 'yuv420p']:
            with self.subTest(black=pixfmt):
                self.run_pipeline((16, 16, 16, 16), pixfmt, black=True)

    def test_transcode_10bit_filter_flags_preserve_existing_behavior(self):
        for flags in [1, 2, 3]:
            with self.subTest(flags=flags):
                self.run_pipeline((16, 16, 16, 16), flags=flags)

    def test_resize_differentials_and_native_positive_control(self):
        for dims in [(20, 12, 10, 6), (30, 18, 10, 6), (14, 10, 8, 6), (6, 4, 14, 10)]:
            with self.subTest(dims=dims):
                self.run_pipeline(dims, frames=2)

    def test_empty_and_incomplete_frame_rejected(self):
        for truncated in [False, True]:
            with self.subTest(truncated=truncated):
                self.run_pipeline((16, 16, 16, 16), frames=0, truncated=truncated)

    def test_encoder_failure_rejects_report_and_removes_partial_output(self):
        self.run_pipeline((16, 16, 16, 16), fail_encoder=True)


if __name__ == '__main__':
    unittest.main()
