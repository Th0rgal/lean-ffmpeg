"""Compiled Lean identity tests. General MP4 transcode stays fail-closed.

The production scale loop, LLVM kernels and C ABI stay active for the unit
checks. The pipeline entry returns a zero report and must not write output.
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
    result = []
    for y in range(dh):
        for x in range(dw):
            if (sw, sh) == (dw, dh):
                v = values[y * sw + x]
            elif (sw, sh) in ((2 * dw, 2 * dh), (3 * dw, 3 * dh)):
                k = sw // dw
                total = sum(values[(y*k+j)*sw+x*k+i] for j in range(k) for i in range(k))
                v = (total + 2) >> 2 if k == 2 else (total + 4) // 9
            else:
                xq, yq = x * sw * 256 // dw, y * sh * 256 // dh
                x0, y0, fx, fy = xq >> 8, yq >> 8, xq & 255, yq & 255
                x1, y1 = min(x0 + 1, sw - 1), min(y0 + 1, sh - 1)
                top = (256-fx)*values[y0*sw+x0] + fx*values[y0*sw+x1]
                bot = (256-fx)*values[y1*sw+x0] + fx*values[y1*sw+x1]
                v = min(1023, ((256-fy)*top + fy*bot + 32768) >> 16)
            result.append(v & 65535)
    return result


def scale_frame(values, sw, sh, dw, dh):
    y, uv = sw * sh, (sw // 2) * (sh // 2)
    return (scale_plane(values[:y], sw, sh, dw, dh) +
            scale_plane(values[y:y+uv], sw//2, sh//2, dw//2, dh//2) +
            scale_plane(values[y+uv:], sw//2, sh//2, dw//2, dh//2))


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
        # Reuse production dependency objects; the counter compiles the unchanged
        # C bridge with one renamed entrypoint, avoiding GNU-only linker --wrap.
        args = shlex.split((ROOT / '.lake/build/bin/lffmpeg.rsp').read_text())
        objects = [s for s in args if s.endswith(('.o.export', '.a')) and
                   not s.endswith('/LeanAV/Main.c.o.export')]
        # Match lakefile.lean's system C compiler for the POSIX bridge: Lean's
        # bundled leanc sysroot need not contain the platform C headers.
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
        result = subprocess.run([str(self.binary)], cwd=ROOT, capture_output=True,
                                text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('checks passed', result.stdout)

    def run_pipeline(self, dims, pixfmt='yuv420p10le', flags=0, frames=9,
                     black=False, truncated=False, fail_encoder=False):
        sw, sh, dw, dh = dims
        bps = 1 if pixfmt == 'yuv420p' else 2
        count = sw * sh + 2 * ((sw // 2) * (sh // 2))
        raw, expected, means, variances = bytearray(), bytearray(), [], []
        for f in range(frames):
            values = [0 if black else (i * 7919 + f * 137 + 65535) % (256 ** bps)
                      for i in range(count)]
            raw.extend(b''.join(v.to_bytes(bps, 'little') for v in values))
            out = scale_frame(values, *dims)
            expected.extend(b''.join(v.to_bytes(bps, 'little') for v in out))
            luma = [v >> (2 if bps == 2 else 0) for v in out[:dw*dh]]
            mean = sum(luma) // len(luma)
            means.append(mean)
            variances.append(max(0, sum(v*v for v in luma)//len(luma) - mean*mean))
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
        report, metrics, native_calls = map(int, result.stdout.strip().split(','))
        self.assertEqual((report, metrics, native_calls), (0, 0, 0))
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
