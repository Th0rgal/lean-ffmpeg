import json
import math
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG") or shutil.which("ffmpeg") or "/usr/bin/ffmpeg"
STRACE = shutil.which("strace")
ISO_ENV = {"PATH": "/nonexistent"}


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


def psnr_db(ref_bytes, got_bytes):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    mse = sum((a - b) * (a - b) for a, b in zip(ref_bytes, got_bytes)) / len(ref_bytes)
    if mse == 0.0:
        return 99.0
    return 10.0 * math.log10((255.0 * 255.0) / mse)


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
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _ffmpeg_decode_yuv420p(self, in_path):
        out_yuv = self.dir / f"{Path(in_path).name}.ff.yuv"
        run(FFMPEG, "-y", "-v", "error", "-i", in_path, "-f", "rawvideo", "-pix_fmt", "yuv420p", out_yuv)
        return out_yuv.read_bytes()

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
        src_yuv.write_bytes(synth_yuv420p(64, 48, 1))
        for tag, pix_fmt in (("main10.265", "yuv420p10le"), ("main444.265", "yuv444p")):
            neg_path = self.dir / tag
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
                "-i", src_yuv,
                "-c:v", "libx265", "-pix_fmt", pix_fmt,
                "-x265-params", "log-level=none", "-f", "hevc", neg_path,
            )
            self.assertNotEqual(run(*decode_args(neg_path, "-"), env=ISO_ENV, check=False).returncode, 0)
            self.assertNotEqual(run(LFFMPEG, "hevc-probe", neg_path, env=ISO_ENV, check=False).returncode, 0)

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
