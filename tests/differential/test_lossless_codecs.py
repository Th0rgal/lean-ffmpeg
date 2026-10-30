import json
import math
import os
import shutil
import struct
import subprocess
import tempfile
import unittest
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG", shutil.which("ffmpeg") or "ffmpeg")
STRACE = shutil.which("strace")


def run(*args, **kwargs):
    return subprocess.run([str(a) for a in args], check=True, capture_output=True, **kwargs)


def ffmpeg_available():
    try:
        out = run(FFMPEG, "-version").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return out.startswith("ffmpeg version ")


def png_chunk(kind, payload):
    body = kind + payload
    return struct.pack(">I", len(payload)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)


def png_bytes(width, height, depth, color, rows, interlace=0, palette=None, trns=None, idat_split=None):
    ihdr = struct.pack(">IIBBBBB", width, height, depth, color, 0, 0, interlace)
    out = b"\x89PNG\r\n\x1a\n" + png_chunk(b"IHDR", ihdr)
    if palette is not None:
        out += png_chunk(b"PLTE", palette)
    if trns is not None:
        out += png_chunk(b"tRNS", trns)
    comp = zlib.compress(rows, 9)
    if idat_split is None or idat_split <= 0:
        out += png_chunk(b"IDAT", comp)
    else:
        for off in range(0, len(comp), idat_split):
            out += png_chunk(b"IDAT", comp[off:off + idat_split])
    out += png_chunk(b"IEND", b"")
    return out


def filtered_rows(pixels, width, height, bpp, filters):
    stride = len(pixels) // height
    out = bytearray()
    prev = bytes(stride)
    for y in range(height):
        row = pixels[y * stride:(y + 1) * stride]
        kind = filters[y % len(filters)]
        out.append(kind)
        for i, x in enumerate(row):
            a = row[i - bpp] if i >= bpp else 0
            b = prev[i]
            c = prev[i - bpp] if i >= bpp else 0
            if kind == 0:
                pred = 0
            elif kind == 1:
                pred = a
            elif kind == 2:
                pred = b
            elif kind == 3:
                pred = (a + b) // 2
            else:
                p = a + b - c
                pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
                pred = a if pa <= pb and pa <= pc else b if pb <= pc else c
            out.append((x - pred) & 255)
        prev = row
    return bytes(out)


def pack_s24le(samples):
    out = bytearray()
    for s in samples:
        v = s & 0xFFFFFF
        out.extend((v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF))
    return bytes(out)


@unittest.skipUnless(LFFMPEG.exists(), "lffmpeg is not built")
class LosslessCodecTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, data):
        path = self.dir / name
        path.write_bytes(data)
        return path

    def test_zlib_roundtrip_and_multiblock_interop(self):
        samples = [
            b"",
            b"a",
            bytes(range(256)) * 7,
            os.urandom(4097),
            b"abc" * 1000,
            bytes((i * 73 + (i >> 8) * 19) & 255 for i in range(70000)),
        ]
        for index, data in enumerate(samples):
            source = self.write(f"in{index}", data)
            reference = self.write(f"ref{index}.z", zlib.compress(data, 9))
            decoded = self.dir / f"dec{index}"
            run(LFFMPEG, "lossless-codec", "zlib-decode", reference, decoded)
            self.assertEqual(decoded.read_bytes(), data)
            for mode in ("stored", "fixed", "dynamic"):
                encoded = self.dir / f"{mode}{index}.z"
                run(LFFMPEG, "lossless-codec", "zlib-encode", mode, source, encoded)
                self.assertEqual(zlib.decompress(encoded.read_bytes()), data)
                again = self.dir / f"again{mode}{index}"
                run(LFFMPEG, "lossless-codec", "zlib-decode", encoded, again)
                self.assertEqual(again.read_bytes(), data)

    def test_zlib_rejects_bad_checksum_header_and_trailing_data(self):
        good = bytearray(zlib.compress(b"lean-ffmpeg"))
        bad_adler = bytearray(good)
        bad_adler[-1] ^= 1
        bad_hdr = bytearray(good)
        bad_hdr[0] = 0x79
        for name, data in (("bad.z", bad_adler), ("hdr.z", bad_hdr), ("tail.z", good + b"x")):
            result = subprocess.run(
                [str(LFFMPEG), "lossless-codec", "zlib-decode", str(self.write(name, bytes(data))), str(self.dir / "out")],
                capture_output=True,
            )
            self.assertNotEqual(result.returncode, 0)

    def test_png_decoder_all_filters_multi_idat_and_corrupt_rejection(self):
        cases = []
        width, height = 13, 9
        rgba = bytes((x * 17 + y * 31 + c * 7) & 255 for y in range(height) for x in range(width) for c in range(4))
        cases.append((8, 6, 4, rgba, None, None))
        rgb16 = bytes((x * 3 + y * 11 + c) & 255 for y in range(height) for x in range(width) for c in range(6))
        cases.append((16, 2, 6, rgb16, None, None))
        gray2 = bytes(((y * 5 + x) * 37) & 255 for y in range(height) for x in range((width * 2 + 7) // 8))
        cases.append((2, 0, 1, gray2, None, None))
        pal = bytes(range(48))
        trns = bytes([255, 128, 64, 0])
        idx4 = bytes(((y + x) * 19) & 255 for y in range(height) for x in range((width * 4 + 7) // 8))
        cases.append((4, 3, 1, idx4, pal, trns))
        for depth, color, bpp, pixels, palette, trns_data in cases:
            png_data = png_bytes(
                width,
                height,
                depth,
                color,
                filtered_rows(pixels, width, height, bpp, [0, 1, 2, 3, 4]),
                palette=palette,
                trns=trns_data,
                idat_split=19,
            )
            png = self.write(f"case{depth}{color}.png", png_data)
            out = self.dir / "pixels"
            run(LFFMPEG, "lossless-codec", "png-decode", png, out)
            self.assertEqual(out.read_bytes(), pixels)

        bad_crc = bytearray(png_data)
        bad_crc[-15] ^= 0x40
        res = subprocess.run(
            [str(LFFMPEG), "-y", "-i", str(self.write("corrupt.png", bytes(bad_crc))), "-f", "rawvideo", "-pix_fmt", "rgba", str(self.dir / "bad.raw")],
            capture_output=True,
        )
        self.assertNotEqual(res.returncode, 0)

    def test_png_adam7_decode_and_cli_rgba(self):
        width, height = 11, 10
        image = [[(x * 23 + y * 7) & 255 for x in range(width)] for y in range(height)]
        raw = bytearray()
        starts = [(0, 0, 8, 8), (4, 0, 8, 8), (0, 4, 4, 8), (2, 0, 4, 4), (0, 2, 2, 4), (1, 0, 2, 2), (0, 1, 1, 2)]
        for sx, sy, dx, dy in starts:
            xs = list(range(sx, width, dx))
            ys = list(range(sy, height, dy))
            if xs and ys:
                for y in ys:
                    raw.append(0)
                    raw.extend(image[y][x] for x in xs)
        png = self.write("adam7.png", png_bytes(width, height, 8, 0, bytes(raw), interlace=1))
        out = self.dir / "adam7.gray"
        run(LFFMPEG, "lossless-codec", "png-decode", png, out)
        expected_gray = bytes(v for row in image for v in row)
        self.assertEqual(out.read_bytes(), expected_gray)

        cli_gray = self.dir / "cli_adam7.gray"
        run(LFFMPEG, "-y", "-i", png, "-f", "rawvideo", "-pix_fmt", "gray", cli_gray)
        self.assertEqual(cli_gray.read_bytes(), expected_gray)

    def test_planir_standalone_tier_and_delegated_boundaries(self):
        png_plan = json.loads(run(LFFMPEG, "-dump-plan", "-i", "in.png", "out.png").stdout.decode())
        self.assertEqual(png_plan["backend"]["tier"], "independent_verified")
        self.assertFalse(png_plan["backend"]["delegated_container"])

        flac_plan = json.loads(run(LFFMPEG, "-dump-plan", "-i", "in.flac", "out.wav").stdout.decode())
        self.assertEqual(flac_plan["backend"]["tier"], "independent_verified")
        self.assertFalse(flac_plan["backend"]["delegated_container"])

        raw_png_plan = json.loads(
            run(LFFMPEG, "-dump-plan", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", "8x8", "-i", "in.raw", "out.png").stdout.decode()
        )
        self.assertEqual(raw_png_plan["backend"]["tier"], "independent_verified")
        self.assertFalse(raw_png_plan["backend"]["delegated_container"])

        af_flac_plan = json.loads(run(LFFMPEG, "-dump-plan", "-i", "in.flac", "-af", "hdcd", "-f", "s24le", "out.pcm").stdout.decode())
        self.assertEqual(af_flac_plan["backend"]["tier"], "delegated_faithful")
        self.assertTrue(af_flac_plan["backend"]["delegated_container"])

        mp4_plan = json.loads(run(LFFMPEG, "-dump-plan", "-i", "in.mp4", "-c", "copy", "out.mp4").stdout.decode())
        self.assertEqual(mp4_plan["backend"]["tier"], "independent_verified")
        self.assertIn("native_stream_copy", mp4_plan["backend"]["reasons"])

        cross_plan = json.loads(run(LFFMPEG, "-dump-plan", "-i", "in.mp4", "-c", "copy", "out.mkv").stdout.decode())
        self.assertEqual(cross_plan["backend"]["tier"], "delegated_faithful")

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_png_cli_and_ffmpeg_differential_all_pix_fmts(self):
        width, height = 17, 11
        pix_cases = [
            ("gray", 1),
            ("ya8", 2),
            ("rgb24", 3),
            ("rgba", 4),
            ("gray16be", 2),
            ("ya16be", 4),
            ("rgb48be", 6),
            ("rgba64be", 8),
        ]
        for pix_fmt, bpp in pix_cases:
            raw_bytes = bytes(((i * 37 + (i >> 4) * 13 + bpp * 7) & 255) for i in range(width * height * bpp))
            raw_in = self.write(f"in_{pix_fmt}.raw", raw_bytes)
            lean_png = self.dir / f"lean_{pix_fmt}.png"
            res = run(
                LFFMPEG, "-y", "-json",
                "-f", "rawvideo", "-pix_fmt", pix_fmt, "-s", f"{width}x{height}",
                "-i", raw_in, lean_png,
            )
            meta = json.loads(res.stdout.decode().strip().splitlines()[-1])
            self.assertEqual(meta["tier"], "independent_verified")
            self.assertEqual(meta["codec"], "png")

            ff_raw = self.dir / f"ff_{pix_fmt}.raw"
            run(FFMPEG, "-y", "-v", "error", "-i", lean_png, "-f", "rawvideo", "-pix_fmt", pix_fmt, ff_raw)
            self.assertEqual(ff_raw.read_bytes(), raw_bytes, f"FFmpeg decode mismatch for {pix_fmt}")

            ff_png = self.dir / f"ff_{pix_fmt}.png"
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", pix_fmt, "-s", f"{width}x{height}",
                "-i", raw_in, "-frames:v", "1", "-pred", "mixed", ff_png,
            )
            lean_raw = self.dir / f"lean_from_ff_{pix_fmt}.raw"
            run(LFFMPEG, "-y", "-i", ff_png, "-f", "rawvideo", "-pix_fmt", pix_fmt, lean_raw)
            self.assertEqual(lean_raw.read_bytes(), raw_bytes, f"Lean decode mismatch for {pix_fmt}")

            reenc_png = self.dir / f"reenc_{pix_fmt}.png"
            run(LFFMPEG, "-y", "-i", ff_png, reenc_png)
            reenc_raw = self.dir / f"reenc_{pix_fmt}.raw"
            run(FFMPEG, "-y", "-v", "error", "-i", reenc_png, "-f", "rawvideo", "-pix_fmt", pix_fmt, reenc_raw)
            self.assertEqual(reenc_raw.read_bytes(), raw_bytes, f"PNG->PNG re-encode mismatch for {pix_fmt}")

        no_overwrite = subprocess.run([str(LFFMPEG), "-n", "-i", str(lean_png), str(reenc_png)], capture_output=True)
        self.assertNotEqual(no_overwrite.returncode, 0)

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_flac_cli_and_ffmpeg_differential_multiframe_and_depths(self):
        num_samples = 9500
        ch0 = [int(22000 * math.sin(i * 0.07) + 4000 * math.cos(i * 0.23)) for i in range(num_samples)]
        ch1 = [int(21000 * math.sin(i * 0.07 + 0.15) - 3500 * math.sin(i * 0.19)) for i in range(num_samples)]
        interleaved_s16 = bytearray()
        for l_s, r_s in zip(ch0, ch1):
            interleaved_s16 += struct.pack("<hh", l_s, r_s)
        pcm16_in = self.write("stereo16.pcm", bytes(interleaved_s16))

        lean_flac = self.dir / "lean_stereo16.flac"
        res = run(LFFMPEG, "-y", "-json", "-f", "s16le", "-ar", "48000", "-ac", "2", "-i", pcm16_in, lean_flac)
        meta = json.loads(res.stdout.decode().strip().splitlines()[-1])
        self.assertEqual(meta["tier"], "independent_verified")
        self.assertEqual(meta["codec"], "flac")
        self.assertEqual(meta["samples"], num_samples)

        run(FFMPEG, "-v", "error", "-i", lean_flac, "-f", "null", "-")
        ff_pcm16 = self.dir / "ff_from_lean16.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", lean_flac, "-f", "s16le", ff_pcm16)
        self.assertEqual(ff_pcm16.read_bytes(), bytes(interleaved_s16))

        for comp_level in ("0", "5", "8", "12"):
            ff_flac = self.dir / f"ff_lvl{comp_level}.flac"
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "s16le", "-ar", "48000", "-ac", "2", "-i", pcm16_in,
                "-compression_level", comp_level, ff_flac,
            )
            lean_pcm = self.dir / f"lean_lvl{comp_level}.pcm"
            run(LFFMPEG, "-y", "-i", ff_flac, "-f", "s16le", lean_pcm)
            self.assertEqual(lean_pcm.read_bytes(), bytes(interleaved_s16), f"FLAC decode mismatch at level {comp_level}")

        lean_wav = self.dir / "lean_out.wav"
        run(LFFMPEG, "-y", "-i", lean_flac, lean_wav)
        re_flac = self.dir / "from_wav.flac"
        run(LFFMPEG, "-y", "-i", lean_wav, re_flac)
        re_pcm = self.dir / "from_wav.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", re_flac, "-f", "s16le", re_pcm)
        self.assertEqual(re_pcm.read_bytes(), bytes(interleaved_s16))

        samples24 = []
        for i in range(5000):
            s0 = int(3_500_000 * math.sin(i * 0.05))
            s1 = 0 if 1200 <= i < 2500 else int(2_800_000 * math.cos(i * 0.11))
            samples24.extend((s0, s1))
        pcm24_bytes = pack_s24le(samples24)
        pcm24_in = self.write("stereo24.pcm", pcm24_bytes)
        lean_flac24 = self.dir / "lean24.flac"
        run(LFFMPEG, "-y", "-f", "s24le", "-ar", "96000", "-ac", "2", "-i", pcm24_in, lean_flac24)
        run(FFMPEG, "-v", "error", "-i", lean_flac24, "-f", "null", "-")
        ff_pcm24 = self.dir / "ff24.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", lean_flac24, "-f", "s24le", ff_pcm24)
        self.assertEqual(ff_pcm24.read_bytes(), pcm24_bytes)

        ff_flac24 = self.dir / "ff24.flac"
        run(FFMPEG, "-y", "-v", "error", "-f", "s24le", "-ar", "96000", "-ac", "2", "-i", pcm24_in, "-sample_fmt", "s32", ff_flac24)
        lean_pcm24 = self.dir / "lean24.pcm"
        run(LFFMPEG, "-y", "-i", ff_flac24, "-f", "s24le", lean_pcm24)
        self.assertEqual(lean_pcm24.read_bytes(), pcm24_bytes)

        ch6_bytes = bytearray()
        for i in range(2048):
            vals = [int(8000 * math.sin(i * 0.04 + c * 0.5)) for c in range(6)]
            ch6_bytes += struct.pack("<6h", *vals)
        pcm6_in = self.write("surround6.pcm", bytes(ch6_bytes))
        ff_flac6 = self.dir / "ff6.flac"
        run(FFMPEG, "-y", "-v", "error", "-f", "s16le", "-ar", "44100", "-ac", "6", "-i", pcm6_in, ff_flac6)
        lean_flac6 = self.dir / "lean6.flac"
        run(LFFMPEG, "-y", "-i", ff_flac6, lean_flac6)
        lean_pcm6 = self.dir / "lean6.pcm"
        run(LFFMPEG, "-y", "-i", lean_flac6, "-f", "s16le", lean_pcm6)
        self.assertEqual(lean_pcm6.read_bytes(), bytes(ch6_bytes))

        bad_md5 = bytearray(lean_flac.read_bytes())
        bad_md5[26] ^= 0x01
        bad_md5_path = self.write("bad_md5.flac", bytes(bad_md5))
        res_bad = subprocess.run([str(LFFMPEG), "-y", "-i", str(bad_md5_path), str(self.dir / "bad.wav")], capture_output=True)
        self.assertNotEqual(res_bad.returncode, 0)

    def test_zero_subprocess_isolation_path_and_strace(self):
        env_isolated = {"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"}
        width, height = 12, 8
        rgb = bytes((i * 29 + 11) & 255 for i in range(width * height * 3))
        raw_in = self.write("iso.rgb", rgb)
        png_out = self.dir / "iso.png"
        png_re = self.dir / "iso_re.png"
        raw_out = self.dir / "iso_out.rgb"

        run(LFFMPEG, "-y", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{width}x{height}", "-i", raw_in, png_out, env=env_isolated)
        run(LFFMPEG, "-y", "-i", png_out, png_re, env=env_isolated)
        run(LFFMPEG, "-y", "-i", png_re, "-f", "rawvideo", "-pix_fmt", "rgb24", raw_out, env=env_isolated)
        self.assertEqual(raw_out.read_bytes(), rgb)

        pcm = struct.pack("<512h", *[((i * 97) % 20000) - 10000 for i in range(512)])
        pcm_in = self.write("iso.pcm", pcm)
        flac_out = self.dir / "iso.flac"
        wav_out = self.dir / "iso.wav"
        flac_re = self.dir / "iso_re.flac"
        pcm_out = self.dir / "iso_out.pcm"

        run(LFFMPEG, "-y", "-f", "s16le", "-ar", "44100", "-ac", "2", "-i", pcm_in, flac_out, env=env_isolated)
        run(LFFMPEG, "-y", "-i", flac_out, wav_out, env=env_isolated)
        run(LFFMPEG, "-y", "-i", wav_out, flac_re, env=env_isolated)
        run(LFFMPEG, "-y", "-i", flac_re, "-f", "s16le", pcm_out, env=env_isolated)
        self.assertEqual(pcm_out.read_bytes(), pcm)

        if STRACE is not None:
            for cmd in (
                [STRACE, "-f", "-e", "trace=execve", str(LFFMPEG), "-y", "-i", str(png_out), str(self.dir / "strace.png")],
                [STRACE, "-f", "-e", "trace=execve", str(LFFMPEG), "-y", "-i", str(flac_out), str(self.dir / "strace.wav")],
            ):
                proc = run(*cmd, env=env_isolated)
                exec_lines = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if "execve(" in ln]
                self.assertEqual(len(exec_lines), 1, f"Expected exactly 1 execve (lffmpeg itself), got: {exec_lines}")
                self.assertIn("lffmpeg", exec_lines[0])

    def test_zlib_flevels_and_oversubscribed_huffman_rejection(self):
        payload = bytes((i * 53 + (i >> 3) * 17) & 255 for i in range(8192))
        for level in (0, 1, 5, 9):
            z_ref = self.write(f"lvl{level}.z", zlib.compress(payload, level))
            dec = self.dir / f"lvl{level}.raw"
            run(LFFMPEG, "lossless-codec", "zlib-decode", z_ref, dec)
            self.assertEqual(dec.read_bytes(), payload)

        # Oversubscribed dynamic Huffman stream (corrupted code-length header) must fail closed
        bad_dyn = bytearray(zlib.compress(b"abcd" * 512, 9))
        bad_dyn[2] = 0x05  # final=1, btype=2 (dynamic), all header bits mangled
        bad_dyn[3] = 0xFF
        bad_dyn[4] = 0xFF
        bad_dyn[5] = 0xFF
        res = subprocess.run(
            [str(LFFMPEG), "lossless-codec", "zlib-decode", str(self.write("oversub.z", bytes(bad_dyn))), str(self.dir / "bad_out")],
            capture_output=True,
        )
        self.assertNotEqual(res.returncode, 0)

    def test_png_strict_chunk_ordering_multiplicity_and_trns_rgb(self):
        w, h = 4, 3
        rgb8 = bytes([
            10, 20, 30,  40, 50, 60,  10, 20, 30,  255, 0, 128,
            0, 0, 0,     10, 20, 30,  7, 8, 9,     11, 22, 33,
            99, 88, 77,  10, 20, 30,  1, 2, 3,     4, 5, 6,
        ])
        trns8 = struct.pack(">HHH", 10, 20, 30)
        png8 = self.write("trns8.png", png_bytes(w, h, 8, 2, filtered_rows(rgb8, w, h, 3, [0]), trns=trns8))
        rgba8_out = self.dir / "trns8.rgba"
        run(LFFMPEG, "-y", "-i", png8, "-f", "rawvideo", "-pix_fmt", "rgba", rgba8_out)
        got8 = rgba8_out.read_bytes()
        for idx in range(w * h):
            r, g, b = rgb8[idx * 3:idx * 3 + 3]
            expected_a = 0 if (r, g, b) == (10, 20, 30) else 255
            self.assertEqual(got8[idx * 4:idx * 4 + 4], bytes([r, g, b, expected_a]))

        # 16-bit RGB tRNS must compare full 16-bit key before downscaling to 8-bit RGBA
        # using exact ((v + 128) // 257) rounding:
        # pixel 0 matches (0x1234, 0x5678, 0x9ABC) -> (0x12, 0x56, 0x9A, 0x00);
        # pixel 1 has same high bytes (0x1200, 0x5600, 0x9A00) -> (0x12, 0x56, 0x99, 0xFF)
        # (since (0x9ABC + 128) // 257 == 0x9A while (0x9A00 + 128) // 257 == 0x99).
        rgb16_pixels = struct.pack(
            ">6H",
            0x1234, 0x5678, 0x9ABC,
            0x1200, 0x5600, 0x9A00,
        )
        trns16 = struct.pack(">HHH", 0x1234, 0x5678, 0x9ABC)
        png16 = self.write("trns16.png", png_bytes(2, 1, 16, 2, b"\x00" + rgb16_pixels, trns=trns16))
        rgba16_out = self.dir / "trns16.rgba"
        run(LFFMPEG, "-y", "-i", png16, "-f", "rawvideo", "-pix_fmt", "rgba", rgba16_out)
        self.assertEqual(
            rgba16_out.read_bytes(),
            bytes([0x12, 0x56, 0x9A, 0x00, 0x12, 0x56, 0x99, 0xFF]),
        )

        # Malformed PNG chunk sequences that RFC 2083 forbids:
        ihdr_rgb = png_chunk(b"IHDR", struct.pack(">IIBBBBB", 2, 1, 8, 2, 0, 0, 0))
        ihdr_gray = png_chunk(b"IHDR", struct.pack(">IIBBBBB", 2, 1, 8, 0, 0, 0, 0))
        ihdr_idx = png_chunk(b"IHDR", struct.pack(">IIBBBBB", 2, 1, 8, 3, 0, 0, 0))
        idat_rgb = png_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02\x03\x04\x05\x06"))
        idat_rgb_part1 = png_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02\x03\x04\x05\x06")[:4])
        idat_rgb_part2 = png_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02\x03\x04\x05\x06")[4:])
        plte = png_chunk(b"PLTE", bytes(range(12)))
        ancillary = png_chunk(b"tEXt", b"k\x00v")
        iend = png_chunk(b"IEND", b"")
        sig = b"\x89PNG\r\n\x1a\n"

        invalid_pngs = [
            ("non_contiguous_idat.png", sig + ihdr_rgb + idat_rgb_part1 + ancillary + idat_rgb_part2 + iend),
            ("plte_on_gray.png", sig + ihdr_gray + plte + png_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02")) + iend),
            ("dup_plte.png", sig + ihdr_idx + plte + plte + png_chunk(b"IDAT", zlib.compress(b"\x00\x00\x01")) + iend),
            ("trns_before_plte.png", sig + ihdr_idx + png_chunk(b"tRNS", b"\x80") + plte + png_chunk(b"IDAT", zlib.compress(b"\x00\x00\x01")) + iend),
            ("plte_after_idat.png", sig + ihdr_rgb + idat_rgb + plte + iend),
            ("missing_plte_idx.png", sig + ihdr_idx + png_chunk(b"IDAT", zlib.compress(b"\x00\x00\x01")) + iend),
            ("bad_trns_len_rgb.png", sig + ihdr_rgb + png_chunk(b"tRNS", b"\x00\x01\x02\x03") + idat_rgb + iend),
            ("nonzero_iend.png", sig + ihdr_rgb + idat_rgb + png_chunk(b"IEND", b"\x00")),
        ]
        for fname, bad_bytes in invalid_pngs:
            bad_path = self.write(fname, bad_bytes)
            res = subprocess.run(
                [str(LFFMPEG), "lossless-codec", "png-decode", str(bad_path), str(self.dir / f"out_{fname}")],
                capture_output=True,
            )
            self.assertNotEqual(res.returncode, 0, f"Expected fail-closed rejection for {fname}")

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_flac_32bit_extremes_wasted_bits_and_wav_extensible_depths(self):
        # 1. Full 32-bit signed stereo with extreme opposite-rail samples (triggers 33-bit side channel & 64-bit Rice residuals)
        s32_pairs = [
            (-2147483648, 2147483647),
            (2147483647, -2147483648),
            (-2147483648, -2147483648),
            (2147483647, 2147483647),
            (0, 0),
            (1234567890, -1234567890),
        ] * 900
        pcm32_bytes = bytearray()
        for l_s, r_s in s32_pairs:
            pcm32_bytes += struct.pack("<ii", l_s, r_s)
        pcm32_in = self.write("extreme32.pcm", bytes(pcm32_bytes))

        lean_flac32 = self.dir / "lean32.flac"
        run(LFFMPEG, "-y", "-f", "s32le", "-ar", "48000", "-ac", "2", "-i", pcm32_in, lean_flac32)
        ff_pcm32 = self.dir / "ff32.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", lean_flac32, "-f", "s32le", ff_pcm32)
        self.assertEqual(ff_pcm32.read_bytes(), bytes(pcm32_bytes))

        # Roundtrip 32-bit FLAC -> WAV (WAVE_FORMAT_EXTENSIBLE) -> FLAC -> s32le without 24-bit truncation
        wav32 = self.dir / "lean32.wav"
        run(LFFMPEG, "-y", "-i", lean_flac32, wav32)
        ff_wav32_pcm = self.dir / "ff_wav32.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", wav32, "-f", "s32le", ff_wav32_pcm)
        self.assertEqual(ff_wav32_pcm.read_bytes(), bytes(pcm32_bytes))

        re_flac32 = self.dir / "re32.flac"
        run(LFFMPEG, "-y", "-i", wav32, re_flac32)
        lean_pcm32 = self.dir / "lean32_out.pcm"
        run(LFFMPEG, "-y", "-i", re_flac32, "-f", "s32le", lean_pcm32)
        self.assertEqual(lean_pcm32.read_bytes(), bytes(pcm32_bytes))

        # Also decode FFmpeg-encoded 32-bit FLAC (including wasted-bits blocks via LSB-shifted samples)
        wasted_pairs = [((i * 1024) - 524288, ((i * 512) - 262144)) for i in range(2048)]
        wasted32 = bytearray()
        for l_s, r_s in wasted_pairs:
            wasted32 += struct.pack("<ii", l_s << 8, r_s << 8)
        wasted_in = self.write("wasted32.pcm", bytes(wasted32))
        ff_wasted_flac = self.dir / "ff_wasted32.flac"
        run(FFMPEG, "-y", "-v", "error", "-f", "s32le", "-ar", "44100", "-ac", "2", "-i", wasted_in, ff_wasted_flac)
        lean_wasted_out = self.dir / "lean_wasted32.pcm"
        run(LFFMPEG, "-y", "-i", ff_wasted_flac, "-f", "s32le", lean_wasted_out)
        self.assertEqual(lean_wasted_out.read_bytes(), bytes(wasted32))

        # 2. 24-bit WAV WAVE_FORMAT_EXTENSIBLE interoperability with FFmpeg
        samples24 = [int(4_000_000 * math.sin(i * 0.09)) for i in range(1024)]
        pcm24 = pack_s24le(samples24)
        pcm24_in = self.write("mono24.pcm", pcm24)
        ff_wav24 = self.dir / "ff24.wav"
        run(FFMPEG, "-y", "-v", "error", "-f", "s24le", "-ar", "48000", "-ac", "1", "-i", pcm24_in, "-c:a", "pcm_s24le", ff_wav24)
        lean_from_ff_wav24 = self.dir / "lean_from_ff24.flac"
        run(LFFMPEG, "-y", "-i", ff_wav24, lean_from_ff_wav24)
        lean_wav24 = self.dir / "lean24.wav"
        run(LFFMPEG, "-y", "-i", lean_from_ff_wav24, lean_wav24)
        ff_check24 = self.dir / "ff_check24.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", lean_wav24, "-f", "s24le", ff_check24)
        self.assertEqual(ff_check24.read_bytes(), pcm24)

        # 3. 12-bit FLAC (via FFmpeg -bits_per_raw_sample 12) -> Lean WAV (MSB-aligned 16-bit extensible) -> FFmpeg s16le
        vals12 = [((i * 73) % 4096) - 2048 for i in range(1024)]
        msb16 = struct.pack(f"<{len(vals12)}h", *[v << 4 for v in vals12])
        msb16_in = self.write("in12_msb16.pcm", msb16)
        ff_flac12 = self.dir / "ff12.flac"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "s16le", "-ar", "32000", "-ac", "1", "-i", msb16_in,
            "-bits_per_raw_sample", "12", ff_flac12,
        )
        lean_wav12 = self.dir / "lean12.wav"
        run(LFFMPEG, "-y", "-i", ff_flac12, lean_wav12)
        ff_out12_s16 = self.dir / "ff12_out.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", lean_wav12, "-f", "s16le", ff_out12_s16)
        self.assertEqual(ff_out12_s16.read_bytes(), msb16)

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_flac_fullscale_alternating_4099_and_audioframe_depths(self):
        # Finding 1: 4,099 full-scale stereo s32le samples (+2147483647 / -2147483648)
        alt_bytes = bytearray()
        for i in range(4099):
            l_s = 2147483647 if (i % 2 == 0) else -2147483648
            r_s = -2147483648 if (i % 2 == 0) else 2147483647
            alt_bytes += struct.pack("<ii", l_s, r_s)
        alt_in = self.write("alt4099.pcm", bytes(alt_bytes))
        alt_flac = self.dir / "alt4099.flac"
        run(LFFMPEG, "-y", "-f", "s32le", "-ar", "48000", "-ac", "2", "-i", alt_in, alt_flac)
        ff_alt_pcm = self.dir / "ff_alt4099.pcm"
        run(FFMPEG, "-y", "-v", "error", "-i", alt_flac, "-f", "s32le", ff_alt_pcm)
        self.assertEqual(ff_alt_pcm.read_bytes(), bytes(alt_bytes))

        # Finding 2: flacDecodedToAudioFrame <-> flacEncodeAudioFrame roundtrip across 8, 12, 16, 24, 32-bit
        u8_raw = bytes([0, 64, 128, 192, 255, 17, 240, 127] * 64)
        flac8 = self.dir / "in8.flac"
        run(LFFMPEG, "-y", "-f", "u8", "-ar", "32000", "-ac", "1", "-i", self.write("in8.pcm", u8_raw), flac8)
        msb12 = struct.pack("<256h", *[(((i * 73) % 4096) - 2048) << 4 for i in range(256)])
        flac12 = self.dir / "in12.flac"
        run(FFMPEG, "-y", "-v", "error", "-f", "s16le", "-ar", "32000", "-ac", "1", "-i", self.write("in12.pcm", msb12), "-bits_per_raw_sample", "12", flac12)
        s16_raw = struct.pack("<256h", *[((i * 131) % 65536) - 32768 for i in range(256)])
        flac16 = self.dir / "in16.flac"
        run(LFFMPEG, "-y", "-f", "s16le", "-ar", "44100", "-ac", "2", "-i", self.write("in16.pcm", s16_raw), flac16)
        pcm24 = pack_s24le([int(3_000_000 * math.sin(i * 0.1)) for i in range(256)])
        flac24 = self.dir / "in24.flac"
        run(LFFMPEG, "-y", "-f", "s24le", "-ar", "48000", "-ac", "1", "-i", self.write("in24.pcm", pcm24), flac24)
        for tag, src_flac, out_fmt in (
            ("8", flac8, "u8"),
            ("12", flac12, "s16le"),
            ("16", flac16, "s16le"),
            ("24", flac24, "s24le"),
            ("32", alt_flac, "s32le"),
        ):
            rt_flac = self.dir / f"af_rt_{tag}.flac"
            run(LFFMPEG, "lossless-codec", "flac-frame-roundtrip", src_flac, rt_flac)
            ref_pcm = self.dir / f"af_ref_{tag}.pcm"
            got_pcm = self.dir / f"af_got_{tag}.pcm"
            run(FFMPEG, "-y", "-v", "error", "-i", src_flac, "-f", out_fmt, ref_pcm)
            run(FFMPEG, "-y", "-v", "error", "-i", rt_flac, "-f", out_fmt, got_pcm)
            self.assertEqual(got_pcm.read_bytes(), ref_pcm.read_bytes(), f"AudioFrame roundtrip mismatch for {tag}-bit")

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_out_of_domain_fallback_corrupt_fail_closed_and_strict_ffmpeg_bin(self):
        # Valid IEEE float32 WAV (format tag 3) -> out-of-domain fallbackDelegated succeeds via FFmpeg
        f32_samples = struct.pack("<64f", *[0.5 * math.sin(i * 0.2) for i in range(64)])
        f32_in = self.write("f32.raw", f32_samples)
        f32_wav = self.dir / "f32.wav"
        run(FFMPEG, "-y", "-v", "error", "-f", "f32le", "-ar", "48000", "-ac", "1", "-i", f32_in, "-c:a", "pcm_f32le", f32_wav)
        f32_flac = self.dir / "f32_delegated.flac"
        run(LFFMPEG, "-y", "-i", f32_wav, f32_flac)
        self.assertTrue(f32_flac.exists() and f32_flac.stat().st_size > 42)

        # Strict LEANAV_FFMPEG_BIN=/nonexistent MUST fail on delegated fallback (never silently use /usr/bin/ffmpeg)
        env_bad_bin = dict(os.environ)
        env_bad_bin["LEANAV_FFMPEG_BIN"] = "/nonexistent/ffmpeg_missing_binary"
        res_bad_bin = subprocess.run(
            [str(LFFMPEG), "-y", "-i", str(f32_wav), str(self.dir / "should_fail.flac")],
            env=env_bad_bin, capture_output=True,
        )
        self.assertNotEqual(res_bad_bin.returncode, 0)

        # Valid ID3v2-prefixed FLAC -> out-of-domain fallbackDelegated succeeds via FFmpeg
        id3_hdr = b"ID3\x03\x00\x00\x00\x00\x00\x04ABCD"
        id3_flac = self.write("id3_tagged.flac", id3_hdr + f32_flac.read_bytes())
        id3_wav = self.dir / "id3_out.wav"
        run(LFFMPEG, "-y", "-i", id3_flac, id3_wav)
        self.assertTrue(id3_wav.exists() and id3_wav.stat().st_size > 44)

        # Corrupt WAV / PNG / FLAC bitstreams MUST fail closed (rc != 0)
        for bad_name, bad_payload, out_ext in (
            ("corrupt.wav", b"RIFF\x24\x00\x00\x00WAVEfmt \x10\x00\x00\x00\x01\x00\x01\x00", "flac"),
            ("corrupt.png", b"\x89PNG\r\n\x1a\n\x00\x00\x00\x0dIHDRbroken", "png"),
            ("corrupt.flac", b"fLaC\x80\x00\x00\x22" + b"\x00" * 10, "wav"),
        ):
            bad_p = self.write(bad_name, bad_payload)
            rc = subprocess.run([str(LFFMPEG), "-y", "-i", str(bad_p), str(self.dir / f"bad_out.{out_ext}")], capture_output=True)
            self.assertNotEqual(rc.returncode, 0, f"Expected fail-closed rc!=0 for {bad_name}")

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_stream_copy_metadata_and_png_16to8_sub8_rounding(self):
        # Finding 4a: PNG -c:v copy and -c copy preserve pal8 + PLTE + tRNS + gAMA + tEXt bit-identically
        ihdr_pal = png_chunk(b"IHDR", struct.pack(">IIBBBBB", 2, 1, 8, 3, 0, 0, 0))
        gama = png_chunk(b"gAMA", struct.pack(">I", 45455))
        plte = png_chunk(b"PLTE", bytes([10, 20, 30, 200, 210, 220]))
        trns = png_chunk(b"tRNS", bytes([0, 255]))
        idat = png_chunk(b"IDAT", zlib.compress(b"\x00\x00\x01", 9))
        text = png_chunk(b"tEXt", b"Comment\x00HelloPngCopy")
        pal_png_bytes = b"\x89PNG\r\n\x1a\n" + ihdr_pal + gama + plte + trns + idat + text + png_chunk(b"IEND", b"")
        pal_in = self.write("pal_gama_text.png", pal_png_bytes)
        for copy_flags in (["-c:v", "copy"], ["-c", "copy"]):
            pal_out = self.dir / f"pal_copy_{copy_flags[0][1:].replace(':', '')}.png"
            run(LFFMPEG, "-y", "-i", pal_in, *copy_flags, pal_out, env={"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"})
            self.assertEqual(pal_out.read_bytes(), pal_png_bytes)

        # Finding 4b: FLAC -c:a copy and -c copy preserve Vorbis comment metadata bit-identically
        s16_in = self.write("tag.pcm", struct.pack("<128h", *[i * 100 - 6400 for i in range(128)]))
        tagged_flac = self.dir / "tagged.flac"
        run(FFMPEG, "-y", "-v", "error", "-f", "s16le", "-ar", "44100", "-ac", "1", "-i", s16_in, "-metadata", "title=HelloFlacTest", tagged_flac)
        tagged_bytes = tagged_flac.read_bytes()
        self.assertIn(b"HelloFlacTest", tagged_bytes)
        for copy_flags in (["-c:a", "copy"], ["-c", "copy"]):
            flac_out = self.dir / f"flac_copy_{copy_flags[0][1:].replace(':', '')}.flac"
            run(LFFMPEG, "-y", "-i", tagged_flac, *copy_flags, flac_out, env={"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"})
            self.assertEqual(flac_out.read_bytes(), tagged_bytes)

        # Finding 5: 16->8 exact /257 rounding and sub-8-bit tRNS + 16-bit replication
        rgba16_px = struct.pack(">4H", 0x12FF, 0xFF00, 0x0080, 0x0081)
        p_rgba16 = self.write("r16.png", png_bytes(1, 1, 16, 6, b"\x00" + rgba16_px))
        o_rgba8 = self.dir / "r16.rgba"
        run(LFFMPEG, "-y", "-i", p_rgba16, "-f", "rawvideo", "-pix_fmt", "rgba", o_rgba8)
        self.assertEqual(o_rgba8.read_bytes(), bytes([0x13, 0xFE, 0x00, 0x01]))

        p_g2_tr = self.write("g2_tr.png", png_bytes(4, 1, 2, 0, b"\x00\x1b", trns=b"\x00\x02"))
        o_g2_rgba = self.dir / "g2_tr.rgba"
        o_g2_rgba64 = self.dir / "g2_tr.rgba64be"
        run(LFFMPEG, "-y", "-i", p_g2_tr, "-f", "rawvideo", "-pix_fmt", "rgba", o_g2_rgba)
        run(LFFMPEG, "-y", "-i", p_g2_tr, "-f", "rawvideo", "-pix_fmt", "rgba64be", o_g2_rgba64)
        self.assertEqual(o_g2_rgba.read_bytes(), bytes([0,0,0,255, 85,85,85,255, 170,170,170,0, 255,255,255,255]))
        self.assertEqual(
            o_g2_rgba64.read_bytes(),
            bytes([0,0,0,0,0,0,255,255, 85,85,85,85,85,85,255,255, 170,170,170,170,170,170,0,0, 255,255,255,255,255,255,255,255]),
        )

    @unittest.skipUnless(ffmpeg_available(), "FFmpeg is required")
    def test_flac_rfc9639_residual_bounds_and_fail_closed(self):
        iso_env = {"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"}
        mono_s32 = [0] * 4 + [-2147483648] + [0] * 123
        mono_bytes = struct.pack(f"<{len(mono_s32)}i", *mono_s32)
        mono_in = self.write("mono_res_min32.pcm", mono_bytes)
        mono_flac = self.dir / "mono_res_min32.flac"
        run(LFFMPEG, "-y", "-f", "s32le", "-ar", "48000", "-ac", "1", "-i", mono_in, mono_flac, env=iso_env)
        ff_mono = self.dir / "ff_mono_res_min32.pcm"
        ff_r1 = run(FFMPEG, "-y", "-v", "error", "-i", mono_flac, "-f", "s32le", ff_mono)
        self.assertEqual(ff_r1.stderr, b"")
        self.assertEqual(ff_mono.read_bytes(), mono_bytes)
        lean_mono = self.dir / "lean_mono_res_min32.pcm"
        run(LFFMPEG, "-y", "-i", mono_flac, "-f", "s32le", lean_mono, env=iso_env)
        self.assertEqual(lean_mono.read_bytes(), mono_bytes)

        st_pairs = [(0, 0)] * 4 + [(-1073741824, 1073741824)] + [(0, 0)] * 123
        st_bytes = b"".join(struct.pack("<ii", l_v, r_v) for l_v, r_v in st_pairs)
        st_in = self.write("st_midside_min32.pcm", st_bytes)
        st_flac = self.dir / "st_midside_min32.flac"
        run(LFFMPEG, "-y", "-f", "s32le", "-ar", "48000", "-ac", "2", "-i", st_in, st_flac, env=iso_env)
        ff_st = self.dir / "ff_st_midside_min32.pcm"
        ff_r2 = run(FFMPEG, "-y", "-v", "error", "-i", st_flac, "-f", "s32le", ff_st)
        self.assertEqual(ff_r2.stderr, b"")
        self.assertEqual(ff_st.read_bytes(), st_bytes)
        lean_st = self.dir / "lean_st_midside_min32.pcm"
        run(LFFMPEG, "-y", "-i", st_flac, "-f", "s32le", lean_st, env=iso_env)
        self.assertEqual(lean_st.read_bytes(), st_bytes)

        def crc8_flac(data):
            crc = 0
            for b in data:
                crc ^= b
                for _ in range(8):
                    crc = ((crc << 1) ^ 0x07) & 0xFF if (crc & 0x80) else ((crc << 1) & 0xFF)
            return crc

        def crc16_flac(data):
            crc = 0
            for b in data:
                crc ^= b << 8
                for _ in range(8):
                    crc = ((crc << 1) ^ 0x8005) & 0xFFFF if (crc & 0x8000) else ((crc << 1) & 0xFFFF)
            return crc

        def pack_bits(bit_pairs):
            bits = []
            for val, width in bit_pairs:
                for shift in range(width - 1, -1, -1):
                    bits.append((val >> shift) & 1)
            while len(bits) % 8:
                bits.append(0)
            return bytes(
                sum(bits[i + j] << (7 - j) for j in range(8))
                for i in range(0, len(bits), 8)
            )

        si_bytes = pack_bits([(16, 16), (16, 16), (0, 24), (0, 24), (48000, 20), (0, 3), (31, 5), (16, 36)]) + b"\x00" * 16
        stream_hdr = b"fLaC\x80\x00\x00\x22" + si_bytes
        fh = bytearray([0xFF, 0xF8, (6 << 4) | 10, (0 << 4) | (7 << 1), 0x00, 15])
        fh.append(crc8_flac(fh))

        spy_log = self.dir / "ffmpeg_spy.log"
        spy_bin = self.dir / "ffmpeg"
        spy_bin.write_text(f"#!/bin/sh\necho invoked >> '{spy_log}'\nexit 0\n")
        spy_bin.chmod(0o755)
        spy_env = dict(os.environ)
        spy_env["PATH"] = f"{self.dir}:{spy_env.get('PATH', '')}"
        spy_env["LEANAV_FFMPEG_BIN"] = str(spy_bin)

        for tag, u_val in (("neg_2p31", 4294967295), ("pos_2p31", 4294967296)):
            q, rem = u_val >> 30, u_val & ((1 << 30) - 1)
            sub_pairs = [(0, 1), (8, 6), (0, 1), (1, 2), (0, 4), (30, 5), (1, q + 1), (rem, 30)] + [(1, 1), (0, 30)] * 15
            fn = bytes(fh) + pack_bits(sub_pairs)
            c16 = crc16_flac(fn)
            bad_flac = self.write(f"bad_rice_{tag}.flac", stream_hdr + fn + struct.pack(">H", c16))
            rc = subprocess.run([str(LFFMPEG), "-y", "-i", str(bad_flac), str(self.dir / f"out_{tag}.wav")], env=spy_env, capture_output=True)
            self.assertNotEqual(rc.returncode, 0, f"Expected fail-closed rc!=0 for {tag}")
            self.assertFalse(spy_log.exists(), f"Invalid FLAC {tag} must never invoke delegated ffmpeg")

        fh_ms = bytearray([0xFF, 0xF8, (6 << 4) | 10, (10 << 4) | (7 << 1), 0x00, 15])
        fh_ms.append(crc8_flac(fh_ms))
        sub_mid = [(0, 1), (0, 6), (0, 1), (0, 32)]
        sub_side_wasted_esc = [(0, 1), (8, 6), (1, 1), (1, 1), (0, 2), (0, 4), (15, 4), (31, 5), (0x40000000, 31)] + [(0, 31)] * 15
        fn_w_esc = bytes(fh_ms) + pack_bits(sub_mid + sub_side_wasted_esc)
        si_stereo = pack_bits([(16, 16), (16, 16), (0, 24), (0, 24), (48000, 20), (1, 3), (31, 5), (16, 36)]) + b"\x00" * 16
        w_esc_flac = self.write("wasted_esc31.flac", b"fLaC\x80\x00\x00\x22" + si_stereo + fn_w_esc + struct.pack(">H", crc16_flac(fn_w_esc)))
        lean_w_esc = self.dir / "lean_w_esc.pcm"
        ff_w_esc = self.dir / "ff_w_esc.pcm"
        run(LFFMPEG, "-y", "-i", w_esc_flac, "-f", "s32le", lean_w_esc, env=iso_env)
        run(FFMPEG, "-y", "-v", "error", "-i", w_esc_flac, "-f", "s32le", ff_w_esc)
        self.assertEqual(lean_w_esc.read_bytes(), ff_w_esc.read_bytes())

        esc_pairs = [(0, 1), (8, 6), (0, 1), (0, 2), (0, 4), (15, 4), (31, 5), (0x40000000, 31)] + [(0, 31)] * 15
        fn_esc = bytes(fh) + pack_bits(esc_pairs)
        ok_esc_flac = self.write("ok_esc31.flac", stream_hdr + fn_esc + struct.pack(">H", crc16_flac(fn_esc)))
        lean_esc_pcm = self.dir / "lean_esc31.pcm"
        ff_esc_pcm = self.dir / "ff_esc31.pcm"
        run(LFFMPEG, "-y", "-i", ok_esc_flac, "-f", "s32le", lean_esc_pcm, env=iso_env)
        run(FFMPEG, "-y", "-v", "error", "-i", ok_esc_flac, "-f", "s32le", ff_esc_pcm)
        self.assertEqual(lean_esc_pcm.read_bytes(), ff_esc_pcm.read_bytes())

    def test_png_grayscale_trns_bitdepth1_and_highbit_masking(self):
        iso_env = {"PATH": "/nonexistent", "LEANAV_FFMPEG_BIN": "/nonexistent"}
        for tag, trns_val in (("exact1", b"\x00\x01"), ("masked1", b"\xff\xfd")):
            p1 = self.write(f"g1_{tag}.png", png_bytes(4, 1, 1, 0, b"\x00\x50", trns=trns_val))
            o_rgba = self.dir / f"g1_{tag}.rgba"
            o_ya8 = self.dir / f"g1_{tag}.ya8"
            run(LFFMPEG, "-y", "-i", p1, "-f", "rawvideo", "-pix_fmt", "rgba", o_rgba, env=iso_env)
            run(LFFMPEG, "-y", "-i", p1, "-f", "rawvideo", o_ya8, env=iso_env)
            self.assertEqual(o_rgba.read_bytes(), bytes([0,0,0,255, 255,255,255,0, 0,0,0,255, 255,255,255,0]))
            self.assertEqual(o_ya8.read_bytes(), bytes([0,255, 255,0, 0,255, 255,0]))

        raw1 = self.write("g1_raw.bin", b"\x50")
        tr1 = self.write("g1_trns.bin", b"\x00\x01")
        enc1 = self.dir / "g1_enc.png"
        run(LFFMPEG, "lossless-codec", "png-encode", "4", "1", "1", "0", raw1, enc1, "-", tr1, env=iso_env)
        self.assertIn(b"\x00\x00\x00\x02tRNS\x00\x01", enc1.read_bytes())
        reenc1 = self.dir / "g1_reenc.png"
        run(LFFMPEG, "-y", "-i", enc1, reenc1, env=iso_env)
        self.assertIn(b"\x00\x00\x00\x02tRNS\x00\x01", reenc1.read_bytes())
        o_re_rgba = self.dir / "g1_reenc.rgba"
        run(LFFMPEG, "-y", "-i", reenc1, "-f", "rawvideo", "-pix_fmt", "rgba", o_re_rgba, env=iso_env)
        self.assertEqual(o_re_rgba.read_bytes(), bytes([0,0,0,255, 255,255,255,0, 0,0,0,255, 255,255,255,0]))

        cases = [
            (2, 4, b"\x00\x1b", b"\xff\xfe", bytes([0,0,0,255, 85,85,85,255, 170,170,170,0, 255,255,255,255])),
            (4, 2, b"\x00\x5a", b"\xab\xca", bytes([85,85,85,255, 170,170,170,0])),
            (8, 2, b"\x00\x12\x34", b"\x99\x34", bytes([0x12,0x12,0x12,255, 0x34,0x34,0x34,0])),
            (16, 2, b"\x00\x12\x34\x56\x78", b"\x12\x34", bytes([0x12,0x12,0x12,0, 0x56,0x56,0x56,255])),
        ]
        for bd, w, rows, tr_bytes, exp_rgba in cases:
            p = self.write(f"g{bd}_mask.png", png_bytes(w, 1, bd, 0, rows, trns=tr_bytes))
            out_p = self.dir / f"g{bd}_mask.rgba"
            run(LFFMPEG, "-y", "-i", p, "-f", "rawvideo", "-pix_fmt", "rgba", out_p, env=iso_env)
            self.assertEqual(out_p.read_bytes(), exp_rgba, f"Failed masked gray tRNS at bd={bd}")


if __name__ == "__main__":
    unittest.main()
