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
        self.assertEqual(mp4_plan["backend"]["tier"], "delegated_faithful")

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
        env_isolated = {"PATH": "/nonexistent"}
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

        # 16-bit RGB tRNS must compare full 16-bit key before downscaling to 8-bit RGBA:
        # pixel 0 matches (0x1234, 0x5678, 0x9ABC) -> alpha 0;
        # pixel 1 has same high bytes (0x1200, 0x5600, 0x9A00) -> alpha 255!
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
            bytes([0x12, 0x56, 0x9A, 0x00, 0x12, 0x56, 0x9A, 0xFF]),
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


if __name__ == "__main__":
    unittest.main()
