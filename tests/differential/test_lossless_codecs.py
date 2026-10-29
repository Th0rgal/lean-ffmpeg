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


def run(*args, **kwargs):
    return subprocess.run([str(a) for a in args], check=True, capture_output=True, **kwargs)


def ffmpeg_version_ok():
    try:
        out = run(FFMPEG, "-version").stdout.decode()
    except (OSError, subprocess.CalledProcessError):
        return False
    return out.startswith("ffmpeg version 6.1.1")


def png_chunk(kind, payload):
    body = kind + payload
    return struct.pack(">I", len(payload)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)


def png_bytes(width, height, depth, color, rows, interlace=0, palette=None):
    ihdr = struct.pack(">IIBBBBB", width, height, depth, color, 0, 0, interlace)
    out = b"\x89PNG\r\n\x1a\n" + png_chunk(b"IHDR", ihdr)
    if palette is not None:
        out += png_chunk(b"PLTE", palette)
    out += png_chunk(b"IDAT", zlib.compress(rows, 9)) + png_chunk(b"IEND", b"")
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

    def test_zlib_roundtrip_and_reference_interop(self):
        samples = [b"", b"a", bytes(range(256)) * 7, os.urandom(4097), b"abc" * 1000]
        for index, data in enumerate(samples):
            source = self.write(f"in{index}", data)
            reference = self.write(f"ref{index}.z", zlib.compress(data, 9))
            decoded = self.dir / f"dec{index}"
            run(LFFMPEG, "lossless-codec", "zlib-decode", reference, decoded)
            self.assertEqual(decoded.read_bytes(), data)
            for mode in ("fixed", "dynamic"):
                encoded = self.dir / f"{mode}{index}.z"
                run(LFFMPEG, "lossless-codec", "zlib-encode", mode, source, encoded)
                self.assertEqual(zlib.decompress(encoded.read_bytes()), data)
                again = self.dir / f"again{mode}{index}"
                run(LFFMPEG, "lossless-codec", "zlib-decode", encoded, again)
                self.assertEqual(again.read_bytes(), data)

    def test_zlib_rejects_bad_checksum_and_trailing_data(self):
        good = bytearray(zlib.compress(b"lean-ffmpeg"))
        bad = bytearray(good)
        bad[-1] ^= 1
        for name, data in (("bad.z", bad), ("tail.z", good + b"x")):
            result = subprocess.run([str(LFFMPEG), "lossless-codec", "zlib-decode", str(self.write(name, bytes(data))),
                                     str(self.dir / "out")], capture_output=True)
            self.assertEqual(result.returncode, 1)

    def test_png_decoder_all_filters_and_formats(self):
        cases = []
        width, height = 13, 9
        rgba = bytes((x * 17 + y * 31 + c * 7) & 255 for y in range(height) for x in range(width) for c in range(4))
        cases.append((8, 6, 4, rgba, None))
        rgb16 = bytes((x * 3 + y * 11 + c) & 255 for y in range(height) for x in range(width) for c in range(6))
        cases.append((16, 2, 6, rgb16, None))
        gray2 = bytes(((y * 5 + x) * 37) & 255 for y in range(height) for x in range((width * 2 + 7) // 8))
        cases.append((2, 0, 1, gray2, None))
        pal = bytes(range(48))
        idx4 = bytes(((y + x) * 19) & 255 for y in range(height) for x in range((width * 4 + 7) // 8))
        cases.append((4, 3, 1, idx4, pal))
        for depth, color, bpp, pixels, palette in cases:
            png = self.write(f"case{depth}{color}.png", png_bytes(width, height, depth, color,
                                                                filtered_rows(pixels, width, height, bpp, [0, 1, 2, 3, 4]),
                                                                palette=palette))
            out = self.dir / "pixels"
            run(LFFMPEG, "lossless-codec", "png-decode", png, out)
            self.assertEqual(out.read_bytes(), pixels)

    def test_png_adam7_decode(self):
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
        self.assertEqual(out.read_bytes(), bytes(v for row in image for v in row))

    @unittest.skipUnless(ffmpeg_version_ok(), "FFmpeg 6.1.1 is required")
    def test_png_ffmpeg_differential(self):
        width, height = 17, 11
        rgb = bytes((x * 13 + y * 29 + c * 71) & 255 for y in range(height) for x in range(width) for c in range(3))
        raw = self.write("in.rgb", rgb)
        ff_png = self.dir / "ff.png"
        run(FFMPEG, "-v", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{width}x{height}", "-i", raw,
            "-frames:v", "1", "-pred", "mixed", ff_png)
        decoded = self.dir / "lean.rgb"
        run(LFFMPEG, "lossless-codec", "png-decode", ff_png, decoded)
        self.assertEqual(decoded.read_bytes(), rgb)
        lean_png = self.dir / "lean.png"
        run(LFFMPEG, "lossless-codec", "png-encode", width, height, 8, 2, raw, lean_png)
        ff_raw = self.dir / "ff.rgb"
        run(FFMPEG, "-v", "error", "-i", lean_png, "-f", "rawvideo", "-pix_fmt", "rgb24", ff_raw)
        self.assertEqual(ff_raw.read_bytes(), rgb)


if __name__ == "__main__":
    unittest.main()
