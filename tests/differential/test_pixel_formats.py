"""Delegated P416 and native-endian YUV422P10 preserve complete sample bytes."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake/build/bin/lffmpeg"
FORMATS = ("p416le", "p416be", "yuv422p10")
WIDTH, HEIGHT, FRAMES = 8, 4, 2


def words(values, endian):
    return b"".join(value.to_bytes(2, endian) for value in values)


def planes(bits, chroma_width):
    # Include values with unequal bytes and nonzero low bits; 8-bit comparisons
    # or a swapped byte order cannot accidentally satisfy these fixtures.
    seeds = ((0, 1, 0x0102, 0x02FF, 0x1234, 0xABCD, 0xFFFF) if bits == 16
             else (0, 1, 255, 256, 257, 511, 512, 1023))
    return [[[seeds[(i + plane * 3 + frame) % len(seeds)]
              for i in range(width * HEIGHT)]
             for plane, width in enumerate((WIDTH, chroma_width, chroma_width))]
            for frame in range(FRAMES)]


def planar_bytes(frames, endian):
    return b"".join(words(plane, endian) for frame in frames for plane in frame)


class PixelFormatRoutingTests(unittest.TestCase):
    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10)
        return result, json.loads(result.stdout)

    def test_formats_delegate_in_both_positions_and_option_spellings(self):
        for pixel_format in (*FORMATS, "yuv422p10le", "yuv422p10be",
                             "p410le", "p410be", "p412le", "p412be"):
            for flag in ("-pix_fmt", "-pixel_format"):
                for position in ("input", "output"):
                    with self.subTest(format=pixel_format, flag=flag, position=position):
                        args = ([flag, pixel_format, "-i", "input.mp4", "-c:v", "h264",
                                 "output.mp4"] if position == "input" else
                                ["-i", "input.mp4", "-c:v", "h264", flag, pixel_format,
                                 "output.mp4"])
                        result, plan = self.plan(args)
                        self.assertEqual(result.returncode, 0, result.stdout)
                        self.assertEqual(plan["error_count"], 0)
                        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")

    def test_native_pixel_format_boundary_is_unchanged(self):
        for pixel_format in ("yuv420p", "yuv420p10le", "p010le"):
            with self.subTest(format=pixel_format):
                result, plan = self.plan(["-i", "input.mp4", "-c:v", "h264",
                                          "-pix_fmt", pixel_format, "output.mp4"])
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(plan["backend"]["tier"], "translated_partial")

    def test_missing_empty_unknown_and_shell_like_values_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "shell-marker"
            for flag in ("-pix_fmt", "-pixel_format"):
                result, _ = self.plan(["-i", "input.mp4", "output.mp4", flag])
                self.assertNotEqual(result.returncode, 0)
                for value in ("", "p416xx", "p414le", "yuv422p10xx", "bogus_pix_fmt",
                              "p416le -i other.raw", f"$(touch {marker})"):
                    for before_input in (True, False):
                        with self.subTest(flag=flag, value=value, input=before_input):
                            args = ([flag, value, "-i", "input.mp4", "output.mp4"]
                                    if before_input else
                                    ["-i", "input.mp4", flag, value, "output.mp4"])
                            result, _ = self.plan(args)
                            self.assertNotEqual(result.returncode, 0)
                            self.assertFalse(marker.exists())

    def test_new_formats_do_not_bypass_input_or_output_path_checks(self):
        for pixel_format in FORMATS:
            for unsafe in ("https://invalid.example/media", "/dev/video0",
                           "/proc/self/mem", "fixtures/../outside.mp4"):
                for position in ("input", "output"):
                    with self.subTest(format=pixel_format, unsafe=unsafe, position=position):
                        args = (["-pix_fmt", pixel_format, "-i", unsafe, "output.mp4"]
                                if position == "input" else
                                ["-i", "input.mp4", "-pix_fmt", pixel_format, unsafe])
                        result, plan = self.plan(args)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unsafe_protocol_or_path_traversal",
                                      plan["backend"]["reasons"])


class PixelFormatPrecisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        configured = os.environ.get("LEANAV_TEST_FFMPEG")
        if configured and not Path(configured).is_file():
            raise RuntimeError(f"LEANAV_TEST_FFMPEG does not exist: {configured}")
        reference = configured or shutil.which("ffmpeg")
        if not reference:
            raise unittest.SkipTest("reference FFmpeg unavailable")
        cls.reference = str(Path(reference).resolve())
        cls.env = dict(os.environ, LEANAV_FFMPEG_BIN=cls.reference)

    def conversion(self, source, input_format, output_format,
                   input_flag="-pixel_format", output_flag="-pix_fmt",
                   environment=None, argv_log=None):
        args = ["-v", "error", "-threads", "1", "-filter_threads", "1",
                "-f", "rawvideo", "-s", f"{WIDTH}x{HEIGHT}", "-r", "2",
                input_flag, input_format, "-i", str(source), "-an", "-c:v", "rawvideo",
                "-threads", "1", output_flag, output_format, "-f", "rawvideo", "-"]
        environment = environment or self.env
        expected = subprocess.run([self.reference, *args], capture_output=True,
                                      timeout=30, env=environment)
        actual = subprocess.run([str(BINARY), *args], capture_output=True,
                                timeout=30, env=environment)
        self.assertEqual(expected.returncode, 0, expected.stderr)
        self.assertTrue(expected.stdout)
        self.assertEqual(actual.returncode, 0, actual.stderr)
        self.assertEqual(actual.stdout, expected.stdout)
        if argv_log is not None:
            self.assertEqual(json.loads(argv_log.read_text()), ["-nostdin", "-n", *args])
        return expected.stdout

    def test_output_pixel_format_alias_spelling_is_preserved_to_backend(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.raw"
            log = Path(directory) / "argv.json"
            shim = Path(directory) / "ffmpeg-shim.py"
            shim.write_text(
                f"#!{sys.executable}\nimport json, os, sys\n"
                f"open({str(log)!r}, 'w').write(json.dumps(sys.argv[1:]))\n"
                f"os.execve({self.reference!r}, [{self.reference!r}, *sys.argv[1:]], os.environ)\n"
            )
            shim.chmod(0o755)
            environment = dict(self.env, LEANAV_FFMPEG_BIN=str(shim))
            for fmt in FORMATS:
                if fmt.startswith("p416"):
                    endian = "little" if fmt.endswith("le") else "big"
                    source.write_bytes(b"".join(
                        words(y, endian) + words([x for pair in zip(u, v) for x in pair], endian)
                        for y, u, v in planes(16, WIDTH)))
                else:
                    source.write_bytes(planar_bytes(planes(10, WIDTH // 2), sys.byteorder))
                for input_flag in ("-pix_fmt", "-pixel_format"):
                    for output_flag in ("-pix_fmt", "-pixel_format"):
                        with self.subTest(format=fmt, input=input_flag, output=output_flag):
                            log.unlink(missing_ok=True)
                            self.conversion(source, fmt, fmt, input_flag=input_flag,
                                            output_flag=output_flag, environment=environment,
                                            argv_log=log)

    def test_p416_output_preserves_all_16_bits_and_endianness(self):
        samples = planes(16, WIDTH)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "planar.raw"
            source.write_bytes(planar_bytes(samples, "little"))
            outputs = {}
            for fmt, endian in (("p416le", "little"), ("p416be", "big")):
                with self.subTest(format=fmt):
                    actual = self.conversion(source, "yuv444p16le", fmt)
                    expected = b"".join(words(y, endian) +
                                        words([x for pair in zip(u, v) for x in pair], endian)
                                        for y, u, v in samples)
                    self.assertEqual(len(actual), FRAMES * WIDTH * HEIGHT * 6)
                    self.assertEqual(actual, expected)
                    outputs[fmt] = actual
            self.assertEqual(set(outputs), {"p416le", "p416be"})
            self.assertNotEqual(outputs["p416le"], outputs["p416be"])
            self.assertEqual(outputs["p416be"],
                             b"".join(outputs["p416le"][i:i+2][::-1]
                                      for i in range(0, len(outputs["p416le"]), 2)))

    def test_p416_input_preserves_all_16_bits_in_both_option_spellings(self):
        samples = planes(16, WIDTH)
        with tempfile.TemporaryDirectory() as directory:
            for fmt, endian in (("p416le", "little"), ("p416be", "big")):
                source = Path(directory) / (fmt + ".raw")
                source.write_bytes(b"".join(words(y, endian) +
                                           words([x for pair in zip(u, v) for x in pair], endian)
                                           for y, u, v in samples))
                for flag in ("-pixel_format", "-pix_fmt"):
                    with self.subTest(format=fmt, flag=flag):
                        actual = self.conversion(source, fmt, "yuv444p16le", flag)
                        self.assertEqual(len(actual), FRAMES * WIDTH * HEIGHT * 6)
                        self.assertEqual(actual, planar_bytes(samples, "little"))

    def test_yuv422p10_output_alias_matches_explicit_native_endian(self):
        samples = planes(10, WIDTH // 2)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "tenbit.raw"
            source.write_bytes(planar_bytes(samples, "little"))
            outputs = {}
            for fmt, endian in (("yuv422p10", sys.byteorder),
                                ("yuv422p10le", "little"), ("yuv422p10be", "big")):
                with self.subTest(format=fmt):
                    actual = self.conversion(source, "yuv422p10le", fmt)
                    self.assertEqual(len(actual), FRAMES * WIDTH * HEIGHT * 4)
                    self.assertEqual(actual, planar_bytes(samples, endian))
                    outputs[fmt] = actual
            self.assertEqual(set(outputs), {"yuv422p10", "yuv422p10le", "yuv422p10be"})
            native = "yuv422p10" + ("le" if sys.byteorder == "little" else "be")
            self.assertEqual(outputs["yuv422p10"], outputs[native])
            self.assertNotEqual(outputs["yuv422p10le"], outputs["yuv422p10be"])

    def test_yuv422p10_input_alias_and_explicit_endians_preserve_10_bits(self):
        samples = planes(10, WIDTH // 2)
        with tempfile.TemporaryDirectory() as directory:
            for fmt, endian in (("yuv422p10", sys.byteorder),
                                ("yuv422p10le", "little"), ("yuv422p10be", "big")):
                source = Path(directory) / (fmt + ".raw")
                source.write_bytes(planar_bytes(samples, endian))
                for flag in ("-pixel_format", "-pix_fmt"):
                    with self.subTest(format=fmt, flag=flag):
                        actual = self.conversion(source, fmt, "yuv422p10le", flag)
                        self.assertEqual(len(actual), FRAMES * WIDTH * HEIGHT * 4)
                        self.assertEqual(actual, planar_bytes(samples, "little"))


if __name__ == "__main__":
    unittest.main()
