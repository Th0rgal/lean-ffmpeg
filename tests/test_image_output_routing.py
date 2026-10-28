"""FITS/WBMP production CLI routing checks with a non-media backend shim.

A successful shim invocation proves delegation and argv preservation, not that
FFmpeg encoded an image or that an upstream FATE case passed.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))
FITS_PIXFMTS = ("gbrap", "gbrap16be", "gbrp", "gbrp16be", "gray", "gray16be")


class ImageOutputRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise AssertionError(f"reviewed executable required: {BINARY}")

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root / "input with spaces.mp4"
        self.source.write_bytes(b"routing placeholder; not media")
        self.log = self.root / "argv.json"
        shim = self.root / "backend.py"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "args = sys.argv[1:]\n"
            "with open(os.environ['IMAGE_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump({'argv': args, 'argv_hex': [os.fsencode(a).hex() for a in args]}, stream)\n"
            "sys.exit(int(os.environ['IMAGE_ROUTING_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        IMAGE_ROUTING_LOG=str(self.log), IMAGE_ROUTING_EXIT="0")

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, IMAGE_ROUTING_EXIT=str(code)))
        return result, argv

    def assert_delegated(self, args, output_format, code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        self.assertTrue(plan["backend"]["delegated_container"])
        self.assertEqual(plan["outputs"][0]["format"], output_format)
        actual, argv = self.invoke(args, code)
        self.assertEqual(actual.returncode, code, actual.stderr)
        record = json.loads(self.log.read_text())
        self.assertEqual(record["argv"], argv)
        self.assertEqual(record["argv_hex"], [os.fsencode(a).hex() for a in argv])
        self.assertEqual(actual.stdout, "")
        if args[-1] != "-":
            self.assertFalse(Path(args[-1]).exists())

    def assert_rejected(self, args, reason=None):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        if reason:
            self.assertIn(reason, plan["backend"]["reasons"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())

    def test_fits_and_wbmp_suffixes_are_case_insensitive(self):
        for suffix, fmt in (("fits", "fits"), ("FITS", "fits"),
                            ("FiTs", "fits"), ("wbmp", "image2"),
                            ("WBMP", "image2"), ("WbMp", "image2")):
            with self.subTest(suffix=suffix):
                output = self.root / ("output with spaces." + suffix)
                self.assert_delegated(["-y", "-i", str(self.source), str(output)], fmt)

    def test_explicit_fits_overrides_suffix_and_supports_stdout(self):
        for output in (str(self.root / "image.wbmp"),
                       str(self.root / "image.unknown"), "-"):
            with self.subTest(output=output):
                self.assert_delegated(["-i", str(self.source), "-f", "fits", output], "fits")

    def test_explicit_other_formats_override_fits_and_wbmp_suffixes(self):
        for fmt, suffix in (("image2", "fits"), ("nut", "fits"), ("nut", "wbmp")):
            with self.subTest(fmt=fmt, suffix=suffix):
                output = str(self.root / ("output." + suffix))
                self.assert_delegated(["-i", str(self.source), "-f", fmt, output], fmt)

    def test_repeated_formats_preserve_order_and_use_last_output_format(self):
        for first, last in (("image2", "fits"), ("fits", "image2")):
            with self.subTest(first=first, last=last):
                self.assert_delegated(["-i", str(self.source), "-f", first,
                                       "-f", last, str(self.root / "output.fits")], last)

    def test_seven_historical_lavf_command_shapes_preserve_argv(self):
        source = str(self.root / "input frames" / "%02d.pgm")
        shared = ["-nostdin", "-nostats", "-noauto_conversion_filters", "-y",
                  "-cpuflags", "all", "-filter_threads", "1"]
        bitexact = ["-flags", "+bitexact", "-idct", "simple", "-sws_flags",
                    "+accurate_rnd+bitexact", "-fflags", "+bitexact", "-threads", "1"]
        for pixfmt in FITS_PIXFMTS:
            with self.subTest(case="fate-lavf-" + pixfmt + ".fits"):
                args = (shared + ["-auto_conversion_filters"] + bitexact +
                        ["-f", "image2", "-c:v", "pgmyuv", "-i", source] + bitexact +
                        ["-dct", "fastint", "-metadata", "title=lavftest", "-t", "1",
                         "-qscale", "10", "-pix_fmt", pixfmt,
                         str(self.root / ("lavf." + pixfmt + ".fits"))])
                self.assert_delegated(args, "fits")
        args = (shared + bitexact + ["-f", "image2", "-c:v", "pgmyuv", "-i", source] +
                bitexact + ["-dct", "fastint", "-metadata", "title=lavftest", "-vf", "scale",
                            "-frames", "13", "-y", "-qscale", "10",
                            str(self.root / "output frames" / "%02d.wbmp")])
        self.assert_delegated(args, "image2")

    def test_backend_error_status_is_preserved(self):
        cases = [(["-i", str(self.source), str(self.root / "out.fits")], "fits"),
                 (["-i", str(self.source), str(self.root / "%02d.wbmp")], "image2"),
                 (["-i", str(self.source), "-f", "fits", "-"], "fits")]
        for code in (1, 73):
            for args, fmt in cases:
                with self.subTest(code=code, args=args):
                    self.assert_delegated(args, fmt, code)

    def test_unknown_suffix_and_invalid_explicit_format_remain_rejected(self):
        for suffix in ("fitsx", "wbmpx", "unknown"):
            with self.subTest(suffix=suffix):
                self.assert_rejected(["-i", str(self.source), str(self.root / ("out." + suffix))],
                                     "unrecognized_output_container_format")
        for fmt in ("FITS", " fits", "fits ", "fitsx", "wbmp", ""):
            with self.subTest(fmt=fmt):
                self.assert_rejected(["-i", str(self.source), "-f", fmt,
                                      str(self.root / "out.fits")])
        self.assert_rejected(["-i", str(self.source), str(self.root / "out.fits"), "-f"])

    def test_protocol_and_traversal_rejections_are_unchanged(self):
        for unsafe in ("concat:first.fits|second.fits", "https://invalid.example/image.fits",
                       "file:image.fits", "pipe:0", "/proc/self/mem", "frames/../image.wbmp"):
            for position in ("input", "output"):
                with self.subTest(unsafe=unsafe, position=position):
                    args = (["-i", unsafe, "-f", "fits", str(self.root / "out.fits")]
                            if position == "input" else
                            ["-i", str(self.source), "-f", "fits", unsafe])
                    self.assert_rejected(args, "unsafe_protocol_or_path_traversal")


if __name__ == "__main__":
    unittest.main()
