"""FITS/WBMP/PFM CLI grammar and fail-closed zero-delegation checks."""
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
        shim = self.root / "ffmpeg"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['IMAGE_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump(sys.argv[1:], stream)\n"
            "sys.exit(0)\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, PATH="/nonexistent",
                        IMAGE_ROUTING_LOG=str(self.log))

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, argv

    def assert_parsed_unsupported_fail_closed(self, args, output_format):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertFalse(plan["ok"])
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        self.assertFalse(plan["backend"]["fallback_allowed"])
        self.assertEqual(plan["outputs"][0]["format"], output_format)
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        if args[-1] != "-":
            self.assertFalse(Path(args[-1]).exists())

    def assert_rejected(self, args, reason=None):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.assertFalse(plan["backend"]["delegated_container"])
        if reason:
            self.assertIn(reason, plan["backend"]["reasons"])
        else:
            self.assertGreater(plan["error_count"], 0)
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())

    def test_fits_and_wbmp_suffixes_are_case_insensitive(self):
        for suffix, fmt in (("fits", "fits"), ("FITS", "fits"),
                            ("FiTs", "fits"), ("wbmp", "image2"),
                            ("WBMP", "image2"), ("WbMp", "image2")):
            with self.subTest(suffix=suffix):
                output = self.root / ("output with spaces." + suffix)
                self.assert_parsed_unsupported_fail_closed(
                    ["-y", "-i", str(self.source), str(output)], fmt)

    def test_explicit_fits_overrides_suffix_and_supports_stdout_grammar(self):
        for output in (str(self.root / "image.wbmp"),
                       str(self.root / "image.unknown"), "-"):
            with self.subTest(output=output):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-f", "fits", output], "fits")

    def test_explicit_other_formats_override_fits_and_wbmp_suffixes(self):
        for fmt, suffix in (("image2", "fits"), ("nut", "fits"), ("nut", "wbmp")):
            with self.subTest(fmt=fmt, suffix=suffix):
                output = str(self.root / ("output." + suffix))
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-f", fmt, output], fmt)

    def test_repeated_formats_preserve_last_output_format(self):
        for first, last in (("image2", "fits"), ("fits", "image2")):
            with self.subTest(first=first, last=last):
                self.assert_parsed_unsupported_fail_closed(
                    ["-i", str(self.source), "-f", first,
                     "-f", last, str(self.root / "output.fits")], last)

    def test_seven_historical_lavf_command_shapes_parse_and_fail_closed(self):
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
                self.assert_parsed_unsupported_fail_closed(args, "fits")
        args = (shared + bitexact + ["-f", "image2", "-c:v", "pgmyuv", "-i", source] +
                bitexact + ["-dct", "fastint", "-metadata", "title=lavftest", "-vf", "scale",
                            "-frames", "13", "-y", "-qscale", "10",
                            str(self.root / "output frames" / "%02d.wbmp")])
        self.assert_parsed_unsupported_fail_closed(args, "image2")

    def test_pfm_parses_float_pixel_formats_to_image2_and_fails_closed(self):
        for suffix in ("pfm", "PFM", "PfM"):
            for pixfmt in ("gbrpf32be", "gbrpf32le", "grayf32be", "grayf32le"):
                with self.subTest(suffix=suffix, pixfmt=pixfmt):
                    self.assert_parsed_unsupported_fail_closed(
                        ["-i", str(self.source), "-pix_fmt", pixfmt,
                         str(self.root / ("output." + suffix))], "image2")

    def test_pfm_explicit_format_precedence_and_rejections(self):
        self.assert_parsed_unsupported_fail_closed(
            ["-i", str(self.source), "-f", "nut", str(self.root / "output.pfm")], "nut")
        self.assert_parsed_unsupported_fail_closed(
            ["-i", str(self.source), str(self.root / "output.pfm")], "image2")
        self.assert_rejected(["-i", str(self.source), "-f", "pfm",
                              str(self.root / "output.pfm")])
        self.assert_rejected(["-i", str(self.source), str(self.root / "output.pfmx")],
                             "unrecognized_output_container_format")
        self.assert_rejected(["-i", str(self.source), "frames/../output.pfm"],
                             "unsafe_protocol_or_path_traversal")

    def test_json_fail_closed_diagnostics(self):
        cases = [(["-i", str(self.source), str(self.root / "out.fits")], "fits"),
                 (["-i", str(self.source), str(self.root / "%02d.wbmp")], "image2"),
                 (["-i", str(self.source), "-f", "fits", "-"], "fits")]
        for args, fmt in cases:
            with self.subTest(args=args):
                actual = subprocess.run([str(BINARY), "-json", "-y", *args],
                                        capture_output=True, text=True,
                                        timeout=10, env=self.env)
                self.assertNotEqual(actual.returncode, 0)
                doc = json.loads(actual.stdout.strip())
                self.assertFalse(doc["ok"])
                self.assertEqual(doc["tier"], "unsupported")
                self.assertEqual(doc["format"], fmt)
                self.assertFalse(self.log.exists())

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
        self.assert_rejected(["-i", str(self.source), "-f", "fits",
                              "concat:first.fits|second.fits"],
                             "unsafe_protocol_or_path_traversal")
        for unsafe in ("concat:first.fits|../second.fits", "concat:single.fits",
                       "concat:https://invalid.example/a.fits|b.fits",
                       "https://invalid.example/image.fits",
                       "file:image.fits", "pipe:0", "/proc/self/mem", "frames/../image.wbmp"):
            for position in ("input", "output"):
                with self.subTest(unsafe=unsafe, position=position):
                    args = (["-i", unsafe, "-f", "fits", str(self.root / "out.fits")]
                            if position == "input" else
                            ["-i", str(self.source), "-f", "fits", unsafe])
                    self.assert_rejected(args, "unsafe_protocol_or_path_traversal")


if __name__ == "__main__":
    unittest.main()
