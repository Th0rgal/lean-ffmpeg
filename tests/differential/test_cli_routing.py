import json
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FIXTURE = ROOT / "tests" / "differential" / "fixtures" / "input-av.mp4"


class CliRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not BINARY.stat().st_mode & 0o111:
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not FIXTURE.is_file():
            raise unittest.SkipTest("media fixture is unavailable")
        try:
            subprocess.run([str(BINARY), "-version"], check=True, capture_output=True, text=True)
        except (OSError, subprocess.SubprocessError):
            raise unittest.SkipTest("lffmpeg runtime is unavailable")

    def run_cli(self, *args, output_name="output.mp4"):
        with tempfile.TemporaryDirectory(prefix="lffmpeg-cli-routing-") as directory:
            output = Path(directory) / output_name
            result = subprocess.run(
                [str(BINARY), *args, str(output)],
                capture_output=True,
                text=True,
                check=False,
            )
            return result

    def assert_one_json_object(self, result):
        lines = result.stdout.splitlines()
        self.assertEqual(len(lines), 1, result.stdout)
        document = json.loads(lines[0])
        self.assertIsInstance(document, dict)
        return document

    def test_json_success_is_one_object_on_stdout_without_human_diagnostics(self):
        result = self.run_cli("-json", "-y", "-i", str(FIXTURE), "-c", "copy")
        self.assertEqual(result.returncode, 0, result.stderr)
        document = self.assert_one_json_object(result)
        self.assertTrue(document["ok"])
        self.assertEqual(result.stderr, "")

    def test_json_malformed_option_is_one_object_without_stderr(self):
        result = self.run_cli("-json", "-y", "-i", str(FIXTURE), "-unsupported-option")
        self.assertNotEqual(result.returncode, 0)
        document = self.assert_one_json_object(result)
        self.assertFalse(document["ok"])
        self.assertEqual(result.stderr, "")

    def test_non_json_failure_routes_diagnostic_to_stderr(self):
        result = self.run_cli("-y", "-i", str(FIXTURE), "-unsupported-option")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertNotEqual(result.stderr, "")

    def test_quiet_levels_suppress_ordinary_stderr(self):
        for level in ("quiet", "-8"):
            with self.subTest(level=level):
                result = self.run_cli("-y", "-v", level, "-i", str(FIXTURE), "-unsupported-option")
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "")

    def test_json_timestamp_overflow_is_object_on_stdout_and_nonzero(self):
        for option in ("-t", "-ss"):
            with self.subTest(option=option):
                result = self.run_cli(
                    "-json",
                    "-y",
                    option,
                    "4294968",
                    "-i",
                    str(FIXTURE),
                    "-c",
                    "copy",
                )
                self.assertNotEqual(result.returncode, 0)
                document = self.assert_one_json_object(result)
                self.assertFalse(document["ok"])
                self.assertEqual(result.stderr, "")

    def test_negative_timestamps_fail_closed(self):
        for option in ("-t", "-ss"):
            with self.subTest(option=option):
                result = self.run_cli(
                    "-json",
                    "-y",
                    option,
                    "-0.001",
                    "-i",
                    str(FIXTURE),
                    "-c",
                    "copy",
                )
                self.assertNotEqual(result.returncode, 0)
                document = self.assert_one_json_object(result)
                self.assertFalse(document["ok"])
                self.assertEqual(result.stderr, "")

    def test_json_and_quiet_transcode_suppress_banner_and_stats_on_stderr(self):
        result_json = self.run_cli("-json", "-y", "-i", str(FIXTURE), "-t", "0.1", "-c:v", "h264")
        self.assertEqual(result_json.returncode, 0, result_json.stderr)
        document = self.assert_one_json_object(result_json)
        self.assertTrue(document["ok"])
        self.assertEqual(result_json.stderr, "")

        for level in ("quiet", "panic", "fatal", "error", "warning", "-8", "0", "8", "16", "24"):
            with self.subTest(level=level):
                result_quiet = self.run_cli("-y", "-v", level, "-i", str(FIXTURE), "-t", "0.1", "-c:v", "h264")
                self.assertEqual(result_quiet.returncode, 0, result_quiet.stderr)
                self.assertEqual(result_quiet.stdout, "")
                self.assertEqual(result_quiet.stderr, "")

    def test_adversarial_corrupt_and_truncated_media_fail_closed_without_artifact(self):
        raw = FIXTURE.read_bytes()
        corrupt_cases = {
            "empty": b"",
            "garbage": b"NOT_AN_MP4_CONTAINER_0123456789",
            "truncated_ftyp": raw[:12],
            "invalid_box_size_below_header": b"\x00\x00\x00\x03ftypisom\x00\x00\x02\x00",
            "overflow_box_size_u32_max": b"\xff\xff\xff\xffftypisom\x00\x00\x02\x00",
            "truncated_moov": raw[:128],
        }
        with tempfile.TemporaryDirectory(prefix="lffmpeg-corrupt-media-") as directory:
            root = Path(directory)
            for name, payload in corrupt_cases.items():
                input_path = root / f"{name}.mp4"
                input_path.write_bytes(payload)
                for mode, codec_args in (("copy", ("-c", "copy")), ("h264", ("-c:v", "h264"))):
                    with self.subTest(case=name, mode=mode):
                        output_path = root / f"{name}-{mode}-out.mp4"
                        result = subprocess.run(
                            [str(BINARY), "-json", "-y", "-i", str(input_path), *codec_args, str(output_path)],
                            capture_output=True,
                            text=True,
                            check=False,
                        )
                        self.assertNotEqual(result.returncode, 0)
                        document = self.assert_one_json_object(result)
                        self.assertFalse(document["ok"])
                        self.assertEqual(result.stderr, "")
                        self.assertFalse(output_path.exists())

            mdat_pos = raw.find(b"mdat")
            self.assertGreater(mdat_pos, 0)
            trunc_mdat = root / "faststart_truncated_mdat.mp4"
            trunc_mdat.write_bytes(raw[: mdat_pos + 4])
            trunc_out = root / "faststart_truncated_mdat-out.mp4"
            result_mdat = subprocess.run(
                [str(BINARY), "-json", "-y", "-i", str(trunc_mdat), "-c:v", "h264", str(trunc_out)],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(result_mdat.returncode, 0)
            document_mdat = self.assert_one_json_object(result_mdat)
            self.assertFalse(document_mdat["ok"])
            self.assertEqual(result_mdat.stderr, "")
            self.assertFalse(trunc_out.exists())


if __name__ == "__main__":
    unittest.main()
