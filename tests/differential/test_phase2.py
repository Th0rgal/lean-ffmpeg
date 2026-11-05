import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
REFERENCE = Path(
    os.environ.get("LEANAV_TEST_FFMPEG")
    or os.environ.get("FFMPEG")
    or shutil.which("ffmpeg")
    or "/usr/bin/ffmpeg"
)
FFPROBE = Path(
    os.environ.get("LEANAV_TEST_FFPROBE")
    or os.environ.get("FFPROBE")
    or shutil.which("ffprobe")
    or "/usr/bin/ffprobe"
)
FIXTURE = ROOT / "tests" / "differential" / "fixtures" / "phase2.json"
MEDIA_FIXTURE = ROOT / "tests" / "differential" / "fixtures" / "input.mp4"


class Phase2DifferentialTests(unittest.TestCase):
    _tmp_fixture_dir = None
    _active_fixture = FIXTURE

    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not REFERENCE.is_file() or not os.access(REFERENCE, os.X_OK):
            raise unittest.SkipTest("reference FFmpeg is unavailable")
        if not FFPROBE.is_file() or not os.access(FFPROBE, os.X_OK):
            raise unittest.SkipTest("reference FFprobe is unavailable")
        fixtures_dir = FIXTURE.parent
        av_fixture = fixtures_dir / "input-av.mp4"
        if MEDIA_FIXTURE.is_file() and av_fixture.is_file():
            cls._active_fixture = FIXTURE
            return
        tmp_dir = Path(tempfile.mkdtemp(prefix="phase2-fixtures-"))
        cls._tmp_fixture_dir = tmp_dir
        for name in ("phase2.json", "input-vfr.mp4", "input-yuv444.mp4"):
            src = fixtures_dir / name
            if src.is_file():
                shutil.copy2(src, tmp_dir / name)
        if MEDIA_FIXTURE.is_file():
            shutil.copy2(MEDIA_FIXTURE, tmp_dir / "input.mp4")
        else:
            subprocess.run(
                [
                    str(REFERENCE), "-hide_banner", "-v", "error", "-y",
                    "-f", "lavfi", "-i", "testsrc=size=32x32:rate=10:duration=2",
                    "-c:v", "libx264", "-preset", "ultrafast", "-pix_fmt", "yuv420p",
                    "-threads", "1", "-map_metadata", "-1", "-movflags", "+faststart",
                    str(tmp_dir / "input.mp4"),
                ],
                check=True,
            )
        if av_fixture.is_file():
            shutil.copy2(av_fixture, tmp_dir / "input-av.mp4")
        else:
            subprocess.run(
                [
                    str(REFERENCE), "-hide_banner", "-v", "error", "-y",
                    "-f", "lavfi", "-i", "testsrc=size=32x32:rate=25:duration=2",
                    "-f", "lavfi", "-i", "sine=frequency=440:sample_rate=48000:duration=2",
                    "-map", "0:v:0", "-map", "1:a:0",
                    "-c:v", "libx264", "-preset", "ultrafast", "-pix_fmt", "yuv420p",
                    "-c:a", "aac", "-b:a", "64k", "-ac", "1",
                    "-threads", "1", "-map_metadata", "-1", "-movflags", "+faststart",
                    str(tmp_dir / "input-av.mp4"),
                ],
                check=True,
            )
        cls._active_fixture = tmp_dir / "phase2.json"

    @classmethod
    def tearDownClass(cls):
        if cls._tmp_fixture_dir is not None:
            shutil.rmtree(cls._tmp_fixture_dir, ignore_errors=True)
            cls._tmp_fixture_dir = None

    def capture(self, runner, directory):
        old_path = os.environ.get("PATH")
        os.environ["PATH"] = "/nonexistent"
        try:
            result_path = runner.run_fixture(
                str(REFERENCE.resolve()),
                str(BINARY.resolve()),
                str(FFPROBE.resolve()),
                self._active_fixture,
                Path(directory),
            )
        finally:
            if old_path is None:
                os.environ.pop("PATH", None)
            else:
                os.environ["PATH"] = old_path
        return json.loads(result_path.read_text(encoding="utf-8"))

    def test_phase2_path_and_color_invariants(self):
        import sys
        sys.path.insert(0, str(ROOT / "tests" / "differential"))
        import runner

        with tempfile.TemporaryDirectory(prefix="phase2-differential-") as directory:
            data = self.capture(runner, directory)

        self.assertTrue(data["capture_only"])
        missing = [record for record in data["records"] if record["name"] == "missing-input-fails-closed"]
        self.assertEqual(len(missing), 2)
        for record in missing:
            self.assertEqual(record["status"], "failed")
            self.assertIsNotNone(record["exit_status"])
            self.assertNotEqual(record["exit_status"], 0)
            self.assertFalse(record["output"]["exists"])

        color = next(item for item in data["comparisons"] if item["name"] == "explicit-color-metadata")
        self.assertEqual(color["comparison"]["status"], "pass")
        self.assertIn("color", color["comparison"]["diagnostics"])

        tiny = [record for record in data["records"] if record["name"] == "tiny-duration"]
        self.assertEqual(len(tiny), 2)
        for record in tiny:
            self.assertEqual(record["status"], "success")
            self.assertTrue(record["output"]["exists"])
            probe = record["probe"]["normalized"]
            video = next(stream for stream in probe["streams"] if stream["codec_type"] == "video")
            self.assertEqual(video["nb_frames"], 1)
            if record["tool"] == "candidate":
                self.assertAlmostEqual(probe["format"]["duration"], 0.001, delta=0.001)
            else:
                self.assertEqual(probe["format"]["duration"], 0.1)

        vfr = [record for record in data["records"] if record["name"] == "vfr-b-frame-packets-and-frames"]
        self.assertEqual(len(vfr), 2)
        for record in vfr:
            self.assertEqual(record["status"], "success")
            probe = record["probe"]["normalized"]
            video = next(stream for stream in probe["streams"] if stream["codec_type"] == "video")
            self.assertEqual(probe["format"]["duration"], 0.966667)
            self.assertEqual(video["r_frame_rate"], {"numerator": 30, "denominator": 1})
            self.assertEqual(video["avg_frame_rate"], {"numerator": 600, "denominator": 29})
            self.assertEqual(video["nb_frames"], 20)
            self.assertEqual(video["pix_fmt"], "yuv420p")
            self.assertEqual(record["timestamp_probe"]["normalized"]["packets"]["count"], 20)
            self.assertEqual(record["timestamp_probe"]["normalized"]["frames"]["count"], 20)
            self.assertGreater(record["timestamp_probe"]["normalized"]["packets"]["duration_time"], 0)
            self.assertEqual(record["decoded_video_probe"]["status"], "success")
            self.assertEqual(record["decoded_video_probe"]["frame_count"], 29)
            self.assertEqual(record["probe"]["normalized"]["streams"][0]["nb_frames"], 20)

        yuv444 = [record for record in data["records"] if record["name"] == "yuv444-10bit-probe"]
        if yuv444:
            self.assertEqual(len(yuv444), 2)
            for record in yuv444:
                self.assertEqual(record["status"], "success")
                probe = record["probe"]["normalized"]
                video = next(stream for stream in probe["streams"] if stream["codec_type"] == "video")
                self.assertEqual(probe["format"]["duration"], 1.0)
                self.assertEqual(video["r_frame_rate"], {"numerator": 25, "denominator": 1})
                self.assertEqual(video["avg_frame_rate"], {"numerator": 25, "denominator": 1})
                self.assertEqual(video["pix_fmt"], "yuv444p10le")
                self.assertEqual(video["nb_frames"], 25)
                self.assertEqual(record["timestamp_probe"]["normalized"]["frames"]["count"], 25)

        audio = [record for record in data["records"] if record["name"] == "input-av-audio-sample-count"]
        self.assertEqual(len(audio), 2)
        for record in audio:
            self.assertEqual(record["status"], "success")
            streams = record["probe"]["normalized"]["streams"]
            audio_stream = next(stream for stream in streams if stream["codec_type"] == "audio")
            self.assertEqual(audio_stream["sample_rate"], 48000)
            self.assertEqual(audio_stream["channels"], 1)
            self.assertEqual(audio_stream["duration_ts"], 96000)
            self.assertEqual(record["decoded_audio_probe"]["status"], "success")

    def test_phase2_reference_and_candidate_are_deterministic(self):
        import sys
        sys.path.insert(0, str(ROOT / "tests" / "differential"))
        import runner

        with tempfile.TemporaryDirectory(prefix="phase2-determinism-") as directory:
            first = self.capture(runner, Path(directory) / "first")
            second = self.capture(runner, Path(directory) / "second")

        for name in ("tiny-duration", "input-av-audio-sample-count"):
            first_records = {record["tool"]: record for record in first["records"] if record["name"] == name}
            second_records = {record["tool"]: record for record in second["records"] if record["name"] == name}
            self.assertEqual(first_records.keys(), second_records.keys())
            for tool in first_records:
                self.assertEqual(first_records[tool]["output"]["sha256"], second_records[tool]["output"]["sha256"])
                self.assertEqual(first_records[tool]["probe"]["normalized"], second_records[tool]["probe"]["normalized"])


if __name__ == "__main__":
    unittest.main()
