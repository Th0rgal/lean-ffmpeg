"""IAMF CLI delegation, argument-file path policy and argv preservation.

The backend is a non-media shim. These checks do not claim IAMF encoding or FATE
coverage; original media commands are validated separately against frozen FFmpeg.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", ROOT / ".lake/build/bin/lffmpeg"))
FLAGS = ("-streamid", "-stream_group", "-/stream_group", "-/filter_complex", "-use_stream_ids_as_track_ids")


class IamfRoutingTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(BINARY.is_file())
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = str(self.root / "input with spaces.wav")
        Path(self.source).write_bytes(b"non-media routing fixture")
        self.output = str(self.root / "output.iamf")
        self.log = self.root / "argv.json"
        shim = self.root / "backend.py"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "with open(os.environ['IAMF_ROUTING_LOG'], 'w') as f:\n"
            "    json.dump(sys.argv[1:], f)\n"
            "sys.exit(int(os.environ['IAMF_ROUTING_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        IAMF_ROUTING_LOG=str(self.log), IAMF_ROUTING_EXIT="0")

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], env=self.env,
                                capture_output=True, text=True, timeout=15)
        return result, json.loads(result.stdout)

    def assert_delegated(self, args, fmt="iamf", exit_code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        self.assertEqual(plan["outputs"][0]["format"], fmt)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        self.log.unlink(missing_ok=True)
        actual = subprocess.run([str(BINARY), *argv], capture_output=True,
                                env=dict(self.env, IAMF_ROUTING_EXIT=str(exit_code)), timeout=15)
        self.assertEqual(actual.returncode, exit_code, actual.stderr)
        self.assertEqual(json.loads(self.log.read_text()), argv)

    def assert_rejected(self, args):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        self.log.unlink(missing_ok=True)
        result = subprocess.run([str(BINARY), *args], env=self.env,
                                capture_output=True, timeout=15)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.log.exists())

    def test_explicit_input_output_formats_and_suffixes(self):
        for suffix in ("iamf", "IAMF", "IaMf"):
            with self.subTest(suffix=suffix):
                self.assert_delegated(["-i", self.source, "-c", "copy",
                                       str(self.root / ("out." + suffix))])
        self.assert_delegated(["-f", "iamf", "-i", self.source, "-c", "copy",
                               "-f", "iamf", str(self.root / "out.unknown")])
        self.assert_delegated(["-i", self.source, "-f", "nut", self.output], "nut")

    def test_group_and_repeated_stream_ids_preserve_raw_order(self):
        group = "type=iamf_audio_element:id=1:st=0,layer=ch_layout=stereo"
        self.assert_delegated(["-i", self.source, "-stream_group", group,
                               "-streamid", "0:0", "-streamid", "0:7",
                               "-use_stream_ids_as_track_ids", "1", self.output])

    def test_argument_files_remain_literal_and_delegated(self):
        for name in ("group with spaces", "group'quoted", "group;literal"):
            with self.subTest(name=name):
                path = self.root / name
                path.write_text("type=iamf_audio_element:id=1:st=0,layer=ch_layout=stereo\n")
                self.assert_delegated(["-i", self.source, "-/stream_group", str(path),
                                       "-/stream_group", str(path), self.output])

    def test_argument_file_unsafe_paths_are_rejected(self):
        for path in ("../group", "groups/../group", "/proc/self/mem", "/dev/zero",
                     "https://invalid.example/group", "file:group", "pipe:0"):
            with self.subTest(path=path):
                for flag in ("-/stream_group", "-/filter_complex"):
                    self.assert_rejected(["-i", self.source, flag, path, self.output])

    def test_missing_and_empty_values_fail_before_backend(self):
        for flag in FLAGS:
            with self.subTest(flag=flag):
                self.assert_rejected(["-i", self.source, self.output, flag])
                self.assert_rejected(["-i", self.source, flag, "", self.output])

    def test_value_semantics_and_failures_are_owned_by_backend(self):
        for flag, value in (("-streamid", "0:-1"), ("-streamid", "invalid"),
                            ("-stream_group", "type=invalid"),
                            ("-use_stream_ids_as_track_ids", "invalid")):
            with self.subTest(flag=flag, value=value):
                self.assert_delegated(["-i", self.source, flag, value, self.output], exit_code=73)

    def test_original_iamf_command_shapes_preserve_argv(self):
        cases = json.loads((ROOT / "tests/vectors/iamf_routing_commands.json").read_text())
        self.assertEqual(len(cases), 14)
        for case in cases:
            with self.subTest(name=case["name"]):
                args = [arg.replace("{FIXTURE}", str(self.root)) for arg in case["argv"]]
                for index, token in enumerate(args[:-1]):
                    if token == "-i":
                        path = Path(args[index + 1])
                        self.assertTrue(path.is_relative_to(self.root))
                        path.parent.mkdir(parents=True, exist_ok=True)
                        path.write_bytes(b"non-media input for argv preservation")
                self.assert_delegated(args, case["output_format"])

    def test_filter_graph_file_with_and_without_media_input(self):
        graph = self.root / "graph with spaces"
        graph.write_text("anullsrc=r=48000:cl=stereo[out]\n")
        self.assert_delegated(["-i", self.source, "-/filter_complex", str(graph), self.output])
        self.assert_delegated(["-/filter_complex", str(graph), "-map", "[out]", self.output])

    def test_group_maps_force_delegation_and_keep_backend_validation(self):
        source = self.root / "native.mp4"
        source.write_bytes(b"non-media routing input")
        output = str(self.root / "out.mp4")
        plain = ["-i", str(source), "-c:v", "h264", output]
        result, plan = self.plan(plain)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "translated_partial")
        for group in ("0:g:i:42", "0:g:i:300", "0:g:0", "0:g:#42", "-0:g:i:42",
                      "0:g:i:42:a:0", "0:g:0?", "0:g:invalid", "0:g:i:"):
            with self.subTest(group=group):
                self.assert_delegated([*plain[:-1], "-map", group, output], "mp4", 73)
        self.assert_rejected([*plain[:-1], "-map", "not_an_index:g:i:42", output])

    def test_unsafe_media_paths_and_unknown_argument_file_options_stay_rejected(self):
        self.assert_rejected(["-i", "https://invalid.example/audio.wav", self.output])
        self.assert_rejected(["-i", self.source, "../out.iamf"])
        self.assert_rejected(["-i", self.source, "-/not_a_supported_option", self.source, self.output])


if __name__ == "__main__":
    unittest.main()
