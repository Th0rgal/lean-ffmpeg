import json
import os
import shutil
import struct
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = Path(os.environ.get("FFMPEG", shutil.which("ffmpeg") or "/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg"))
FFPROBE = Path(os.environ.get("FFPROBE", shutil.which("ffprobe") or "/tmp/opencode/ffmpeg-runtime-full/bin/ffprobe"))
STRACE = Path("/usr/bin/strace")


def _ffmpeg_usable() -> bool:
    if not FFMPEG.is_file() or not os.access(FFMPEG, os.X_OK):
        return False
    try:
        res = subprocess.run([str(FFMPEG), "-version"], capture_output=True, text=True, check=True)
        return res.stdout.startswith("ffmpeg version ")
    except (OSError, subprocess.CalledProcessError):
        return False


def _ref_raw(args):
    return subprocess.run(
        [str(FFMPEG), "-hide_banner", "-v", "error", *args],
        capture_output=True,
        check=True,
    ).stdout


class LavfiGraphDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not _ffmpeg_usable() or not FFPROBE.is_file():
            raise unittest.SkipTest("reference ffmpeg/ffprobe unavailable")
        cls.work = Path(tempfile.mkdtemp(prefix="leanav-lavfi-diff-"))
        cls.bad_stub = cls.work / "hostile_ffmpeg_stub"
        cls.bad_stub.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
        cls.bad_stub.chmod(0o755)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.work, ignore_errors=True)

    def _run(self, args, expect_ok=True, json_out=False):
        log = self.work / "run.strace" if STRACE.is_file() else None
        cmd = [str(STRACE), "-f", "-s", "4096", "-e", "trace=execve", "-o", str(log), str(BINARY)] if log is not None else [str(BINARY)]
        env = dict(os.environ)
        env["LEANAV_FFMPEG_BIN"] = str(self.bad_stub)
        env["LEANAV_FFPROBE_BIN"] = str(self.bad_stub)
        env["PATH"] = "/nonexistent"
        res = subprocess.run(
            [*cmd, *(["-json"] if json_out else []), *args],
            capture_output=True,
            env=env,
            check=False,
        )
        if expect_ok:
            self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace") or res.stdout.decode(errors="replace"))
        else:
            self.assertNotEqual(res.returncode, 0)
        if log is not None:
            execves = [ln for ln in log.read_text(encoding="utf-8", errors="replace").splitlines() if "execve(" in ln]
            self.assertEqual(len(execves), 1, execves)
            self.assertIn(str(BINARY), execves[0])
            self.assertNotIn("ffmpeg", execves[0].replace(str(BINARY), ""))
        return res

    def test_plan_routes_lavfi_inproc(self):
        res = self._run(
            ["plan", "-f", "lavfi", "-i", "color=c=red:s=8x8:r=10:d=0.1", "-f", "rawvideo", str(self.work / "plan.yuv")],
            json_out=False,
        )
        doc = json.loads(res.stdout.decode())
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["backend"]["tier"], "independent_verified")
        self.assertEqual(doc["backend"]["reasons"], ["inproc_lavfi_dag"])

    def test_lavfi_probe_reports_acyclic_graph(self):
        res = self._run(
            ["lavfi-probe", "color=c=blue:s=32x32:r=10:d=0.1[bg];color=c=red:s=8x8:r=10:d=0.1[fg];[bg][fg]overlay=x=4:y=4"],
        )
        doc = json.loads(res.stdout.decode())
        self.assertTrue(doc["ok"])
        self.assertTrue(doc["acyclic"])
        self.assertEqual(doc["nodes"], 3)

    def test_named_colors_byte_exact(self):
        for color in ["black", "white", "red", "green", "lime", "blue", "yellow", "cyan", "magenta", "gray", "orange"]:
            with self.subTest(color=color):
                out = self.work / f"color_{color}.yuv"
                self._run(["-y", "-f", "lavfi", "-i", f"color=c={color}:s=8x8:r=10:d=0.1", "-f", "rawvideo", str(out)])
                ref = _ref_raw(["-f", "lavfi", "-i", f"color=c={color}:s=8x8:r=10:d=0.1", "-f", "rawvideo", "-"])
                self.assertEqual(out.read_bytes(), ref)

    def test_sine_within_one_lsb(self):
        out = self.work / "sine.pcm"
        self._run(["-y", "-f", "lavfi", "-i", "sine=f=440:r=8000:d=0.01", "-f", "s16le", str(out)])
        ref = _ref_raw(["-f", "lavfi", "-i", "sine=f=440:r=8000:d=0.01", "-f", "s16le", "-"])
        cand = struct.unpack("<80h", out.read_bytes())
        gold = struct.unpack("<80h", ref)
        self.assertEqual(len(cand), len(gold))
        self.assertLessEqual(max(abs(a - b) for a, b in zip(cand, gold)), 1)

    def test_testsrc_rgb24_byte_exact(self):
        out = self.work / "testsrc16.rgb"
        self._run(["-y", "-f", "lavfi", "-i", "testsrc=s=16x16:r=10:d=0.1", "-pix_fmt", "rgb24", "-f", "rawvideo", str(out)])
        ref = _ref_raw(["-f", "lavfi", "-i", "testsrc=s=16x16:r=10:d=0.1", "-pix_fmt", "rgb24", "-f", "rawvideo", "-"])
        self.assertEqual(out.read_bytes(), ref)

    def test_testsrc_yuv420p_luma_exact(self):
        out = self.work / "testsrc32.yuv"
        self._run(["-y", "-f", "lavfi", "-i", "testsrc=s=32x32:r=10:d=0.1", "-pix_fmt", "yuv420p", "-f", "rawvideo", str(out)])
        ref = _ref_raw(["-f", "lavfi", "-i", "testsrc=s=32x32:r=10:d=0.1", "-pix_fmt", "yuv420p", "-f", "rawvideo", "-"])
        self.assertEqual(out.read_bytes()[:1024], ref[:1024])

    def test_overlay_stdout_byte_exact(self):
        spec = "[0:v][1:v]overlay=x=4:y=4"
        res = self._run([
            "-f", "lavfi", "-i", "color=c=blue:s=32x32:r=10:d=0.1",
            "-f", "lavfi", "-i", "color=c=red:s=8x8:r=10:d=0.1",
            "-filter_complex", spec, "-f", "rawvideo", "-",
        ])
        ref = _ref_raw([
            "-f", "lavfi", "-i", "color=c=blue:s=32x32:r=10:d=0.1",
            "-f", "lavfi", "-i", "color=c=red:s=8x8:r=10:d=0.1",
            "-filter_complex", spec + ",format=yuv420p", "-f", "rawvideo", "-",
        ])
        self.assertEqual(res.stdout, ref)

    def test_amix_within_two_lsb(self):
        spec = "sine=f=440:r=8000:d=0.02[a];sine=f=880:r=8000:d=0.02[b];[a][b]amix=inputs=2"
        out = self.work / "amix.pcm"
        self._run(["-y", "-lavfi", spec, "-f", "s16le", str(out)])
        ref = _ref_raw(["-f", "lavfi", "-i", spec, "-f", "s16le", "-"])
        cand = struct.unpack("<160h", out.read_bytes())
        gold = struct.unpack("<160h", ref)
        self.assertLessEqual(max(abs(a - b) for a, b in zip(cand, gold)), 2)

    def test_md5_muxer_byte_exact(self):
        res = self._run(["-f", "lavfi", "-i", "color=c=red:s=8x8:r=10:d=0.1", "-f", "md5", "-"])
        ref = _ref_raw(["-f", "lavfi", "-i", "color=c=red:s=8x8:r=10:d=0.1", "-f", "md5", "-"])
        self.assertEqual(res.stdout, ref)

    def test_container_muxers_decode_with_reference(self):
        cases = [
            ("synth.mp4", "color=c=green:s=32x32:r=10:d=0.2[v];sine=f=440:r=48000:d=0.2[a]", ["-map", "[v]", "-map", "[a]"]),
            ("synth.wav", "sine=f=440:r=8000:d=0.05", []),
            ("synth.flac", "sine=f=440:r=8000:d=0.05", []),
            ("synth.png", "color=c=red:s=16x16:r=10:d=0.1", []),
            ("synth.mkv", "color=c=cyan:s=16x16:r=10:d=0.2", []),
        ]
        for name, spec, extra in cases:
            with self.subTest(name=name):
                out = self.work / name
                self._run(["-y", "-lavfi", spec, *extra, str(out)])
                probe = subprocess.run(
                    [str(FFPROBE), "-v", "error", "-show_streams", "-of", "json", str(out)],
                    capture_output=True, text=True, check=True,
                )
                self.assertGreaterEqual(len(json.loads(probe.stdout)["streams"]), 1)
                dec = subprocess.run(
                    [str(FFMPEG), "-v", "error", "-i", str(out), "-f", "null", "-"],
                    capture_output=True, text=True,
                )
                self.assertEqual(dec.returncode, 0, dec.stderr)

    def test_multi_pad_dags_and_filters(self):
        cases = [
            "color=c=red:s=16x16:r=10:d=0.1,split=2[a][b];[a]hflip[af];[af][b]hstack=inputs=2",
            "color=c=blue:s=16x16:r=10:d=0.1,split=2[a][b];[a]vflip[af];[af][b]vstack=inputs=2",
            "color=c=yellow:s=32x32:r=10:d=0.1,crop=16:16:8:8,pad=32:32:8:8:black,scale=16:16,eq=contrast=1:brightness=0",
        ]
        for idx, spec in enumerate(cases):
            with self.subTest(idx=idx):
                out = self.work / f"dag_{idx}.yuv"
                self._run(["-y", "-lavfi", spec, "-f", "rawvideo", str(out)])
                self.assertGreater(len(out.read_bytes()), 0)
        aspec = "sine=f=440:r=8000:d=0.02,asplit=2[a][b];[a]volume=0.5[av];[av][b]amerge=inputs=2"
        aout = self.work / "amerge.pcm"
        self._run(["-y", "-lavfi", aspec, "-f", "s16le", str(aout)])
        self.assertEqual(len(aout.read_bytes()), 160 * 2 * 2)

    def test_fail_closed_cycle_and_ill_typed_link(self):
        self._run(["-y", "-lavfi", "[a]null[b];[b]null[a]", "-f", "null", "-"], expect_ok=False)
        self._run(["-y", "-lavfi", "sine=f=440:r=8000:d=0.01[a];[a]scale=16:16", "-f", "null", "-"], expect_ok=False)
        self._run(["-y", "-lavfi", "color=c=red:s=8x8:r=10:d=0.1[v];[v]volume=0.5", "-f", "null", "-"], expect_ok=False)
        self._run(["-y", "-lavfi", "color=c=red:s=8x8:r=10:d=0.1,crop=16:16:0:0", "-f", "null", "-"], expect_ok=False)
        self._run(["-y", "-lavfi", "color=c=red:s=8x8:r=10:d=0.1;[missing]null", "-f", "null", "-"], expect_ok=False)


if __name__ == "__main__":
    unittest.main()
