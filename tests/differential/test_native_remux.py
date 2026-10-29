"""M1-B native independent_verified stream copy: zero-exec and FFmpeg differential coverage."""
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = os.environ.get("FFMPEG") or shutil.which("ffmpeg")
FFPROBE = os.environ.get("FFPROBE") or shutil.which("ffprobe")
INTROSPECTION = ["-version", "-buildconf", "-formats", "-muxers", "-demuxers", "-codecs", "-decoders",
                 "-encoders", "-bsfs", "-filters", "-pix_fmts", "-protocols", "-h", "-help"]


def zero_exec_env(tmp: Path):
    poison = tmp / "poison-bin"
    poison.mkdir(exist_ok=True)
    marker = tmp / "ffmpeg-was-executed"
    for name in ("ffmpeg", "ffprobe"):
        script = poison / name
        script.write_text(f"#!/bin/sh\ntouch {marker}\nexit 97\n")
        script.chmod(0o755)
    env = {k: v for k, v in os.environ.items() if k not in ("LD_LIBRARY_PATH",)}
    env["PATH"] = f"{poison}:/usr/bin:/bin"
    return env, marker


class NativeRemuxTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file():
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        if not FFMPEG or not FFPROBE:
            raise unittest.SkipTest("reference FFmpeg/ffprobe unavailable")
        cls.tmp = Path(tempfile.mkdtemp(prefix="m1b-native-"))
        src = "testsrc=size=64x48:rate=10:duration=2"
        tone = "sine=frequency=440:duration=2"
        gens = {
            "in.mp4": ["-f", "lavfi", "-i", src, "-c:v", "libx264", "-g", "5", "-bf", "0", "-an"],
            "in.ivf": ["-f", "lavfi", "-i", src, "-c:v", "libvpx-vp9", "-g", "5"],
            "in.wav": ["-f", "lavfi", "-i", tone, "-c:a", "pcm_s16le"],
            "in.flac": ["-f", "lavfi", "-i", tone, "-c:a", "flac"],
            "in.webm": ["-f", "lavfi", "-i", src, "-c:v", "libvpx-vp9"],
            "in.mkv": ["-f", "lavfi", "-i", src, "-c:v", "libx264"],
            "av.mp4": ["-f", "lavfi", "-i", src, "-f", "lavfi", "-i", tone, "-c:v", "libx264", "-c:a", "aac", "-shortest"],
        }
        for name, args in gens.items():
            res = subprocess.run([FFMPEG, "-v", "error", "-y", *args, str(cls.tmp / name)], capture_output=True)
            if res.returncode != 0:
                raise unittest.SkipTest(f"fixture generation failed for {name}: {res.stderr[-300:]}")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def native(self, *args):
        env, marker = zero_exec_env(self.tmp)
        if marker.exists():
            marker.unlink()
        res = subprocess.run([str(BINARY), *map(str, args)], capture_output=True, text=True, env=env, cwd=self.tmp)
        return res, marker.exists()

    def ref(self, *args):
        return subprocess.run([FFMPEG, "-v", "error", "-y", *map(str, args)], capture_output=True, text=True)

    def probe(self, path, *extra):
        res = subprocess.run([FFPROBE, "-v", "error", *extra, "-of", "json", str(path)], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, res.stderr)
        return json.loads(res.stdout)

    def packets(self, path):
        doc = self.probe(path, "-show_packets", "-show_entries", "packet=pts,dts,size,flags")
        return [(p.get("pts"), p.get("dts"), p.get("size"), p.get("flags")) for p in doc.get("packets", [])]

    def framemd5(self, path):
        res = subprocess.run([FFMPEG, "-v", "error", "-i", str(path), "-f", "framemd5", "-"], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, res.stderr)
        return [l.split(",")[-1].strip() for l in res.stdout.splitlines() if l and not l.startswith("#")]

    def test_same_container_copy_is_native_zero_exec_and_matches_ffmpeg(self):
        for ext in ("mp4", "ivf", "wav", "flac", "webm", "mkv"):
            with self.subTest(ext=ext):
                out = self.tmp / f"native.{ext}"
                res, executed = self.native("-json", "-y", "-i", f"in.{ext}", "-c", "copy", out)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertFalse(executed, "FFmpeg executable was spawned")
                doc = json.loads(res.stdout)
                self.assertEqual(doc["mode"], "ffmpeg-cli-native-copy")
                self.assertEqual(doc["tier"], "independent_verified")
                ref_out = self.tmp / f"ref.{ext}"
                self.assertEqual(self.ref("-i", self.tmp / f"in.{ext}", "-c", "copy", ref_out).returncode, 0)
                self.assertEqual(self.framemd5(out), self.framemd5(ref_out))
                self.assertEqual([p[2] for p in self.packets(out)], [p[2] for p in self.packets(ref_out)])

    def test_byte_preserving_formats(self):
        for ext in ("ivf", "wav", "flac", "webm", "mkv"):
            with self.subTest(ext=ext):
                out = self.tmp / f"bp.{ext}"
                res, executed = self.native("-y", "-i", f"in.{ext}", "-c", "copy", out)
                self.assertEqual(res.returncode, 0, res.stderr)
                self.assertFalse(executed)
                self.assertEqual(out.read_bytes(), (self.tmp / f"in.{ext}").read_bytes())

    def test_native_trim_mp4_ivf_wav(self):
        for ext in ("mp4", "ivf", "wav"):
            with self.subTest(ext=ext):
                out = self.tmp / f"trim.{ext}"
                res, executed = self.native("-json", "-y", "-ss", "0.5", "-t", "1", "-i", f"in.{ext}", "-c", "copy", out)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertFalse(executed)
                self.assertEqual(json.loads(res.stdout)["tier"], "independent_verified")
                pkts = self.packets(out)
                self.assertTrue(pkts)
                src = self.packets(self.tmp / f"in.{ext}")
                self.assertLess(len(pkts), len(src))
                if ext != "wav":
                    self.assertIn("K", pkts[0][3])
                    self.assertEqual(int(pkts[0][1]), 0)
                    dts = [int(p[1]) for p in pkts]
                    self.assertEqual(dts, sorted(dts))
                else:
                    dur = float(self.probe(out, "-show_entries", "format=duration")["format"]["duration"])
                    self.assertAlmostEqual(dur, 1.0, places=3)

    def test_mp4_metadata_native_preserves_frames(self):
        out = self.tmp / "meta.mp4"
        res, executed = self.native("-json", "-y", "-i", "in.mp4", "-metadata", "title=Hello",
                                    "-metadata", "artist=Lean", "-c", "copy", out)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        tags = self.probe(out, "-show_entries", "format_tags")["format"]["tags"]
        self.assertEqual(tags.get("title"), "Hello")
        self.assertEqual(tags.get("artist"), "Lean")
        self.assertEqual(self.framemd5(out), self.framemd5(self.tmp / "in.mp4"))

    def test_invalid_inputs_fail_closed_without_output(self):
        for name, payload in (("bad.mp4", b"garbage" * 10), ("bad.ivf", b"DKIF" + b"\0" * 10),
                              ("bad.wav", b"RIFF\0\0\0\0WAVE"), ("bad.flac", b"fLaC\0"),
                              ("bad.mkv", b"\x1a\x45\xdf\xa3" + b"\0" * 8)):
            with self.subTest(name=name):
                (self.tmp / name).write_bytes(payload)
                out = self.tmp / ("o_" + name)
                res, executed = self.native("-json", "-y", "-i", name, "-c", "copy", out)
                self.assertNotEqual(res.returncode, 0)
                self.assertFalse(executed)
                self.assertFalse(out.exists())
                self.assertFalse(json.loads(res.stdout)["ok"])
        trunc = self.tmp / "trunc.mp4"
        trunc.write_bytes((self.tmp / "in.mp4").read_bytes()[:3000])
        res, executed = self.native("-json", "-y", "-i", trunc, "-c", "copy", self.tmp / "t.mp4")
        self.assertNotEqual(res.returncode, 0)
        self.assertFalse(executed)

    def test_unsupported_combinations_are_explicitly_delegated(self):
        cases = [
            ["-i", "in.mp4", "-metadata", "genre=x", "-c", "copy", "o.mp4"],
            ["-i", "in.mkv", "-c", "copy", "o.webm"],
            ["-i", "in.mp4", "-c", "copy", "o.mkv"],
            ["-ss", "1", "-i", "in.flac", "-c", "copy", "o.flac"],
            ["-ss", "1", "-i", "in.mkv", "-c", "copy", "o.mkv"],
        ]
        for argv in cases:
            with self.subTest(argv=argv):
                res = subprocess.run([str(BINARY), "plan", "-y", *argv], capture_output=True, text=True, cwd=self.tmp)
                backend = json.loads(res.stdout)["backend"]
                self.assertEqual(backend["tier"], "delegated_faithful")
        res, _ = self.native("-json", "-y", "-i", "av.mp4", "-c", "copy", "o.mp4")
        lines = [l for l in res.stdout.splitlines() if l.startswith("{")]
        if res.returncode == 0:
            self.assertTrue(lines)
            doc = json.loads(lines[-1])
            self.assertEqual(doc["mode"], "ffmpeg-cli-delegated-faithful")
            self.assertEqual(doc["tier"], "delegated_faithful")
        else:
            self.assertNotIn("ffmpeg-cli-native-copy", res.stdout)

    def test_native_introspection_zero_exec(self):
        for flag in INTROSPECTION:
            with self.subTest(flag=flag):
                res, executed = self.native(flag)
                self.assertEqual(res.returncode, 0, res.stderr)
                self.assertFalse(executed)
                self.assertTrue(res.stdout.strip())
        res, executed = self.native("-hide_banner", "-formats")
        self.assertEqual(res.returncode, 0)
        self.assertFalse(executed)
        self.assertIn("ivf", res.stdout)


if __name__ == "__main__":
    unittest.main()
