"""M1-B / M1-B2 native independent_verified stream copy: zero-exec, multi-track, trim, and adversarial coverage."""
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
        cls.tmp = Path(tempfile.mkdtemp(prefix="m1b2-native-"))
        src = "testsrc=size=64x64:rate=10:duration=2.5"
        tone48 = "sine=frequency=440:sample_rate=48000:duration=2.5"
        tone44 = "sine=frequency=880:sample_rate=44100:duration=2.5"
        srt = cls.tmp / "cues.srt"
        srt.write_text(
            "1\n00:00:00,200 --> 00:00:01,000\nFirst cue\n\n"
            "2\n00:00:01,200 --> 00:00:02,200\nSecond cue\n"
        )
        gens = {
            "in.mp4": ["-f", "lavfi", "-i", src, "-c:v", "libx264", "-g", "5", "-bf", "0", "-an"],
            "in.ivf": ["-f", "lavfi", "-i", src, "-c:v", "libvpx-vp9", "-g", "5"],
            "in.wav": ["-f", "lavfi", "-i", tone48, "-c:a", "pcm_s16le"],
            "in.flac": ["-f", "lavfi", "-i", tone48, "-c:a", "flac"],
            "in.webm": ["-f", "lavfi", "-i", src, "-c:v", "libvpx-vp9", "-g", "5"],
            "in.mkv": ["-f", "lavfi", "-i", src, "-c:v", "libx264", "-g", "5"],
            "av.mp4": [
                "-f", "lavfi", "-i", src, "-f", "lavfi", "-i", tone48, "-f", "lavfi", "-i", tone44,
                "-map", "0:v:0", "-map", "1:a:0", "-map", "2:a:0",
                "-c:v", "libx264", "-g", "10", "-bf", "2",
                "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709",
                "-c:a:0", "aac", "-c:a:1", "libopus", "-strict", "-2",
            ],
            "prores_pcm.mov": [
                "-f", "lavfi", "-i", src, "-f", "lavfi", "-i", tone48,
                "-c:v", "prores_ks", "-c:a", "pcm_s24le",
            ],
            "multi.mkv": [
                "-f", "lavfi", "-i", src, "-f", "lavfi", "-i", tone48, "-i", str(srt),
                "-map", "0:v", "-map", "1:a", "-map", "2:s",
                "-c:v", "libx264", "-g", "10", "-c:a", "libopus", "-c:s", "srt",
            ],
            "multi.webm": [
                "-f", "lavfi", "-i", src, "-f", "lavfi", "-i", tone48,
                "-c:v", "libvpx-vp9", "-g", "10", "-c:a", "libopus",
            ],
            "frag.mp4": [
                "-f", "lavfi", "-i", src, "-c:v", "libx264",
                "-movflags", "frag_keyframe+empty_moov",
            ],
            "adpcm.wav": ["-f", "lavfi", "-i", tone48, "-c:a", "adpcm_ima_wav"],
        }
        for name, args in gens.items():
            res = subprocess.run([FFMPEG, "-v", "error", "-y", *args, str(cls.tmp / name)], capture_output=True)
            if res.returncode != 0:
                raise unittest.SkipTest(f"fixture generation failed for {name}: {res.stderr[-300:]}")
        # Optional AV1 IVF fixture if SVT-AV1 or libaom-av1 is available
        cls.has_av1_ivf = False
        for av1_enc in ("libsvtav1", "libaom-av1"):
            extra = ["-cpu-used", "8"] if av1_enc == "libaom-av1" else []
            res = subprocess.run(
                [FFMPEG, "-v", "error", "-y", "-f", "lavfi",
                 "-i", "testsrc=size=64x64:rate=10:duration=3.0",
                 "-c:v", av1_enc, *extra, "-g", "10", str(cls.tmp / "av1.ivf")],
                capture_output=True,
            )
            if res.returncode == 0:
                cls.has_av1_ivf = True
                break

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

    def packets(self, path, *extra):
        doc = self.probe(path, "-show_packets", "-show_entries", "packet=pts,dts,size,flags,stream_index", *extra)
        return [(p.get("pts"), p.get("dts"), p.get("size"), p.get("flags"), p.get("stream_index"))
                for p in doc.get("packets", [])]

    def framemd5(self, path, *extra):
        res = subprocess.run([FFMPEG, "-v", "error", "-i", str(path), *extra, "-f", "framemd5", "-"],
                             capture_output=True, text=True)
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

    def test_native_trim_mp4_ivf_wav_flac_mkv_webm(self):
        for ext in ("mp4", "ivf", "wav", "flac", "mkv", "webm"):
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
                self.assertTrue(self.framemd5(out))
                if ext == "wav":
                    dur = float(self.probe(out, "-show_entries", "format=duration")["format"]["duration"])
                    self.assertAlmostEqual(dur, 1.0, places=5)
                elif ext == "flac":
                    self.assertEqual(int(pkts[0][0]), 0)
                else:
                    self.assertIn("K", pkts[0][3])
                    ts0 = pkts[0][1] if pkts[0][1] is not None else pkts[0][0]
                    self.assertEqual(int(ts0), 0)
                    if all(p[1] is not None for p in pkts):
                        dts = [int(p[1]) for p in pkts]
                        self.assertEqual(dts, sorted(dts))

    def test_multitrack_mp4_bframes_colr_stream_selection_and_trim(self):
        # Default FFmpeg stream copy (1 video + 1 audio)
        out_def = self.tmp / "av_def.mp4"
        res, executed = self.native("-json", "-y", "-i", "av.mp4", "-c", "copy", out_def)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertEqual(json.loads(res.stdout)["tier"], "independent_verified")
        ref_def = self.tmp / "av_ref_def.mp4"
        self.assertEqual(self.ref("-i", self.tmp / "av.mp4", "-c", "copy", ref_def).returncode, 0)
        self.assertEqual(self.framemd5(out_def), self.framemd5(ref_def))

        # -map 0 preserves all 3 tracks (H.264 B-frames + 48 kHz AAC + 44.1 kHz Opus) + colr atom
        out_all = self.tmp / "av_all.mp4"
        res, executed = self.native("-json", "-y", "-i", "av.mp4", "-map", "0", "-c", "copy", out_all)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        streams = self.probe(out_all, "-show_streams")["streams"]
        self.assertEqual([s["codec_name"] for s in streams], ["h264", "aac", "opus"])
        self.assertEqual(streams[0].get("color_space"), "bt709")
        for spec in ("0:v:0", "0:a:0", "0:a:1"):
            self.assertEqual(self.framemd5(out_all, "-map", spec),
                             self.framemd5(self.tmp / "av.mp4", "-map", spec))

        # -an, -vn, and -map 0:a:1
        out_an = self.tmp / "av_an.mp4"
        res, executed = self.native("-json", "-y", "-i", "av.mp4", "-an", "-c", "copy", out_an)
        self.assertEqual(res.returncode, 0)
        self.assertFalse(executed)
        self.assertEqual([s["codec_type"] for s in self.probe(out_an, "-show_streams")["streams"]], ["video"])

        out_a1 = self.tmp / "av_a1.mp4"
        res, executed = self.native("-json", "-y", "-i", "av.mp4", "-map", "0:a:1", "-c", "copy", out_a1)
        self.assertEqual(res.returncode, 0)
        self.assertFalse(executed)
        st_a1 = self.probe(out_a1, "-show_streams")["streams"]
        self.assertEqual(len(st_a1), 1)
        self.assertEqual(st_a1[0]["codec_name"], "opus")

        # Multi-track B-frame trim with edts/elst pre-roll
        out_trim = self.tmp / "av_trim.mp4"
        res, executed = self.native("-json", "-y", "-ss", "1.2", "-t", "0.8", "-i", "av.mp4",
                                    "-map", "0", "-c", "copy", out_trim)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertTrue(self.framemd5(out_trim, "-map", "0:v:0"))
        self.assertTrue(self.framemd5(out_trim, "-map", "0:a:0"))

    def test_mov_prores_and_fixed_stsz_pcm_copy_and_trim(self):
        # 2.5s @ 48 kHz = 120,000 fixed-size PCM samples (>65536 stsc chunk sample count)
        out_mov = self.tmp / "prores_out.mov"
        res, executed = self.native("-json", "-y", "-i", "prores_pcm.mov", "-c", "copy", out_mov)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertEqual(self.framemd5(out_mov, "-map", "0:v:0"),
                         self.framemd5(self.tmp / "prores_pcm.mov", "-map", "0:v:0"))
        self.assertEqual(self.framemd5(out_mov, "-map", "0:a:0"),
                         self.framemd5(self.tmp / "prores_pcm.mov", "-map", "0:a:0"))

        out_trim = self.tmp / "prores_trim.mov"
        res, executed = self.native("-json", "-y", "-ss", "0.5", "-t", "1.0",
                                    "-i", "prores_pcm.mov", "-c", "copy", out_trim)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        dur = float(self.probe(out_trim, "-show_entries", "format=duration")["format"]["duration"])
        self.assertAlmostEqual(dur, 1.0, delta=0.15)
        self.assertTrue(self.framemd5(out_trim, "-map", "0:a:0"))

    def test_mkv_and_webm_multitrack_selection_and_trim(self):
        # Multi-track MKV (video + audio + subtitle)
        out_mkv = self.tmp / "multi_out.mkv"
        res, executed = self.native("-json", "-y", "-i", "multi.mkv", "-map", "0", "-c", "copy", out_mkv)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertEqual([s["codec_type"] for s in self.probe(out_mkv, "-show_streams")["streams"]],
                         ["video", "audio", "subtitle"])

        # Audio-only extraction with Opus negative pre-skip timestamp rebasing
        out_a = self.tmp / "mkv_audio.mkv"
        res, executed = self.native("-json", "-y", "-i", "multi.mkv", "-vn", "-sn", "-c", "copy", out_a)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertEqual([s["codec_type"] for s in self.probe(out_a, "-show_streams")["streams"]], ["audio"])
        self.assertTrue(self.framemd5(out_a))

        # Multi-track MKV trim
        out_trim = self.tmp / "mkv_trim.mkv"
        res, executed = self.native("-json", "-y", "-ss", "1.2", "-t", "0.8", "-i", "multi.mkv",
                                    "-map", "0", "-c", "copy", out_trim)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertTrue(self.framemd5(out_trim, "-map", "0:v:0"))

        # Multi-track WebM VP9 + Opus trim + -an
        out_webm = self.tmp / "webm_trim_v.webm"
        res, executed = self.native("-json", "-y", "-ss", "1.2", "-t", "0.8", "-i", "multi.webm",
                                    "-an", "-c", "copy", out_webm)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        self.assertEqual([s["codec_type"] for s in self.probe(out_webm, "-show_streams")["streams"]], ["video"])
        self.assertTrue(self.framemd5(out_webm))

    def test_wav_all_pcm_bit_depths_float_extensible_and_chunks(self):
        tone = "sine=frequency=440:sample_rate=48000:duration=2.0"
        specs = [
            ("pcm_u8", "u8", 1),
            ("pcm_s24le", "s24le", 3),
            ("pcm_s32le", "s32le", 4),
            ("pcm_f32le", "f32le", 4),
            ("pcm_f64le", "f64le", 8),
        ]
        for codec, raw_fmt, bps in specs:
            with self.subTest(codec=codec):
                src_wav = self.tmp / f"src_{codec}.wav"
                self.assertEqual(
                    self.ref("-f", "lavfi", "-i", tone, "-metadata", "artist=LeanWAV", "-c:a", codec, src_wav).returncode,
                    0,
                )
                out_wav = self.tmp / f"trim_{codec}.wav"
                res, executed = self.native("-json", "-y", "-ss", "0.5", "-t", "0.75",
                                            "-i", src_wav, "-c", "copy", out_wav)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertFalse(executed)
                pf = self.probe(out_wav, "-show_format", "-show_streams")
                self.assertAlmostEqual(float(pf["format"]["duration"]), 0.75, places=6)
                self.assertEqual(pf["format"].get("tags", {}).get("artist"), "LeanWAV")
                full_pcm = subprocess.check_output([FFMPEG, "-v", "error", "-i", str(src_wav), "-f", raw_fmt, "-"])
                nat_pcm = subprocess.check_output([FFMPEG, "-v", "error", "-i", str(out_wav), "-f", raw_fmt, "-"])
                self.assertEqual(nat_pcm, full_pcm[24000 * bps : 60000 * bps])

        # 5.1 surround WAVE_FORMAT_EXTENSIBLE (0xFFFE)
        src_5p1 = self.tmp / "src_5p1.wav"
        self.assertEqual(self.ref("-f", "lavfi", "-i", tone, "-ac", "6", "-c:a", "pcm_s24le", src_5p1).returncode, 0)
        out_5p1 = self.tmp / "trim_5p1.wav"
        res, executed = self.native("-json", "-y", "-ss", "0.25", "-t", "0.5", "-i", src_5p1, "-c", "copy", out_5p1)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        pf51 = self.probe(out_5p1, "-show_format", "-show_streams")
        self.assertEqual(pf51["streams"][0]["channels"], 6)
        self.assertAlmostEqual(float(pf51["format"]["duration"]), 0.5, places=6)

    def test_av1_ivf_keyframe_snap_and_post_snap_duration_window(self):
        # VP9 IVF post-snap window: keyframe interval 5 @ 10fps -> keyframes at 0.0s, 0.5s, 1.0s...
        # -ss 0.8 -t 0.2 snaps back to 0.5s keyframe and keeps [0.5s, 1.0s) = 5 packets (not [0.5s, 0.7s) = 2 packets)
        out_vp9 = self.tmp / "vp9_snap.ivf"
        res, executed = self.native("-json", "-y", "-ss", "0.8", "-t", "0.2", "-i", "in.ivf", "-c", "copy", out_vp9)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertFalse(executed)
        vp9_pkts = self.packets(out_vp9)
        self.assertEqual(len(vp9_pkts), 5)
        self.assertIn("K", vp9_pkts[0][3])

        if self.has_av1_ivf:
            # AV1 IVF: keyframe interval 10 @ 10fps -> keyframes at 0.0s, 1.0s, 2.0s
            # -ss 1.5 -t 0.5 snaps back to 1.0s keyframe and keeps [1.0s, 2.0s) = 10 packets
            out_av1 = self.tmp / "av1_snap.ivf"
            res, executed = self.native("-json", "-y", "-ss", "1.5", "-t", "0.5",
                                        "-i", "av1.ivf", "-c", "copy", out_av1)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertFalse(executed)
            av1_pkts = self.packets(out_av1)
            self.assertEqual(len(av1_pkts), 10)
            self.assertIn("K", av1_pkts[0][3])
            self.assertEqual(len(self.framemd5(out_av1)), 10)

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

    def test_invalid_and_adversarial_inputs_fail_closed_without_output(self):
        raw_mkv = (self.tmp / "multi.mkv").read_bytes()
        raw_wav = (self.tmp / "in.wav").read_bytes()
        raw_flac = bytearray((self.tmp / "in.flac").read_bytes())
        raw_flac[-12] ^= 0xFF
        adversarial = [
            ("bad.mp4", b"garbage" * 10),
            ("bad.ivf", b"DKIF" + b"\0" * 10),
            ("bad.wav", b"RIFF\0\0\0\0WAVE"),
            ("trunc.wav", raw_wav[:-64]),
            ("bad.flac", b"fLaC\0"),
            ("corrupt_crc.flac", bytes(raw_flac)),
            ("bad.mkv", b"\x1a\x45\xdf\xa3" + b"\0" * 8),
            ("trunc_mid.mkv", raw_mkv[: len(raw_mkv) // 2]),
            ("trunc.mp4", (self.tmp / "in.mp4").read_bytes()[:3000]),
        ]
        for name, payload in adversarial:
            with self.subTest(name=name):
                (self.tmp / name).write_bytes(payload)
                out = self.tmp / ("o_" + name)
                res, executed = self.native("-json", "-y", "-i", name, "-c", "copy", out)
                self.assertNotEqual(res.returncode, 0, f"{name} unexpectedly succeeded")
                self.assertFalse(executed)
                self.assertFalse(out.exists())
                self.assertFalse(json.loads(res.stdout)["ok"])

        # Out-of-range explicit -map must fail closed without spawning FFmpeg
        out_badmap = self.tmp / "badmap.mp4"
        res, executed = self.native("-json", "-y", "-i", "in.mp4", "-map", "0:a:0", "-c", "copy", out_badmap)
        self.assertNotEqual(res.returncode, 0)
        self.assertFalse(executed)
        self.assertFalse(out_badmap.exists())

    def test_unsupported_combinations_are_explicitly_delegated(self):
        cases = [
            ["-i", "in.mp4", "-metadata", "genre=x", "-c", "copy", "o.mp4"],
            ["-i", "in.mkv", "-c", "copy", "o.webm"],
            ["-i", "in.mp4", "-c", "copy", "o.mkv"],
            ["-i", "in.flac", "-metadata", "title=x", "-c", "copy", "o.flac"],
            ["-i", "in.mkv", "-metadata", "title=x", "-c", "copy", "o.mkv"],
        ]
        for argv in cases:
            with self.subTest(argv=argv):
                res = subprocess.run([str(BINARY), "plan", "-y", *argv], capture_output=True, text=True, cwd=self.tmp)
                backend = json.loads(res.stdout)["backend"]
                self.assertEqual(backend["tier"], "delegated_faithful")

        # Fragmented MP4 (moof/mvex) and non-PCM WAV (ADPCM) demote cleanly to delegated_faithful
        for src_name, out_name in (("frag.mp4", "o_frag.mp4"), ("adpcm.wav", "o_adpcm.wav")):
            with self.subTest(src=src_name):
                res = subprocess.run([str(BINARY), "plan", "-y", "-i", src_name, "-c", "copy", out_name],
                                     capture_output=True, text=True, cwd=self.tmp)
                backend = json.loads(res.stdout)["backend"]
                self.assertEqual(backend["tier"], "delegated_faithful")
                self.assertEqual(backend["reasons"], ["native_stream_copy_layout_unsupported"])

        # Multi-track av.mp4 and single-track in.mp4 are both independent_verified in M1-B2
        for src_name in ("in.mp4", "av.mp4"):
            res = subprocess.run([str(BINARY), "plan", "-y", "-i", src_name, "-c", "copy", "o.mp4"],
                                 capture_output=True, text=True, cwd=self.tmp)
            self.assertEqual(json.loads(res.stdout)["backend"]["tier"], "independent_verified")

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
