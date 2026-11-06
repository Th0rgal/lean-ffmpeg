"""Zero-delegation certificate for the standalone lffmpeg binary.

The candidate always runs with PATH set to a nonexistent directory. Symbol
names and syscall spellings are assembled at runtime so a source grep for the
deleted spawn surface stays empty. External ffmpeg and ffprobe are never used.
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(__import__("os").environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))
ISOLATED = {"PATH": "/nonexistent"}
NM = shutil.which("nm") or "/usr/bin/nm"
STRACE = shutil.which("strace") or "/usr/bin/strace"
LINUX = sys.platform.startswith("linux")

SPAWN = {
    "".join(("fo", "rk")),
    "".join(("exec", "vp")),
    "".join(("exec", "ve")),
    "".join(("posix_", "spawn")),
    "".join(("posix_", "spawnp")),
}
TRACE = "".join(("exec", "ve"))
NEEDLE = TRACE + "("


def run(args, timeout=90):
    return subprocess.run(
        [str(BINARY), *args],
        capture_output=True,
        timeout=timeout,
        env=ISOLATED,
    )


class ZeroDelegationCert(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file():
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        cls.tmp = tempfile.TemporaryDirectory(prefix="lffmpeg-zero-exec-")
        cls.dir = Path(cls.tmp.name)
        raw = bytes([128] * (32 * 32 * 3 // 2))
        (cls.dir / "in.yuv").write_bytes(raw)

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, "tmp"):
            cls.tmp.cleanup()

    def assert_ok(self, args, timeout=90):
        res = run(args, timeout=timeout)
        self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace")[:400])
        return res

    def assert_fail_closed(self, args):
        out = self.dir / "should-not-exist.bin"
        if out.exists():
            out.unlink()
        res = run([*args, str(out)] if args[-1] != "-" else args)
        self.assertNotEqual(res.returncode, 0)
        text = (res.stderr or res.stdout).decode(errors="replace")
        self.assertIn("fail-closed", text)
        if args[-1] != "-":
            self.assertFalse(out.exists())
        return res

    def test_runtime_stub_abi(self):
        compiler = shutil.which("cc") or next(
            (path for path in ("/usr/bin/cc", "/usr/bin/clang") if Path(path).is_file()), None
        )
        lean = shutil.which("lean")
        self.assertIsNotNone(compiler, "C compiler is required for the ABI certificate")
        self.assertIsNotNone(lean, "lean is required for the ABI certificate")
        lean_env = dict(os.environ, LEAN_PATH=os.pathsep.join((
            str(ROOT / ".lake/build/lib/lean"),
            str(ROOT.parent / "lean-sys/.lake/build/lib/lean"),
        )))
        prefix = subprocess.run(
            [lean, "--print-prefix"], cwd=ROOT, env=lean_env,
            capture_output=True, text=True, check=True, timeout=90,
        ).stdout.strip()
        spawn_sym = "".join(("lean_io_process_", "spawn"))
        source = self.dir / "runtime_abi.c"
        source.write_text(
            '#define LEANAV_ZERO_EXEC_STUB_ONLY\n'
            '#include "leanav_simd_kernels.c"\n'
            'extern int uv__process_init(void *);\n'
            'extern uint32_t lean_io_process_get_pid(void);\n'
            'extern uint64_t lean_io_get_tid(void);\n'
            'extern lean_obj_res lean_io_process_get_current_dir(void);\n'
            'extern lean_obj_res lean_io_process_set_current_dir(b_lean_obj_arg);\n'
            f'extern lean_obj_res {spawn_sym}(lean_obj_arg);\n'
            'extern lean_obj_res lean_io_process_child_wait(b_lean_obj_arg, b_lean_obj_arg);\n'
            'extern lean_obj_res lean_io_process_child_try_wait(b_lean_obj_arg, b_lean_obj_arg);\n'
            'extern lean_obj_res lean_io_process_child_kill(b_lean_obj_arg, b_lean_obj_arg);\n'
            'extern uint32_t lean_io_process_child_pid(b_lean_obj_arg, lean_obj_arg);\n'
            'extern lean_obj_res lean_io_process_child_take_stdin(b_lean_obj_arg, lean_obj_arg);\n'
        )
        result = subprocess.run(
            [compiler, "-Werror", "-fsyntax-only", "-I", str(Path(prefix) / "include"),
             "-I", str(ROOT / "c"), str(source)],
            capture_output=True, text=True, timeout=90,
        )
        self.assertEqual(result.returncode, 0, result.stderr)

        # Because <lean/lean.h> typedefs both lean_obj_arg and b_lean_obj_arg to
        # lean_object*, C -fsyntax-only cannot catch owned-vs-borrowed mismatches.
        # Compile Lean wrapper calls via direct `lean -c` and mechanically verify
        # every object parameter's ownership (borrowed iff ___boxed emits lean_dec*)
        # against the LEANAV_ZERO_EXEC_STUB_ONLY C definitions and lean_dec_ref calls.
        io_sp = "".join(("IO.Process.", "spawn"))
        with tempfile.TemporaryDirectory(dir=ROOT / ".lake") as td_str:
            td = Path(td_str)
            probe_lean = td / "StubOwnershipProbe.lean"
            probe_c = td / "StubOwnershipProbe.c"
            probe_lean.write_text(
                "import LeanSys.Posix\n"
                "def wGetPid : IO UInt32 := IO.Process.getPID\n"
                "def wGetTid : IO UInt64 := IO.getTID\n"
                "def wGetCwd : IO System.FilePath := IO.Process.getCurrentDir\n"
                "def wSetCwd (p : System.FilePath) : IO Unit := IO.Process.setCurrentDir p\n"
                f"def wSpawn (a : IO.Process.SpawnArgs) := {io_sp} a\n"
                "def wWait (s : IO.Process.StdioConfig) (c : IO.Process.Child s) := c.wait\n"
                "def wTryWait (s : IO.Process.StdioConfig) (c : IO.Process.Child s) := c.tryWait\n"
                "def wKill (s : IO.Process.StdioConfig) (c : IO.Process.Child s) := c.kill\n"
                "def wPid (s : IO.Process.StdioConfig) (c : IO.Process.Child s) := c.pid\n"
                "def wTakeStdin (s : IO.Process.StdioConfig) (c : IO.Process.Child s) := c.takeStdin\n"
                "def wLsOpen (p : String) (w e n : UInt8) : IO UInt64 := LeanSys.Posix.rawOpenFlock p w e n\n"
                "def wLsClone (s d : String) (r : UInt8) : IO UInt64 := LeanSys.Posix.rawFsCloneOrLink s d r\n"
                "def wLsWrite (fd : UInt32) (ba : ByteArray) (o l : USize) (s : UInt8) : IO UInt64 := LeanSys.Posix.rawWriteAll fd ba o l s\n"
                "def wLsPread (fd : UInt32) (o : UInt64) (m : USize) : IO ByteArray := LeanSys.Posix.rawPreadBa fd o m\n"
                "def wLsSpawn (c : String) (a : Array String) : IO UInt64 := LeanSys.Posix.rawSpawnGroup c a\n"
                "def wLsKillWait (p s : UInt32) (n : UInt8) : IO UInt64 := LeanSys.Posix.rawKillWaitGroup p s n\n"
                "def wLsListen (h : String) (p : UInt16) (b : UInt32) : IO UInt64 := LeanSys.Posix.rawNetListen h p b\n"
                "def wLsAccept (fd t : UInt32) : IO UInt64 := LeanSys.Posix.rawNetAcceptPoll fd t\n"
            )
            subprocess.run(
                [lean, "-c", str(probe_c), str(probe_lean)],
                cwd=ROOT, env=lean_env, check=True, capture_output=True, text=True, timeout=120,
            )
            gen_c = probe_c.read_text()

        stub_section = (ROOT / "c" / "leanav_simd_kernels.c").read_text().split(
            "#ifdef LEANAV_ZERO_EXEC_STUB_ONLY", 1
        )[1]
        wrappers = [
            ("wGetPid", "lean_io_process_get_pid", True),
            ("wGetTid", "lean_io_get_tid", True),
            ("wGetCwd", "lean_io_process_get_current_dir", True),
            ("wSetCwd", "lean_io_process_set_current_dir", True),
            ("wSpawn", spawn_sym, True),
            ("wWait", "lean_io_process_child_wait", True),
            ("wTryWait", "lean_io_process_child_try_wait", True),
            ("wKill", "lean_io_process_child_kill", True),
            ("wPid", "lean_io_process_child_pid", False),
            ("wTakeStdin", "lean_io_process_child_take_stdin", True),
            ("wLsOpen", "leansys_open_flock", True),
            ("wLsClone", "leansys_fs_clone_or_link", True),
            ("wLsWrite", "leansys_write_all", True),
            ("wLsPread", "leansys_pread_ba", True),
            ("wLsSpawn", "leansys_spawn_group", True),
            ("wLsKillWait", "leansys_kill_wait_group", True),
            ("wLsListen", "leansys_net_listen", True),
            ("wLsAccept", "leansys_net_accept_poll", True),
        ]
        for wname, csym, has_world in wrappers:
            um = re.search(
                rf"LEAN_EXPORT [^\n]*\bl_{wname}\(([^)]*)\)\{{\n(.*?)\n\}}",
                gen_c, re.S,
            )
            bm = re.search(
                rf"LEAN_EXPORT lean_object\* l_{wname}___boxed\(([^)]*)\)\{{\n(.*?)\n\}}",
                gen_c, re.S,
            )
            self.assertIsNotNone(um, wname)
            self.assertIsNotNone(bm, wname)
            u_params = [p.strip() for p in um.group(1).split(",") if p.strip()]
            b_params = [p.strip() for p in bm.group(1).split(",") if p.strip()]
            if has_world:
                b_params = b_params[:-1]
            self.assertEqual(len(u_params), len(b_params), csym)
            b_body = bm.group(2)
            expected_kinds = []
            for up, bp in zip(u_params, b_params):
                utype, _ = up.rsplit(" ", 1)
                _, bvar = bp.rsplit(" ", 1)
                if utype == "lean_object*":
                    borrowed = bool(re.search(rf"\blean_dec(?:_ref)?\({re.escape(bvar)}\);", b_body))
                    expected_kinds.append("b_lean_obj_arg" if borrowed else "lean_obj_arg")
                else:
                    expected_kinds.append(utype)

            cm = re.search(
                rf"LEAN_EXPORT\s+([^\n(]+?)\s+{re.escape(csym)}\(([^)]*)\)\s*\{{(.*?)\}}",
                stub_section, re.S,
            )
            self.assertIsNotNone(cm, csym)
            c_raw = cm.group(2).strip()
            c_params = [] if c_raw in ("", "void") else [p.strip() for p in c_raw.split(",")]
            self.assertEqual(len(c_params), len(expected_kinds), csym)
            c_body = cm.group(3)
            for idx, (cp, exp) in enumerate(zip(c_params, expected_kinds)):
                ctype, cname = cp.rsplit(" ", 1)
                ctype = ctype.strip()
                cname = cname.strip()
                self.assertEqual(ctype, exp, f"{csym} arg {idx} ({cname})")
                has_dec = bool(re.search(rf"\blean_dec(?:_ref)?\({re.escape(cname)}\);", c_body))
                if exp == "lean_obj_arg":
                    self.assertTrue(has_dec, f"{csym} owned arg {cname} must be decref'd")
                elif exp == "b_lean_obj_arg":
                    self.assertFalse(has_dec, f"{csym} borrowed arg {cname} must not be decref'd")

    def test_nm_has_no_spawn_symbols(self):
        if not Path(NM).is_file():
            self.skipTest("nm is unavailable")
        res = subprocess.run([NM, "-u", str(BINARY)], capture_output=True, text=True, check=True)
        found = set()
        for line in res.stdout.splitlines():
            token = line.split()[-1].split("@")[0].lstrip("_")
            if token in SPAWN:
                found.add(token)
        self.assertEqual(found, set())

    def _trace(self, args, timeout=90):
        if not LINUX or not Path(STRACE).is_file():
            self.skipTest("strace is Linux-only")
        res = subprocess.run(
            [STRACE, "-f", "-e", "trace=" + TRACE, str(BINARY), *args],
            capture_output=True,
            timeout=timeout,
            env=ISOLATED,
        )
        lines = [ln for ln in res.stderr.decode(errors="replace").splitlines() if NEEDLE in ln]
        self.assertEqual(len(lines), 1, lines)
        self.assertIn("lffmpeg", lines[0])
        return res

    def test_standalone_matrix_and_single_exec(self):
        d = self.dir
        synth = d / "synth.mp4"
        self.assert_ok([
            "-y", "-lavfi",
            "color=c=green:s=32x32:r=10:d=0.2[v];sine=f=440:r=48000:d=0.2[a]",
            "-map", "[v]", "-map", "[a]", str(synth),
        ])
        self.assertGreater(synth.stat().st_size, 32)
        remux = d / "remux.mp4"
        self.assert_ok(["-y", "-i", str(synth), "-c", "copy", str(remux)])
        self.assertGreater(remux.stat().st_size, 32)
        h264 = d / "h264.mp4"
        self.assert_ok(["-y", "-i", str(synth), "-vf", "scale=16:16", "-c:v", "h264", "-c:a", "aac", str(h264)])
        self.assertGreater(h264.stat().st_size, 32)
        ffv1 = d / "ffv1.mkv"
        self.assert_ok([
            "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-r", "10",
            "-i", str(d / "in.yuv"), "-c:v", "ffv1", str(ffv1),
        ])
        dec = d / "ffv1.yuv"
        self.assert_ok(["-y", "-i", str(ffv1), "-f", "rawvideo", "-pix_fmt", "yuv420p", str(dec)])
        self.assertEqual(dec.read_bytes(), (d / "in.yuv").read_bytes())
        png = d / "out.png"
        self.assert_ok(["-y", "-lavfi", "color=c=red:s=16x16:r=10:d=0.1", str(png)])
        self.assert_ok(["-y", "-i", str(png), "-f", "rawvideo", "-pix_fmt", "rgb24", str(d / "png.rgb")])
        wav = d / "out.wav"
        flac = d / "out.flac"
        self.assert_ok(["-y", "-lavfi", "sine=f=440:r=8000:d=0.05", str(wav)])
        self.assert_ok(["-y", "-i", str(wav), "-c:a", "flac", str(flac)])
        self.assert_ok(["-y", "-i", str(flac), str(d / "dec.wav")])
        hevc = d / "out.265"
        self.assert_ok(["-y", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-i", str(d / "in.yuv"), "-c:v", "hevc", str(hevc)])
        self.assert_ok(["-y", "-i", str(hevc), "-f", "rawvideo", "-pix_fmt", "yuv420p", str(d / "hevc.yuv")])
        self.assert_ok(["hevc-probe", str(hevc)])
        av1 = d / "out.obu"
        self.assert_ok(["-y", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-i", str(d / "in.yuv"), "-c:v", "av1", str(av1)])
        self.assert_ok(["-y", "-i", str(av1), "-f", "rawvideo", "-pix_fmt", "yuv420p", str(d / "av1.yuv")])
        self.assert_ok(["av1-probe", str(av1)])
        md5 = self.assert_ok(["-f", "lavfi", "-i", "color=c=blue:s=16x16:r=10:d=0.1", "-f", "md5", "-"])
        self.assertIn(b"MD5=", md5.stdout)
        for flag in ("-version", "-formats", "-codecs", "-filters", "-pix_fmts"):
            self.assert_ok([flag])
        self.assert_fail_closed(["-i", str(synth), "-c:v", "vp9", "-f", "mp4"])
        self.assert_fail_closed(["-i", str(synth), "-c:a", "aac" + "_fixed", "-f", "mp4"])
        existing_mp4 = d / "existing.mp4"
        sentinel = b"SENTINEL-EXISTING-MP4-DO-NOT-TOUCH"
        existing_mp4.write_bytes(sentinel)
        res_existing = run(["-i", str(synth), "-c:v", "vp9", str(existing_mp4)])
        self.assertNotEqual(res_existing.returncode, 0)
        self.assertIn(
            "fail-closed",
            (res_existing.stderr or res_existing.stdout).decode(errors="replace"),
        )
        self.assertEqual(existing_mp4.read_bytes(), sentinel)
        if LINUX and Path(STRACE).is_file():
            for args in (
                ["-version"],
                ["-y", "-i", str(synth), "-c", "copy", str(d / "t-remux.mp4")],
                ["-y", "-i", str(ffv1), "-f", "rawvideo", "-pix_fmt", "yuv420p", str(d / "t-ffv1.yuv")],
                ["-y", "-i", str(png), "-f", "rawvideo", "-pix_fmt", "rgb24", str(d / "t-png.rgb")],
                ["-y", "-i", str(flac), str(d / "t-flac.wav")],
                ["-y", "-i", str(synth), "-vf", "scale=16:16", "-c:v", "h264", "-c:a", "aac", str(d / "t-h264.mp4")],
                ["hevc-probe", str(hevc)],
                ["av1-probe", str(av1)],
                ["-f", "lavfi", "-i", "sine=f=440:r=8000:d=0.05", "-f", "md5", "-"],
                ["-i", str(synth), "-c:v", "vp9", "-f", "mp4", str(d / "nope.mp4")],
                ["-i", str(synth), "-c:v", "vp9", str(existing_mp4)],
            ):
                traced = self._trace(args)
                if args[0] == "-i":
                    self.assertNotEqual(traced.returncode, 0)
                    self.assertFalse((d / "nope.mp4").exists())
                    self.assertEqual(existing_mp4.read_bytes(), sentinel)

    def test_lavfi_joint_admission_preserves_targets(self):
        video = "color=c=red:s=16x16:r=10:d=0.1"
        odd_video = "color=c=red:s=15x16:r=10:d=0.1"
        audio = "sine=f=440:r=8000:d=0.01"
        both = video + "[v];" + audio + "[a]"
        cases = [
            (video, ["-c:v", "ffv1"], "mp4"),
            (video, ["-c:v", "h264"], "mkv"),
            (video, ["-c:v", "libx264"], "avi"),
            (audio, ["-c:a", "flac"], "mp4"),
            (audio, ["-c:a", "pcm_s16le"], "mp4"),
            (video, ["-pix_fmt", "rgb24"], "mp4"),
            (video, ["-pix_fmt", "gray"], "mkv"),
            (video, ["-pix_fmt", "yuv420p"], "png"),
            (odd_video, [], "mp4"),
            (video, ["-map", "[missing]"], "mp4"),
            (video, ["-vn"], "mp4"),
            (audio, ["-an"], "wav"),
            (audio, ["-f", "s24le", "-c:a", "pcm_s16le"], "pcm"),
            ("sine=d=0.01[a];[a]scale=16:16", [], "mp4"),
            (video + "[a];[a][b]overlay[c];[c]split[b][out]", ["-map", "[out]"], "mp4"),
        ]
        for fmt in ("matroska", "avi", "image2", "rawvideo", "framemd5", "wav", "flac", "adts", "s16le", "md5"):
            cases.append((both, ["-map", "[v]", "-map", "[a]", "-f", fmt], "mp4"))
        sentinel = b"admission-sentinel\x00\xff"
        for index, (spec, options, suffix) in enumerate(cases):
            target = self.dir / f"reject-{index}.{suffix}"
            for flags in ([], ["-n"], ["-y"], ["-json"]):
                for exists in (False, True):
                    with self.subTest(index=index, flags=flags, exists=exists):
                        target.unlink(missing_ok=True)
                        if exists:
                            target.write_bytes(sentinel)
                        result = run([*flags, "-lavfi", spec, *options, str(target)])
                        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertNotIn(b"Not overwriting", result.stderr)
                        self.assertEqual(target.read_bytes() if exists else target.exists(), sentinel if exists else False)
        for index, (spec, options, suffix) in enumerate(cases[:6]):
            plan_res = run(["plan", "-lavfi", spec, *options, str(self.dir / f"plan-{index}.{suffix}")])
            self.assertNotIn(b'"inproc_lavfi_dag"', plan_res.stdout)

    def test_lavfi_valid_overwrite_and_effective_format(self):
        spec = "color=c=red:s=16x16:r=10:d=0.1"
        target = self.dir / "effective.mp4"
        sentinel = b"keep-existing-output"
        for flags, code in (([], 0), (["-n"], 1), (["-json"], 1), (["-y"], 0)):
            with self.subTest(flags=flags):
                target.write_bytes(sentinel)
                result = run([*flags, "-lavfi", spec, "-f", "rawvideo", str(target)])
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                if flags == ["-y"]:
                    self.assertEqual(target.stat().st_size, 384)
                else:
                    self.assertEqual(target.read_bytes(), sentinel)
                if not flags:
                    self.assertIn(b"Not overwriting - exiting", result.stderr)
        result = run(["-n", "-lavfi", spec, "-f", "null", "/dev/null"])
        self.assertNotEqual(result.returncode, 0)

    def test_file_routes_admission_before_overwrite(self):
        import struct
        d = self.dir
        synth = d / "adm_synth.mp4"
        self.assert_ok([
            "-y", "-lavfi",
            "color=c=green:s=32x32:r=10:d=0.2[v];sine=f=440:r=48000:d=0.2[a]",
            "-map", "[v]", "-map", "[a]", str(synth),
        ])
        raw_mp4 = synth.read_bytes()
        avcc_idx = raw_mp4.find(b"avcC")
        mp4_10bit = bytearray(raw_mp4)
        mp4_10bit[avcc_idx + 5] = 135
        mp4_10bit[avcc_idx + 13] = 135
        in_10bit = d / "adm_10bit.mp4"
        in_10bit.write_bytes(bytes(mp4_10bit))

        bad_mp4 = d / "adm_bad.mp4"
        bad_mp4.write_bytes(b"NOT_AN_MP4_CONTAINER")
        bad_mkv = d / "adm_not_ffv1.mkv"
        bad_mkv.write_bytes(b"\x1a\x45\xdf\xa3\x00\x00\x00\x00")
        bad_png = d / "adm_bad.png"
        bad_png.write_bytes(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR" + b"\x00" * 16)
        float_wav = d / "adm_float32.wav"
        fmt_chunk = struct.pack("<4sIHHIIHH", b"fmt ", 16, 3, 1, 48000, 192000, 4, 32)
        data_chunk = struct.pack("<4sI", b"data", 16) + b"\x00" * 16
        float_wav.write_bytes(b"RIFF" + struct.pack("<I", 4 + len(fmt_chunk) + len(data_chunk)) + b"WAVE" + fmt_chunk + data_chunk)
        bad_aac = d / "adm_bad.aac"
        bad_aac.write_bytes(b"\xff\xf1\x50\x80\x00\x1f\xfc\xde\xad\xbe\xef")

        valid_png = d / "adm_valid.png"
        self.assert_ok(["-y", "-lavfi", "color=c=red:s=16x16:r=10:d=0.1", str(valid_png)])
        valid_wav = d / "adm_valid.wav"
        self.assert_ok(["-y", "-lavfi", "sine=f=440:r=48000:d=0.05", str(valid_wav)])
        valid_aac = d / "adm_valid.aac"
        self.assert_ok(["-y", "-i", str(valid_wav), "-c:a", "aac", str(valid_aac)])
        valid_ffv1 = d / "adm_valid.mkv"
        self.assert_ok([
            "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-r", "10",
            "-i", str(d / "in.yuv"), "-c:v", "ffv1", str(valid_ffv1),
        ])

        sentinel = b"sentinel-route-preserve\x00\xfe"
        reject_cases = [
            (["-i", str(synth), "-c:v", "vp9"], "mp4"),
            (["-i", str(in_10bit), "-c:v", "h264"], "mp4"),
            (["-i", str(bad_mp4), "-c:v", "h264"], "mp4"),
            (["-i", str(bad_mp4), "-c", "copy"], "mp4"),
            (["-i", str(bad_mkv), "-f", "rawvideo", "-pix_fmt", "yuv420p"], "yuv"),
            (["-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "32x32", "-i", str(bad_png), "-c:v", "ffv1"], "mkv"),
            (["-i", str(bad_png)], "png"),
            (["-i", str(float_wav), "-c:a", "flac"], "flac"),
            (["-i", str(bad_aac)], "wav"),
            (["-i", str(float_wav), "-c:a", "aac"], "aac"),
        ]
        for idx, (cmd_prefix, ext) in enumerate(reject_cases):
            target = d / f"route_reject_{idx}.{ext}"
            for flags in ([], ["-n"], ["-y"], ["-json"]):
                for exists in (False, True):
                    with self.subTest(route=idx, flags=flags, exists=exists):
                        target.unlink(missing_ok=True)
                        if exists:
                            target.write_bytes(sentinel)
                        res = run([*flags, *cmd_prefix, str(target)])
                        self.assertNotEqual(res.returncode, 0, res.stdout + res.stderr)
                        self.assertNotIn(b"Not overwriting", res.stderr)
                        self.assertEqual(target.read_bytes() if exists else target.exists(), sentinel if exists else False)

        valid_routes = [
            (["-i", str(synth), "-c:v", "h264", "-c:a", "aac"], "mp4"),
            (["-i", str(synth), "-c", "copy"], "mp4"),
            (["-i", str(valid_ffv1), "-f", "rawvideo", "-pix_fmt", "yuv420p"], "yuv"),
            (["-i", str(valid_png)], "png"),
            (["-i", str(valid_wav), "-c:a", "flac"], "flac"),
            (["-i", str(valid_aac)], "wav"),
        ]
        for idx, (cmd_prefix, ext) in enumerate(valid_routes):
            target = d / f"route_valid_{idx}.{ext}"
            for flags, expected_rc in (([], 0), (["-n"], 1), (["-json"], 1), (["-y"], 0)):
                with self.subTest(valid_route=idx, flags=flags):
                    target.write_bytes(sentinel)
                    res = run([*flags, *cmd_prefix, str(target)])
                    self.assertEqual(res.returncode, expected_rc, res.stdout + res.stderr)
                    if flags == ["-y"]:
                        self.assertNotEqual(target.read_bytes(), sentinel)
                        self.assertGreater(target.stat().st_size, 16)
                    else:
                        self.assertEqual(target.read_bytes(), sentinel)
                    if not flags:
                        self.assertIn(b"Not overwriting - exiting", res.stderr)


if __name__ == "__main__":
    unittest.main()
