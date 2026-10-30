import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FIXTURE_AV = ROOT / "tests" / "differential" / "fixtures" / "input-av.mp4"


def _make_yuv420p(w: int, h: int, frames: int) -> bytes:
    out = bytearray()
    cw, ch = (w + 1) // 2, (h + 1) // 2
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                out.append((x * 13 + y * 29 + f * 47 + (x ^ y)) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                out.append((128 + x * 7 - y * 11 + f * 19) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                out.append((128 - x * 9 + y * 17 - f * 23) & 0xFF)
    return bytes(out)


def _make_packed_or_gray(size_per_frame: int, frames: int) -> bytes:
    out = bytearray()
    for f in range(frames):
        for i in range(size_per_frame):
            out.append(((i * 37) ^ (f * 73) ^ (i >> 3)) & 0xFF)
    return bytes(out)


def _normalize_framemd5(raw: bytes) -> tuple[bool, list[str]]:
    lines = raw.decode("utf-8").splitlines()
    has_sw = False
    kept: list[str] = []
    for ln in lines:
        if ln.startswith("#software:"):
            has_sw = True
        else:
            kept.append(ln)
    return has_sw, kept


class NativeFfv1Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not (BINARY.stat().st_mode & 0o111):
            raise unittest.SkipTest("lffmpeg binary is unavailable")
        ref = os.environ.get("LEANAV_TEST_FFMPEG") or shutil.which("ffmpeg")
        if not ref:
            raise unittest.SkipTest("reference FFmpeg is unavailable")
        cls.ffmpeg = str(Path(ref).resolve())
        cls.isolated_env = {
            "PATH": "/nonexistent",
            "LEANAV_FFMPEG_BIN": "/nonexistent/ffmpeg",
            "LANG": "C",
            "LC_ALL": "C",
        }

    def run_isolated(self, *args: str, stdin_bytes: bytes | None = None):
        return subprocess.run(
            [str(BINARY), *args],
            input=stdin_bytes,
            env=self.isolated_env,
            capture_output=True,
            timeout=30,
        )

    def run_ref(self, *args: str, stdin_bytes: bytes | None = None):
        return subprocess.run(
            [self.ffmpeg, "-nostdin", "-hide_banner", "-loglevel", "error", *args],
            input=stdin_bytes,
            capture_output=True,
            timeout=30,
        )

    def test_plan_promotes_ffv1_and_containers_to_independent_verified(self):
        for cmd, expected_fallback in (
            (["plan", "-i", "in.y4m", "-c:v", "ffv1", "out.mkv"], False),
            (["plan", "-i", "in.mkv", "-f", "framemd5", "-"], True),
            (["plan", "-i", "in.mov", "-f", "md5", "-"], True),
            (["plan", "-i", "in.avi", "out.y4m"], True),
        ):
            with self.subTest(cmd=cmd):
                res = self.run_isolated(*cmd)
                self.assertEqual(res.returncode, 0, res.stderr.decode(errors="replace"))
                plan = json.loads(res.stdout.decode("utf-8"))
                self.assertEqual(plan["backend"]["tier"], "independent_verified")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertEqual(plan["backend"]["fallback_allowed"], expected_fallback)
                self.assertEqual(plan["error_count"], 0)

    def test_bidirectional_yuv420p_matrix_isolated_from_ffmpeg(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-yuv-") as tmp:
            root = Path(tmp)
            w, h, frames = 24, 16, 3
            raw_bytes = _make_yuv420p(w, h, frames)
            raw_in = root / "src.yuv"
            raw_in.write_bytes(raw_bytes)
            for ext in ("mkv", "mov", "avi"):
                for coder in ("0", "1", "-2"):
                    for context in ("0", "1"):
                        for slices in ("1", "4"):
                            for slicecrc in ("0", "1"):
                                with self.subTest(ext=ext, coder=coder, ctx=context, slices=slices, crc=slicecrc):
                                    lean_media = root / f"lean_{coder}_{context}_{slices}_{slicecrc}.{ext}"
                                    enc = self.run_isolated(
                                        "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                                        "-video_size", f"{w}x{h}", "-framerate", "25",
                                        "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                                        "-coder", coder, "-context", context,
                                        "-slices", slices, "-slicecrc", slicecrc, "-g", "2",
                                        str(lean_media),
                                    )
                                    self.assertEqual(enc.returncode, 0, enc.stderr.decode(errors="replace"))
                                    ref_dec = self.run_ref(
                                        "-i", str(lean_media), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-",
                                    )
                                    self.assertEqual(ref_dec.returncode, 0, ref_dec.stderr.decode(errors="replace"))
                                    self.assertEqual(ref_dec.stdout, raw_bytes)

                                    ff_media = root / f"ff_{coder}_{context}_{slices}_{slicecrc}.{ext}"
                                    ff_enc = self.run_ref(
                                        "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                                        "-video_size", f"{w}x{h}", "-framerate", "25",
                                        "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                                        "-coder", coder, "-context", context,
                                        "-slices", slices, "-slicecrc", slicecrc, "-g", "2",
                                        str(ff_media),
                                    )
                                    self.assertEqual(ff_enc.returncode, 0, ff_enc.stderr.decode(errors="replace"))
                                    lean_dec = self.run_isolated(
                                        "-i", str(ff_media), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-",
                                    )
                                    self.assertEqual(lean_dec.returncode, 0, lean_dec.stderr.decode(errors="replace"))
                                    self.assertEqual(lean_dec.stdout, raw_bytes)

    def test_bidirectional_gray_rgb24_bgr0_and_64_slices(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-pix-") as tmp:
            root = Path(tmp)
            w, h, frames = 24, 16, 2
            specs = (
                ("gray", w * h),
                ("rgb24", w * h * 3),
                ("bgr0", w * h * 4),
            )
            for pix_fmt, frame_bytes in specs:
                raw_data = _make_packed_or_gray(frame_bytes, frames)
                if pix_fmt == "bgr0":
                    ba = bytearray(raw_data)
                    for i in range(3, len(ba), 4):
                        ba[i] = 0x00
                    raw_data = bytes(ba)
                raw_in = root / f"src_{pix_fmt}.raw"
                raw_in.write_bytes(raw_data)
                for ext in ("mkv", "mov", "avi"):
                    for coder, slices in (("0", "4"), ("1", "64"), ("-2", "9")):
                        with self.subTest(pix_fmt=pix_fmt, ext=ext, coder=coder, slices=slices):
                            lean_out = root / f"lean_{pix_fmt}_{coder}_{slices}.{ext}"
                            enc = self.run_isolated(
                                "-y", "-f", "rawvideo", "-pix_fmt", pix_fmt,
                                "-video_size", f"{w}x{h}", "-framerate", "30",
                                "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                                "-coder", coder, "-slices", slices, "-slicecrc", "1",
                                str(lean_out),
                            )
                            self.assertEqual(enc.returncode, 0, enc.stderr.decode(errors="replace"))
                            ref_dec = self.run_ref("-i", str(lean_out), "-f", "rawvideo", "-pix_fmt", pix_fmt, "-")
                            self.assertEqual(ref_dec.returncode, 0, ref_dec.stderr.decode(errors="replace"))
                            self.assertEqual(ref_dec.stdout, raw_data)

                            ff_out = root / f"ff_{pix_fmt}_{coder}_{slices}.{ext}"
                            ff_enc = self.run_ref(
                                "-y", "-f", "rawvideo", "-pix_fmt", pix_fmt,
                                "-video_size", f"{w}x{h}", "-framerate", "30",
                                "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                                "-coder", coder, "-slices", slices, "-slicecrc", "1",
                                str(ff_out),
                            )
                            self.assertEqual(ff_enc.returncode, 0, ff_enc.stderr.decode(errors="replace"))
                            lean_dec = self.run_isolated("-i", str(ff_out), "-f", "rawvideo", "-pix_fmt", pix_fmt, "-")
                            self.assertEqual(lean_dec.returncode, 0, lean_dec.stderr.decode(errors="replace"))
                            self.assertEqual(lean_dec.stdout, raw_data)

    def test_md5_framemd5_y4m_and_remux_chain_parity(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-mux-") as tmp:
            root = Path(tmp)
            y4m_src = root / "input.y4m"
            gen = self.run_ref(
                "-y", "-f", "lavfi", "-i", "testsrc2=size=32x24:rate=25",
                "-frames:v", "3", "-pix_fmt", "yuv420p", str(y4m_src),
            )
            self.assertEqual(gen.returncode, 0, gen.stderr.decode(errors="replace"))

            mkv_a = root / "a.mkv"
            mov_b = root / "b.mov"
            avi_c = root / "c.avi"
            mkv_d = root / "d.mkv"
            self.assertEqual(self.run_isolated("-y", "-i", str(y4m_src), "-c:v", "ffv1", "-coder", "1", "-slices", "4", str(mkv_a)).returncode, 0)
            self.assertEqual(self.run_isolated("-y", "-i", str(mkv_a), "-c:v", "copy", str(mov_b)).returncode, 0)
            self.assertEqual(self.run_isolated("-y", "-i", str(mov_b), "-c", "copy", str(avi_c)).returncode, 0)
            self.assertEqual(self.run_isolated("-y", "-i", str(avi_c), "-c:v", "copy", str(mkv_d)).returncode, 0)

            for fmt in ("md5", "framemd5", "yuv4mpegpipe"):
                with self.subTest(fmt=fmt):
                    ref_out = self.run_ref("-i", str(mkv_d), "-f", fmt, "-")
                    lean_out = self.run_isolated("-i", str(mkv_d), "-f", fmt, "-")
                    self.assertEqual(ref_out.returncode, 0, ref_out.stderr.decode(errors="replace"))
                    self.assertEqual(lean_out.returncode, 0, lean_out.stderr.decode(errors="replace"))
                    if fmt == "framemd5":
                        ref_sw, ref_lines = _normalize_framemd5(ref_out.stdout)
                        lean_sw, lean_lines = _normalize_framemd5(lean_out.stdout)
                        self.assertTrue(ref_sw)
                        self.assertTrue(lean_sw)
                        self.assertEqual(lean_lines, ref_lines)
                    else:
                        self.assertEqual(lean_out.stdout, ref_out.stdout)

            expected_md5 = f"MD5={hashlib.md5(self.run_ref('-i', str(y4m_src), '-f', 'rawvideo', '-').stdout).hexdigest()}\n".encode()
            lean_md5 = self.run_isolated("-i", str(mkv_a), "-f", "md5", "-")
            self.assertEqual(lean_md5.stdout, expected_md5)

    def test_corrupt_crc_and_malformed_containers_fail_closed_in_process(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-corrupt-") as tmp:
            root = Path(tmp)
            raw_in = root / "src.yuv"
            raw_in.write_bytes(_make_yuv420p(16, 16, 2))
            good_mkv = root / "good.mkv"
            enc = self.run_isolated(
                "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-video_size", "16x16",
                "-i", str(raw_in), "-c:v", "ffv1", "-coder", "1", "-slices", "4", "-slicecrc", "1",
                str(good_mkv),
            )
            self.assertEqual(enc.returncode, 0)
            corrupt_mkv = root / "corrupt_crc.mkv"
            payload = bytearray(good_mkv.read_bytes())
            payload[-5] ^= 0x5A
            corrupt_mkv.write_bytes(bytes(payload))
            res_crc = self.run_isolated("-i", str(corrupt_mkv), "-f", "framemd5", "-")
            self.assertNotEqual(res_crc.returncode, 0)

            trunc_mov = root / "trunc.mov"
            trunc_mov.write_bytes(b"\x00\x00\x00\x14ftypqt  \x00\x00\x00\xffmoov")
            res_trunc = self.run_isolated("-i", str(trunc_mov), "-f", "md5", "-")
            self.assertNotEqual(res_trunc.returncode, 0)

            overwrite_target = root / "existing.mkv"
            overwrite_target.write_bytes(b"keep")
            res_no_overwrite = self.run_isolated(
                "-n", "-f", "rawvideo", "-pix_fmt", "yuv420p", "-video_size", "16x16",
                "-i", str(raw_in), "-c:v", "ffv1", str(overwrite_target),
            )
            self.assertNotEqual(res_no_overwrite.returncode, 0)
            self.assertEqual(overwrite_target.read_bytes(), b"keep")

    def test_strace_confirms_zero_child_execve_and_multi_stream_delegates(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-strace-") as tmp:
            root = Path(tmp)
            raw_in = root / "src.yuv"
            raw_in.write_bytes(_make_yuv420p(16, 16, 1))
            out_mkv = root / "out.mkv"
            strace_bin = shutil.which("strace")
            if strace_bin:
                trace_log = root / "strace.log"
                proc = subprocess.run(
                    [
                        strace_bin, "-f", "-e", "trace=execve", "-o", str(trace_log),
                        str(BINARY), "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                        "-video_size", "16x16", "-i", str(raw_in), "-c:v", "ffv1", str(out_mkv),
                    ],
                    env=self.isolated_env,
                    capture_output=True,
                    timeout=30,
                )
                self.assertEqual(proc.returncode, 0, proc.stderr.decode(errors="replace"))
                exec_lines = [ln for ln in trace_log.read_text(encoding="utf-8").splitlines() if "execve(" in ln]
                self.assertEqual(len(exec_lines), 1, exec_lines)

            if FIXTURE_AV.is_file():
                delegated_env = dict(os.environ, LEANAV_FFMPEG_BIN=self.ffmpeg)
                delegated_out = root / "delegated.mkv"
                del_res = subprocess.run(
                    [str(BINARY), "-y", "-i", str(FIXTURE_AV), "-c", "copy", str(delegated_out)],
                    env=delegated_env,
                    capture_output=True,
                    timeout=30,
                )
                self.assertEqual(del_res.returncode, 0, del_res.stderr.decode(errors="replace"))

    def test_two_pass_coder2_custom_transition_table_decode_parity(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-2pass-") as tmp:
            root = Path(tmp)
            w, h, frames = 32, 24, 4
            raw_bytes = _make_yuv420p(w, h, frames)
            raw_in = root / "src.yuv"
            raw_in.write_bytes(raw_bytes)
            passlog = root / "ffv1_2pass"
            out_mkv = root / "twopass.mkv"
            p1 = self.run_ref(
                "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                "-video_size", f"{w}x{h}", "-framerate", "25",
                "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                "-coder", "1", "-context", "1", "-slices", "4", "-slicecrc", "1", "-g", "2",
                "-pass", "1", "-passlogfile", str(passlog),
                "-f", "null", os.devnull,
            )
            self.assertEqual(p1.returncode, 0, p1.stderr.decode(errors="replace"))
            p2 = self.run_ref(
                "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                "-video_size", f"{w}x{h}", "-framerate", "25",
                "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                "-coder", "1", "-context", "1", "-slices", "4", "-slicecrc", "1", "-g", "2",
                "-pass", "2", "-passlogfile", str(passlog),
                str(out_mkv),
            )
            self.assertEqual(p2.returncode, 0, p2.stderr.decode(errors="replace"))

            lean_raw = self.run_isolated("-i", str(out_mkv), "-f", "rawvideo", "-pix_fmt", "yuv420p", "-")
            self.assertEqual(lean_raw.returncode, 0, lean_raw.stderr.decode(errors="replace"))
            self.assertEqual(lean_raw.stdout, raw_bytes)

            ref_fmd5 = self.run_ref("-i", str(out_mkv), "-f", "framemd5", "-")
            lean_fmd5 = self.run_isolated("-i", str(out_mkv), "-f", "framemd5", "-")
            self.assertEqual(ref_fmd5.returncode, 0, ref_fmd5.stderr.decode(errors="replace"))
            self.assertEqual(lean_fmd5.returncode, 0, lean_fmd5.stderr.decode(errors="replace"))
            ref_sw, ref_lines = _normalize_framemd5(ref_fmd5.stdout)
            lean_sw, lean_lines = _normalize_framemd5(lean_fmd5.stdout)
            self.assertTrue(ref_sw and lean_sw)
            self.assertEqual(lean_lines, ref_lines)

    def test_unsupported_ffv1_pix_fmt_honors_nonexistent_ffmpeg_bin_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-noescape-") as tmp:
            root = Path(tmp)
            nv12_in = root / "src.nv12"
            nv12_in.write_bytes(bytes(16 * 16 * 3 // 2))
            out_mkv = root / "out_nv12.mkv"
            env_nonexistent = {
                "PATH": "/nonexistent",
                "LEANAV_FFMPEG_BIN": "/nonexistent",
                "LEANAV_FFPROBE_BIN": "/nonexistent",
                "LANG": "C",
                "LC_ALL": "C",
            }
            strace_bin = shutil.which("strace")
            if strace_bin:
                trace_log = root / "nv12_strace.log"
                proc = subprocess.run(
                    [
                        strace_bin, "-f", "-e", "trace=execve", "-o", str(trace_log),
                        str(BINARY), "-y", "-f", "rawvideo", "-pix_fmt", "nv12",
                        "-video_size", "16x16", "-framerate", "25",
                        "-i", str(nv12_in), "-c:v", "ffv1", str(out_mkv),
                    ],
                    env=env_nonexistent,
                    capture_output=True,
                    timeout=30,
                )
                self.assertNotEqual(proc.returncode, 0)
                trace_text = trace_log.read_text(encoding="utf-8")
                self.assertNotIn('"/usr/bin/ffmpeg"', trace_text)
                self.assertNotIn('"/usr/local/bin/ffmpeg"', trace_text)
            else:
                proc = subprocess.run(
                    [
                        str(BINARY), "-y", "-f", "rawvideo", "-pix_fmt", "nv12",
                        "-video_size", "16x16", "-framerate", "25",
                        "-i", str(nv12_in), "-c:v", "ffv1", str(out_mkv),
                    ],
                    env=env_nonexistent,
                    capture_output=True,
                    timeout=30,
                )
                self.assertNotEqual(proc.returncode, 0)
            self.assertFalse(out_mkv.exists())

    def test_matroska_sar_display_unit_bidirectional_parity(self):
        with tempfile.TemporaryDirectory(prefix="native-ffv1-sar-") as tmp:
            root = Path(tmp)
            w, h, frames = 16, 12, 2
            raw_bytes = _make_yuv420p(w, h, frames)
            raw_in = root / "src.yuv"
            raw_in.write_bytes(raw_bytes)
            cases = (
                ("0_1", "0:0", [], "#sar 0: 0/1"),
                ("1_1", "1:1", ["-vf", "setsar=1/1"], "#sar 0: 1/1"),
                ("4_3", "4:3", ["-vf", "setsar=4/3"], "#sar 0: 4/3"),
            )
            for label, y4m_sar, vf_args, expected_sar_line in cases:
                with self.subTest(sar=label):
                    ff_mkv = root / f"ff_{label}.mkv"
                    ff_enc = self.run_ref(
                        "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                        "-video_size", f"{w}x{h}", "-framerate", "25",
                        "-i", str(raw_in), *vf_args,
                        "-c:v", "ffv1", "-level", "3", "-coder", "1", "-slices", "4",
                        str(ff_mkv),
                    )
                    self.assertEqual(ff_enc.returncode, 0, ff_enc.stderr.decode(errors="replace"))

                    lean_mkv = root / f"lean_{label}.mkv"
                    if label == "0_1":
                        lean_enc = self.run_isolated(
                            "-y", "-f", "rawvideo", "-pix_fmt", "yuv420p",
                            "-video_size", f"{w}x{h}", "-framerate", "25",
                            "-i", str(raw_in), "-c:v", "ffv1", "-level", "3",
                            "-coder", "1", "-slices", "4", str(lean_mkv),
                        )
                    else:
                        y4m_in = root / f"in_{label}.y4m"
                        hdr = f"YUV4MPEG2 W{w} H{h} F25:1 Ip A{y4m_sar} C420jpeg\n".encode("ascii")
                        frame_sz = w * h * 3 // 2
                        body = bytearray(hdr)
                        for idx in range(frames):
                            body.extend(b"FRAME\n")
                            body.extend(raw_bytes[idx * frame_sz : (idx + 1) * frame_sz])
                        y4m_in.write_bytes(bytes(body))
                        lean_enc = self.run_isolated(
                            "-y", "-i", str(y4m_in), "-c:v", "ffv1", "-level", "3",
                            "-coder", "1", "-slices", "4", str(lean_mkv),
                        )
                    self.assertEqual(lean_enc.returncode, 0, lean_enc.stderr.decode(errors="replace"))

                    for tag, media_path in (("ff_mkv", ff_mkv), ("lean_mkv", lean_mkv)):
                        with self.subTest(sar=label, producer=tag):
                            ref_fmd5 = self.run_ref("-i", str(media_path), "-f", "framemd5", "-")
                            lean_fmd5 = self.run_isolated("-i", str(media_path), "-f", "framemd5", "-")
                            self.assertEqual(ref_fmd5.returncode, 0, ref_fmd5.stderr.decode(errors="replace"))
                            self.assertEqual(lean_fmd5.returncode, 0, lean_fmd5.stderr.decode(errors="replace"))
                            ref_sw, ref_lines = _normalize_framemd5(ref_fmd5.stdout)
                            lean_sw, lean_lines = _normalize_framemd5(lean_fmd5.stdout)
                            self.assertTrue(ref_sw and lean_sw)
                            self.assertIn(expected_sar_line, ref_lines)
                            self.assertEqual(lean_lines, ref_lines)


if __name__ == "__main__":
    unittest.main()





