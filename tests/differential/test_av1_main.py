import base64
import hashlib
import json
import math
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

REFMV_COMPOUND_UNCAP_M11_IVF_B64 = (
    "REtJRgAAIABBVjAxIAAgABkAAAABAAAABQAAAAAAAADmAQAAAAAAAAAAAAASAAoKAAAAAif+bXyAIDLVAxAAnQAA"
    "AgAAgM8MBG7Dij4myyXeK9qrIvQMxT3Ps8SQMzuAtbEr1PwXIuhniyZKyOAU+aTBtcnZdSgR94zx4vujT97sr8VW"
    "Fo4kutFctn30F/7WyoWExsOk//+EFs6ZprbCzAhCwd/xTEOcH0i4ikhS+QMFnvBDmKsEZd2Z0uNI3rkxTl+01GQm"
    "KGF0XN8k/x9OnqjuxcMGioOED1cEgDg45NXiI7LqHxFCv4Z+SI8MStuIwgUw8O9YGsvVJ05W5O6s2pjVfh7UfRv8"
    "ruosmeJWMmN4f3Gu/Ez28CrrfAGXBiErZkBmCCRrat51Rx22pyvFLrbH8Q28NGxSFmWPEiUSjnzZ17Aw1q8QGV2m"
    "MD1tiiLox2rYUHBFHZZHlVnRTJHvE2hrLNHTuFnsk7tmgfKcED6xOY1woFr+RWte6JZcmZQUQePDs8f033D7NpPv"
    "QmN5VndXISf8Kbkxe87OExJasA8rnfMWDvYLKawL7Nyj9eyLkbaYoBxExJLD8ZDTJkTsCBY8M14lBL4ig2SuM/Ab"
    "r56H06f9Q/YKkuw1h60O+JyJbeOnA3hFYO0dRXClNpqRrXUlngq6ZYk1l54ElOJUVcWMcGpIKFmgrx2DgC0GHP9v"
    "QWBrAgAAAQAAAAAAAAASADKnAygE4EAAACNZAAABJZdQAM8RuAZ11yU+eBMM5t0iZb4WquTF1MtdO/JHyGyM8F0O"
    "TKAT1RPFiBWlEFHPpY2aeCY2AIIES4yX5gykte1P9LkUqPK+Ze4tAzlbwzqWlaFNiv6pfn5zdNBn74B6nLxkkkqs"
    "UFwM/os+VwiX+IpMFU5t8Swc11Ml39V/Tz4ZbAmFoeoZjt5M3zetWw0JGsWSSprs5nhAK9873FlLpUMUadBBgTsz"
    "hFUjg61/XFtXICglLHkFfOY9P0KCBZnPOC98Q6LpKEsciPQjue2D3GqLAfCOINDQ3u0tjdX0aBUuY6S7nyZIjILV"
    "CILQcnIVWLpJwrKpUnk8K+UKuedbFnJv1qwGjZuMyGNFb11qz4U6ybvhoMdEM0I2bWqSbjQwTZux1QCk3FvczJWn"
    "UtG/mrvkBcImaWhhJAbT1uiBnmJAS7gFpljDADqQXFqjEjZpC6PYPMPlipmhQV34AxBOMKI3SMu1GCFVaxF4MngH"
    "HKc4qPGLRw4IdOxUEXwNqMpQyKnaHJEUu1ySZG1QTA+ITiDDSWAme+7rydRVQDJaKALggAAAo16AAAEgAVAAz0ma"
    "u8m4P+0AzHvltwspQrwnHrLOfIt7Ne1BcdOgpMjSUzQHJbmoOYZ/Gc5RLd1YZLCWK5aU6cj2JTVkcWJbj+tnLlsR"
    "S5fUS9aXMmEwA8IAAIEGyAAAAoss0ADPovSwnXG6NQLEYADgfhFUIjmulqH9mwIh6Ep2sUyEOXh/NknNLuXdciZM"
    "Mx5fn1Rb9bTbr5rpelOCH4efH2Y9QCZhCH+HkGO45TSX9rMTHCetBQAAAAIAAAAAAAAAEgAaAahiAAAAAwAAAAAA"
    "AAASADJeMAZECYABBsgAAAKALtAAwEYLZ4hJj61ISKJAWAwnfzOY4KQAY+MFD8YKzuF887uH2JTG5E1fs3Gf7fcd"
    "jG2uLgNyQMgBCtu+2Yw+B43T8AmjZzBT8nvQBpz8l2RUOhUAAAAEAAAAAAAAABIAMhEwCAgRABk7IAAACgAAgACH"
    "CQ=="
)
REFMV_COMPOUND_UNCAP_M11_YUV_SHA256 = (
    "79ec3fde567bce380b89bf6d9d321f66a64ca114024e3b17b0acb0aac1067365"
)
UNI_COMPOUND_CPU2_96X80_IVF_B64 = (
    "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"
    "J82tFfr2EwR1fz4QIVwWuKzKL5o/RiNw"
)
UNI_COMPOUND_CPU2_96X80_YUV_SHA256 = (
    "39baeb07af079ac0eba1602f878d94a5b686663fba86f59b8aa833991c849d34"
)

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG", shutil.which("ffmpeg") or "ffmpeg")
FFPROBE = os.environ.get("FFPROBE", shutil.which("ffprobe") or "ffprobe")
STRACE = shutil.which("strace")
ISO_ENV = {
    "PATH": "/nonexistent",
    "LEANAV_FFMPEG_BIN": "/nonexistent",
    "LEANAV_FFPROBE_BIN": "/nonexistent",
}


def run(*args, env=None, check=True):
    return subprocess.run(
        [str(a) for a in args],
        check=check,
        capture_output=True,
        env=env,
    )


def libaom_av1_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return "libaom-av1" in out


def libsvtav1_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return "libsvtav1" in out


def ffprobe_available():
    try:
        out = run(FFPROBE, "-version").stdout.decode(errors="replace")
    except (OSError, subprocess.CalledProcessError):
        return False
    return out.startswith("ffprobe version ")


def synth_yuv420p(w, h, frames):
    buf = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 7 + y * 5 + f * 19 + ((x ^ y) & 15) * 3) & 0xFF
                buf.append(v)
        cw = w // 2
        ch = h // 2
        for y in range(ch):
            for x in range(cw):
                buf.append((88 + x * 3 + y * 2 + f * 11) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                buf.append((164 - x * 2 + y * 3 - f * 7) & 0xFF)
    return bytes(buf)


def psnr_db(ref_bytes, got_bytes):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    mse = sum((a - b) * (a - b) for a, b in zip(ref_bytes, got_bytes)) / len(ref_bytes)
    if mse == 0.0:
        return 99.0
    return 10.0 * math.log10((255.0 * 255.0) / mse)


@unittest.skipUnless(LFFMPEG.exists(), "lffmpeg is not built")
class TestAv1Main(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _ffmpeg_decode_yuv420p(self, in_path):
        out_yuv = self.dir / f"{Path(in_path).name}.ff.yuv"
        run(
            FFMPEG, "-y", "-v", "error",
            "-i", in_path,
            "-f", "rawvideo", "-pix_fmt", "yuv420p", out_yuv,
        )
        return out_yuv.read_bytes()

    def test_libaom_av1_to_lffmpeg_bit_exact_matrix(self):
        if not libaom_av1_available():
            self.skipTest("ffmpeg with libaom-av1 unavailable")
        cases = [
            ("intra_nocdef.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1", "-aom-params", "enable-cdef=0"]),
            ("intra_cdef_cpu8.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1"]),
            ("intra_cdef_cpu4.ivf", 64, 48, 1, "ivf", ["-cpu-used", "4", "-crf", "30", "-g", "1"]),
            ("ip_lag0_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36", "-lag-in-frames", "0"]),
            ("ip_lag0_cpu4.ivf", 96, 80, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-lag-in-frames", "0"]),
            ("ip_altref_def_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36"]),
            ("ip_altref_def_cpu4.ivf", 96, 80, 5, "ivf", ["-cpu-used", "4", "-crf", "34"]),
            ("tiles_2x2_lag0.ivf", 160, 128, 4, "ivf", ["-cpu-used", "8", "-crf", "34", "-lag-in-frames", "0", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("tiles_2x2_altref_cpu4.ivf", 160, 128, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("crop_98x66_cpu8.ivf", 98, 66, 4, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_98x66_cpu4.ivf", 98, 66, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("crop_130x98_cpu8.ivf", 130, 98, 3, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_130x98_cpu4.ivf", 130, 98, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("lossless_intra.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "0", "-g", "1", "-aom-params", "lossless=1"]),
            ("lossless_inter.ivf", 64, 48, 3, "ivf", ["-cpu-used", "8", "-crf", "0", "-lag-in-frames", "0", "-aom-params", "lossless=1"]),
            ("raw_stream.obu", 96, 80, 4, "obu", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_av1c.mp4", 96, 80, 5, "mp4", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_crop_98x66.mp4", 98, 66, 3, "mp4", ["-cpu-used", "8", "-crf", "34"]),
            ("uni_compound_cpu2_96x80.ivf", 96, 80, 6, "ivf", [
                "-cpu-used", "2", "-crf", "28", "-g", "6", "-aom-params",
                "enable-warped-motion=1:enable-obmc=1:enable-onesided-comp=1:"
                "enable-dist-wtd-comp=1:enable-diff-wtd-comp=1:enable-masked-comp=1:"
                "enable-interinter-wedge=1:enable-interintra-wedge=1:"
                "enable-interintra-comp=1:enable-smooth-interintra=1:"
                "enable-paeth-intra=1:enable-cfl-intra=1:enable-palette=1:"
                "enable-intrabc=1:enable-global-motion=1:enable-ref-frame-mvs=1:"
                "enable-dual-filter=1",
            ]),
            ("uni_compound_cpu2_tiles_128x96.ivf", 128, 96, 6, "ivf", [
                "-cpu-used", "2", "-crf", "28", "-g", "6",
                "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0",
                "-aom-params",
                "enable-warped-motion=1:enable-obmc=1:enable-onesided-comp=1:"
                "enable-dist-wtd-comp=1:enable-diff-wtd-comp=1:enable-masked-comp=1:"
                "enable-interinter-wedge=1:enable-interintra-wedge=1:"
                "enable-interintra-comp=1:enable-smooth-interintra=1:"
                "enable-paeth-intra=1:enable-cfl-intra=1:enable-palette=1:"
                "enable-intrabc=1:enable-global-motion=1:enable-ref-frame-mvs=1:"
                "enable-dual-filter=1",
            ]),
        ]
        for name, w, h, nf, mux_fmt, aom_opts in cases:
            with self.subTest(case=name):
                src_yuv = self.dir / f"src_{name}.yuv"
                raw_src = synth_yuv420p(w, h, nf)
                src_yuv.write_bytes(raw_src)
                stream_path = self.dir / name
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_yuv,
                    "-c:v", "libaom-av1", "-pix_fmt", "yuv420p",
                    *aom_opts,
                ]
                if mux_fmt == "obu":
                    cmd += ["-f", "obu"]
                elif mux_fmt == "ivf":
                    cmd += ["-f", "ivf"]
                cmd.append(stream_path)
                run(*cmd)

                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(LFFMPEG, "av1-decode-raw", stream_path, lean_yuv_path, env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                lean_bytes = lean_yuv_path.read_bytes()
                self.assertEqual(lean_bytes, ref_yuv)
                if "lossless" in name:
                    self.assertEqual(lean_bytes, raw_src)

                probe_proc = run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV)
                probe = json.loads(probe_proc.stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["codec"], "av1")
                self.assertEqual(probe["container"], mux_fmt)
                self.assertEqual(probe["profile"], 0)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["bit_depth"], 8)
                self.assertEqual(probe["chroma_subsampling"], "4:2:0")
                self.assertEqual(probe["frames"], nf)

    def test_svtav1_superres_to_lffmpeg_bit_exact(self):
        if not libsvtav1_available():
            self.skipTest("ffmpeg with libsvtav1 unavailable")
        cases = [
            ("sr_kf_d12.ivf", 128, 96, 1, "lp=2:superres-mode=1:superres-denom=8:superres-kf-denom=12"),
            ("sr_kf_d16.ivf", 128, 96, 1, "lp=2:superres-mode=1:superres-denom=8:superres-kf-denom=16"),
            ("sr_kf_d14_lr.ivf", 256, 192, 1, "lp=2:superres-mode=1:superres-denom=8:superres-kf-denom=14:enable-restoration-filtering=1"),
            ("sr_kf_d12_inter.ivf", 128, 96, 4, "lp=2:superres-mode=1:superres-denom=8:superres-kf-denom=12"),
            ("sr_kf_d14_inter_lr.ivf", 256, 192, 6, "lp=2:superres-mode=1:superres-denom=8:superres-kf-denom=14:enable-restoration-filtering=1"),
        ]
        for name, w, h, nf, svt_params in cases:
            with self.subTest(case=name):
                stream_path = self.dir / name
                run(
                    FFMPEG, "-y", "-v", "error",
                    "-f", "lavfi", "-i", f"testsrc2=size={w}x{h}:rate=25:duration=1",
                    "-c:v", "libsvtav1", "-preset", "10", "-pix_fmt", "yuv420p",
                    "-svtav1-params", svt_params,
                    "-frames:v", str(nf), "-f", "ivf", stream_path,
                )
                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(LFFMPEG, "av1-decode-raw", stream_path, lean_yuv_path, env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                self.assertEqual(lean_yuv_path.read_bytes(), ref_yuv)
                probe = json.loads(run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertTrue(probe["superres"])
                self.assertEqual(probe["frames"], nf)

    def test_lffmpeg_encode_to_ffmpeg_and_ffprobe_parity(self):
        if not libaom_av1_available():
            self.skipTest("ffmpeg unavailable")
        has_ffprobe = ffprobe_available()
        cases = [
            ("enc_lossless_64x48.obu", 64, 48, 2, 0, "obu", 1, 1),
            ("enc_lossless_98x66.ivf", 98, 66, 2, 0, "ivf", 1, 1),
            ("enc_lossless_mp4.mp4", 64, 48, 2, 0, "mp4", 1, 1),
            ("enc_q60_64x48.obu", 64, 48, 3, 60, "obu", 1, 1),
            ("enc_q60_96x80.ivf", 96, 80, 3, 60, "ivf", 1, 1),
            ("enc_q60_96x80.mp4", 96, 80, 3, 60, "mp4", 1, 1),
            ("enc_q60_crop_130x98.ivf", 130, 98, 2, 60, "ivf", 1, 1),
            ("enc_q60_tiles_2x2.obu", 128, 128, 2, 60, "obu", 2, 2),
            ("enc_q60_tiles_2x2.ivf", 128, 128, 3, 60, "ivf", 2, 2),
            ("enc_q60_tiles_2x2.mp4", 128, 128, 2, 60, "mp4", 2, 2),
        ]
        for name, w, h, nf, qidx, fmt, tc, tr in cases:
            with self.subTest(case=name):
                raw_in = synth_yuv420p(w, h, nf)
                in_path = self.dir / f"in_{name}.yuv"
                out_bs = self.dir / name
                lean_dec = self.dir / f"dec_{name}.yuv"
                in_path.write_bytes(raw_in)

                enc_proc = run(
                    LFFMPEG, "av1-encode-raw", w, h, in_path, out_bs, qidx, fmt, tc, tr,
                    env=ISO_ENV,
                )
                enc_meta = json.loads(enc_proc.stdout.decode())
                self.assertTrue(enc_meta["ok"])
                self.assertEqual(enc_meta["frames"], nf)
                self.assertGreater(out_bs.stat().st_size, 0)

                run(LFFMPEG, "av1-decode-raw", out_bs, lean_dec, env=ISO_ENV)
                ff_yuv = self._ffmpeg_decode_yuv420p(out_bs)
                lean_bytes = lean_dec.read_bytes()
                self.assertEqual(lean_bytes, ff_yuv)
                if qidx == 0:
                    self.assertEqual(ff_yuv, raw_in)
                else:
                    self.assertGreater(psnr_db(raw_in, ff_yuv), 30.0)

                probe = json.loads(run(LFFMPEG, "av1-probe", out_bs, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["container"], fmt)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["frames"], nf)
                self.assertEqual(probe["tile_cols"], tc)
                self.assertEqual(probe["tile_rows"], tr)

                if has_ffprobe:
                    fp_proc = run(
                        FFPROBE, "-v", "error", "-select_streams", "v:0",
                        "-count_frames",
                        "-show_entries", "stream=codec_name,profile,pix_fmt,width,height,nb_read_frames",
                        "-of", "json", out_bs,
                    )
                    st = json.loads(fp_proc.stdout.decode())["streams"][0]
                    self.assertEqual(st["codec_name"], "av1")
                    self.assertEqual(st["profile"], "Main")
                    self.assertEqual(st["pix_fmt"], "yuv420p")
                    self.assertEqual(st["width"], w)
                    self.assertEqual(st["height"], h)
                    self.assertEqual(int(st["nb_read_frames"]), nf)

    def test_non_main_and_malformed_inputs_fail_closed(self):
        in_good = self.dir / "good.yuv"
        in_good.write_bytes(synth_yuv420p(64, 48, 1))
        good_obu = self.dir / "good.obu"
        run(LFFMPEG, "av1-encode-raw", 64, 48, in_good, good_obu, 60, "obu", env=ISO_ENV)
        good_raw = good_obu.read_bytes()

        bad_cases = {
            "empty.obu": b"",
            "junk.obu": b"\xff\xff\xff\xff\x00\x01\x02",
            "trunc_seq.obu": good_raw[:6],
            "trunc_frame.obu": good_raw[: max(18, len(good_raw) // 2)],
        }
        for tag, payload in bad_cases.items():
            p = self.dir / tag
            p.write_bytes(payload)
            self.assertNotEqual(
                run(LFFMPEG, "av1-decode-raw", p, "-", env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        for tag in ("empty.obu", "junk.obu", "trunc_seq.obu"):
            p = self.dir / tag
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", p, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        in_odd = self.dir / "odd.yuv"
        in_odd.write_bytes(b"\x80" * (63 * 48 * 3 // 2))
        self.assertNotEqual(
            run(LFFMPEG, "av1-encode-raw", 63, 48, in_odd, self.dir / "odd.obu", env=ISO_ENV, check=False).returncode,
            0,
        )

        if not libaom_av1_available():
            return
        src_yuv = self.dir / "neg_src.yuv"
        src_yuv.write_bytes(synth_yuv420p(64, 48, 1))
        for tag, pix_fmt in (("av1_10bit.ivf", "yuv420p10le"), ("av1_444.ivf", "yuv444p")):
            neg_path = self.dir / tag
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
                "-i", src_yuv,
                "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", pix_fmt,
                "-frames:v", "1", "-f", "ivf", neg_path,
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-decode-raw", neg_path, "-", env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", neg_path, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        fg_path = self.dir / "film_grain_active.ivf"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
            "-i", src_yuv,
            "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "yuv420p",
            "-aom-params", "film-grain-test=1",
            "-frames:v", "1", "-f", "ivf", fg_path,
        )
        self.assertNotEqual(
            run(LFFMPEG, "av1-decode-raw", fg_path, "-", env=ISO_ENV, check=False).returncode,
            0,
            "film_grain_active.ivf",
        )
        self.assertNotEqual(
            run(LFFMPEG, "av1-probe", fg_path, env=ISO_ENV, check=False).returncode,
            0,
            "film_grain_active.ivf",
        )

        if libsvtav1_available():
            scaled_path = self.dir / "scaled_inter_superres.ivf"
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "lavfi", "-i", "testsrc2=size=128x96:rate=25:duration=0.2",
                "-c:v", "libsvtav1", "-preset", "12", "-pix_fmt", "yuv420p",
                "-svtav1-params", "lp=2:superres-mode=1:superres-denom=12:superres-kf-denom=8",
                "-frames:v", "4", "-f", "ivf", scaled_path,
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-decode-raw", scaled_path, "-", env=ISO_ENV, check=False).returncode,
                0,
                "scaled_inter_superres.ivf",
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", scaled_path, env=ISO_ENV, check=False).returncode,
                0,
                "scaled_inter_superres.ivf",
            )

    def test_embedded_uni_compound_cpu2_fixture(self):
        ivf_path = self.dir / "uni_compound_cpu2_96x80.ivf"
        ivf_path.write_bytes(base64.b64decode(UNI_COMPOUND_CPU2_96X80_IVF_B64))
        lean_yuv = self.dir / "uni_compound_cpu2_96x80.yuv"
        dec_proc = run(LFFMPEG, "av1-decode-raw", ivf_path, lean_yuv, env=ISO_ENV)
        dec_meta = json.loads(dec_proc.stdout.decode())
        self.assertTrue(dec_meta["ok"])
        self.assertEqual(dec_meta["width"], 96)
        self.assertEqual(dec_meta["height"], 80)
        self.assertEqual(dec_meta["frames"], 6)
        lean_bytes = lean_yuv.read_bytes()
        self.assertEqual(len(lean_bytes), 96 * 80 * 3 // 2 * 6)
        self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), UNI_COMPOUND_CPU2_96X80_YUV_SHA256)
        if libaom_av1_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(ivf_path))

    def test_embedded_tmv_and_compound_extended_refmv_fixture(self):
        ivf_path = self.dir / "refmv_compound_uncap_m11_32x32.ivf"
        ivf_path.write_bytes(base64.b64decode(REFMV_COMPOUND_UNCAP_M11_IVF_B64))
        lean_yuv = self.dir / "refmv_compound_uncap_m11_32x32.yuv"
        dec_proc = run(LFFMPEG, "av1-decode-raw", ivf_path, lean_yuv, env=ISO_ENV)
        dec_meta = json.loads(dec_proc.stdout.decode())
        self.assertTrue(dec_meta["ok"])
        self.assertEqual(dec_meta["width"], 32)
        self.assertEqual(dec_meta["height"], 32)
        self.assertEqual(dec_meta["frames"], 5)
        lean_bytes = lean_yuv.read_bytes()
        self.assertEqual(len(lean_bytes), 32 * 32 * 3 // 2 * 5)
        self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), REFMV_COMPOUND_UNCAP_M11_YUV_SHA256)
        if libaom_av1_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(ivf_path))

    def test_strace_execve_zero_children(self):
        in_path = self.dir / "iso_in.yuv"
        in_path.write_bytes(synth_yuv420p(64, 48, 2))
        bs_path = self.dir / "iso.obu"
        out_yuv = self.dir / "iso_out.yuv"
        run(LFFMPEG, "av1-encode-raw", 64, 48, in_path, bs_path, 60, "obu", 1, 1, env=ISO_ENV)
        run(LFFMPEG, "av1-decode-raw", bs_path, out_yuv, env=ISO_ENV)
        run(LFFMPEG, "av1-probe", bs_path, env=ISO_ENV)
        if STRACE is None:
            return
        for cmd in (
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-probe", bs_path],
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-encode-raw", 64, 48, in_path, self.dir / "s.obu"],
            [STRACE, "-f", "-s", "4096", "-e", "trace=execve", LFFMPEG, "av1-decode-raw", bs_path, self.dir / "s.yuv"],
        ):
            proc = run(*cmd, env=ISO_ENV)
            execves = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if "execve(" in ln]
            self.assertEqual(len(execves), 1, execves)
            self.assertIn("lffmpeg", execves[0])


if __name__ == "__main__":
    unittest.main()
