"""P1.1 Track E differential suite: HDR10/HLG colorimetry, ISOBMFF & Matroska/WebM HDR/DoVi,
HEVC UNSPEC62 RPU + AV1 ITU-T T.35 EMDF OBU passthrough, and cross-container MP4 <-> MKV/WebM remux.
"""
import json
import os
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"


def _find_tool(env_key: str, name: str) -> str:
    cand = os.environ.get(env_key) or shutil.which(name)
    if cand and Path(cand).is_file():
        return cand
    for extra in (
        f"/var/lib/sandboxed-node/.scratch/209e2e68-7454-4656-8d75-fe26e00af9d4/opencode/ffbin/{name}",
        f"/usr/local/bin/{name}",
        f"/usr/bin/{name}",
    ):
        if Path(extra).is_file():
            return extra
    raise RuntimeError(f"Required differential tool {name} not found")


FFMPEG = _find_tool("FFMPEG", "ffmpeg")
FFPROBE = _find_tool("FFPROBE", "ffprobe")

RPU_105_HEX = (
    "080908406136506f003ff801ffc00fffd0000008000006800000400000340000"
    "02000001c8000000000000000800000000000000080000000000000000000000"
    "00001000000000000000100000000000000010003fffc0000000000000001808"
    "1f603c01f326b39280"
)
RPU_105 = bytes.fromhex(RPU_105_HEX)


def _patch_mp4_sample_entry_extra(mp4: bytes, entry_fourcc: bytes, extra_boxes: bytes) -> bytes:
    """Append `extra_boxes` inside the first `entry_fourcc` visual sample entry and shift `stco`/`co64`."""
    def walk_patch(buf: bytes, path: tuple[bytes, ...], shift_mdat: int) -> tuple[bytes, bool]:
        out = bytearray()
        pos = 0
        changed = False
        containers = {b"moov", b"trak", b"mdia", b"minf", b"stbl"}
        while pos + 8 <= len(buf):
            sz = struct.unpack(">I", buf[pos:pos + 4])[0]
            fcc = buf[pos + 4:pos + 8]
            if sz < 8 or pos + sz > len(buf):
                out.extend(buf[pos:])
                break
            body = buf[pos + 8:pos + sz]
            if fcc in containers:
                new_body, ch = walk_patch(body, path + (fcc,), shift_mdat)
                changed = changed or ch
                out.extend(struct.pack(">I4s", 8 + len(new_body), fcc) + new_body)
            elif fcc == b"stsd" and len(body) >= 16:
                hdr8 = body[:8]
                eb = body[8:]
                esz = struct.unpack(">I", eb[:4])[0]
                efcc = eb[4:8]
                if efcc == entry_fourcc and esz == len(eb):
                    new_eb = struct.pack(">I4s", esz + len(extra_boxes), efcc) + eb[8:] + extra_boxes
                    new_body = hdr8 + new_eb
                    out.extend(struct.pack(">I4s", 8 + len(new_body), fcc) + new_body)
                    changed = True
                else:
                    out.extend(buf[pos:pos + sz])
            elif fcc == b"stco" and shift_mdat and len(body) >= 8:
                cnt = struct.unpack(">I", body[4:8])[0]
                offs = [struct.unpack(">I", body[8 + 4 * i:12 + 4 * i])[0] + shift_mdat for i in range(cnt)]
                new_body = body[:8] + b"".join(struct.pack(">I", o) for o in offs)
                out.extend(struct.pack(">I4s", 8 + len(new_body), fcc) + new_body)
            elif fcc == b"co64" and shift_mdat and len(body) >= 8:
                cnt = struct.unpack(">I", body[4:8])[0]
                offs = [struct.unpack(">Q", body[8 + 8 * i:16 + 8 * i])[0] + shift_mdat for i in range(cnt)]
                new_body = body[:8] + b"".join(struct.pack(">Q", o) for o in offs)
                out.extend(struct.pack(">I4s", 8 + len(new_body), fcc) + new_body)
            else:
                out.extend(buf[pos:pos + sz])
            pos += sz
        return bytes(out), changed

    # Check whether moov precedes mdat
    pos = 0
    moov_pos = mdat_pos = -1
    while pos + 8 <= len(mp4):
        sz = struct.unpack(">I", mp4[pos:pos + 4])[0]
        fcc = mp4[pos + 4:pos + 8]
        if sz < 8 or pos + sz > len(mp4):
            break
        if fcc == b"moov":
            moov_pos = pos
        elif fcc == b"mdat":
            mdat_pos = pos
        pos += sz
    shift = len(extra_boxes) if (0 <= moov_pos < mdat_pos) else 0
    patched, ok = walk_patch(mp4, (), shift)
    if not ok:
        raise AssertionError(f"Failed to locate sample entry {entry_fourcc!r}")
    return patched


def _make_mdcv_dci_p3() -> bytes:
    return struct.pack(
        ">I4s8H2I",
        32, b"mdcv",
        13250, 34500, 7500, 3000, 34000, 16000, 15635, 16450,
        10000000, 50,
    )


def _make_clli(max_cll: int = 1000, max_fall: int = 400) -> bytes:
    return struct.pack(">I4s2H", 12, b"clli", max_cll, max_fall)


def _make_dvvc(profile: int = 8, level: int = 1, compat: int = 1) -> bytes:
    fcc = b"dvvC" if profile > 7 else b"dvcC"
    flags = (profile << 9) | (level << 3) | 4 | 1
    body = struct.pack(">BBHB", 1, 0, flags, (compat & 0xF) << 4) + bytes(19)
    return struct.pack(">I4s", 32, fcc) + body


def _ffprobe_json(path: Path) -> dict:
    proc = subprocess.run(
        [FFPROBE, "-v", "error", "-show_format", "-show_streams", "-show_frames", "-of", "json", str(path)],
        capture_output=True, text=True, check=True, timeout=60,
    )
    if proc.stderr.strip():
        raise AssertionError(f"ffprobe emitted errors on {path.name}: {proc.stderr}")
    return json.loads(proc.stdout)


HARNESS_LEAN = r"""import LeanAV.Format
import LeanAV.Cli
import LeanAV.PlanIR

open LeanAV.Format LeanAV.Cli LeanAV.PlanIR

def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def tagOfFmt (s : String) : UInt32 :=
  if s == "mp4" then 1 else if s == "mkv" then 2 else if s == "webm" then 3 else 0

def patchFirstMp4SamplePayload (mp4 : ByteArray) (f : ByteArray → Option ByteArray) : Option ByteArray := Id.run do
  let some tracks := p11DemuxMp4ToCrossTracks mp4 | return none
  let mut outTracks : Array P11CrossRemuxTrack := #[]
  let mut patched := false
  for t in tracks do
    if t.kind == .video && !patched && t.samples.size > 0 then
      let mut smps : Array P11CrossSample := #[]
      for s in t.samples do
        let some pay' := f s.data | return none
        smps := smps.push { s with data := pay' }
      outTracks := outTracks.push { t with samples := smps }
      patched := true
    else
      outTracks := outTracks.push t
  if !patched then return none
  p11MuxMp4FromCrossTracks outTracks

def main (args : List String) : IO UInt32 := do
  match args with
  | ["unit-gates"] =>
    let rpuHex := [
      0x08, 0x09, 0x08, 0x40, 0x61, 0x36, 0x50, 0x6F, 0x00, 0x3F, 0xF8, 0x01, 0xFF, 0xC0, 0x0F, 0xFF,
      0xD0, 0x00, 0x00, 0x08, 0x00, 0x00, 0x06, 0x80, 0x00, 0x00, 0x40, 0x00, 0x00, 0x34, 0x00, 0x00,
      0x02, 0x00, 0x00, 0x01, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x10, 0x00, 0x3F, 0xFF, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x08,
      0x1F, 0x60, 0x3C, 0x01, 0xF3, 0x26, 0xB3, 0x92, 0x80].map Nat.toUInt8
    require (hevcRpuPayloadOk (0x19 :: rpuHex)) "105B RPU CRC32 check failed"
    let nal := encodeHevcRpuNal rpuHex
    require (decodeHevcRpuNal nal == some rpuHex) "105B HEVC RPU NAL roundtrip failed"
    let emdf := packDoviEmdf rpuHex
    require (emdf.length == 113) "EMDF length != 113"
    require (unpackDoviEmdf emdf == some rpuHex) "105B EMDF roundtrip failed"
    let bigBody := List.replicate 260 (0x42 : UInt8)
    let bigRpu := bigBody ++ u32beToList (mpeg2Crc32List bigBody) ++ [0x80]
    require (hevcRpuPayloadOk (0x19 :: bigRpu)) "265B RPU CRC32 check failed"
    require (doviVarBitsSizeChunks 255 == [(255, 8), (0, 1)]) "255 variable_bits(8) mismatch"
    require (doviVarBitsSizeChunks 256 == [(0, 8), (1, 1), (0, 8), (0, 1)]) "256 variable_bits(8) mismatch"
    require (doviVarBitsSizeChunks 265 == [(0, 8), (1, 1), (9, 8), (0, 1)]) "265 variable_bits(8) mismatch"
    require (doviVarBitsSizeChunks 512 == [(1, 8), (1, 1), (0, 8), (0, 1)]) "512 variable_bits(8) mismatch"
    require (unpackDoviEmdf (packDoviEmdf bigRpu) == some bigRpu) "265B EMDF (>=256 variable_bits) roundtrip failed"
    let bigObu := encodeAv1T35DoviObu bigRpu
    require (decodeAv1T35DoviObu bigObu == some bigRpu) "265B AV1 T.35 OBU multi-byte LEB128 roundtrip failed"
    let tdAndSeq := ByteArray.mk #[0x12, 0x00, 0x0A, 0x04, 0x00, 0x00, 0x00, 0x42, 0x32, 0x04, 0x01, 0x02, 0x03, 0x04]
    let some injectedTd := injectAv1RpuIntoTu tdAndSeq (ByteArray.mk bigRpu.toArray)
      | throw (IO.userError "injectAv1RpuIntoTu failed on TD+Seq+Frame TU")
    require (extractAv1RpuFromTu injectedTd == some (ByteArray.mk bigRpu.toArray)) "extractAv1RpuFromTu failed on TD+Seq+Meta+Frame TU"
    let tdNoSize := ByteArray.mk (#[0x10] ++ (encodeAv1DoviEmdfObu bigRpu).toArray ++ #[0x32, 0x02, 0xAA, 0xBB])
    require (extractAv1RpuFromTu tdNoSize == some (ByteArray.mk bigRpu.toArray)) "extractAv1RpuFromTu failed on size-less TD TU"
    let badRpu := rpuHex.take 103 ++ [0x00, 0x80]
    require (!hevcRpuPayloadOk (0x19 :: badRpu)) "corrupted RPU CRC32 accepted"
    for fcc in ["avc1", "hvc1", "hev1", "av01"] do
      let box := buildP11HighBitDepthStsdBox fcc 64 48
        (if fcc == "avc1" then "avcC" else if fcc == "av01" then "av1C" else "hvcC")
        [1, 2, 3, 4]
        (encodeColrNclxBoxSpec { colourPrimaries := 9, transferCharacteristics := 16, matrixCoefficients := 9, fullRangeFlag := false })
        (encodeMdcvBoxFull dciP3D65Mastering)
        (encodeClliBoxSpec { maxContentLightLevel := 1000, maxPicAverageLightLevel := 400 })
        (p11WrapMp4BoxStr "dvvC" ⟨(encodeDoviConfigBody doviProfile8).toArray⟩).toList
      require (box.length > 160) s!"stsd builder empty for {fcc}"
    IO.println "p11 unit gates ok"
    return 0
  | ["cross-remux", inFmt, outFmt, inPath, outPath] =>
    let raw ← IO.FS.readBinFile inPath
    let out := leanavLeanP11CrossRemux (tagOfFmt inFmt) (tagOfFmt outFmt) raw
    if out.isEmpty then return 2
    IO.FS.writeBinFile outPath out
    return 0
  | ["hevc-rpu-inject", inMp4, rpuHexStr, outMp4] =>
    let mp4 ← IO.FS.readBinFile inMp4
    let rpu ← IO.FS.readBinFile rpuHexStr
    let some patched := patchFirstMp4SamplePayload mp4 (fun au =>
      let res := leanavLeanP11HevcRpuOp 1 au rpu
      if res.isEmpty then none else some res) | return 3
    IO.FS.writeBinFile outMp4 patched
    return 0
  | ["hevc-rpu-extract", inMp4, outBin] =>
    let mp4 ← IO.FS.readBinFile inMp4
    let some tracks := p11DemuxMp4ToCrossTracks mp4 | return 4
    let some vt := tracks.find? (fun t => t.kind == .video && t.samples.size > 0) | return 4
    let au := (vt.samples[0]!).data
    let got := leanavLeanP11HevcRpuOp 0 au ByteArray.empty
    if got.isEmpty then return 5
    IO.FS.writeBinFile outBin got
    return 0
  | ["av1-rpu-inject", inMp4, rpuBin, outMp4] =>
    let mp4 ← IO.FS.readBinFile inMp4
    let rpu ← IO.FS.readBinFile rpuBin
    let some patched := patchFirstMp4SamplePayload mp4 (fun tu =>
      let res := leanavLeanP11Av1RpuOp 1 tu rpu
      if res.isEmpty then none else some res) | return 6
    IO.FS.writeBinFile outMp4 patched
    return 0
  | ["av1-rpu-extract", inMp4, outBin] =>
    let mp4 ← IO.FS.readBinFile inMp4
    let some tracks := p11DemuxMp4ToCrossTracks mp4 | return 7
    let some vt := tracks.find? (fun t => t.kind == .video && t.samples.size > 0) | return 7
    let tu := (vt.samples[0]!).data
    let got := leanavLeanP11Av1RpuOp 0 tu ByteArray.empty
    if got.isEmpty then return 8
    IO.FS.writeBinFile outBin got
    return 0
  | ["emdf-pack", inBin, outBin] =>
    let raw ← IO.FS.readBinFile inBin
    let packed := packDoviEmdf raw.toList
    IO.FS.writeBinFile outBin (ByteArray.mk packed.toArray)
    return 0
  | ["emdf-unpack", inBin, outBin] =>
    let raw ← IO.FS.readBinFile inBin
    let some unpacked := unpackDoviEmdf raw.toList | return 10
    IO.FS.writeBinFile outBin (ByteArray.mk unpacked.toArray)
    return 0
  | _ => return 9
"""


class P11HdrDoviContainerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file():
            raise AssertionError(f"Missing built lffmpeg binary at {BINARY}")
        cls.tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.work = Path(cls.tmp.name)

        # Compile zero-subprocess Lean harness linked against built LeanAV objects
        lean_src = cls.work / "p11_harness.lean"
        c_src = cls.work / "p11_harness.c"
        cls.harness = cls.work / "p11_harness"
        lean_src.write_text(HARNESS_LEAN)
        lean_bin_dir = "/opt/orb/elan/toolchains/leanprover--lean4---v4.35.0/bin"
        env = dict(os.environ)
        if Path(lean_bin_dir).is_dir():
            env["PATH"] = lean_bin_dir + os.pathsep + env.get("PATH", "")
        env["LEAN_PATH"] = os.pathsep.join(
            (str(ROOT / ".lake/build/lib/lean"), str(ROOT.parent / "lean-sys/.lake/build/lib/lean"))
        )
        subprocess.run(
            ["lean", "-c", str(c_src), str(lean_src)],
            cwd=ROOT, env=env, check=True, capture_output=True, text=True, timeout=180,
        )
        rsp_path = ROOT / ".lake/build/bin/lffmpeg.rsp"
        if rsp_path.is_file():
            rsp_text = rsp_path.read_text()
            args = (
                [s.strip().strip('"') for s in rsp_text.splitlines() if s.strip()]
                if "\n" in rsp_text else shlex.split(rsp_text)
            )
            objects = [
                s for s in args
                if s.endswith((".o.export", ".a", "leanav_zero_exec_stub.o"))
                and not s.endswith("/LeanAV/Main.c.o.export")
            ]
        else:
            objects = (
                [str(ROOT / ".lake/build/c/leanav_zero_exec_stub.o")]
                + [
                    str(p) for p in sorted((ROOT / ".lake/build/ir").rglob("*.c.o.export"))
                    if p.name != "Main.c.o.export"
                ]
                + [str(p) for p in sorted((ROOT.parent / "lean-sys/.lake/build/ir").rglob("*.c.o.export"))]
                + [
                    str(ROOT.parent / "lean-sys/.lake/build/lib/liblean_sys_shim.a"),
                    str(ROOT / ".lake/build/lib/libleanav_dsp.a"),
                ]
            )
        link_args = [] if sys.platform == "darwin" else ["-lpthread"]
        res = subprocess.run(
            ["leanc", "-O2", "-o", str(cls.harness), str(c_src), *objects, *link_args],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=180,
        )
        if res.returncode != 0:
            raise AssertionError(res.stdout + res.stderr)

        cls.rpu_file = cls.work / "rpu105.bin"
        cls.rpu_file.write_bytes(RPU_105)

        # Build compact 10-bit HEVC + AAC MP4 fixture via reference ffmpeg, then attach mdcv/clli/dvvC
        hevc_raw_mp4 = cls.work / "hevc_base.mp4"
        subprocess.run(
            [
                FFMPEG, "-v", "error", "-y",
                "-f", "lavfi", "-i", "testsrc=size=64x48:rate=10:duration=0.3",
                "-f", "lavfi", "-i", "sine=frequency=440:sample_rate=48000:duration=0.3",
                "-c:v", "libx265", "-pix_fmt", "yuv420p10le", "-tag:v", "hvc1",
                "-x265-params", "log-level=error:keyint=5:bframes=0:colorprim=bt2020:transfer=smpte2084:colormatrix=bt2020nc",
                "-color_primaries", "bt2020", "-color_trc", "smpte2084", "-colorspace", "bt2020nc",
                "-c:a", "aac", "-b:a", "96k",
                str(hevc_raw_mp4),
            ],
            check=True, capture_output=True, timeout=120,
        )
        cls.hevc_hdr_dovi_mp4 = cls.work / "hevc_hdr_dovi.mp4"
        cls.hevc_hdr_dovi_mp4.write_bytes(
            _patch_mp4_sample_entry_extra(
                hevc_raw_mp4.read_bytes(),
                b"hvc1",
                _make_mdcv_dci_p3() + _make_clli(1000, 400) + _make_dvvc(8, 1, 1),
            )
        )

        # Build compact 10-bit AV1 + Opus HLG MP4 fixture via reference ffmpeg, plus DoVi profile 10 variant
        av1_raw_mp4 = cls.work / "av1_base.mp4"
        subprocess.run(
            [
                FFMPEG, "-v", "error", "-y",
                "-f", "lavfi", "-i", "testsrc=size=64x48:rate=10:duration=0.2",
                "-f", "lavfi", "-i", "sine=frequency=660:sample_rate=48000:duration=0.2",
                "-vf", "setparams=color_primaries=bt2020:color_trc=arib-std-b67:colorspace=bt2020nc",
                "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "yuv420p10le",
                "-color_primaries", "bt2020", "-color_trc", "arib-std-b67", "-colorspace", "bt2020nc",
                "-c:a", "libopus", "-b:a", "64k", "-strict", "-2",
                str(av1_raw_mp4),
            ],
            check=True, capture_output=True, timeout=120,
        )
        cls.av1_hlg_mp4 = av1_raw_mp4
        cls.av1_dovi_mp4 = cls.work / "av1_dovi10.mp4"
        cls.av1_dovi_mp4.write_bytes(
            _patch_mp4_sample_entry_extra(
                av1_raw_mp4.read_bytes(),
                b"av01",
                _make_mdcv_dci_p3() + _make_clli(1000, 350) + _make_dvvc(10, 1, 1),
            )
        )

    def _run_harness(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(self.harness), *args],
            cwd=ROOT, env={"PATH": "/nonexistent"},
            capture_output=True, text=True, timeout=60,
        )

    def _run_cli_plan(self, argv: list[str]) -> dict:
        proc = subprocess.run(
            [str(BINARY), "plan", *argv],
            cwd=ROOT, env={"PATH": "/nonexistent"},
            capture_output=True, text=True, timeout=30,
        )
        self.assertTrue(proc.stdout.strip(), proc.stderr)
        return json.loads(proc.stdout)

    def test_unit_gates_rpu_crc_emdf_and_high_bitdepth_stsd(self):
        res = self._run_harness("unit-gates")
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("p11 unit gates ok", res.stdout)

    def test_cli_and_plan_ir_hdr_colorimetry_and_p11_pix_fmts_zero_exec(self):
        for pf in (
            "yuv420p10le", "p010le", "yuv422p10le", "yuv444p10le",
            "yuv420p12le", "yuv422p12le", "yuv444p12le", "gbrp10le", "rgba64le",
        ):
            plan = self._run_cli_plan([
                "-i", str(self.hevc_hdr_dovi_mp4),
                "-c:v", "hevc", "-pix_fmt", pf,
                "-color_primaries", "bt2020",
                "-color_trc", "smpte2084",
                "-colorspace", "bt2020nc",
                str(self.work / f"plan_{pf}.mp4"),
            ])
            self.assertEqual(plan["error_count"], 0, pf)
            if pf not in ("yuv420p10le", "p010le"):
                self.assertEqual(plan["backend"]["tier"], "unsupported")
                self.assertFalse(plan["backend"]["delegated_container"])
                self.assertFalse(plan["backend"]["fallback_allowed"])

        bad = subprocess.run(
            [str(BINARY), "plan", "-i", str(self.hevc_hdr_dovi_mp4), "-color_trc", "not_a_trc", "o.mp4"],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=30,
        )
        self.assertNotEqual(bad.returncode, 0)
        self.assertGreater(json.loads(bad.stdout)["error_count"], 0)

    def test_mp4_to_mkv_and_back_preserves_hdr10_mastering_clli_dovi8_and_aac(self):
        mkv_out = self.work / "remux_hevc.mkv"
        mp4_back = self.work / "remux_hevc_back.mp4"

        r1 = self._run_harness("cross-remux", "mp4", "mkv", str(self.hevc_hdr_dovi_mp4), str(mkv_out))
        self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
        p_mkv = _ffprobe_json(mkv_out)
        vs = [s for s in p_mkv["streams"] if s["codec_type"] == "video"][0]
        aus = [s for s in p_mkv["streams"] if s["codec_type"] == "audio"][0]
        self.assertEqual(vs["codec_name"], "hevc")
        self.assertEqual(vs["color_primaries"], "bt2020")
        self.assertEqual(vs["color_transfer"], "smpte2084")
        self.assertEqual(vs["color_space"], "bt2020nc")
        self.assertEqual(aus["codec_name"], "aac")
        sd_types = {sd["side_data_type"] for sd in vs.get("side_data_list", [])}
        self.assertIn("Mastering display metadata", sd_types)
        self.assertIn("Content light level metadata", sd_types)
        self.assertIn("DOVI configuration record", sd_types)
        dovi_sd = [sd for sd in vs["side_data_list"] if sd["side_data_type"] == "DOVI configuration record"][0]
        self.assertEqual(dovi_sd["dv_profile"], 8)
        cll_sd = [sd for sd in vs["side_data_list"] if sd["side_data_type"] == "Content light level metadata"][0]
        self.assertEqual(cll_sd["max_content"], 1000)
        self.assertEqual(cll_sd["max_average"], 400)

        r2 = self._run_harness("cross-remux", "mkv", "mp4", str(mkv_out), str(mp4_back))
        self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
        p_mp4 = _ffprobe_json(mp4_back)
        vs2 = [s for s in p_mp4["streams"] if s["codec_type"] == "video"][0]
        aus2 = [s for s in p_mp4["streams"] if s["codec_type"] == "audio"][0]
        self.assertEqual(vs2["codec_name"], "hevc")
        self.assertEqual(vs2["color_primaries"], "bt2020")
        self.assertEqual(vs2["color_transfer"], "smpte2084")
        self.assertEqual(aus2["codec_name"], "aac")
        sd2 = {sd["side_data_type"] for sd in vs2.get("side_data_list", [])}
        self.assertIn("Mastering display metadata", sd2)
        self.assertIn("Content light level metadata", sd2)
        self.assertIn("DOVI configuration record", sd2)

    def test_mp4_to_webm_and_back_preserves_av1_hlg_and_opus(self):
        webm_out = self.work / "remux_av1.webm"
        mp4_back = self.work / "remux_av1_back.mp4"

        r1 = self._run_harness("cross-remux", "mp4", "webm", str(self.av1_hlg_mp4), str(webm_out))
        self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
        p_webm = _ffprobe_json(webm_out)
        self.assertIn("webm", p_webm["format"]["format_name"])
        vs = [s for s in p_webm["streams"] if s["codec_type"] == "video"][0]
        aus = [s for s in p_webm["streams"] if s["codec_type"] == "audio"][0]
        self.assertEqual(vs["codec_name"], "av1")
        self.assertEqual(vs["color_primaries"], "bt2020")
        self.assertEqual(vs["color_transfer"], "arib-std-b67")
        self.assertEqual(vs["color_space"], "bt2020nc")
        self.assertEqual(aus["codec_name"], "opus")

        r2 = self._run_harness("cross-remux", "webm", "mp4", str(webm_out), str(mp4_back))
        self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
        p_mp4 = _ffprobe_json(mp4_back)
        vs2 = [s for s in p_mp4["streams"] if s["codec_type"] == "video"][0]
        aus2 = [s for s in p_mp4["streams"] if s["codec_type"] == "audio"][0]
        self.assertEqual(vs2["codec_name"], "av1")
        self.assertEqual(vs2["color_transfer"], "arib-std-b67")
        self.assertEqual(aus2["codec_name"], "opus")

    def test_hevc_unspec62_rpu_inject_extract_and_ffprobe_frame_metadata(self):
        injected_mp4 = self.work / "hevc_with_rpu.mp4"
        injected_mkv = self.work / "hevc_with_rpu.mkv"
        extracted_rpu = self.work / "hevc_extracted.rpu"

        inj = self._run_harness("hevc-rpu-inject", str(self.hevc_hdr_dovi_mp4), str(self.rpu_file), str(injected_mp4))
        self.assertEqual(inj.returncode, 0, inj.stdout + inj.stderr)

        ext = self._run_harness("hevc-rpu-extract", str(injected_mp4), str(extracted_rpu))
        self.assertEqual(ext.returncode, 0, ext.stdout + ext.stderr)
        self.assertEqual(extracted_rpu.read_bytes(), RPU_105)

        probe_mp4 = _ffprobe_json(injected_mp4)
        vframes = [f for f in probe_mp4["frames"] if f.get("media_type") == "video"]
        self.assertGreater(len(vframes), 0)
        f_sd = {sd["side_data_type"] for sd in vframes[0].get("side_data_list", [])}
        self.assertIn("Dolby Vision RPU Data", f_sd)
        self.assertIn("Dolby Vision Metadata", f_sd)

        to_mkv = self._run_harness("cross-remux", "mp4", "mkv", str(injected_mp4), str(injected_mkv))
        self.assertEqual(to_mkv.returncode, 0, to_mkv.stdout + to_mkv.stderr)
        probe_mkv = _ffprobe_json(injected_mkv)
        vframes_mkv = [f for f in probe_mkv["frames"] if f.get("media_type") == "video"]
        f_sd_mkv = {sd["side_data_type"] for sd in vframes_mkv[0].get("side_data_list", [])}
        self.assertIn("Dolby Vision Metadata", f_sd_mkv)

    def test_av1_t35_emdf_rpu_inject_extract_and_ffprobe_frame_metadata(self):
        injected_mp4 = self.work / "av1_with_rpu.mp4"
        injected_webm = self.work / "av1_with_rpu.webm"
        extracted_rpu = self.work / "av1_extracted.rpu"

        inj = self._run_harness("av1-rpu-inject", str(self.av1_dovi_mp4), str(self.rpu_file), str(injected_mp4))
        self.assertEqual(inj.returncode, 0, inj.stdout + inj.stderr)

        ext = self._run_harness("av1-rpu-extract", str(injected_mp4), str(extracted_rpu))
        self.assertEqual(ext.returncode, 0, ext.stdout + ext.stderr)
        self.assertEqual(extracted_rpu.read_bytes(), RPU_105)

        probe_mp4 = _ffprobe_json(injected_mp4)
        vframes = [f for f in probe_mp4["frames"] if f.get("media_type") == "video"]
        self.assertGreater(len(vframes), 0)
        f_sd_list = vframes[0].get("side_data_list", [])
        f_sd = {sd["side_data_type"] for sd in f_sd_list}
        self.assertIn("Dolby Vision Metadata", f_sd)
        dovi_meta = [sd for sd in f_sd_list if sd["side_data_type"] == "Dolby Vision Metadata"][0]
        self.assertEqual(dovi_meta["rpu_type"], 2)

        to_webm = self._run_harness("cross-remux", "mp4", "webm", str(injected_mp4), str(injected_webm))
        self.assertEqual(to_webm.returncode, 0, to_webm.stdout + to_webm.stderr)
        probe_webm = _ffprobe_json(injected_webm)
        vs = [s for s in probe_webm["streams"] if s["codec_type"] == "video"][0]
        s_sd = {sd["side_data_type"] for sd in vs.get("side_data_list", [])}
        self.assertIn("DOVI configuration record", s_sd)
        vframes_webm = [f for f in probe_webm["frames"] if f.get("media_type") == "video"]
        f_sd_webm = {sd["side_data_type"] for sd in vframes_webm[0].get("side_data_list", [])}
        self.assertIn("Dolby Vision Metadata", f_sd_webm)

        reencoded_mp4 = self.work / "av1_reencoded_with_rpu.mp4"
        reencoded_rpu = self.work / "av1_reencoded_extracted.rpu"
        proc_reenc = subprocess.run(
            [str(BINARY), "-y", "-i", str(injected_mp4), "-an", "-c:v", "av1", "-pix_fmt", "yuv420p10le", str(reencoded_mp4)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(proc_reenc.returncode, 0, proc_reenc.stdout + proc_reenc.stderr)
        ext_reenc = self._run_harness("av1-rpu-extract", str(reencoded_mp4), str(reencoded_rpu))
        self.assertEqual(ext_reenc.returncode, 0, ext_reenc.stdout + ext_reenc.stderr)
        self.assertEqual(reencoded_rpu.read_bytes(), RPU_105)
        probe_reenc = _ffprobe_json(reencoded_mp4)
        vframes_reenc = [f for f in probe_reenc["frames"] if f.get("media_type") == "video"]
        f_sd_reenc = {sd["side_data_type"] for sd in vframes_reenc[0].get("side_data_list", [])}
        self.assertIn("Dolby Vision Metadata", f_sd_reenc)

    def test_av1_itu_t35_dovi_emdf_multi_chunk_variable_bits_and_ffprobe(self):
        def ref_pack_emdf(rpu: bytes) -> bytes:
            # Independent ETSI TS 103 190-1 §4.2.3 variable_bits(8) + AV1 OBU trailing_bits() reference
            n = len(rpu)
            chunks = []
            v = n
            while True:
                chunks.append(v & 0xFF)
                if v < 256:
                    break
                v = (v >> 8) - 1
            chunks.reverse()
            bits = []
            def push(val: int, width: int) -> None:
                for shift in range(width - 1, -1, -1):
                    bits.append((val >> shift) & 1)
            push(0x01BE6841, 27)
            for idx, ch in enumerate(chunks):
                push(ch, 8)
                push(1 if idx + 1 < len(chunks) else 0, 1)
            for b in rpu:
                push(b, 8)
            push(0x0400, 17)
            push(1, 1)
            while len(bits) % 8 != 0:
                bits.append(0)
            out = bytearray(sum(bits[i + j] << (7 - j) for j in range(8)) for i in range(0, len(bits), 8))
            out.append(0x80)
            return bytes(out)

        for sz in (1, 105, 254, 255, 256, 284, 511, 512, 770):
            payload = bytes(((i * 37 + 13) & 0xFF) for i in range(sz))
            in_p = self.work / f"emdf_in_{sz}.bin"
            pk_p = self.work / f"emdf_pk_{sz}.bin"
            un_p = self.work / f"emdf_un_{sz}.bin"
            in_p.write_bytes(payload)
            r_pk = self._run_harness("emdf-pack", str(in_p), str(pk_p))
            self.assertEqual(r_pk.returncode, 0, r_pk.stdout + r_pk.stderr)
            self.assertEqual(pk_p.read_bytes(), ref_pack_emdf(payload), f"EMDF mismatch at size={sz}")
            r_un = self._run_harness("emdf-unpack", str(pk_p), str(un_p))
            self.assertEqual(r_un.returncode, 0, r_un.stdout + r_un.stderr)
            self.assertEqual(un_p.read_bytes(), payload, f"EMDF unpack mismatch at size={sz}")

        def mpeg2_crc32(data: bytes) -> int:
            crc = 0xFFFFFFFF
            for b in data:
                crc ^= b << 24
                for _ in range(8):
                    crc = ((crc << 1) ^ 0x04C11DB7) & 0xFFFFFFFF if (crc & 0x80000000) else (crc << 1) & 0xFFFFFFFF
            return crc

        # Construct a valid 284-byte (>=256B, 2-chunk variable_bits(8) + 2-byte AV1 LEB128) Dolby Vision RPU
        bs = "".join(f"{b:08b}" for b in RPU_105[:-5])[:-1] + "000010101"
        while len(bs) % 8 != 0:
            bs += "0"
        bs += ("0001000" + "00000101" + ("0" * 56)) * 20
        while len(bs) % 8 != 0:
            bs += "0"
        body_284 = bytes(int(bs[i : i + 8], 2) for i in range(0, len(bs), 8))
        rpu_284 = body_284 + mpeg2_crc32(body_284).to_bytes(4, "big") + b"\x80"
        self.assertEqual(len(rpu_284), 284)

        rpu_284_path = self.work / "dovi_284.rpu"
        rpu_284_path.write_bytes(rpu_284)
        inj_284_mp4 = self.work / "av1_injected_284.mp4"
        ext_284_rpu = self.work / "av1_extracted_284.rpu"
        reenc_284_mp4 = self.work / "av1_reencoded_284.mp4"
        reenc_284_rpu = self.work / "av1_reencoded_284.rpu"

        inj = self._run_harness("av1-rpu-inject", str(self.av1_dovi_mp4), str(rpu_284_path), str(inj_284_mp4))
        self.assertEqual(inj.returncode, 0, inj.stdout + inj.stderr)
        ext = self._run_harness("av1-rpu-extract", str(inj_284_mp4), str(ext_284_rpu))
        self.assertEqual(ext.returncode, 0, ext.stdout + ext.stderr)
        self.assertEqual(ext_284_rpu.read_bytes(), rpu_284)

        pr_inj = subprocess.run(
            [FFPROBE, "-v", "warning", "-show_frames", "-of", "json", str(inj_284_mp4)],
            check=True, capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(pr_inj.stderr, "", f"libdav1d emitted warning on >=256B EMDF: {pr_inj.stderr}")
        vf_inj = [f for f in json.loads(pr_inj.stdout)["frames"] if f.get("media_type") == "video"]
        self.assertIn("Dolby Vision Metadata", {sd["side_data_type"] for sd in vf_inj[0].get("side_data_list", [])})

        proc_reenc = subprocess.run(
            [str(BINARY), "-y", "-i", str(inj_284_mp4), "-an", "-c:v", "av1", "-pix_fmt", "yuv420p10le", str(reenc_284_mp4)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(proc_reenc.returncode, 0, proc_reenc.stdout + proc_reenc.stderr)
        ext2 = self._run_harness("av1-rpu-extract", str(reenc_284_mp4), str(reenc_284_rpu))
        self.assertEqual(ext2.returncode, 0, ext2.stdout + ext2.stderr)
        self.assertEqual(reenc_284_rpu.read_bytes(), rpu_284)
        pr_reenc = subprocess.run(
            [FFPROBE, "-v", "warning", "-show_frames", "-of", "json", str(reenc_284_mp4)],
            check=True, capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(pr_reenc.stderr, "", f"libdav1d emitted warning after re-encode: {pr_reenc.stderr}")
        vf_reenc = [f for f in json.loads(pr_reenc.stdout)["frames"] if f.get("media_type") == "video"]
        self.assertIn("Dolby Vision Metadata", {sd["side_data_type"] for sd in vf_reenc[0].get("side_data_list", [])})

    def test_native_same_family_remux_preserves_hdr_dovi_and_rejects_cross_container_cli(self):
        same_out = self.work / "native_same_hdr.mp4"
        proc = subprocess.run(
            [str(BINARY), "-y", "-i", str(self.hevc_hdr_dovi_mp4), "-c", "copy", str(same_out)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        p_same = _ffprobe_json(same_out)
        vs = [s for s in p_same["streams"] if s["codec_type"] == "video"][0]
        sd = {x["side_data_type"] for x in vs.get("side_data_list", [])}
        self.assertIn("Mastering display metadata", sd)
        self.assertIn("Content light level metadata", sd)
        self.assertIn("DOVI configuration record", sd)

        # Same-family rejection in cross-remux helper
        bad = self._run_harness("cross-remux", "mp4", "mp4", str(self.hevc_hdr_dovi_mp4), str(self.work / "no.mp4"))
        self.assertNotEqual(bad.returncode, 0)

    def test_bframe_hevc_hdr_cross_container_cli_preserves_decode_and_pts_order(self):
        bframe_raw = self.work / "hevc_bframe_raw.mp4"
        subprocess.run(
            [
                FFMPEG, "-v", "error", "-y",
                "-f", "lavfi", "-i", "testsrc=size=64x48:rate=25:duration=0.4",
                "-f", "lavfi", "-i", "sine=frequency=440:sample_rate=48000:duration=0.4",
                "-c:v", "libx265", "-pix_fmt", "yuv420p10le", "-tag:v", "hvc1",
                "-x265-params", "log-level=error:keyint=10:bframes=3:b-adapt=0:colorprim=bt2020:transfer=smpte2084:colormatrix=bt2020nc",
                "-color_primaries", "bt2020", "-color_trc", "smpte2084", "-colorspace", "bt2020nc",
                "-c:a", "aac", "-b:a", "96k",
                str(bframe_raw),
            ],
            check=True, capture_output=True, timeout=120,
        )
        bframe_mp4 = self.work / "hevc_bframe_hdr.mp4"
        bframe_mp4.write_bytes(
            _patch_mp4_sample_entry_extra(
                bframe_raw.read_bytes(),
                b"hvc1",
                _make_mdcv_dci_p3() + _make_clli(1000, 400) + _make_dvvc(8, 1, 1),
            )
        )
        out_mkv = self.work / "hevc_bframe_hdr.mkv"
        out_mp4 = self.work / "hevc_bframe_hdr_rt.mp4"
        r1 = subprocess.run(
            [str(BINARY), "-y", "-i", str(bframe_mp4), "-c", "copy", str(out_mkv)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
        r2 = subprocess.run(
            [str(BINARY), "-y", "-i", str(out_mkv), "-c", "copy", str(out_mp4)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)

        def _video_pkt_hashes_and_pts_order(path: Path) -> tuple[list[bytes], list[str]]:
            pkts = json.loads(
                subprocess.run(
                    [FFPROBE, "-v", "error", "-select_streams", "v:0", "-show_packets", "-show_data_hash", "MD5", "-of", "json", str(path)],
                    check=True, capture_output=True, text=True, timeout=30,
                ).stdout
            )["packets"]
            hashes = [p["data_hash"].encode() for p in pkts]
            # Confirm stream genuinely contains out-of-order B-frame presentation timestamps
            pts_list = [float(p["pts_time"]) for p in pkts]
            self.assertNotEqual(pts_list, sorted(pts_list), f"Expected B-frame reordering in {path}")
            raw_yuv = subprocess.run(
                [FFMPEG, "-v", "error", "-i", str(path), "-f", "rawvideo", "-pix_fmt", "yuv420p10le", "-"],
                check=True, capture_output=True, timeout=30,
            ).stdout
            fbytes = 64 * 48 * 3
            self.assertEqual(len(raw_yuv), 10 * fbytes)
            import hashlib
            frame_md5s = [hashlib.md5(raw_yuv[i * fbytes:(i + 1) * fbytes]).hexdigest() for i in range(10)]
            return hashes, frame_md5s

        orig_hashes, orig_frames = _video_pkt_hashes_and_pts_order(bframe_mp4)
        mkv_hashes, mkv_frames = _video_pkt_hashes_and_pts_order(out_mkv)
        rt_hashes, rt_frames = _video_pkt_hashes_and_pts_order(out_mp4)
        self.assertEqual(mkv_hashes, orig_hashes)
        self.assertEqual(rt_hashes, orig_hashes)
        self.assertEqual(mkv_frames, orig_frames)
        self.assertEqual(rt_frames, orig_frames)

    def test_malformed_mp4_and_mkv_hdr_dovi_boxes_fail_closed(self):
        base_bytes = self.hevc_hdr_dovi_mp4.read_bytes()
        # 1. Truncated mdcv box (size 16 instead of 32)
        bad_mdcv = self.work / "bad_mdcv.mp4"
        bad_mdcv.write_bytes(
            _patch_mp4_sample_entry_extra(
                (self.work / "hevc_base.mp4").read_bytes(),
                b"hvc1",
                struct.pack(">I4s8s", 16, b"mdcv", b"\x00" * 8),
            )
        )
        # 2. Invalid clli box (maxFALL > maxCLL when maxCLL > 0)
        bad_clli = self.work / "bad_clli.mp4"
        bad_clli.write_bytes(
            _patch_mp4_sample_entry_extra(
                (self.work / "hevc_base.mp4").read_bytes(),
                b"hvc1",
                _make_clli(400, 900),
            )
        )
        # 3. Malformed dvvC box (version_major=99 fails doviConfigGateSpec)
        bad_dvvc = self.work / "bad_dvvc.mp4"
        bad_dvvc.write_bytes(
            _patch_mp4_sample_entry_extra(
                (self.work / "hevc_base.mp4").read_bytes(),
                b"hvc1",
                struct.pack(">I4sBBBB20s", 32, b"dvvC", 99, 0, (8 << 1) | 1, 1 << 3, b"\x00" * 20),
            )
        )
        for idx, bad_src in enumerate((bad_mdcv, bad_clli, bad_dvvc)):
            bad_out = self.work / f"bad_out_{idx}.mkv"
            proc = subprocess.run(
                [str(BINARY), "-y", "-i", str(bad_src), "-c", "copy", str(bad_out)],
                cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=30,
            )
            self.assertNotEqual(proc.returncode, 0, f"Expected fail-closed for {bad_src.name}")
            self.assertFalse(bad_out.exists(), f"Output file created on malformed {bad_src.name}")

        # 4. Valid MKV mutated with invalid MaxFALL > MaxCLL inside Colour (0x55BC / 0x55BD)
        good_mkv = self.work / "good_for_tamper.mkv"
        r_good = subprocess.run(
            [str(BINARY), "-y", "-i", str(self.hevc_hdr_dovi_mp4), "-c", "copy", str(good_mkv)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(r_good.returncode, 0, r_good.stdout + r_good.stderr)
        mkv_raw = good_mkv.read_bytes()
        cll_pat = bytes([0x55, 0xBC, 0x82, 0x03, 0xE8, 0x55, 0xBD, 0x82, 0x01, 0x90])
        self.assertIn(cll_pat, mkv_raw)
        bad_mkv = self.work / "bad_clli.mkv"
        bad_mkv.write_bytes(mkv_raw.replace(cll_pat, bytes([0x55, 0xBC, 0x82, 0x01, 0x90, 0x55, 0xBD, 0x82, 0x03, 0xE8]), 1))
        bad_mkv_out = self.work / "bad_mkv_out.mp4"
        proc_mkv = subprocess.run(
            [str(BINARY), "-y", "-i", str(bad_mkv), "-c", "copy", str(bad_mkv_out)],
            cwd=ROOT, env={"PATH": "/nonexistent"}, capture_output=True, text=True, timeout=30,
        )
        self.assertNotEqual(proc_mkv.returncode, 0, "Expected fail-closed on MKV MaxFALL > MaxCLL")
        self.assertFalse(bad_mkv_out.exists())


if __name__ == "__main__":
    unittest.main()
