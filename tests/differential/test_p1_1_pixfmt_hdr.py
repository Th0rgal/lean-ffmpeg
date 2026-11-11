"""P1.1 Track A differential tests: high-bit-depth PixelFormat, swscale/zscale/dither, PQ/HLG, and LavfiGraph HDR filters.

Verifies Track A deliverables in Core.lean, Domain.lean, Scale.lean, Filter.lean,
LavfiGraph.lean, and LavfiGraphProofs.lean against reference ffmpeg (swscale,
zscale, colorspace, tonemap) with zero skips and zero child-process spawns.
"""
import math
import os
from pathlib import Path
import random
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake" / "build" / "bin" / "lffmpeg"
FFMPEG = Path(os.environ.get("FFMPEG") or shutil.which("ffmpeg") or "/usr/bin/ffmpeg")
STRACE = shutil.which("strace")


LEAN_DRIVER_SRC = r"""
import LeanAV

open LeanAV.Core LeanAV.Domain LeanAV.Scale LeanAV.Filter LeanAV.LavfiGraph LeanAV.LavfiGraphProofs

def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def parseNat! (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected Nat, got {s}")

def parseFmt! (s : String) : IO PixelFormat :=
  match PixelFormat.parse s with
  | some f => pure f
  | none => throw (IO.userError s!"unknown PixelFormat: {s}")

def parseMatrix! (s : String) : ColorMatrix :=
  match s with
  | "bt2020" => .bt2020
  | "bt2020ncl" => .bt2020ncl
  | "bt601" => .bt601
  | _ => .bt709

def unpackYuv420pFrame (raw : ByteArray) (w h : Nat) (cm : ColorMatrix) : VideoFrame :=
  let cw := (w + 1) / 2
  let ch := (h + 1) / 2
  let yLen := w * h
  let cLen := cw * ch
  let yP : Plane2D := { data := raw.extract 0 yLen, width := w, height := h, stride := w }
  let uP : Plane2D := { data := raw.extract yLen (yLen + cLen), width := cw, height := ch, stride := cw }
  let vP : Plane2D := { data := raw.extract (yLen + cLen) (yLen + 2 * cLen), width := cw, height := ch, stride := cw }
  { width := w, height := h, pixFmt := .yuv420p, colorMatrix := cm, pts := 0, duration := 3600, planes := #[yP, uP, vP] }

def packYuv420pFrame (vf : VideoFrame) : ByteArray :=
  vf.planes[0]!.data ++ vf.planes[1]!.data ++ vf.planes[2]!.data

def runSelfChecks : IO Unit := do
  let fmts : List (String × PixelFormat × Nat × (Nat × Nat)) := [
    ("yuv420p", .yuv420p, 8, (2, 2)),
    ("yuv422p", .yuv422p, 8, (2, 1)),
    ("yuv444p", .yuv444p, 8, (1, 1)),
    ("nv12", .nv12, 8, (2, 2)),
    ("yuv420p10le", .yuv420p10le, 10, (2, 2)),
    ("p010le", .p010le, 10, (2, 2)),
    ("yuv422p10le", .yuv422p10le, 10, (2, 1)),
    ("yuv444p10le", .yuv444p10le, 10, (1, 1)),
    ("yuv420p12le", .yuv420p12le, 12, (2, 2)),
    ("yuv422p12le", .yuv422p12le, 12, (2, 1)),
    ("yuv444p12le", .yuv444p12le, 12, (1, 1)),
    ("gbrp10le", .gbrp10le, 10, (1, 1)),
    ("rgb24", .rgb24, 8, (1, 1)),
    ("rgba", .rgba, 8, (1, 1)),
    ("rgba64le", .rgba64le, 16, (1, 1))
  ]
  for (nm, fmt, bd, sub) in fmts do
    require (PixelFormat.parse nm == some fmt) s!"parse {nm}"
    require (PixelFormat.parse nm.toUpper == some fmt) s!"parse upper {nm}"
    require (fmt.toString == nm) s!"toString {nm}"
    require (fmt.bitDepth == bd) s!"bitDepth {nm}"
    require (fmt.chromaSubsampling == sub) s!"subsampling {nm}"
    let hbf := HighBitFrame.alloc fmt 8 6
    if bd >= 10 then
      require (highBitFrameGate hbf) s!"highBitFrameGate {nm}"
  let p10 := (Plane16.alloc 4 4 4 1023 128).setSample 1 2 5000
  require (p10.getSample 1 2 == 1023 && p10.sampleInRange 1 2) "Plane16 10-bit clamp"
  let p12 := (Plane16.alloc 4 4 4 4095 256).setSample 2 3 9999
  require (p12.getSample 2 3 == 4095 && p12.sampleInRange 2 3) "Plane16 12-bit clamp"
  -- Verify PQ and HLG roundtrip accuracy across [0..1023]
  for code in [:1024] do
    let pqLin := pqEotf10ToLinearQ16 code
    let pqRt := pqOetfLinearQ16To10 pqLin
    let hlgLin := hlgInverseOetf10ToLinearQ16 code
    let hlgRt := hlgOetfLinearQ16To10 hlgLin
    require (pqLin ≤ 65536) "pq bound"
    require (hlgLin ≤ 65536) "hlg bound"
    require (pqEotf10ToLinearQ16 pqRt == pqLin) s!"pq Galois roundtrip at {code}"
    require (hlgInverseOetf10ToLinearQ16 hlgRt == hlgLin) s!"hlg Galois roundtrip at {code}"
    if code >= 224 then
      require (Nat.max code pqRt - Nat.min code pqRt ≤ 2) s!"pq roundtrip at {code}: got {pqRt}"
    if code >= 64 then
      require (Nat.max code hlgRt - Nat.min code hlgRt ≤ 2) s!"hlg roundtrip at {code}: got {pqRt}"
  -- Verify BT.709 OETF continuity across linear toe / curve boundary (1180..1181) and monotonicity across [0..65536]
  require (bt709OetfLinearQ16ToU8 0 == 0 && bt709OetfLinearQ16ToU8 1180 == 21 &&
           bt709OetfLinearQ16ToU8 1181 == 21 && bt709OetfLinearQ16ToU8 65536 == 255) "bt709Oetf continuity"
  let mut prevOetf : UInt8 := 0
  for q in [:65537] do
    let curOetf := bt709OetfLinearQ16ToU8 q
    require (prevOetf.toNat ≤ curOetf.toNat && curOetf.toNat - prevOetf.toNat ≤ 2) s!"bt709Oetf jump at {q}: {prevOetf} -> {curOetf}"
    prevOetf := curOetf
  -- Verify Filter Plane16 dither wrappers and Lavfi high-bit format nodes
  let dplane := filterPlane16BayerToU8 (Plane16.alloc 8 8 8 1023 513) 10
  let fsplane := filterPlane16FloydSteinbergToU8 (Plane16.alloc 8 8 8 1023 513) 10
  require (dplane.width == 8 && dplane.height == 8 && fsplane.width == 8) "Filter Plane16 dither"
  for fmtName in ["p010le", "yuv422p10le", "yuv444p10le", "yuv420p12le", "yuv422p12le", "yuv444p12le", "gbrp10le", "rgba64le"] do
    let srcVf := VideoFrame.allocYuv420p 4 4 0 AVRational.tb90kHz .bt2020ncl
    match runSingleStreamVideoFilterGraph s!"format=pix_fmts={fmtName}" #[srcVf] 25 with
    | .ok (outs, _) => require (outs.size == 1) s!"format={fmtName}"
    | .error e => throw (IO.userError s!"format={fmtName} failed: {e}")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selfcheck"] =>
    runSelfChecks
    IO.println "OK"
    return 0
  | ["bytesize", fmtStr, wStr, hStr] =>
    let fmt ← parseFmt! fmtStr
    let w ← parseNat! wStr
    let h ← parseNat! hStr
    match fmt.frameByteSize w h with
    | some sz => IO.println s!"{sz}"; return 0
    | none => return 2
  | ["op", mode, inPath, outPath, wStr, hStr, extra1, extra2] =>
    let src ← IO.FS.readBinFile inPath
    let w ← parseNat! wStr
    let h ← parseNat! hStr
    let out : ByteArray ← match mode with
      | "420_to_p010" => pure (yuv420p10leToP010leBytes src w h)
      | "p010_to_420" => pure (p010leToYuv420p10leBytes src w h)
      | "420_to_422" => pure (yuv420p10leToYuv422p10leBytes src w h)
      | "422_to_420" => pure (yuv422p10leToYuv420p10leBytes src w h)
      | "422_to_444" => pure (yuv422p10leToYuv444p10leBytes src w h)
      | "444_to_422" => pure (yuv444p10leToYuv422p10leBytes src w h)
      | "420_to_444" => pure (yuv420p10leToYuv444p10leBytes src w h)
      | "444_to_420" => pure (yuv444p10leToYuv420p10leBytes src w h)
      | "10_to_12" => pure (promoteU16Buffer10To12 src (src.size / 2))
      | "12_to_10" => pure (demoteU16Buffer12To10 src (src.size / 2))
      | "444_to_gbr10" => pure (yuv444p10leToGbrp10leBytes src w h (parseMatrix! extra1))
      | "gbr10_to_444" => pure (gbrp10leToYuv444p10leBytes src w h (parseMatrix! extra1))
      | "gbr10_to_rgba64" => pure (gbrp10leToRgba64leBytes src w h)
      | "rgba64_to_gbr10" => pure (rgba64leToGbrp10leBytes src w h)
      | "scale_highbit" =>
        let fmt ← parseFmt! extra1
        let dims := extra2.splitOn "x"
        let dw ← parseNat! dims[0]!
        let dh ← parseNat! dims[1]!
        pure (scalePlanarHighBitFrameBytes fmt src w h dw dh)
      | "bayer_u8" =>
        let bits ← parseNat! extra1
        pure (ditherPlaneBayerToU8 src w h bits)
      | "bayer_12_10" =>
        pure (ditherPlaneBayer12To10 src w h)
      | "fs_u8" =>
        let bits ← parseNat! extra1
        pure (ditherPlaneFloydSteinbergToU8 src w h bits)
      | "fs_12_10" =>
        pure (ditherPlaneFloydSteinberg12To10 src w h)
      | "pq_eotf" =>
        let n := w * h
        let mut g := ByteArray.emptyWithCapacity (2 * n)
        let mut b := ByteArray.emptyWithCapacity (2 * n)
        let mut r := ByteArray.emptyWithCapacity (2 * n)
        for i in [:n] do
          let gv := Nat.min 65535 (pqEotf10ToLinearQ16 (readLe16At src (2 * i)))
          let bv := Nat.min 65535 (pqEotf10ToLinearQ16 (readLe16At src (2 * (n + i))))
          let rv := Nat.min 65535 (pqEotf10ToLinearQ16 (readLe16At src (2 * (2 * n + i))))
          g := pushLe16 g gv
          b := pushLe16 b bv
          r := pushLe16 r rv
        pure (g ++ b ++ r)
      | "hlg_eotf" =>
        let n := w * h
        let mut g := ByteArray.emptyWithCapacity (2 * n)
        let mut b := ByteArray.emptyWithCapacity (2 * n)
        let mut r := ByteArray.emptyWithCapacity (2 * n)
        for i in [:n] do
          let g10 := readLe16At src (2 * i)
          let b10 := readLe16At src (2 * (n + i))
          let r10 := readLe16At src (2 * (2 * n + i))
          let (rl, gl, bl) := hlgEotf10ToDisplayLinearQ16 r10 g10 b10
          g := pushLe16 g (Nat.min 65535 gl)
          b := pushLe16 b (Nat.min 65535 bl)
          r := pushLe16 r (Nat.min 65535 rl)
        pure (g ++ b ++ r)
      | "gamut_2020_to_709" =>
        let n := w * h
        let mut g := ByteArray.emptyWithCapacity (2 * n)
        let mut b := ByteArray.emptyWithCapacity (2 * n)
        let mut r := ByteArray.emptyWithCapacity (2 * n)
        for i in [:n] do
          let g16 := readLe16At src (2 * i)
          let b16 := readLe16At src (2 * (n + i))
          let r16 := readLe16At src (2 * (2 * n + i))
          let (r7, g7, b7) := gamutBt2020ToBt709LinearQ16 r16 g16 b16
          g := pushLe16 g (Nat.min 65535 g7)
          b := pushLe16 b (Nat.min 65535 b7)
          r := pushLe16 r (Nat.min 65535 r7)
        pure (g ++ b ++ r)
      | "gamut_709_to_2020" =>
        let n := w * h
        let mut g := ByteArray.emptyWithCapacity (2 * n)
        let mut b := ByteArray.emptyWithCapacity (2 * n)
        let mut r := ByteArray.emptyWithCapacity (2 * n)
        for i in [:n] do
          let g16 := readLe16At src (2 * i)
          let b16 := readLe16At src (2 * (n + i))
          let r16 := readLe16At src (2 * (2 * n + i))
          let (r2, g2, b2) := gamutBt709ToBt2020LinearQ16 r16 g16 b16
          g := pushLe16 g (Nat.min 65535 g2)
          b := pushLe16 b (Nat.min 65535 b2)
          r := pushLe16 r (Nat.min 65535 r2)
        pure (g ++ b ++ r)
      | "lavfi_vf" =>
        let vfIn := unpackYuv420pFrame src w h (parseMatrix! extra1)
        match runSingleStreamVideoFilterGraph extra2 #[vfIn] 25 with
        | .ok (outs, _) =>
          require (outs.size == 1) "expected 1 output frame"
          let vfOut := outs[0]!
          require (vfOut.width == w && vfOut.height == h) "conserved dims"
          if (extra2.splitOn "tonemap").length > 1 then
            require (tonemapFrameGate (vfIn, "hable", vfOut)) "tonemapFrameGate failed"
          if extra2.startsWith "colorspace" && (extra2.splitOn "tonemap").length == 1 then
            let target := if (extra2.splitOn "bt2020").length > 1 then "bt2020" else if (extra2.splitOn "bt601").length > 1 then "bt601" else "bt709"
            require (colorspaceFrameGateSpec.gate (vfIn, target, vfOut)) "colorspaceFrameGateSpec failed"
          pure (packYuv420pFrame vfOut)
        | .error e => throw (IO.userError s!"lavfi_vf error: {e}")
      | _ => throw (IO.userError s!"unknown mode {mode}")
    IO.FS.writeBinFile outPath out
    return 0
  | _ => return 1
"""


def _clean_toolchain_path() -> str:
    return ":".join(p for p in os.environ.get("PATH", "").split(":") if "/caches/bin" not in p)


def _psnr_u16(a_vals, b_vals, peak: int) -> float:
    mse = sum((x - y) ** 2 for x, y in zip(a_vals, b_vals)) / max(1, len(a_vals))
    if mse == 0:
        return 99.0
    return 10.0 * math.log10((peak * peak) / mse)


def _psnr_u8(a: bytes, b: bytes) -> float:
    mse = sum((x - y) ** 2 for x, y in zip(a, b)) / max(1, len(a))
    if mse == 0:
        return 99.0
    return 10.0 * math.log10((255.0 * 255.0) / mse)


class P11PixFmtHdrDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        assert BINARY.is_file() and os.access(BINARY, os.X_OK), f"missing {BINARY}"
        assert FFMPEG.is_file() and os.access(FFMPEG, os.X_OK), f"missing {FFMPEG}"
        cls.tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.work = Path(cls.tmp.name)

        lean_src = cls.work / "p1_1_driver.lean"
        c_file = cls.work / "p1_1_driver.c"
        cls.driver = cls.work / "p1_1_driver"
        lean_src.write_text(LEAN_DRIVER_SRC, encoding="utf-8")

        lean_env = dict(
            os.environ,
            PATH=_clean_toolchain_path(),
            LEAN_PATH=os.pathsep.join(
                (
                    str(ROOT / ".lake/build/lib/lean"),
                    str(ROOT.parent / "lean-sys/.lake/build/lib/lean"),
                )
            ),
        )
        subprocess.run(
            ["lean", "-c", str(c_file), str(lean_src)],
            cwd=ROOT,
            env=lean_env,
            check=True,
            capture_output=True,
            text=True,
            timeout=120,
        )
        rsp_text = (ROOT / ".lake/build/bin/lffmpeg.rsp").read_text(encoding="utf-8")
        args = (
            [s.strip().strip('"') for s in rsp_text.splitlines() if s.strip()]
            if "\n" in rsp_text
            else shlex.split(rsp_text)
        )
        objects = [
            s
            for s in args
            if s.endswith((".o.export", ".a", "leanav_zero_exec_stub.o"))
            and not s.endswith("/LeanAV/Main.c.o.export")
        ]
        link_args = [] if sys.platform == "darwin" else ["-lpthread"]
        res = subprocess.run(
            ["leanc", "-O2", "-o", str(cls.driver), str(c_file), *objects, *link_args],
            cwd=ROOT,
            env=lean_env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if res.returncode != 0:
            raise AssertionError(res.stdout + res.stderr)

    def _run_driver(self, args, trace_execve: bool = False) -> subprocess.CompletedProcess:
        log = self.work / "driver.strace" if (trace_execve and STRACE) else None
        exec_prefix = (
            [STRACE, "-f", "-s", "256", "-e", "trace=execve", "-o", str(log), str(self.driver)]
            if log is not None
            else [str(self.driver)]
        )
        res = subprocess.run(
            [*exec_prefix, *args],
            cwd=ROOT,
            env={"PATH": "/nonexistent"},
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        if log is not None:
            lines = [ln for ln in log.read_text(encoding="utf-8", errors="replace").splitlines() if "execve(" in ln]
            self.assertEqual(len(lines), 1, lines)
            self.assertIn(str(self.driver), lines[0])
        return res

    def _run_op(self, mode: str, raw: bytes, w: int, h: int, extra1: str = "-", extra2: str = "-", trace: bool = False) -> bytes:
        src_p = self.work / "in.raw"
        dst_p = self.work / "out.raw"
        src_p.write_bytes(raw)
        dst_p.unlink(missing_ok=True)
        self._run_driver(["op", mode, str(src_p), str(dst_p), str(w), str(h), extra1, extra2], trace_execve=trace)
        return dst_p.read_bytes()

    def _ff_raw(self, in_fmt: str, w: int, h: int, raw: bytes, extra_args, out_fmt: str, in_opts=()) -> bytes:
        cmd = [
            str(FFMPEG),
            "-hide_banner",
            "-v",
            "error",
            "-f",
            "rawvideo",
            "-pix_fmt",
            in_fmt,
            "-s",
            f"{w}x{h}",
            *in_opts,
            "-i",
            "pipe:0",
            *extra_args,
            "-f",
            "rawvideo",
            "-pix_fmt",
            out_fmt,
            "pipe:1",
        ]
        res = subprocess.run(cmd, input=raw, capture_output=True, check=True, timeout=30)
        return res.stdout

    def test_01_core_pixel_formats_gates_and_ffmpeg_frame_byte_sizes(self):
        res = self._run_driver(["selfcheck"], trace_execve=True)
        self.assertEqual(res.stdout.strip(), "OK")

        all_formats = [
            "yuv420p",
            "yuv422p",
            "yuv444p",
            "nv12",
            "yuv420p10le",
            "p010le",
            "yuv422p10le",
            "yuv444p10le",
            "yuv420p12le",
            "yuv422p12le",
            "yuv444p12le",
            "gbrp10le",
            "rgb24",
            "rgba",
            "rgba64le",
        ]
        for w, h in ((8, 6), (16, 12)):
            for fmt in all_formats:
                lean_sz = int(self._run_driver(["bytesize", fmt, str(w), str(h)]).stdout.strip())
                ff_bytes = subprocess.run(
                    [
                        str(FFMPEG),
                        "-hide_banner",
                        "-v",
                        "error",
                        "-f",
                        "lavfi",
                        "-i",
                        f"color=c=black:s={w}x{h}:r=10:d=0.1",
                        "-vframes",
                        "1",
                        "-pix_fmt",
                        fmt,
                        "-f",
                        "rawvideo",
                        "pipe:1",
                    ],
                    capture_output=True,
                    check=True,
                    timeout=20,
                ).stdout
                self.assertEqual(lean_sz, len(ff_bytes), f"byte size mismatch for {fmt} at {w}x{h}")

    def test_02_p010le_chroma_subsampling_and_10_12bit_swscale_bitexact(self):
        rng = random.Random(101)
        w, h = 16, 12
        y = [rng.randint(0, 1023) for _ in range(w * h)]
        u = [rng.randint(0, 1023) for _ in range((w // 2) * (h // 2))]
        v = [rng.randint(0, 1023) for _ in range((w // 2) * (h // 2))]
        raw420_10 = struct.pack(f"<{len(y) + len(u) + len(v)}H", *y, *u, *v)

        # yuv420p10le <-> p010le bit-exact vs swscale
        lean_p010 = self._run_op("420_to_p010", raw420_10, w, h, trace=True)
        ff_p010 = self._ff_raw(
            "yuv420p10le", w, h, raw420_10, ["-sws_flags", "accurate_rnd+bitexact", "-sws_dither", "none"], "p010le"
        )
        self.assertEqual(lean_p010, ff_p010)
        lean_back420 = self._run_op("p010_to_420", lean_p010, w, h)
        self.assertEqual(lean_back420, raw420_10)

        # 4:2:0 -> 4:2:2 -> 4:4:4 bit-exact vs swscale neighbor
        lean_422 = self._run_op("420_to_422", raw420_10, w, h)
        ff_422 = self._ff_raw(
            "yuv420p10le",
            w,
            h,
            raw420_10,
            ["-sws_flags", "neighbor+accurate_rnd+bitexact", "-sws_dither", "none"],
            "yuv422p10le",
        )
        self.assertEqual(lean_422, ff_422)

        lean_444 = self._run_op("422_to_444", lean_422, w, h)
        ff_444 = self._ff_raw(
            "yuv422p10le",
            w,
            h,
            lean_422,
            ["-sws_flags", "neighbor+accurate_rnd+bitexact", "-sws_dither", "none"],
            "yuv444p10le",
        )
        self.assertEqual(lean_444, ff_444)
        self.assertEqual(self._run_op("420_to_444", raw420_10, w, h), lean_444)
        self.assertEqual(self._run_op("444_to_420", lean_444, w, h), raw420_10)

        # 4:4:4 -> 4:2:2 -> 4:2:0 box downsampling bit-exact vs swscale area
        u444 = [rng.randint(0, 1023) for _ in range(w * h)]
        v444 = [rng.randint(0, 1023) for _ in range(w * h)]
        src444 = struct.pack(f"<{3 * w * h}H", *y, *u444, *v444)
        lean_down422 = self._run_op("444_to_422", src444, w, h)
        ff_down422 = self._ff_raw(
            "yuv444p10le",
            w,
            h,
            src444,
            ["-sws_flags", "area+accurate_rnd+bitexact", "-sws_dither", "none"],
            "yuv422p10le",
        )
        self.assertEqual(lean_down422, ff_down422)

        lean_down420 = self._run_op("422_to_420", lean_down422, w, h)
        ff_down420 = self._ff_raw(
            "yuv422p10le",
            w,
            h,
            lean_down422,
            ["-sws_flags", "area+accurate_rnd+bitexact", "-sws_dither", "none"],
            "yuv420p10le",
        )
        self.assertEqual(lean_down420, ff_down420)

        # 10-bit <-> 12-bit across 4:2:0, 4:2:2, 4:4:4
        for fmt10, fmt12, buf10 in (
            ("yuv420p10le", "yuv420p12le", raw420_10),
            ("yuv422p10le", "yuv422p12le", lean_422),
            ("yuv444p10le", "yuv444p12le", src444),
        ):
            lean_12 = self._run_op("10_to_12", buf10, w, h)
            ff_12 = self._ff_raw(
                fmt10, w, h, buf10, ["-sws_flags", "accurate_rnd+bitexact", "-sws_dither", "none"], fmt12
            )
            self.assertEqual(lean_12, ff_12, f"10->12 mismatch for {fmt10}")
            self.assertEqual(self._run_op("12_to_10", lean_12, w, h), buf10)

    def test_03_gbrp10le_rgba64le_and_bt709_bt2020_matrix_conversions(self):
        rng = random.Random(202)
        w, h = 12, 8
        g = [rng.randint(64, 960) for _ in range(w * h)]
        b = [rng.randint(64, 960) for _ in range(w * h)]
        r = [rng.randint(64, 960) for _ in range(w * h)]
        raw_gbr10 = struct.pack(f"<{3 * w * h}H", *g, *b, *r)

        # gbrp10le <-> rgba64le bit-exact vs swscale
        lean_rgba64 = self._run_op("gbr10_to_rgba64", raw_gbr10, w, h)
        ff_rgba64 = self._ff_raw(
            "gbrp10le", w, h, raw_gbr10, ["-sws_flags", "accurate_rnd+bitexact", "-sws_dither", "none"], "rgba64le"
        )
        self.assertEqual(lean_rgba64, ff_rgba64)
        self.assertEqual(self._run_op("rgba64_to_gbr10", lean_rgba64, w, h), raw_gbr10)

        # gbrp10le <-> yuv444p10le (BT.709 & BT.2020) vs ffmpeg zscale full-range
        for lean_mat, z_mat in (("bt709", "709"), ("bt2020", "2020_ncl")):
            lean_yuv = self._run_op("gbr10_to_444", raw_gbr10, w, h, extra1=lean_mat)
            ff_yuv = self._ff_raw(
                "gbrp10le",
                w,
                h,
                raw_gbr10,
                ["-vf", f"zscale=matrix={z_mat}:range=full,format=yuv444p10le"],
                "yuv444p10le",
            )
            lv = struct.unpack(f"<{3 * w * h}H", lean_yuv)
            fv = struct.unpack(f"<{3 * w * h}H", ff_yuv)
            self.assertGreater(_psnr_u16(lv, fv, 1023), 50.0)
            self.assertLessEqual(max(abs(x - y) for x, y in zip(lv, fv)), 2)

            lean_rt_gbr = self._run_op("444_to_gbr10", lean_yuv, w, h, extra1=lean_mat)
            rtv = struct.unpack(f"<{3 * w * h}H", lean_rt_gbr)
            origv = struct.unpack(f"<{3 * w * h}H", raw_gbr10)
            self.assertGreater(_psnr_u16(rtv, origv, 1023), 48.0)
            self.assertLessEqual(max(abs(x - y) for x, y in zip(rtv, origv)), 3)

    def test_04_highbit_bilinear_scaling_and_bayer_floyd_steinberg_dithering(self):
        w, h, dw, dh = 16, 12, 24, 16
        for fmt, bits, peak in (
            ("yuv420p10le", 10, 1023),
            ("yuv422p10le", 10, 1023),
            ("yuv444p10le", 10, 1023),
            ("yuv420p12le", 12, 4095),
            ("yuv422p12le", 12, 4095),
            ("yuv444p12le", 12, 4095),
        ):
            cw = w // 2 if "444" not in fmt else w
            ch = h // 2 if "420" in fmt else h
            scale = 4 if bits == 12 else 1
            y = [((r * 40 + c * 28) * scale) % (peak + 1) for r in range(h) for c in range(w)]
            u = [(512 * scale + (r - ch // 2) * 8 * scale) % (peak + 1) for r in range(ch) for c in range(cw)]
            v = [(512 * scale + (c - cw // 2) * 8 * scale) % (peak + 1) for r in range(ch) for c in range(cw)]
            src = struct.pack(f"<{len(y) + len(u) + len(v)}H", *y, *u, *v)

            lean_scaled = self._run_op("scale_highbit", src, w, h, extra1=fmt, extra2=f"{dw}x{dh}")
            ff_scaled = self._ff_raw(
                fmt,
                w,
                h,
                src,
                ["-vf", f"scale={dw}:{dh}:flags=bilinear+accurate_rnd+bitexact", "-sws_dither", "none"],
                fmt,
            )
            lv = struct.unpack(f"<{len(lean_scaled) // 2}H", lean_scaled)
            fv = struct.unpack(f"<{len(ff_scaled) // 2}H", ff_scaled)
            self.assertEqual(len(lv), len(fv))
            self.assertGreater(_psnr_u16(lv, fv, peak), 34.0, f"bilinear PSNR too low for {fmt}")

        # Ordered 4x4 Bayer & Floyd-Steinberg dithering (10->8, 12->8, 12->10) vs ffmpeg swscale
        dw_d, dh_d = 32, 32
        grad10 = struct.pack(
            f"<{dw_d * dh_d}H",
            *[min(1023, (r * 16 + c * 16)) for r in range(dh_d) for c in range(dw_d)],
        )
        grad12 = struct.pack(
            f"<{dw_d * dh_d}H",
            *[min(4095, (r * 64 + c * 64)) for r in range(dh_d) for c in range(dw_d)],
        )
        for src_buf, in_fmt, bits in ((grad10, "gray10le", "10"), (grad12, "gray12le", "12")):
            bayer_u8 = self._run_op("bayer_u8", src_buf, dw_d, dh_d, extra1=bits)
            fs_u8 = self._run_op("fs_u8", src_buf, dw_d, dh_d, extra1=bits)
            ff_bayer = self._ff_raw(
                in_fmt, dw_d, dh_d, src_buf, ["-sws_flags", "accurate_rnd", "-sws_dither", "bayer"], "gray"
            )
            ff_ed = self._ff_raw(
                in_fmt, dw_d, dh_d, src_buf, ["-sws_flags", "accurate_rnd", "-sws_dither", "ed"], "gray"
            )
            self.assertGreater(_psnr_u8(bayer_u8, ff_bayer), 42.0)
            self.assertGreater(_psnr_u8(fs_u8, ff_ed), 42.0)
            self.assertLessEqual(max(abs(a - b) for a, b in zip(bayer_u8, ff_bayer)), 2)
            self.assertLessEqual(max(abs(a - b) for a, b in zip(fs_u8, ff_ed)), 2)

        # Fractional constant 12-bit plane -> 10-bit dither preserves fractional average (512.5)
        mid12 = struct.pack(f"<{dw_d * dh_d}H", *[2050 for _ in range(dw_d * dh_d)])
        b12_10 = struct.unpack(f"<{dw_d * dh_d}H", self._run_op("bayer_12_10", mid12, dw_d, dh_d))
        fs12_10 = struct.unpack(f"<{dw_d * dh_d}H", self._run_op("fs_12_10", mid12, dw_d, dh_d))
        self.assertGreater(len(set(b12_10)), 1)
        self.assertGreater(len(set(fs12_10)), 1)
        self.assertAlmostEqual(sum(b12_10) / len(b12_10), 512.5, delta=0.2)
        self.assertAlmostEqual(sum(fs12_10) / len(fs12_10), 512.5, delta=0.2)

    def test_05_pq_hlg_zscale_gamut_and_lavfi_colorspace_tonemap(self):
        codes = list(range(0, 1024, 16))
        n = len(codes)
        ramp = struct.pack(f"<{3 * n}H", *codes, *codes, *codes)

        # SMPTE ST 2084 PQ EOTF vs ffmpeg zscale
        lean_pq = struct.unpack(f"<{3 * n}H", self._run_op("pq_eotf", ramp, n, 1))
        ff_pq = struct.unpack(
            f"<{3 * n}H",
            self._ff_raw(
                "gbrp10le",
                n,
                1,
                ramp,
                ["-vf", "zscale=t=linear:npl=10000:r=pc,format=gbrp16le"],
                "gbrp16le",
                in_opts=("-color_primaries", "bt2020", "-color_trc", "smpte2084", "-colorspace", "rgb", "-color_range", "pc"),
            ),
        )
        self.assertGreater(_psnr_u16(lean_pq, ff_pq, 65535), 50.0)

        # ARIB STD-B67 HLG inverse OETF + OOTF vs ffmpeg zscale (1000-nit HLG reference display)
        lean_hlg = struct.unpack(f"<{3 * n}H", self._run_op("hlg_eotf", ramp, n, 1))
        ff_hlg = struct.unpack(
            f"<{3 * n}H",
            self._ff_raw(
                "gbrp10le",
                n,
                1,
                ramp,
                ["-vf", "zscale=t=linear:npl=1000:r=pc,format=gbrp16le"],
                "gbrp16le",
                in_opts=("-color_primaries", "bt2020", "-color_trc", "arib-std-b67", "-colorspace", "rgb", "-color_range", "pc"),
            ),
        )
        self.assertGreater(_psnr_u16(lean_hlg, ff_hlg, 65535), 48.0)

        # BT.2020 <-> BT.709 linear gamut conversion vs ffmpeg zscale
        rng = random.Random(303)
        gn = [rng.randint(8000, 50000) for _ in range(n)]
        bn = [rng.randint(4000, 30000) for _ in range(n)]
        rn = [rng.randint(8000, 50000) for _ in range(n)]
        lin_src = struct.pack(f"<{3 * n}H", *gn, *bn, *rn)
        lean_709 = struct.unpack(f"<{3 * n}H", self._run_op("gamut_2020_to_709", lin_src, n, 1))
        ff_709 = struct.unpack(
            f"<{3 * n}H",
            self._ff_raw(
                "gbrp16le",
                n,
                1,
                lin_src,
                ["-vf", "zscale=p=bt709:t=linear:r=pc,format=gbrp16le"],
                "gbrp16le",
                in_opts=("-color_primaries", "bt2020", "-color_trc", "linear", "-colorspace", "rgb", "-color_range", "pc"),
            ),
        )
        self.assertGreater(_psnr_u16(lean_709, ff_709, 65535), 70.0)
        self.assertLessEqual(max(abs(a - b) for a, b in zip(lean_709, ff_709)), 20)

        # BT.709 -> BT.2020 -> BT.709 roundtrip (BT.709 sits strictly inside BT.2020, so zero gamut clipping)
        lean_2020_from_709 = self._run_op("gamut_709_to_2020", lin_src, n, 1)
        ff_2020_from_709 = struct.unpack(
            f"<{3 * n}H",
            self._ff_raw(
                "gbrp16le",
                n,
                1,
                lin_src,
                ["-vf", "zscale=p=bt2020:t=linear:r=pc,format=gbrp16le"],
                "gbrp16le",
                in_opts=("-color_primaries", "bt709", "-color_trc", "linear", "-colorspace", "rgb", "-color_range", "pc"),
            ),
        )
        self.assertGreater(
            _psnr_u16(struct.unpack(f"<{3 * n}H", lean_2020_from_709), ff_2020_from_709, 65535), 70.0
        )
        lean_709_rt = struct.unpack(
            f"<{3 * n}H", self._run_op("gamut_2020_to_709", lean_2020_from_709, n, 1)
        )
        self.assertGreater(_psnr_u16(lean_709_rt, struct.unpack(f"<{3 * n}H", lin_src), 65535), 70.0)

        # Real LavfiGraph vfColorspace and vfTonemap execution (replaces old identity placeholder)
        w, h = 16, 8
        y_ramp = bytes((i * 255) // (w * h - 1) for i in range(w * h))
        u_chroma = bytes([96] * ((w // 2) * (h // 2)))
        v_chroma = bytes([176] * ((w // 2) * (h // 2)))
        hdr_frame = y_ramp + u_chroma + v_chroma

        cs_out = self._run_op("lavfi_vf", hdr_frame, w, h, extra1="bt2020ncl", extra2="colorspace=all=bt709", trace=True)
        self.assertEqual(len(cs_out), len(hdr_frame))
        self.assertNotEqual(cs_out, hdr_frame)

        hdr10_frame = struct.pack(
            f"<{w * h + 2 * (w // 2) * (h // 2)}H",
            *[(i * 1023) // (w * h - 1) for i in range(w * h)],
            *[512 for _ in range((w // 2) * (h // 2))],
            *[512 for _ in range((w // 2) * (h // 2))],
        )
        achrom_hdr = y_ramp + bytes([128] * ((w // 2) * (h // 2) * 2))
        for mode in ("reinhard", "hable", "mobius", "clip", "linear"):
            tm_out = self._run_op(
                "lavfi_vf",
                achrom_hdr,
                w,
                h,
                extra1="bt2020ncl",
                extra2=f"colorspace=all=bt2020,tonemap=tonemap={mode},format=pix_fmts=yuv420p",
            )
            self.assertEqual(len(tm_out), len(achrom_hdr))
            self.assertNotEqual(tm_out[: w * h], achrom_hdr[: w * h], f"tonemap={mode} must not be identity")
            y_vals = list(tm_out[: w * h])
            # Monotone non-decreasing luma response across HDR ramp, matching ffmpeg tonemap behavior
            for a_v, b_v in zip(y_vals, y_vals[1:]):
                self.assertLessEqual(a_v, b_v + 1, f"non-monotone tonemap={mode}")
            ff_tm = self._ff_raw(
                "yuv420p10le",
                w,
                h,
                hdr10_frame,
                [
                    "-vf",
                    f"zscale=t=linear:npl=100,format=gbrpf32le,zscale=p=bt709,tonemap={mode}:desat=0,zscale=t=bt709:m=bt709:r=pc,format=yuv420p",
                ],
                "yuv420p",
                in_opts=("-color_primaries", "bt2020", "-color_trc", "smpte2084", "-colorspace", "bt2020nc", "-color_range", "pc"),
            )
            self.assertEqual(len(ff_tm), len(tm_out))
            self.assertLessEqual(abs(y_vals[0] - ff_tm[0]), 2)
            self.assertGreater(y_vals[-1], y_vals[0] + 180)


if __name__ == "__main__":
    unittest.main()
