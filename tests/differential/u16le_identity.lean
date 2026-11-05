import LeanAV.Encoder

open LeanAV.Scale LeanAV.Encoder LeanAV.Format LeanAV.NativeKernels

@[extern "identity_test_take_calls"] opaque takeCalls : IO UInt64
@[extern "identity_test_take_luma_stats_calls"] opaque takeLumaStatsCalls : IO UInt64
@[extern "identity_test_take_extract_msb8_calls"] opaque takeExtractMsb8Calls : IO UInt64

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def pureScale (src : ByteArray) (sw sh dw dh : Nat) : ByteArray :=
  let xt := buildBilinearTabQ8 sw dw
  let yt := buildBilinearTabQ8 sh dh
  let uxt := buildBilinearTabQ8 (sw / 2) (dw / 2)
  let uyt := buildBilinearTabQ8 (sh / 2) (dh / 2)
  scalePlaneBilinearU16LeBytes src 0 sw sh dw dh xt yt ++
    scalePlaneBilinearU16LeBytes src (sw * sh * 2) (sw / 2) (sh / 2) (dw / 2) (dh / 2) uxt uyt ++
    scalePlaneBilinearU16LeBytes src ((sw * sh + (sw / 2) * (sh / 2)) * 2)
      (sw / 2) (sh / 2) (dw / 2) (dh / 2) uxt uyt

def pureLumaStatsPacked (src : ByteArray) (nPixels step : Nat) : UInt64 := Id.run do
  let n := Nat.min nPixels (src.size / 2)
  if n == 0 || step == 0 then return 0
  let mut sum : UInt64 := 0
  let mut sumSq : UInt64 := 0
  let mut cnt : UInt64 := 0
  let mut i : Nat := 0
  while i < n do
    let bOff := i * 2
    let u16 : UInt64 := (src.get! bOff).toUInt64 ||| ((src.get! (bOff + 1)).toUInt64 <<< 8)
    let v := u16 >>> 2
    sum := sum + v
    sumSq := sumSq + v * v
    cnt := cnt + 1
    i := i + step
  return computeLumaMeanVarPackedU64 sum sumSq cnt

unsafe def unitTests : IO Unit := do
  let _ ← takeCalls
  let _ ← takeLumaStatsCalls
  let _ ← takeExtractMsb8Calls
  -- Admission boundaries are checked without allocating the claimed footprint.
  for (a, expected) in [
      ((2, 2, 2, 2, 12), true), ((2, 2, 2, 2, 13), true),
      ((0xFFFFFE, 0xFFFFFE, 0xFFFFFE, 0xFFFFFE, 0xFFFFFFFFFFFFFFFF), true),
      ((2, 2, 2, 2, 11), false), ((0, 2, 0, 2, 0), false),
      ((2, 0, 2, 0, 0), false), ((1, 2, 1, 2, 4), false),
      ((3, 2, 3, 2, 16), false), ((2, 3, 2, 3, 16), false),
      ((2, 2, 4, 2, 12), false), ((2, 2, 2, 4, 12), false),
      ((0x1000000, 2, 0x1000000, 2, 0xFFFFFFFFFFFFFFFF), false),
      ((2, 0x1000000, 2, 0x1000000, 0xFFFFFFFFFFFFFFFF), false),
      ((2, 2, 2, 2, 0x10000000000000000), false)] do
    require (yuv420p10leIdentityZeroCopyGateSpec.gate a == expected) s!"gate {a}"
  for (w, h) in [(2, 2), (4, 6), (16, 16), (18, 10), (256, 256)] do
    let n := w * h + 2 * ((w / 2) * (h / 2))
    let mut raw := ByteArray.emptyWithCapacity (n * 2)
    for i in [:n] do
      -- The largest frame exhausts all 65,536 UInt16 bit patterns.
      raw := (raw.push i.toUInt8).push (i / 256).toUInt8
    for padding in [0, 1, 2, 17] do
      let src := raw ++ ByteArray.mk (Array.replicate padding 0xA5)
      let _ ← takeCalls
      let out := scaleFrameYuv420p10LeAuto src w h w h #[] #[] #[] #[]
      require (out.data == raw.data) "identity bytes / padding"
      require ((← takeCalls) == 0) "identity called native scaler"
      if padding == 0 then require (ptrEq src out) "identity allocated instead of reusing source"
      require (out.data == (pureScale src w h w h).data) "pure identity mismatch"
      let native := execLnirScale2dYuv420p10LeBaC src w.toUInt64 h.toUInt64 w.toUInt64 h.toUInt64
      require (out.data == native.data) "native memcpy mismatch"
      require ((← takeCalls) == 1) "native counter positive control"
    for cap in [0, 1, raw.size - 1] do
      let short := raw.extract 0 cap
      let out := scaleFrameYuv420p10LeAuto short w h w h #[] #[] #[] #[]
      require (out.data == (pureScale short w h w h).data) "short fallback mismatch"
      require ((← takeCalls) == 0) "short source called native scaler"
  for (w, h) in [(0, 0), (0, 2), (2, 0), (1, 2), (3, 2), (2, 3)] do
    let n := (w * h + 2 * ((w / 2) * (h / 2))) * 2
    let src := ByteArray.mk (Array.replicate n 0xFF)
    let out := scaleFrameYuv420p10LeAuto src w h w h #[] #[] #[] #[]
    require (out.data == (pureScale src w h w h).data) "odd / empty fallback mismatch"
    require ((← takeCalls) == 0) "invalid geometry called native scaler"
  for (sw, sh, dw, dh) in [(20, 12, 10, 6), (30, 18, 10, 6), (14, 10, 8, 6), (6, 4, 14, 10)] do
    let n := (sw * sh + 2 * ((sw / 2) * (sh / 2))) * 2
    let src := ByteArray.mk ((List.range n).toArray.map (fun i => (i * 137 + 255).toUInt8))
    let out := scaleFrameYuv420p10LeAuto src sw sh dw dh #[] #[] #[] #[]
    require (out.data == (pureScale src sw sh dw dh).data) "resize differential mismatch"
    require ((← takeCalls) == 1) "resize bypassed native scaler"
  -- Direct C-ABI interposition & differential checks for luma_stats_u16le and extract_u16le_msb8
  -- across empty, short/odd-byte, normal, SIMD-tail, and strided (>65536) inputs.
  for n in [0, 1, 2, 15, 16, 17, 31, 32, 33, 65536, 65537] do
    let mut base := ByteArray.emptyWithCapacity (n * 2)
    for i in [:n] do
      let v := (i * 7919 + 65535) % 65536
      base := (base.push v.toUInt8).push (v / 256).toUInt8
    for tail in [#[], #[0xFD], #[0x34, 0x12, 0xFE]] do
      let src := base ++ ByteArray.mk tail
      let capPx := src.size / 2
      for req in [0, 1, capPx / 2, capPx, capPx + 9] do
        let _ ← takeExtractMsb8Calls
        let extDirect := execLnirExtractU16LeMsb8BaC src req.toUInt64
        require ((← takeExtractMsb8Calls) == 1) "direct extract C-ABI counter"
        let extPure := extractU16LeMsb8Pure src req
        require (extDirect.data == extPure.data) s!"direct extract mismatch n={n} req={req}"
        let extFast := extractU16LeMsb8Fast src req
        require ((← takeExtractMsb8Calls) == 1) "fast extract C-ABI counter"
        require (extFast.data == extPure.data) s!"fast extract mismatch n={n} req={req}"
        for step in [0, 1, 3, 16, 17] do
          let _ ← takeLumaStatsCalls
          let stDirect := execLnirLumaStatsU16LeBaC src req.toUInt64 step.toUInt64
          require ((← takeLumaStatsCalls) == 1) "direct stats C-ABI counter"
          let stRef := pureLumaStatsPacked src req step
          require (stDirect == stRef) s!"direct stats mismatch n={n} req={req} step={step}"
        let _ ← takeLumaStatsCalls
        let stFast := computeLumaStatsU16LeFast src req
        require ((← takeLumaStatsCalls) == 1) "fast stats C-ABI counter"
        require (stFast == computeLumaStatsU16LePure src req) s!"fast stats mismatch n={n} req={req}"
  require ((← takeCalls) == 0) "unexpected scale calls during stats/extract checks"
  IO.println "unit identity, pointer reuse, native/pure differential and fallback checks passed"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [] => unitTests
  | ["wrappers", inPath, outScalePath, outMsbPath, swStr, shStr, dwStr, dhStr, nPxStr, stepStr] =>
    let src ← IO.FS.readBinFile inPath
    let sw := swStr.toNat!
    let sh := shStr.toNat!
    let dw := dwStr.toNat!
    let dh := dhStr.toNat!
    let nPx := nPxStr.toNat!
    let step := stepStr.toNat!
    let _ ← takeCalls
    let _ ← takeLumaStatsCalls
    let _ ← takeExtractMsb8Calls
    let scaled := execLnirScale2dYuv420p10LeBaC src sw.toUInt64 sh.toUInt64 dw.toUInt64 dh.toUInt64
    let stats := execLnirLumaStatsU16LeBaC src nPx.toUInt64 step.toUInt64
    let msb := execLnirExtractU16LeMsb8BaC src nPx.toUInt64
    let sc ← takeCalls
    let lc ← takeLumaStatsCalls
    let ec ← takeExtractMsb8Calls
    IO.FS.writeBinFile outScalePath scaled
    IO.FS.writeBinFile outMsbPath msb
    IO.println s!"{stats &&& 0xFFFFFFFF},{stats >>> 32},{sc},{lc},{ec}"
  | _ =>
    -- General MP4 transcode is fail-closed: it must not scale, compute stats, extract, write, or spawn.
    encoderCliOptionsRef.set { pixFmt := args[2]!, showStats := false, showBanner := false }
    let n (i : Nat) := (args[i]!).toNat!.toUInt32
    let _ ← takeCalls
    let _ ← takeLumaStatsCalls
    let _ ← takeExtractMsb8Calls
    let report ← transcodeMp4GeneralVerifiedIO (args[0]!) (args[1]!)
      (n 3) (n 4) (n 5) (n 6) 0 0 1 0 (n 7) (some ByteArray.empty)
    let metrics ← lastAcceptanceMetricsRef.get
    let sc ← takeCalls
    let lc ← takeLumaStatsCalls
    let ec ← takeExtractMsb8Calls
    require (report == 0 && metrics == 0 && sc == 0 && lc == 0 && ec == 0) "general transcode must stay closed"
    IO.println s!"{report},{metrics},{sc},{lc},{ec}"
