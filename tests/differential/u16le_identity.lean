import LeanAV.Encoder

open LeanAV.Scale LeanAV.Encoder LeanAV.NativeKernels

@[extern "identity_test_take_calls"] opaque takeCalls : IO UInt64

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

unsafe def unitTests : IO Unit := do
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
  IO.println "unit identity, pointer reuse, native/pure differential and fallback checks passed"

unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then unitTests
  else
    encoderCliOptionsRef.set { pixFmt := args[2]!, showStats := false, showBanner := false }
    let n (i : Nat) := (args[i]!).toNat!.toUInt32
    -- Exclude imported module initializers from the measured transcode.
    let _ ← takeCalls
    let report ← transcodeMp4GeneralVerifiedIO (args[0]!) (args[1]!)
      (n 3) (n 4) (n 5) (n 6) 0 0 1 0 (n 7) (some ByteArray.empty)
    let metrics ← lastAcceptanceMetricsRef.get
    let calls ← takeCalls
    IO.println s!"{report},{metrics},{calls}"
