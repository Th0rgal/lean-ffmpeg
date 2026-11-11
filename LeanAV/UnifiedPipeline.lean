import LeanAV.Cli
import LeanAV.InprocTranscode
import LeanAV.HevcMain
import LeanAV.Av1Main
import LeanAV.LavfiGraph

namespace LeanAV.UnifiedPipeline

open LeanSys.Posix LeanAV.Spec LeanAV.Core LeanAV.Format LeanAV.LavfiGraph

structure Media where
  video : Array VideoFrame := #[]
  audio : Option AudioFrame := none
  audioBits : Nat := 16
  fps : Nat := 25
  audioCopy : Option SynthMp4Track := none
  rawVideo : ByteArray := ByteArray.empty
  videoPixFmt : String := "yuv420p"
  videoWidth : Nat := 0
  videoHeight : Nat := 0
  videoFrames : Nat := 0
  videoCodecSrc : String := ""
  colour : MkvHdrColour := { matrixCoefficients := 2, transferCharacteristics := 2, primaries := 2, maxCll := 0, maxFall := 0, hasMastering := false }
  mastering : MasteringDisplaySpec := dciP3D65Mastering
  dovi : DoviConfigRecord := doviProfile8
  hasDovi : Bool := false
  rpus : Array ByteArray := #[]
  filmGrain? : Option LeanAV.Av1Main.Av1FilmGrainParams := none
  deriving Inhabited

structure Options where
  videoCodec : String := "h264"
  audioCodec : String := "aac"
  format : String := "mp4"
  videoFilter : String := ""
  audioFilter : String := ""
  filterComplex : String := ""
  maps : Array String := #[]
  noVideo : Bool := false
  noAudio : Bool := false
  qp : Nat := 28
  log2Ctb : Nat := 6
  tileColumns : Nat := 1
  tileRows : Nat := 1
  av1TileColumns : Nat := 0
  av1TileRows : Nat := 0
  maxFrames : Option Nat := none
  pixFmt : String := ""
  explicitVideoCodec : Bool := false
  colorPrimaries : Option UInt16 := none
  colorTrc : Option UInt16 := none
  colorspace : Option UInt16 := none
  filmGrain : Nat := 0
  ditherMode : String := "bayer"
  deriving Inhabited

def P11UnifiedHdrSafe (x : Nat × Nat × Nat × Nat) : Prop :=
  let (w, h, bd, cfmt) := x
  0 < w ∧ 0 < h ∧ (bd = 8 ∨ bd = 10 ∨ bd = 12 ∨ bd = 16) ∧
  cfmt ≤ 3 ∧ ((cfmt = 1 ∨ cfmt = 2) → w % 2 = 0) ∧ (cfmt = 1 → h % 2 = 0)

instance (x : Nat × Nat × Nat × Nat) : Decidable (P11UnifiedHdrSafe x) := by
  unfold P11UnifiedHdrSafe
  infer_instance

def p11UnifiedHdrGateSpec : AVGateSpec (Nat × Nat × Nat × Nat) P11UnifiedHdrSafe where
  gate x := decide (P11UnifiedHdrSafe x)
  sound _ h := of_decide_eq_true h
  complete _ h := decide_eq_true h
  posWitness := (16, 16, 10, 1)
  negWitness := (15, 16, 10, 1)
  nonVacuous := rfl
  tight := rfl

theorem p11UnifiedHdrGateSpec_iff (x : Nat × Nat × Nat × Nat) :
    p11UnifiedHdrGateSpec.gate x = true ↔ P11UnifiedHdrSafe x :=
  p11UnifiedHdrGateSpec.iff_safe x

def RawVideoSafe (x : Nat × Nat × Nat) : Prop :=
  0 < x.1 ∧ 0 < x.2.1 ∧ x.1 % 2 = 0 ∧ x.2.1 % 2 = 0 ∧
  0 < x.2.2 ∧ x.2.2 % (x.1 * x.2.1 * 3 / 2) = 0

instance (x : Nat × Nat × Nat) : Decidable (RawVideoSafe x) :=
  inferInstanceAs (Decidable (0 < x.1 ∧ 0 < x.2.1 ∧ x.1 % 2 = 0 ∧ x.2.1 % 2 = 0 ∧
    0 < x.2.2 ∧ x.2.2 % (x.1 * x.2.1 * 3 / 2) = 0))

def rawVideoGateSpec : AVGateSpec (Nat × Nat × Nat) RawVideoSafe where
  gate x := decide (RawVideoSafe x)
  sound _ h := of_decide_eq_true h
  complete _ h := decide_eq_true h
  posWitness := (2, 2, 6)
  negWitness := (2, 2, 7)
  nonVacuous := rfl
  tight := rfl

theorem rawVideoGateSpec_iff (x : Nat × Nat × Nat) :
    rawVideoGateSpec.gate x = true ↔ RawVideoSafe x := rawVideoGateSpec.iff_safe x

def unpackYuv420p (width height : Nat) (raw : ByteArray) : Option (Array VideoFrame) := do
  if !rawVideoGateSpec.gate (width, height, raw.size) then none
  else
    let frameBytes := width * height * 3 / 2
    let mut out := #[]
    for i in [:raw.size / frameBytes] do
      let mut vf := VideoFrame.allocYuv420p width height i.toUInt64
      let mut cursor := i * frameBytes
      let mut planes := vf.planes
      for p in [:3] do
        let mut plane := planes[p]!
        for r in [:plane.height] do
          for c in [:plane.width] do
            plane := plane.setPixel r c (raw.get! cursor)
            cursor := cursor + 1
        planes := planes.set! p plane
      vf := { vf with planes := planes }
      out := out.push vf
    some out

def canonicalFilmGrain (seed : Nat) : LeanAV.Av1Main.Av1FilmGrainParams :=
  { applyGrain := true
  , grainSeed := seed % 65536
  , updateGrain := true
  , filmGrainParamsRefIdx := 0
  , numYPoints := 4
  , yPoints := #[(0, 20), (64, 45), (160, 60), (255, 35)]
  , chromaScalingFromLuma := true
  , numCbPoints := 0
  , cbPoints := #[]
  , numCrPoints := 0
  , crPoints := #[]
  , grainScalingMinus8 := 3
  , arCoeffLag := 2
  , arCoeffsY := #[1, -2, 3, -1, 2, 0, -3, 4, -2, 1, 2, -4]
  , arCoeffsCb := #[1, -1, 2, -2, 1, 0, -2, 3, -1, 1, 0, -2, 3]
  , arCoeffsCr := #[-1, 2, -2, 1, 0, -1, 2, -3, 1, -1, 2, 1, -4]
  , arCoeffShiftMinus6 := 2
  , grainScaleShift := 1
  , cbMult := 128
  , cbLumaMult := 192
  , cbOffset := 256
  , crMult := 128
  , crLumaMult := 192
  , crOffset := 256
  , overlapFlag := true
  , clipToRestrictedRange := false
  }

def hbdReadLe16 (b : ByteArray) (off : Nat) : Nat :=
  if off + 1 < b.size then (b.get! off).toNat ||| ((b.get! (off + 1)).toNat <<< 8) else 0

def hbdPushLe16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v &&& 0xFF).toUInt8).push ((v >>> 8) &&& 0xFF).toUInt8

def hbdPixFmtGeom (pf : String) : Option (Nat × Nat) :=
  match PixelFormat.parse pf with
  | some fmt =>
    let bd := fmt.bitDepth
    let cfmt :=
      if fmt == .gbrp10le || fmt == .rgba64le then 3
      else
        let (sx, sy) := fmt.chromaSubsampling
        if sx == 2 && sy == 2 then 1
        else if sx == 2 && sy == 1 then 2
        else 3
    some (bd, cfmt)
  | none => none

def validateHbdRawBuffer (pf : String) (w h : Nat) (raw : ByteArray) : Option Nat := do
  let fmt ← PixelFormat.parse pf
  let (bd, cfmt) ← hbdPixFmtGeom pf
  if !p11UnifiedHdrGateSpec.gate (w, h, bd, cfmt) then none
  let fb ← fmt.frameByteSize w h
  if fb == 0 || raw.size == 0 || raw.size % fb != 0 then none
  some (raw.size / fb)

def mapFramesRaw (raw : ByteArray) (nFrames : Nat) (f : ByteArray → Option ByteArray) : Option ByteArray := Id.run do
  if nFrames == 0 || raw.size == 0 || raw.size % nFrames != 0 then return none
  let fb := raw.size / nFrames
  let mut out := ByteArray.empty
  for i in [:nFrames] do
    let some chunk := f (raw.extract (i * fb) ((i + 1) * fb)) | return none
    out := out ++ chunk
  return some out

def unpackYuv420p10ToVideoFrames (w h : Nat) (raw10 : ByteArray) (cm : ColorMatrix := .bt2020ncl) :
    Option (Array VideoFrame) := Id.run do
  let fb := 3 * w * h
  if w == 0 || h == 0 || w % 2 != 0 || h % 2 != 0 || fb == 0 || raw10.size == 0 || raw10.size % fb != 0 then
    return none
  let cw := w / 2
  let ch := h / 2
  let yBytes := 2 * w * h
  let uvBytes := 2 * cw * ch
  let nFrames := raw10.size / fb
  let mut out : Array VideoFrame := #[]
  for f in [:nFrames] do
    let base := f * fb
    let mut pY := Plane2D.alloc w h w 16
    let mut pU := Plane2D.alloc cw ch cw 128
    let mut pV := Plane2D.alloc cw ch cw 128
    for r in [:h] do
      for c in [:w] do
        let v10 := Nat.min 1023 (hbdReadLe16 raw10 (base + 2 * (r * w + c)))
        pY := pY.setPixel r c (Nat.min 255 ((v10 + 2) / 4)).toUInt8
    for r in [:ch] do
      for c in [:cw] do
        let u10 := Nat.min 1023 (hbdReadLe16 raw10 (base + yBytes + 2 * (r * cw + c)))
        let v10 := Nat.min 1023 (hbdReadLe16 raw10 (base + yBytes + uvBytes + 2 * (r * cw + c)))
        pU := pU.setPixel r c (Nat.min 255 ((u10 + 2) / 4)).toUInt8
        pV := pV.setPixel r c (Nat.min 255 ((v10 + 2) / 4)).toUInt8
    let vf0 := VideoFrame.allocYuv420p w h f.toUInt64
    out := out.push { vf0 with colorMatrix := cm, planes := #[pY, pU, pV] }
  return some out

def dither12To10Frame (src : ByteArray) (pf12 : String) (w h : Nat) (mode : String) : Option (String × ByteArray) := do
  let (pf10, cw, ch) ←
    if pf12 == "yuv420p12le" then some ("yuv420p10le", w / 2, h / 2)
    else if pf12 == "yuv422p12le" then some ("yuv422p10le", w / 2, h)
    else if pf12 == "yuv444p12le" then some ("yuv444p10le", w, h)
    else none
  let ySz := 2 * w * h
  let uvSz := 2 * cw * ch
  if src.size != ySz + 2 * uvSz then none
  let yIn := src.extract 0 ySz
  let uIn := src.extract ySz (ySz + uvSz)
  let vIn := src.extract (ySz + uvSz) (ySz + 2 * uvSz)
  let fn := if mode == "floyd_steinberg" || mode == "fs" then
      LeanAV.Scale.ditherPlaneFloydSteinberg12To10
    else LeanAV.Scale.ditherPlaneBayer12To10
  some (pf10, fn yIn w h ++ fn uIn cw ch ++ fn vIn cw ch)

def ditherHbdTo8Frame (src : ByteArray) (pf : String) (w h : Nat) (mode : String) : Option (String × ByteArray) := do
  let (pf8, cw, ch, bits) ←
    if pf == "yuv420p10le" then some ("yuv420p", w / 2, h / 2, 10)
    else if pf == "yuv422p10le" then some ("yuv422p", w / 2, h, 10)
    else if pf == "yuv444p10le" then some ("yuv444p", w, h, 10)
    else if pf == "yuv420p12le" then some ("yuv420p", w / 2, h / 2, 12)
    else if pf == "yuv422p12le" then some ("yuv422p", w / 2, h, 12)
    else if pf == "yuv444p12le" then some ("yuv444p", w, h, 12)
    else none
  let ySz := 2 * w * h
  let uvSz := 2 * cw * ch
  if src.size != ySz + 2 * uvSz then none
  let yIn := src.extract 0 ySz
  let uIn := src.extract ySz (ySz + uvSz)
  let vIn := src.extract (ySz + uvSz) (ySz + 2 * uvSz)
  let fn := if mode == "floyd_steinberg" || mode == "fs" then
      fun b pw ph => LeanAV.Scale.ditherPlaneFloydSteinbergToU8 b pw ph bits
    else
      fun b pw ph => LeanAV.Scale.ditherPlaneBayerToU8 b pw ph bits
  some (pf8, fn yIn w h ++ fn uIn cw ch ++ fn vIn cw ch)

def promote8To10Buffer (src : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (2 * src.size)
  for i in [:src.size] do
    out := hbdPushLe16 out ((src.get! i).toNat <<< 2)
  return out

def convertFrameToYuv444p10le (src : ByteArray) (pf : String) (w h : Nat) (cm : ColorMatrix := .bt2020ncl) :
    Option ByteArray := do
  if pf == "yuv444p10le" then some src
  else if pf == "yuv420p10le" then some (LeanAV.Scale.yuv420p10leToYuv444p10leBytes src w h)
  else if pf == "p010le" then
    some (LeanAV.Scale.yuv420p10leToYuv444p10leBytes (LeanAV.Scale.p010leToYuv420p10leBytes src w h) w h)
  else if pf == "yuv422p10le" then some (LeanAV.Scale.yuv422p10leToYuv444p10leBytes src w h)
  else if pf == "gbrp10le" then some (LeanAV.Scale.gbrp10leToYuv444p10leBytes src w h cm)
  else if pf == "rgba64le" then
    let gbr := LeanAV.Scale.rgba64leToGbrp10leBytes src w h
    some (LeanAV.Scale.gbrp10leToYuv444p10leBytes gbr w h cm)
  else if pf == "yuv420p12le" || pf == "yuv422p12le" || pf == "yuv444p12le" then
    let s10 := LeanAV.Scale.demoteU16Buffer12To10 src (src.size / 2)
    let pf10 := if pf == "yuv420p12le" then "yuv420p10le" else if pf == "yuv422p12le" then "yuv422p10le" else "yuv444p10le"
    if pf10 == "yuv444p10le" then some s10
    else if pf10 == "yuv422p10le" then some (LeanAV.Scale.yuv422p10leToYuv444p10leBytes s10 w h)
    else some (LeanAV.Scale.yuv420p10leToYuv444p10leBytes s10 w h)
  else if pf == "yuv420p" then
    some (LeanAV.Scale.yuv420p10leToYuv444p10leBytes (promote8To10Buffer src) w h)
  else if pf == "yuv422p" then
    some (LeanAV.Scale.yuv422p10leToYuv444p10leBytes (promote8To10Buffer src) w h)
  else if pf == "yuv444p" then
    some (promote8To10Buffer src)
  else none

def convertYuv444p10leToTarget (src444 : ByteArray) (dstPf : String) (w h : Nat)
    (cm : ColorMatrix := .bt2020ncl) (ditherMode : String := "bayer") : Option ByteArray := do
  if dstPf == "yuv444p10le" then some src444
  else if dstPf == "yuv422p10le" then some (LeanAV.Scale.yuv444p10leToYuv422p10leBytes src444 w h)
  else if dstPf == "yuv420p10le" then some (LeanAV.Scale.yuv444p10leToYuv420p10leBytes src444 w h)
  else if dstPf == "p010le" then
    let y420 := LeanAV.Scale.yuv444p10leToYuv420p10leBytes src444 w h
    some (LeanAV.Scale.yuv420p10leToP010leBytes y420 w h)
  else if dstPf == "gbrp10le" then some (LeanAV.Scale.yuv444p10leToGbrp10leBytes src444 w h cm)
  else if dstPf == "rgba64le" then
    let gbr := LeanAV.Scale.yuv444p10leToGbrp10leBytes src444 w h cm
    some (LeanAV.Scale.gbrp10leToRgba64leBytes gbr w h)
  else if dstPf == "yuv444p12le" then
    some (LeanAV.Scale.promoteU16Buffer10To12 src444 (src444.size / 2))
  else if dstPf == "yuv422p12le" then
    let y422 := LeanAV.Scale.yuv444p10leToYuv422p10leBytes src444 w h
    some (LeanAV.Scale.promoteU16Buffer10To12 y422 (y422.size / 2))
  else if dstPf == "yuv420p12le" then
    let y420 := LeanAV.Scale.yuv444p10leToYuv420p10leBytes src444 w h
    some (LeanAV.Scale.promoteU16Buffer10To12 y420 (y420.size / 2))
  else if dstPf == "yuv420p" then
    let y420 := LeanAV.Scale.yuv444p10leToYuv420p10leBytes src444 w h
    let (_, b8) ← ditherHbdTo8Frame y420 "yuv420p10le" w h ditherMode
    some b8
  else if dstPf == "yuv422p" then
    let y422 := LeanAV.Scale.yuv444p10leToYuv422p10leBytes src444 w h
    let (_, b8) ← ditherHbdTo8Frame y422 "yuv422p10le" w h ditherMode
    some b8
  else if dstPf == "yuv444p" then
    let (_, b8) ← ditherHbdTo8Frame src444 "yuv444p10le" w h ditherMode
    some b8
  else none

def convertRawVideoPixFmt (raw : ByteArray) (srcPf dstPf : String) (w h nFrames : Nat)
    (cm : ColorMatrix := .bt2020ncl) (ditherMode : String := "bayer") : Option ByteArray := do
  let srcFmt ← PixelFormat.parse srcPf
  let dstFmt ← PixelFormat.parse dstPf
  let srcC := srcFmt.toString
  let dstC := dstFmt.toString
  if srcC == dstC then some raw
  else if srcC == "yuv420p10le" && dstC == "p010le" then
    mapFramesRaw raw nFrames (fun f => some (LeanAV.Scale.yuv420p10leToP010leBytes f w h))
  else if srcC == "p010le" && dstC == "yuv420p10le" then
    mapFramesRaw raw nFrames (fun f => some (LeanAV.Scale.p010leToYuv420p10leBytes f w h))
  else if (srcC == "yuv420p12le" && dstC == "yuv420p10le") ||
          (srcC == "yuv422p12le" && dstC == "yuv422p10le") ||
          (srcC == "yuv444p12le" && dstC == "yuv444p10le") then
    mapFramesRaw raw nFrames (fun f => do
      let (_, b10) ← dither12To10Frame f srcC w h ditherMode
      some b10)
  else if (srcC == "yuv420p10le" && dstC == "yuv420p") ||
          (srcC == "yuv422p10le" && dstC == "yuv422p") ||
          (srcC == "yuv444p10le" && dstC == "yuv444p") ||
          (srcC == "yuv420p12le" && dstC == "yuv420p") ||
          (srcC == "yuv422p12le" && dstC == "yuv422p") ||
          (srcC == "yuv444p12le" && dstC == "yuv444p") then
    mapFramesRaw raw nFrames (fun f => do
      let (_, b8) ← ditherHbdTo8Frame f srcC w h ditherMode
      some b8)
  else
    mapFramesRaw raw nFrames (fun f => do
      let f444 ← convertFrameToYuv444p10le f srcC w h cm
      convertYuv444p10leToTarget f444 dstC w h cm ditherMode)

def scaleRawVideoFrames (raw : ByteArray) (pf : String) (srcW srcH dstW dstH nFrames : Nat)
    (cm : ColorMatrix := .bt2020ncl) : Option ByteArray := do
  let fmt ← PixelFormat.parse pf
  let pfC := fmt.toString
  if srcW == dstW && srcH == dstH then some raw
  else if pfC == "p010le" then
    let y420 ← convertRawVideoPixFmt raw "p010le" "yuv420p10le" srcW srcH nFrames cm
    let scaled ← mapFramesRaw y420 nFrames (fun f =>
      some (LeanAV.Scale.scalePlanarHighBitFrameBytes .yuv420p10le f srcW srcH dstW dstH))
    convertRawVideoPixFmt scaled "yuv420p10le" "p010le" dstW dstH nFrames cm
  else if pfC == "rgba64le" then
    let gbr ← convertRawVideoPixFmt raw "rgba64le" "gbrp10le" srcW srcH nFrames cm
    let scaled ← mapFramesRaw gbr nFrames (fun f =>
      some (LeanAV.Scale.scalePlanarHighBitFrameBytes .gbrp10le f srcW srcH dstW dstH))
    convertRawVideoPixFmt scaled "gbrp10le" "rgba64le" dstW dstH nFrames cm
  else if fmt.bitDepth == 10 || fmt.bitDepth == 12 then
    mapFramesRaw raw nFrames (fun f =>
      some (LeanAV.Scale.scalePlanarHighBitFrameBytes fmt f srcW srcH dstW dstH))
  else
    let y10 ← convertRawVideoPixFmt raw pfC "yuv444p10le" srcW srcH nFrames cm
    let scaled ← mapFramesRaw y10 nFrames (fun f =>
      some (LeanAV.Scale.scalePlanarHighBitFrameBytes .yuv444p10le f srcW srcH dstW dstH))
    convertRawVideoPixFmt scaled "yuv444p10le" pfC dstW dstH nFrames cm

def syncMediaFromVideoFrames (media : Media) : Media :=
  if media.video.isEmpty then media
  else
    let vf0 := media.video[0]!
    { media with
      rawVideo := packVideoFramesYuv420pRaw media.video
      videoPixFmt := "yuv420p"
      videoWidth := vf0.width
      videoHeight := vf0.height
      videoFrames := media.video.size }

def unpackYuv420p8OrPlaceholder (w h count : Nat) (pfC : String) (raw : ByteArray) : Option (Array VideoFrame) :=
  if pfC == "yuv420p" then unpackYuv420p w h raw
  else if pfC == "yuv420p10le" then unpackYuv420p10ToVideoFrames w h raw
  else if pfC == "p010le" then do
    let y10 ← convertRawVideoPixFmt raw "p010le" "yuv420p10le" w h count
    unpackYuv420p10ToVideoFrames w h y10
  else do
    let y10 ← convertRawVideoPixFmt raw pfC "yuv420p10le" w (if h % 2 == 0 then h else h + 1) count
    unpackYuv420p10ToVideoFrames (if w % 2 == 0 then w else w + 1) (if h % 2 == 0 then h else h + 1) y10

def syncMediaFromRaw (media : Media) (w h nFrames : Nat) (pf : String) (raw : ByteArray)
    (fps : Nat := 25) : Option Media := do
  let fmt ← PixelFormat.parse pf
  let pfC := fmt.toString
  let count ← validateHbdRawBuffer pfC w h raw
  if count != nFrames || count == 0 then none
  let vfs ←
    if pfC == "yuv420p" then unpackYuv420p w h raw
    else if pfC == "yuv420p10le" then unpackYuv420p10ToVideoFrames w h raw
    else if pfC == "p010le" then
      let y10 ← convertRawVideoPixFmt raw "p010le" "yuv420p10le" w h count
      unpackYuv420p10ToVideoFrames w h y10
    else if w % 2 == 0 && h % 2 == 0 then
      let y10 ← convertRawVideoPixFmt raw pfC "yuv420p10le" w h count
      unpackYuv420p10ToVideoFrames w h y10
    else
      some (Array.ofFn fun i : Fin count => VideoFrame.allocYuv420p ((w + 1) / 2 * 2) ((h + 1) / 2 * 2) i.val.toUInt64)
  some { media with
    video := vfs
    fps := fps
    rawVideo := raw
    videoPixFmt := pfC
    videoWidth := w
    videoHeight := h
    videoFrames := count }

def decodedVideo (decoded : Option (Nat × Nat × Nat × ByteArray)) (fps : Nat := 25) : Option Media := do
  let (w, h, count, raw) ← decoded
  let frames ← unpackYuv420p w h raw
  if count != frames.size then none else some (syncMediaFromVideoFrames { video := frames, fps := fps })

def decodeHevcStreamMedia (raw : ByteArray) (fps : Nat := 25) : Option Media := do
  let (w, h, count, pf, rawBytes, vp, vt, vm) ← LeanAV.HevcMain.decodeHevcGenWithColor raw
  let base : Media := {
    videoCodecSrc := "hevc"
    colour := { primaries := vp, transferCharacteristics := vt, matrixCoefficients := vm, maxCll := 0, maxFall := 0, hasMastering := false } }
  syncMediaFromRaw base w h count pf rawBytes fps

def decodeAv1StreamMedia (raw : ByteArray) (fps : Nat := 25) : Option Media := do
  let (_, _, pkts) ← LeanAV.Av1Main.av1ExtractContainerPackets raw
  let mut rpus : Array ByteArray := #[]
  for pkt in pkts do
    if let some rpu := extractAv1RpuFromTu pkt then
      rpus := rpus.push rpu
  let (w, h, count, _, pf, rawBytes) ← LeanAV.Av1Main.decodeAv1ToRaw raw
  let base : Media := { videoCodecSrc := "av1", hasDovi := !rpus.isEmpty, rpus := rpus }
  syncMediaFromRaw base w h count pf rawBytes fps

def decodeH264StreamMedia (raw : ByteArray) (fps : Nat := 25) : Option Media :=
  if let some pics := LeanAV.H264IntraTransform.decodeAnnexBToPicturesHbd raw then
    if let some p0 := pics[0]? then
      if p0.chromaFormatIdc != 1 || p0.bitDepthY != 8 then do
        let pf ←
          if p0.chromaFormatIdc == 1 && p0.bitDepthY == 10 then some "yuv420p10le"
          else if p0.chromaFormatIdc == 1 && p0.bitDepthY == 12 then some "yuv420p12le"
          else if p0.chromaFormatIdc == 2 && p0.bitDepthY == 8 then some "yuv422p"
          else if p0.chromaFormatIdc == 2 && p0.bitDepthY == 10 then some "yuv422p10le"
          else if p0.chromaFormatIdc == 2 && p0.bitDepthY == 12 then some "yuv422p12le"
          else if p0.chromaFormatIdc == 3 && p0.bitDepthY == 8 then some "yuv444p"
          else if p0.chromaFormatIdc == 3 && p0.bitDepthY == 10 then some "yuv444p10le"
          else if p0.chromaFormatIdc == 3 && p0.bitDepthY == 12 then some "yuv444p12le"
          else none
        let rawBytes ← LeanAV.H264IntraTransform.packPicturesHbdCanonicalRaw pics
        syncMediaFromRaw { videoCodecSrc := "h264" } p0.width p0.height pics.size pf rawBytes fps
      else if let some frames := LeanAV.InprocTranscode.decodeAnnexBH264StreamToFrames raw then
        if frames.isEmpty then none
        else some (syncMediaFromVideoFrames { video := frames, fps := fps, videoCodecSrc := "h264" })
      else none
    else none
  else if let some frames := LeanAV.InprocTranscode.decodeAnnexBH264StreamToFrames raw then
    if frames.isEmpty then none
    else some (syncMediaFromVideoFrames { video := frames, fps := fps, videoCodecSrc := "h264" })
  else none

def extractMp4SampleRpus (raw : ByteArray) (samples : Array NativeMp4Sample) (isAv1 : Bool) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[]
  for s in samples do
    if s.fileOff + s.byteLen ≤ raw.size then
      let au := raw.extract s.fileOff (s.fileOff + s.byteLen)
      let slice := ByteSlice.ofByteArray au
      if isAv1 then
        if au.size > 0 then
          if let some rpu := extractAv1RpuFromTu au then
            out := out.push rpu
      else
        let mut p := 0
        let mut found : Option ByteArray := none
        while p + 4 ≤ au.size && found.isNone do
          let len := (readU32BE slice p).toNat
          p := p + 4
          if len > 0 && p + len ≤ au.size then
            let nal := au.extract p (p + len)
            if let some rpu := decodeHevcRpuNal nal.toList then
              found := some (ByteArray.mk rpu.toArray)
          p := p + len
        if let some r := found then
          out := out.push r
  return out

def decodeMp4 (raw : ByteArray) (noAudio : Bool := false) : Option Media := do
  let tracks ← demuxNativeMp4ContainerTracks (ByteSlice.ofByteArray raw)
  let mut media : Media := {}
  for tr in tracks do
    if tr.hasEncrypted || tr.multiStsd || tr.timescale == 0 then none
    else if tr.kind == .video then
      if !media.video.isEmpty then none
      let duration := tr.samples.foldl (fun n s => n + s.dur) 0
      let fpsEst (cnt : Nat) : Nat := if duration == 0 then 25 else Nat.max 1 (cnt * tr.timescale / duration)
      let codecId :=
        if tr.stsdFourcc == "hvc1" || tr.stsdFourcc == "hev1" then "V_MPEGH/ISO/HEVC"
        else if tr.stsdFourcc == "av01" then "V_AV1"
        else "V_MPEG4/ISO/AVC"
      let meta? := p11ExtractCrossMeta tr.stsdBox codecId
      let (colour, mastering, dovi, hasDovi) := match meta? with
        | some (_, _, _, c, m, d, hd) => (c, m, d, hd)
        | none => (media.colour, media.mastering, media.dovi, false)
      let vMedia ←
        if tr.stsdFourcc == "avc1" || tr.stsdFourcc == "avc3" then
          let avccBody? := extractMp4StsdAvcCBody tr.stsdBox
          let sps? : Option LeanAV.H264Syntax.H264SpsFull := do
            let avccBody ← avccBody?
            let avcc ← LeanAV.H264Syntax.parseAvcDecoderConfigRecord avccBody
            let spsNal ← avcc.spsNalus[0]?
            LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray spsNal)
          let is8Bit420 := match sps? with
            | some sps => sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 0 && sps.bitDepthChromaMinus8 == 0
            | none => true
          if is8Bit420 then
            if let some (frames, _, _) := LeanAV.InprocTranscode.decodeMp4AvcTrackToFrames raw tr then
              if frames.isEmpty then none
              else
                let baseM : Media :=
                  { media with
                    video := frames
                    fps := fpsEst frames.size
                    videoCodecSrc := "h264"
                    colour := colour
                    mastering := mastering
                    dovi := dovi
                    hasDovi := hasDovi }
                some (syncMediaFromVideoFrames baseM)
            else none
          else do
            let sps ← sps?
            if sps.profileIdc == 135 then none
            let rawBytes ← LeanAV.H264IntraTransform.decodeMp4ToCanonicalRaw raw
            let pf ←
              if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 0 then some "yuv420p"
              else if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 2 then some "yuv420p10le"
              else if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 4 then some "yuv420p12le"
              else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 0 then some "yuv422p"
              else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 2 then some "yuv422p10le"
              else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 4 then some "yuv422p12le"
              else if sps.chromaFormatIdc == 3 && sps.bitDepthLumaMinus8 == 0 then some "yuv444p"
              else if sps.chromaFormatIdc == 3 && sps.bitDepthLumaMinus8 == 2 then some "yuv444p10le"
              else if sps.chromaFormatIdc == 3 && sps.bitDepthLumaMinus8 == 4 then some "yuv444p12le"
              else none
            let cnt ← validateHbdRawBuffer pf sps.widthPx.toNat sps.heightPx.toNat rawBytes
            let baseM : Media :=
              { media with
                videoCodecSrc := "h264"
                colour := colour
                mastering := mastering
                dovi := dovi
                hasDovi := hasDovi }
            syncMediaFromRaw baseM sps.widthPx.toNat sps.heightPx.toNat cnt pf rawBytes (fpsEst cnt)
        else if tr.stsdFourcc == "hvc1" || tr.stsdFourcc == "hev1" then do
          let (w, h, cnt, pf, rawBytes, vp, vt, vm) ← LeanAV.HevcMain.decodeHevcGenWithColor raw
          let rpus := extractMp4SampleRpus raw tr.samples false
          let mergedColour : MkvHdrColour := { colour with
            primaries := if colour.primaries == 0 || colour.primaries == 2 then vp else colour.primaries
            transferCharacteristics := if colour.transferCharacteristics == 0 || colour.transferCharacteristics == 2 then vt else colour.transferCharacteristics
            matrixCoefficients := if colour.matrixCoefficients == 0 || colour.matrixCoefficients == 2 then vm else colour.matrixCoefficients }
          let baseM : Media :=
            { media with
              videoCodecSrc := "hevc"
              colour := mergedColour
              mastering := mastering
              dovi := dovi
              hasDovi := hasDovi || !rpus.isEmpty
              rpus := rpus }
          syncMediaFromRaw baseM w h cnt pf rawBytes (fpsEst cnt)
        else if tr.stsdFourcc == "av01" then do
          let (w, h, cnt, _, pf, rawBytes) ← LeanAV.Av1Main.decodeAv1ToRaw raw
          let rpus := extractMp4SampleRpus raw tr.samples true
          let baseM : Media :=
            { media with
              videoCodecSrc := "av1"
              colour := colour
              mastering := mastering
              dovi := dovi
              hasDovi := hasDovi || !rpus.isEmpty
              rpus := rpus }
          syncMediaFromRaw baseM w h cnt pf rawBytes (fpsEst cnt)
        else if tr.stsdFourcc == "apcn" then do
          let mut frames := #[]
          for s in tr.samples do
            if s.fileOff + s.byteLen > raw.size then none
            let vf ← LeanAV.Video.decodeProResFrameToYuv420p
              (ByteSlice.ofByteArray (raw.extract s.fileOff (s.fileOff + s.byteLen))) s.dts.toUInt64
            frames := frames.push vf
          if frames.isEmpty then none
          else
            let baseM : Media :=
              { media with video := frames, fps := fpsEst frames.size, videoCodecSrc := "prores" }
            some (syncMediaFromVideoFrames baseM)
        else none
      media := vMedia
    else if tr.kind == .audio then
      if noAudio then
        pure ()
      else if media.audio.isSome then none
      else if tr.stsdFourcc == "mp4a" then
        let (channels, sr, bps) ← LeanAV.InprocTranscode.decodeMp4AacTrackToChannels raw tr
        let copied ← LeanAV.InprocTranscode.copyMp4AacTrackToSynth raw tr
        media := { media with
          audio := some (channelArraysToAudioFrame (scaleChannelsBps channels bps 16) sr)
          audioCopy := some copied }
      else if tr.stsdFourcc == "Opus" then
        let dops ← extractMp4StsdChildBody tr.stsdBox ["Opus"] "dOps"
        if dops.size < 10 || dops.get! 0 != 0 then none
        let outCh := dops.get! 1
        let preSkip := ((dops.get! 2).toNat <<< 8) ||| (dops.get! 3).toNat
        let mut opusPackets := #[]
        for s in tr.samples do
          if s.fileOff + s.byteLen > raw.size then none
          opusPackets := opusPackets.push (ByteSlice.ofByteArray (raw.extract s.fileOff (s.fileOff + s.byteLen)))
        let af ← LeanAV.Audio.decodeOpusPacketsToAudioFrame opusPackets outCh preSkip
        media := { media with audio := some af }
      else none
    else none
  if media.video.isEmpty && media.audio.isNone then none else some media

def decodeMkv (raw : ByteArray) (noAudio : Bool := false) : Option Media := do
  let tracks ← p11DemuxMkvToCrossTracks raw
  let mp4Bytes ← p11MuxMp4FromCrossTracks tracks
  let decoded ← decodeMp4 mp4Bytes noAudio
  if decoded.videoCodecSrc == "h264" && decoded.videoPixFmt == "yuv420p" &&
     !decoded.hasDovi && !decoded.colour.hasMastering && decoded.colour.primaries != 9 &&
     decoded.colour.transferCharacteristics != 16 && decoded.colour.transferCharacteristics != 18 then
    none
  else some decoded

def decodeOggOpus (raw : ByteArray) : Option Media := do
  let packets ← demuxOggLogicalPackets (ByteSlice.ofByteArray raw)
  if packets.size < 3 then none
  let header ← LeanAV.Audio.parseOpusHeadPacket (ByteSlice.ofByteArray packets[0]!.data)
  if !LeanAV.Audio.verifyOpusTagsPacket (ByteSlice.ofByteArray packets[1]!.data) then none
  if packets.any (fun p => p.serialNo != packets[0]!.serialNo) then none
  let audioPackets := (packets.extract 2 packets.size).map (fun p => ByteSlice.ofByteArray p.data)
  let af ← LeanAV.Audio.decodeOpusPacketsToAudioFrame audioPackets header.channels header.preSkip.toNat
    (some packets[packets.size - 1]!.granulePos)
  some { audio := some af }

def decodeMpegTs (raw : ByteArray) : Option Media := do
  let streams ← demuxMpegTsProgram (ByteSlice.ofByteArray raw)
  let mut media : Media := {}
  for stream in streams do
    let payload := stream.packets.foldl (fun bytes p => bytes ++ p.1) ByteArray.empty
    if stream.streamType == 0x1B || stream.streamType == 0x24 then
      if !media.video.isEmpty then none
      let frames ←
        if stream.streamType == 0x1B then LeanAV.InprocTranscode.decodeAnnexBH264StreamToFrames payload
        else do
          let decoded ← decodedVideo (LeanAV.HevcMain.decodeHevcToYuv420p payload)
          some decoded.video
      if frames.size < 2 || stream.packets.size != frames.size then none
      let firstPts := stream.packets[0]!.2.toNat
      let nextPts := stream.packets[1]!.2.toNat
      if nextPts <= firstPts || nextPts >= 8589934592 then none
      let step := nextPts - firstPts
      if 90000 % step != 0 then none
      for i in [:stream.packets.size] do
        let pts := stream.packets[i]!.2.toNat
        if pts >= 8589934592 || pts != firstPts + i * step then none
      let frames := frames.mapIdx fun i vf =>
        { vf with
          pts := (i * step).toUInt64
          duration := step.toUInt64
          timeBase := AVRational.mkSafe 1 90000 }
      let vCodecSrc := if stream.streamType == 0x1B then "h264" else "hevc"
      let baseM : Media := { media with video := frames, fps := 90000 / step, videoCodecSrc := vCodecSrc }
      media := syncMediaFromVideoFrames baseM
    else if stream.streamType == 0x0F then
      if media.audio.isSome then none
      let (pcm, sr, bps) ← LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray payload) true
      media := { media with audio := some (channelArraysToAudioFrame (scaleChannelsBps pcm bps 16) sr) }
    else none
  some media

def decode (raw : ByteArray) (format : String) (width height : Nat := 0)
    (sampleRate : UInt32 := 48000) (channels : Nat := 2) (noAudio : Bool := false)
    (pixFmt : String := "yuv420p") : Option Media := do
  if raw.isEmpty then none
  else if format == "rawvideo" then
    let pf := if pixFmt == "" then "yuv420p" else pixFmt
    let fmt ← PixelFormat.parse pf
    let pfC := fmt.toString
    if pfC == "yuv420p" then
      let frames ← unpackYuv420p width height raw
      some (syncMediaFromVideoFrames { video := frames, videoCodecSrc := "rawvideo" })
    else
      let cnt ← validateHbdRawBuffer pfC width height raw
      syncMediaFromRaw { videoCodecSrc := "rawvideo" } width height cnt pfC raw 25
  else if format == "s16le" || format == "s24le" || format == "s32le" then
    let bps := if format == "s32le" then 32 else if format == "s24le" then 24 else 16
    let pcm ← pcmRawLEToChannels (ByteSlice.ofByteArray raw) channels bps
    if sampleRate == 0 then none
    some { audio := some (channelArraysToAudioFrame pcm sampleRate bps), audioBits := bps }
  else if format == "mp4" || format == "mov" then decodeMp4 raw noAudio
  else if format == "mkv" || format == "matroska" || format == "webm" then decodeMkv raw noAudio
  else if format == "hevc" then decodeHevcStreamMedia raw
  else if format == "av1" || format == "obu" || format == "ivf" then decodeAv1StreamMedia raw
  else if format == "h264" then decodeH264StreamMedia raw
  else if format == "wav" || format == "adts" then
    let (pcm, sr, bps) ←
      if format == "wav" then demuxWavPcmLE (ByteSlice.ofByteArray raw)
      else LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray raw) true
    let outBits := if format == "wav" then bps else 16
    some {
      audio := some (channelArraysToAudioFrame (scaleChannelsBps pcm bps outBits) sr outBits)
      audioBits := outBits }
  else if format == "flac" then
    let decoded ← LeanAV.Audio.flacDecodeStream (ByteSlice.ofByteArray raw)
    some {
      audio := some (LeanAV.Audio.flacDecodedToAudioFrame decoded)
      audioBits := decoded.info.bitsPerSample.toNat }
  else if format == "ogg" || format == "opus" then decodeOggOpus raw
  else if format == "mpegts" then decodeMpegTs raw
  else none

def filterAllowsPixFmtChange (vfSpec fcSpec : String) : Bool :=
  let s := (vfSpec ++ "," ++ fcSpec).toLower
  (s.splitOn "format=").length > 1 ||
  (s.splitOn "scale=").length > 1 ||
  (s.splitOn "zscale=").length > 1 ||
  (s.splitOn "colorspace").length > 1 ||
  (s.splitOn "tonemap").length > 1 ||
  (s.splitOn "dither").length > 1

def applyHbdVideoFilterChain (media : Media) (options : Options) : Option Media := Id.run do
  let mut cur := media
  let mut ditherMode := options.ditherMode
  let vfSpec := if options.videoFilter != "" then options.videoFilter else options.filterComplex
  let g? :=
    if options.videoFilter != "" then
      match parseFilterGraph ("[0:v]" ++ options.videoFilter ++ "[vout]") with
      | .ok g => some g
      | .error _ => none
    else if options.filterComplex != "" then
      match parseFilterGraph options.filterComplex with
      | .ok g => some g
      | .error _ => none
    else none
  if let some g := g? then
    for node in g.nodes do
      let nm := node.name.toLower
      if nm == "scale" || nm == "zscale" then
        let wArg := (FilterArg.lookupNat node.args "w" 0 cur.videoWidth).getD cur.videoWidth
        let hArg := (FilterArg.lookupNat node.args "h" 1 cur.videoHeight).getD cur.videoHeight
        if let some dStr := FilterArg.lookup node.args "dither" 2 then
          ditherMode := dStr.toLower
        if wArg > 0 && hArg > 0 && (wArg != cur.videoWidth || hArg != cur.videoHeight) then
          let some scaled := scaleRawVideoFrames cur.rawVideo cur.videoPixFmt cur.videoWidth cur.videoHeight wArg hArg cur.videoFrames
            | return none
          let some nextM := syncMediaFromRaw cur wArg hArg cur.videoFrames cur.videoPixFmt scaled cur.fps
            | return none
          cur := nextM
      else if nm == "format" then
        if let some pfArg := FilterArg.lookup node.args "pix_fmts" 0 then
          let targetPf := (pfArg.splitOn "|").headD pfArg
          if let some fmt := PixelFormat.parse targetPf then
            let dstC := fmt.toString
            if dstC != cur.videoPixFmt then
              let some conv := convertRawVideoPixFmt cur.rawVideo cur.videoPixFmt dstC cur.videoWidth cur.videoHeight cur.videoFrames .bt2020ncl ditherMode
                | return none
              let some nextM := syncMediaFromRaw cur cur.videoWidth cur.videoHeight cur.videoFrames dstC conv cur.fps
                | return none
              cur := nextM
      else if nm == "dither" then
        let mStr := (FilterArg.lookup node.args "mode" 0).getD (FilterArg.lookup node.args "dither" 0 |>.getD "bayer")
        ditherMode := mStr.toLower
        let targetPf :=
          if options.pixFmt != "" then options.pixFmt
          else if cur.videoPixFmt == "yuv420p12le" then "yuv420p10le"
          else if cur.videoPixFmt == "yuv422p12le" then "yuv422p10le"
          else if cur.videoPixFmt == "yuv444p12le" then "yuv444p10le"
          else if cur.videoPixFmt == "yuv422p10le" then "yuv422p"
          else if cur.videoPixFmt == "yuv444p10le" then "yuv444p"
          else "yuv420p"
        if let some fmt := PixelFormat.parse targetPf then
          let dstC := fmt.toString
          if dstC != cur.videoPixFmt then
            let some conv := convertRawVideoPixFmt cur.rawVideo cur.videoPixFmt dstC cur.videoWidth cur.videoHeight cur.videoFrames .bt2020ncl ditherMode
              | return none
            let some nextM := syncMediaFromRaw cur cur.videoWidth cur.videoHeight cur.videoFrames dstC conv cur.fps
              | return none
            cur := nextM
      else if nm == "tonemap" then
        let mode := ((FilterArg.lookup node.args "tonemap" 0).getD (FilterArg.lookup node.args "mode" 0 |>.getD "hable")).toLower
        let trc := if cur.colour.transferCharacteristics == 18 then 18 else 16
        let srcCm : ColorMatrix :=
          if cur.colour.matrixCoefficients == 1 then .bt709
          else if cur.colour.matrixCoefficients == 5 || cur.colour.matrixCoefficients == 6 then .bt601
          else .bt2020ncl
        let mapped ←
          if cur.videoPixFmt != "yuv420p" && cur.rawVideo.size > 0 &&
             cur.videoWidth > 0 && cur.videoHeight > 0 &&
             cur.videoWidth % 2 == 0 && cur.videoHeight % 2 == 0 && cur.videoFrames > 0 then
            let some y10 :=
              if cur.videoPixFmt == "yuv420p10le" then some cur.rawVideo
              else convertRawVideoPixFmt cur.rawVideo cur.videoPixFmt "yuv420p10le" cur.videoWidth cur.videoHeight cur.videoFrames srcCm ditherMode
              | return none
            let fb10 := 3 * cur.videoWidth * cur.videoHeight
            if y10.size != cur.videoFrames * fb10 then return none
            pure (Array.ofFn fun i : Fin cur.videoFrames =>
              let slice := y10.extract (i.val * fb10) ((i.val + 1) * fb10)
              LeanAV.Scale.tonemapYuv420p10FrameToSdrVideoFrame slice cur.videoWidth cur.videoHeight srcCm mode trc i.val.toUInt64)
          else
            pure (cur.video.map (fun vf => LeanAV.Scale.tonemapVideoFrameHdrToSdrWithTransfer vf mode trc))
        cur := syncMediaFromVideoFrames { cur with
          video := mapped
          colour := { cur.colour with primaries := 1, transferCharacteristics := 1, matrixCoefficients := 1, hasMastering := false, maxCll := 0, maxFall := 0 }
          hasDovi := false
          rpus := #[] }
      else if nm == "colorspace" then
        let allArg := (FilterArg.lookup node.args "all" 0).getD "bt709"
        let dstM : ColorMatrix := if allArg.toLower == "bt2020" || allArg.toLower == "bt2020nc" || allArg.toLower == "bt2020ncl" then .bt2020ncl else if allArg.toLower == "bt601" then .bt601 else .bt709
        if dstM == .bt709 && (options.pixFmt == "" || options.pixFmt == "yuv420p") then
          let mapped := cur.video.map (fun vf => LeanAV.Scale.convertVideoFrameColorspace vf .bt709)
          cur := syncMediaFromVideoFrames { cur with
            video := mapped
            colour := { cur.colour with primaries := 1, transferCharacteristics := 1, matrixCoefficients := 1 } }
        else if dstM == .bt2020ncl then
          cur := { cur with colour := { cur.colour with primaries := 9, matrixCoefficients := 9 } }
  if options.pixFmt != "" then
    let some dstFmt := PixelFormat.parse options.pixFmt | return none
    let dstC := dstFmt.toString
    if dstC != cur.videoPixFmt then
      let trivial10 := (cur.videoPixFmt == "yuv420p10le" && dstC == "p010le") ||
                       (cur.videoPixFmt == "p010le" && dstC == "yuv420p10le")
      if !trivial10 && !filterAllowsPixFmtChange vfSpec "" then
        return none
      let some conv := convertRawVideoPixFmt cur.rawVideo cur.videoPixFmt dstC cur.videoWidth cur.videoHeight cur.videoFrames .bt2020ncl ditherMode
        | return none
      let some nextM := syncMediaFromRaw cur cur.videoWidth cur.videoHeight cur.videoFrames dstC conv cur.fps
        | return none
      cur := nextM
  if let some n := options.maxFrames then
    if n < cur.videoFrames then
      let some fmt := PixelFormat.parse cur.videoPixFmt | return none
      let some fb := fmt.frameByteSize cur.videoWidth cur.videoHeight | return none
      let slicedRaw := cur.rawVideo.extract 0 (n * fb)
      let some nextM := syncMediaFromRaw cur cur.videoWidth cur.videoHeight n cur.videoPixFmt slicedRaw cur.fps
        | return none
      cur := { nextM with rpus := cur.rpus.extract 0 n }
  return some cur

def filter (media : Media) (options : Options) : Except String Media := do
  if media.video.isEmpty && options.videoFilter != "" then throw "video filter without video stream"
  if media.audio.isNone && options.audioFilter != "" then throw "audio filter without audio stream"
  if !media.video.isEmpty && !options.explicitVideoCodec &&
     options.pixFmt == "" && options.videoFilter == "" && options.filterComplex == "" &&
     (options.format == "rawvideo" || options.format == "null") &&
     media.videoPixFmt != "yuv420p" then
    throw "implicit high-tier rawvideo/null decode without -pix_fmt or -vf rejected (fail-closed)"
  if !media.video.isEmpty && !options.explicitVideoCodec && options.videoCodec == "h264" &&
     options.pixFmt == "" && options.videoFilter == "" && options.filterComplex == "" &&
     options.format != "rawvideo" && options.format != "null" && options.format != "md5" && options.format != "framemd5" &&
     media.videoPixFmt != "yuv420p" && media.videoCodecSrc == "h264" then
    throw "implicit high-tier H.264 transcode without -pix_fmt rejected (fail-closed)"
  if !media.video.isEmpty && options.videoCodec == "h264" &&
     options.pixFmt == "" && options.videoFilter == "" && options.filterComplex == "" &&
     media.videoPixFmt != "yuv420p" && media.videoCodecSrc != "h264" then
    throw "high-bit-depth input to H.264 without explicit -pix_fmt or -vf rejected (fail-closed)"
  let isHbdFlow : Bool :=
    !media.video.isEmpty &&
    (media.videoPixFmt != "yuv420p" || (options.pixFmt != "" && options.pixFmt != "yuv420p") ||
     media.hasDovi || media.colour.hasMastering || media.colour.primaries == 9 ||
     media.colour.transferCharacteristics == 16 || media.colour.transferCharacteristics == 18 ||
     options.colorPrimaries.isSome || options.colorTrc.isSome || options.colorspace.isSome ||
     options.filmGrain > 0)
  let audio ← match media.audio with
    | some af => do
      let filtered ← runSingleStreamAudioFilterGraph options.audioFilter af
      pure (some filtered)
    | none => pure none
  let audioBits := if options.audioFilter != "" then 16 else media.audioBits
  let baseColour : MkvHdrColour := {
    media.colour with
    primaries := (options.colorPrimaries.map UInt16.toNat).getD media.colour.primaries
    transferCharacteristics := (options.colorTrc.map UInt16.toNat).getD media.colour.transferCharacteristics
    matrixCoefficients := (options.colorspace.map UInt16.toNat).getD media.colour.matrixCoefficients
  }
  let fg? : Option LeanAV.Av1Main.Av1FilmGrainParams :=
    if options.filmGrain > 0 then some (canonicalFilmGrain options.filmGrain) else media.filmGrain?
  if isHbdFlow then
    let (_, outFps) ←
      if options.videoFilter != "" then runSingleStreamVideoFilterGraph options.videoFilter media.video media.fps
      else pure (media.video, media.fps)
    let some hbdMedia := applyHbdVideoFilterChain { media with fps := outFps, colour := baseColour, filmGrain? := fg? } options
      | throw "unsupported high-bit-depth pixel format conversion without explicit filter stage (fail-closed)"
    return { hbdMedia with
      video := if options.noVideo then #[] else hbdMedia.video
      rawVideo := if options.noVideo then ByteArray.empty else hbdMedia.rawVideo
      videoFrames := if options.noVideo then 0 else hbdMedia.videoFrames
      audio := if options.noAudio then none else audio
      audioBits := audioBits
      audioCopy := if options.noAudio || options.audioFilter != "" then none else media.audioCopy }
  else
    let (frames, outFps) ← runSingleStreamVideoFilterGraph options.videoFilter media.video media.fps
    let frames := match options.maxFrames with
      | some n => frames.extract 0 n
      | none => frames
    let outMedia := { media with
      video := if options.noVideo then #[] else frames
      fps := outFps
      audio := if options.noAudio then none else audio
      audioBits := audioBits
      colour := baseColour
      filmGrain? := fg?
      audioCopy := if options.noAudio || options.audioFilter != "" then none else media.audioCopy }
    return syncMediaFromVideoFrames outMedia

def audioChannels16 (media : Media) (af : AudioFrame) : Array (Array Int32) :=
  let raw := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
  scaleChannelsBps raw media.audioBits 16

def encodeH264StreamForMedia (media : Media) (options : Options) : Option (ByteArray × Array ByteArray × Array ByteArray) := do
  let w := if media.videoWidth > 0 then media.videoWidth else (media.video[0]?.map (·.width)).getD 0
  let h := if media.videoHeight > 0 then media.videoHeight else (media.video[0]?.map (·.height)).getD 0
  if w == 0 || h == 0 then none
  let pf := media.videoPixFmt
  let raw := if media.rawVideo.size > 0 then media.rawVideo else packVideoFramesYuv420pRaw media.video
  if pf == "yuv420p" && options.qp > 0 then
    let (avcc, _, _, lenPrefixed) ← LeanAV.InprocTranscode.encodeFramesToH264Cavlc media.video options.qp
    let annexB ← LeanAV.InprocTranscode.encodeFramesToH264AnnexBPackets media.video options.qp
    some (avcc, lenPrefixed, annexB)
  else
    let lossless := options.qp == 0
    let annex ← LeanAV.H264IntraTransform.encodeCanonicalRawToAnnexB raw pf w h lossless
    let pics ← LeanAV.H264IntraTransform.unpackCanonicalRawPicturesHbd raw pf w h
    let pic0 ← pics[0]?
    let profile ← LeanAV.H264IntraTransform.highTierProfileFor pic0.chromaFormatIdc pic0.bitDepthY lossless
    let nals := LeanAV.H264Entropy.splitAnnexB annex
    let spsNal ← nals[0]?
    let ppsNal ← nals[1]?
    let sps ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray spsNal)
    let avccRec := LeanAV.H264Syntax.buildAvcDecoderConfigRecordFromSps { sps with profileIdc := profile } spsNal ppsNal
    let avccBody ← LeanAV.H264Syntax.serializeAvcDecoderConfigRecord avccRec
    let mut lenPrefixed : Array ByteArray := #[]
    let mut annexBPkts : Array ByteArray := #[]
    let mut i := 2
    while i < nals.size do
      let sliceNal := nals[i]!
      let pkt ← LeanAV.H264Syntax.packAvccPacket #[sliceNal] 4
      lenPrefixed := lenPrefixed.push pkt
      let auNals := if i == 2 then #[spsNal, ppsNal, sliceNal] else #[sliceNal]
      annexBPkts := annexBPkts.push (LeanAV.H264Entropy.joinAnnexB auNals)
      i := i + 1
    some (avccBody, lenPrefixed, annexBPkts)

def encodeHevcStreamForMedia (media : Media) (options : Options) : Option (ByteArray × Array (ByteArray × Bool) × Array ByteArray) := do
  let w := if media.videoWidth > 0 then media.videoWidth else (media.video[0]?.map (·.width)).getD 0
  let h := if media.videoHeight > 0 then media.videoHeight else (media.video[0]?.map (·.height)).getD 0
  if w == 0 || h == 0 then none
  let pf := media.videoPixFmt
  let raw := if media.rawVideo.size > 0 then media.rawVideo else packVideoFramesYuv420pRaw media.video
  let c := media.colour
  let vuiColour? : Option (Nat × Nat × Nat) :=
    if (c.primaries != 0 && c.primaries != 2) ||
       (c.transferCharacteristics != 0 && c.transferCharacteristics != 2) ||
       (c.matrixCoefficients != 0 && c.matrixCoefficients != 2) then
      some (
        if c.primaries == 0 then 2 else c.primaries,
        if c.transferCharacteristics == 0 then 2 else c.transferCharacteristics,
        if c.matrixCoefficients == 0 then 2 else c.matrixCoefficients)
    else none
  if pf == "yuv420p" && !media.hasDovi && vuiColour?.isNone then
    let (vps, sps, pps, encoded) ← LeanAV.HevcMain.encodeHevcNals w h raw options.qp options.log2Ctb options.tileColumns options.tileRows
    let hvcc := LeanAV.HevcMain.buildHvccRecord vps sps pps
    let mp4Pkts := encoded.mapIdx (fun i p => (LeanAV.HevcMain.packLenPrefixed4 p, i == 0))
    let annexB := encoded.mapIdx fun i s => LeanAV.HevcMain.muxAnnexB (if i == 0 then #[vps, sps, pps, s] else #[s])
    some (hvcc, mp4Pkts, annexB)
  else
    let (bitDepth, chromaFmt, vps, sps, pps, slices) ←
      LeanAV.HevcMain.encodeHevcNalsGen w h pf raw options.qp (options.qp == 0) options.log2Ctb options.tileColumns options.tileRows vuiColour?
    let hvcc ← LeanAV.HevcMain.buildHvccRecordGen vps sps pps bitDepth chromaFmt
    let mp4Pkts := slices.mapIdx fun i sl => Id.run do
      let mut sample := LeanAV.HevcMain.packLenPrefixed4 sl
      if i < media.rpus.size then
        let rpuNal := ByteArray.mk (encodeHevcRpuNal media.rpus[i]!.toList).toArray
        sample := sample ++ LeanAV.HevcMain.packLenPrefixed4 rpuNal
      return (sample, i == 0)
    let annexB := slices.mapIdx fun i sl => Id.run do
      let mut nals : Array ByteArray := if i == 0 then #[vps, sps, pps, sl] else #[sl]
      if i < media.rpus.size then
        nals := nals.push (ByteArray.mk (encodeHevcRpuNal media.rpus[i]!.toList).toArray)
      return LeanAV.HevcMain.muxAnnexB nals
    some (hvcc, mp4Pkts, annexB)

def encodeAv1StreamForMedia (media : Media) (options : Options) (outFmt : String) : Option (ByteArray × Array (ByteArray × Bool) × ByteArray) := do
  let w := if media.videoWidth > 0 then media.videoWidth else (media.video[0]?.map (·.width)).getD 0
  let h := if media.videoHeight > 0 then media.videoHeight else (media.video[0]?.map (·.height)).getD 0
  if w == 0 || h == 0 then none
  let pf := media.videoPixFmt
  let raw := if media.rawVideo.size > 0 then media.rawVideo else packVideoFramesYuv420pRaw media.video
  let fg? := if options.filmGrain > 0 then some (canonicalFilmGrain options.filmGrain) else media.filmGrain?
  if pf == "yuv420p" && !media.hasDovi && fg?.isNone then
    let (av1c, mp4Pkts) ← LeanAV.Av1Main.encodeAv1Mp4TrackPayloads w h raw options.qp options.av1TileColumns options.av1TileRows
    let rawStream ←
      if outFmt == "ivf" || outFmt == "obu" then
        LeanAV.Av1Main.encodeAv1FromYuv420p w h raw options.qp outFmt options.av1TileColumns options.av1TileRows
      else pure ByteArray.empty
    some (av1c, mp4Pkts, rawStream)
  else
    let (av1cBase, mp4Base) ← LeanAV.Av1Main.encodeAv1Mp4TrackPayloadsRaw w h pf raw options.qp options.av1TileColumns options.av1TileRows fg?
    let mp4Pkts := mp4Base.mapIdx fun i (pkt, sync) =>
      if i < media.rpus.size then
        match injectAv1RpuIntoTu pkt media.rpus[i]! with
        | some injected => (injected, sync)
        | none =>
          let rpuObu := ByteArray.mk (encodeAv1DoviEmdfObu media.rpus[i]!.toList).toArray
          (pkt ++ rpuObu, sync)
      else (pkt, sync)
    let rawStream ←
      if outFmt == "ivf" then
        let ivfFrames := mp4Pkts.map fun (pkt, _) => LeanAV.Av1Main.av1WrapObu LeanAV.Av1Main.av1ObuTd ByteArray.empty true ++ pkt
        pure (LeanAV.Av1Main.av1MuxIvf w h ivfFrames (Nat.max 1 media.fps) 1)
      else if outFmt == "obu" || outFmt == "av1" then
        let mut cat := ByteArray.empty
        for (pkt, _) in mp4Pkts do
          cat := cat ++ LeanAV.Av1Main.av1WrapObu LeanAV.Av1Main.av1ObuTd ByteArray.empty true ++ pkt
        pure cat
      else
        LeanAV.Av1Main.encodeAv1FromRaw w h pf raw options.qp "obu" options.av1TileColumns options.av1TileRows fg?
    some (av1cBase, mp4Pkts, rawStream)

def encodeVideoTrack (media : Media) (options : Options) : Option SynthMp4Track := do
  let first ← media.video[0]?
  let w := if media.videoWidth > 0 then media.videoWidth else first.width
  let h := if media.videoHeight > 0 then media.videoHeight else first.height
  let fps := Nat.max 1 media.fps
  let fmt ← PixelFormat.parse media.videoPixFmt
  let depth := fmt.bitDepth
  let c := media.colour
  let isHdr := c.primaries == 9 || c.transferCharacteristics == 16 || c.transferCharacteristics == 18 ||
               c.hasMastering || c.maxCll > 0 || options.colorPrimaries.isSome ||
               options.colorTrc.isSome || options.colorspace.isSome
  let mut stsd := ByteArray.empty
  let mut packets : Array (ByteArray × Bool) := #[]
  if options.videoCodec == "h264" then
    let (avcc, encoded, _) ← encodeH264StreamForMedia media options
    stsd :=
      if depth == 8 && !isHdr && !media.hasDovi then buildAvc1StsdBox w h avcc
      else
        p11BuildCrossStsd {
          kind := .video, codecId := "V_MPEG4/ISO/AVC", width := w, height := h,
          channels := 0, sampleRate := 0, timescale := fps * 1000, codecPrivate := avcc,
          colour := c, mastering := media.mastering, dovi := media.dovi, hasDovi := media.hasDovi, samples := #[] }
    packets := encoded.map (fun p => (p, true))
  else if options.videoCodec == "hevc" then
    let (hvcc, encoded, _) ← encodeHevcStreamForMedia media options
    stsd :=
      if depth == 8 && !isHdr && !media.hasDovi then buildHvc1StsdBox w h hvcc
      else
        p11BuildCrossStsd {
          kind := .video, codecId := "V_MPEGH/ISO/HEVC", width := w, height := h,
          channels := 0, sampleRate := 0, timescale := fps * 1000, codecPrivate := hvcc,
          colour := c, mastering := media.mastering, dovi := media.dovi, hasDovi := media.hasDovi, samples := #[] }
    packets := encoded
  else if options.videoCodec == "av1" then
    let (av1c, encoded, _) ← encodeAv1StreamForMedia media options "mp4"
    stsd :=
      if depth == 8 && !isHdr && !media.hasDovi then buildAv01StsdBox w h av1c
      else
        p11BuildCrossStsd {
          kind := .video, codecId := "V_AV1", width := w, height := h,
          channels := 0, sampleRate := 0, timescale := fps * 1000, codecPrivate := av1c,
          colour := c, mastering := media.mastering, dovi := media.dovi, hasDovi := media.hasDovi, samples := #[] }
    packets := encoded
  else if options.videoCodec == "prores" then
    stsd := buildApcnStsdBox w h
    for vf in media.video do
      let p ← LeanAV.Video.encodeYuv420pToProResFrame vf
      packets := packets.push (p, true)
  else none
  some {
    kind := .video
    timescale := fps * 1000
    width := w
    height := h
    stsdBox := stsd
    samples := packets.map fun p => { data := p.1, dur := 1000, cttsOff := 0, isSync := p.2 }
  }

def muxMkvHdrContainer (media : Media) (options : Options) : Option ByteArray := do
  if media.video.isEmpty then none
  let w := if media.videoWidth > 0 then media.videoWidth else (media.video[0]?.map (·.width)).getD 0
  let h := if media.videoHeight > 0 then media.videoHeight else (media.video[0]?.map (·.height)).getD 0
  if w == 0 || h == 0 then none
  let docType := if options.format == "webm" then "webm" else "matroska"
  let mut codecId := ""
  let mut codecPrivate := ByteArray.empty
  let mut packets : Array (ByteArray × Bool) := #[]
  if options.videoCodec == "hevc" && docType != "webm" then
    let (hvcc, mp4Pkts, _) ← encodeHevcStreamForMedia media options
    codecId := "V_MPEGH/ISO/HEVC"
    codecPrivate := hvcc
    packets := mp4Pkts
  else if options.videoCodec == "av1" then
    let (av1c, mp4Pkts, _) ← encodeAv1StreamForMedia media options "mp4"
    codecId := "V_AV1"
    codecPrivate := av1c
    packets := mp4Pkts
  else if options.videoCodec == "h264" && docType != "webm" then
    let (avcc, lenPrefixed, _) ← encodeH264StreamForMedia media options
    codecId := "V_MPEG4/ISO/AVC"
    codecPrivate := avcc
    packets := lenPrefixed.map (fun p => (p, true))
  else none
  let stepMs := Nat.max 1 (1000 / Nat.max 1 media.fps)
  let vTrack : P11CrossRemuxTrack := {
    kind := .video
    codecId := codecId
    width := w
    height := h
    channels := 0
    sampleRate := 0
    timescale := 1000
    codecPrivate := codecPrivate
    colour := media.colour
    mastering := media.mastering
    dovi := media.dovi
    hasDovi := media.hasDovi
    samples := packets.map (fun (p, sync) => (p, stepMs, sync))
  }
  let mut tracks : Array P11CrossRemuxTrack := #[vTrack]
  if let some af := media.audio then
    if options.audioCodec == "opus" || (docType == "webm" && options.audioCodec == "") then
      let af16 := if media.audioBits == 16 && af.sampleFmt == .s16p then af
        else channelArraysToAudioFrame (audioChannels16 media af) af.sampleRate 16
      let (ch, opPkts) ← LeanAV.Audio.encodeAudioFrameToOpusPackets af16
      tracks := tracks.push {
        kind := .audio
        codecId := "A_OPUS"
        width := 0
        height := 0
        channels := ch.toNat
        sampleRate := 48000
        timescale := 1000
        codecPrivate := LeanAV.Audio.buildOpusHeadPacket ch
        colour := media.colour
        mastering := media.mastering
        dovi := media.dovi
        hasDovi := false
        samples := opPkts.map (fun (p, _) => (p, 20, true))
      }
  p11MuxMkvFromCrossTracks docType tracks

def encodeAudioTrack (media : Media) (options : Options) : Option SynthMp4Track := do
  let af ← media.audio
  if options.audioCodec == "copy" then media.audioCopy
  else if options.audioCodec == "aac" then
    LeanAV.InprocTranscode.encodeChannelsToMp4AacTrack (audioChannels16 media af) af.sampleRate
  else if options.audioCodec == "opus" then
    let af16 := if media.audioBits == 16 && af.sampleFmt == .s16p then af
      else channelArraysToAudioFrame (audioChannels16 media af) af.sampleRate 16
    let (channels, packets) ← LeanAV.Audio.encodeAudioFrameToOpusPackets af16
    some {
      kind := .audio
      timescale := 48000
      width := 0
      height := 0
      stsdBox := buildOpusMp4StsdBox channels.toNat
      samples := packets.map fun p => { data := p.1, dur := 960, cttsOff := 0, isSync := true }
    }
  else none

def muxMpegTs (media : Media) (options : Options) : Option ByteArray := do
  let mut streams : Array MpegTsElementaryStream := #[]
  if !media.video.isEmpty then
    let packets ←
      if options.videoCodec == "h264" then do
        let (_, _, annexB) ← encodeH264StreamForMedia media options
        some annexB
      else if options.videoCodec == "hevc" then do
        let (_, _, annexB) ← encodeHevcStreamForMedia media options
        some annexB
      else none
    streams := streams.push {
      pid := 0x100
      streamType := if options.videoCodec == "h264" then 0x1B else 0x24
      packets := packets.mapIdx fun i p => (p, (i * 90000 / Nat.max 1 media.fps).toUInt64)
    }
  if let some af := media.audio then
    if options.audioCodec != "aac" then none
    let adts ← LeanAV.AacLc.aacEncodeAdtsStream (audioChannels16 media af) af.sampleRate 16 128000 true
    streams := streams.push { pid := 0x101, streamType := 0x0F, packets := #[(adts, 0)] }
  muxMpegTsProgram streams

def pcmCodecDepth? : String → Option Nat
  | "pcm_u8" => some 8
  | "pcm_s16le" => some 16
  | "pcm_s24le" => some 24
  | "pcm_s32le" => some 32
  | _ => none

def mux (media : Media) (options : Options) : Option ByteArray := do
  if media.video.isEmpty && media.audio.isNone then none
  else if options.format == "mp4" || options.format == "mov" then
    let mut tracks := #[]
    if !media.video.isEmpty then
      let video ← encodeVideoTrack media options
      tracks := tracks.push video
    if media.audio.isSome then
      let audio ← encodeAudioTrack media options
      tracks := tracks.push audio
    muxSynthMp4Container tracks
  else if options.format == "null" then some ByteArray.empty
  else if options.format == "rawvideo" || options.format == "framemd5" then
    if media.video.isEmpty || media.audio.isSome then none
    else if options.format == "framemd5" then muxLavfiFrameMd5Bytes media.video media.fps
    else
      let raw := if media.rawVideo.size > 0 then media.rawVideo else packVideoFramesYuv420pRaw media.video
      some raw
  else if options.format == "md5" then
    if !media.video.isEmpty && media.audio.isNone then
      let raw := if media.rawVideo.size > 0 then media.rawVideo else packVideoFramesYuv420pRaw media.video
      some (muxLavfiMd5Bytes raw)
    else if media.video.isEmpty then do
      let af ← media.audio
      some (muxLavfiMd5Bytes (channelsToPcmRawLE (audioChannels16 media af) 16))
    else none
  else if options.format == "ogg" || options.format == "opus" then
    if !media.video.isEmpty || options.audioCodec != "opus" then none
    let af ← media.audio
    let af16 := if media.audioBits == 16 && af.sampleFmt == .s16p then af
      else channelArraysToAudioFrame (audioChannels16 media af) af.sampleRate 16
    let (channels, packets) ← LeanAV.Audio.encodeAudioFrameToOpusPackets af16
    let header := LeanAV.Audio.buildOpusHeadPacket channels
    let tags := LeanAV.Audio.buildOpusTagsPacket
    muxOggLogicalStream (#[(header, 0), (tags, 0)] ++ packets)
  else if options.format == "mpegts" then muxMpegTs media options
  else if options.format == "wav" then
    if !media.video.isEmpty then none
    let af ← media.audio
    let srcChans := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
    let outBps ←
      if options.audioCodec == "" then some media.audioBits
      else pcmCodecDepth? options.audioCodec
    let outChans := scaleChannelsBps srcChans media.audioBits outBps
    some (muxWavPcmLE outChans af.sampleRate outBps)
  else if options.format == "s16le" || options.format == "s24le" || options.format == "s32le" then
    let targetBps := if options.format == "s32le" then 32 else if options.format == "s24le" then 24 else 16
    let expectedCodec := if targetBps == 32 then "pcm_s32le" else if targetBps == 24 then "pcm_s24le" else "pcm_s16le"
    if !media.video.isEmpty || (options.audioCodec != expectedCodec && options.audioCodec != "") then none
    let af ← media.audio
    let srcChans := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
    let outChans := scaleChannelsBps srcChans media.audioBits targetBps
    some (channelsToPcmRawLE outChans targetBps)
  else if options.format == "flac" then
    if !media.video.isEmpty || (options.audioCodec != "flac" && options.audioCodec != "") then none
    let af ← media.audio
    let bps := if 4 ≤ media.audioBits && media.audioBits ≤ 32 then media.audioBits else 16
    LeanAV.Audio.flacEncodeAudioFrame af bps
  else if options.format == "adts" then
    if !media.video.isEmpty || (options.audioCodec != "aac" && options.audioCodec != "") then none
    let af ← media.audio
    LeanAV.AacLc.aacEncodeAdtsStream (audioChannels16 media af) af.sampleRate 16 128000 true
  else if options.format == "mkv" || options.format == "matroska" || options.format == "webm" || options.format == "avi" then
    if options.videoCodec == "ffv1" && (options.format == "mkv" || options.format == "avi") then
      if media.video.isEmpty || media.audio.isSome then none
      else muxLavfiFfv1Bytes options.format media.video media.fps
    else if options.format == "mkv" || options.format == "matroska" || options.format == "webm" then
      muxMkvHdrContainer media options
    else none
  else if options.format == "hevc" || options.format == "h264" || options.format == "ivf" || options.format == "obu" then
    if media.video.isEmpty || media.audio.isSome then none
    if options.format == "hevc" && options.videoCodec == "hevc" then
      let (_, _, annexB) ← encodeHevcStreamForMedia media options
      some (annexB.foldl (· ++ ·) ByteArray.empty)
    else if options.format == "h264" && options.videoCodec == "h264" then
      let (_, _, annexB) ← encodeH264StreamForMedia media options
      some (annexB.foldl (· ++ ·) ByteArray.empty)
    else if options.videoCodec == "av1" && (options.format == "ivf" || options.format == "obu") then
      let (_, _, rawStream) ← encodeAv1StreamForMedia media options options.format
      some rawStream
    else none
  else none

def normalizePadLabel (raw : String) : String :=
  if raw.startsWith "[" && raw.endsWith "]" && raw.length ≥ 2 then
    String.ofList ((raw.toList.drop 1).dropLast)
  else raw

def filterStreams (inputs : Array Media) (options : Options) : Except String Media := do
  if inputs.isEmpty then throw "no decoded inputs"
  if options.filterComplex != "" then
    if options.videoFilter != "" || options.audioFilter != "" then
      throw "cannot combine -filter_complex with -vf or -af"
    if options.audioCodec == "copy" then
      throw "cannot combine -filter_complex with -c:a copy"
    if inputs.size == 1 &&
       (inputs[0]!.videoPixFmt != "yuv420p" || (options.pixFmt != "" && options.pixFmt != "yuv420p")) then
      let m0 := inputs[0]!
      let (_, outFps) ← runSingleStreamVideoFilterGraph options.filterComplex m0.video m0.fps
      let some hbdM := applyHbdVideoFilterChain { m0 with fps := outFps } options
        | throw "unsupported high-bit-depth filter_complex conversion (fail-closed)"
      return hbdM
    let graph ← parseFilterGraph options.filterComplex
    let inputLabels := graph.nodes.toList.flatMap (·.inputs)
    let mut videoIn : List (String × Array VideoFrame × Nat) := []
    let mut audioIn : List (String × AudioFrame) := []
    for idx in [:inputs.size] do
      if (inputLabels.contains s!"{idx}:v" && inputLabels.contains s!"{idx}:v:0") ||
         (inputLabels.contains s!"{idx}:a" && inputLabels.contains s!"{idx}:a:0") then
        throw "input stream consumed through multiple aliases without split/asplit (fail-closed)"
      let m := inputs[idx]!
      if !m.video.isEmpty then
        videoIn := videoIn ++ [(s!"{idx}:v", m.video, m.fps), (s!"{idx}:v:0", m.video, m.fps)]
      if let some af := m.audio then
        audioIn := audioIn ++ [(s!"{idx}:a", af), (s!"{idx}:a:0", af)]
    let outs ← runMultiStreamFilterGraph options.filterComplex videoIn audioIn
    let selected ←
      if options.maps.isEmpty then pure outs
      else do
        let mut sel : List (String × PadFormat × EdgeBufferQueue) := []
        for rawMap in options.maps do
          let lbl := normalizePadLabel rawMap
          match outs.find? (fun (oLbl, _, _) => oLbl == lbl) with
          | some hit => sel := sel ++ [hit]
          | none => throw s!"unmapped filter_complex output pad {rawMap} (fail-closed)"
        pure sel
    if (selected.filter (fun (_, fmt, _) => fmt.kind == .video)).length > 1 ||
       (selected.filter (fun (_, fmt, _) => fmt.kind == .audio)).length > 1 then
      throw "multiple output streams of the same kind are unsupported (fail-closed)"
    let (frames, fps) :=
      if options.noVideo then (#[], 25)
      else match selected.find? (fun (_, fmt, _) => fmt.kind == .video) with
        | some (_, fmt, q) =>
          let all := drainVideoQueue q
          let capped := match options.maxFrames with | some n => all.extract 0 n | none => all
          (capped, Nat.max 1 fmt.fpsNum)
        | none => (#[], 25)
    let audio :=
      if options.noAudio then none
      else match selected.find? (fun (_, fmt, _) => fmt.kind == .audio) with
        | some (_, _, q) => some (drainAudioQueue q)
        | none => none
    return syncMediaFromVideoFrames { video := frames, audio := audio, fps := fps, audioCopy := none }
  if inputs.size != 1 || !options.maps.isEmpty then
    throw "multiple inputs or explicit -map require -filter_complex (fail-closed)"
  filter inputs[0]! options

def runStreams (inputs : Array Media) (options : Options) : Except String ByteArray := do
  let filtered ← filterStreams inputs options
  match mux filtered options with
  | some bytes => return bytes
  | none => throw "unsupported codec/container combination or encoding failure (fail-closed)"

def run (media : Media) (options : Options) : Except String ByteArray :=
  runStreams #[media] options

structure Input where
  path : String
  format : String
  width : Nat := 0
  height : Nat := 0
  sampleRate : UInt32 := 48000
  channels : Nat := 2
  pixFmt : String := "yuv420p"
  deriving Inhabited

structure Invocation where
  inputs : Array Input := #[]
  output : String := ""
  options : Options := {}
  deriving Inhabited

def inferFormat (path : String) : String :=
  let p := path.toLower
  if p.endsWith ".mp4" || p.endsWith ".m4v" || p.endsWith ".m4a" then "mp4"
  else if p.endsWith ".mov" then "mov"
  else if p.endsWith ".hevc" || p.endsWith ".265" then "hevc"
  else if p.endsWith ".h264" || p.endsWith ".264" then "h264"
  else if p.endsWith ".obu" then "obu"
  else if p.endsWith ".ivf" then "ivf"
  else if p.endsWith ".yuv" || p.endsWith ".raw" then "rawvideo"
  else if p.endsWith ".wav" then "wav"
  else if p.endsWith ".flac" then "flac"
  else if p.endsWith ".aac" then "adts"
  else if p.endsWith ".ogg" || p.endsWith ".opus" || p.endsWith ".oga" then "ogg"
  else if p.endsWith ".ts" then "mpegts"
  else if p.endsWith ".mkv" then "mkv"
  else if p.endsWith ".webm" then "webm"
  else if p.endsWith ".avi" then "avi"
  else "unknown"

def parseEncoderKVParams (raw : String) (opts : Options) : Option Options := do
  let mut cur := opts
  for item in raw.splitOn ":" do
    if item != "" then
      let [k, v] := item.splitOn "=" | none
      let kl := k.toLower
      if kl == "ctu" then
        let n ← v.toNat?
        let l2 ← if n == 16 then some 4 else if n == 32 then some 5 else if n == 64 then some 6 else none
        cur := { cur with log2Ctb := l2 }
      else if kl == "tiles" then
        let [cols, rows] := v.splitOn "x" | none
        let cols ← cols.toNat?
        let rows ← rows.toNat?
        if cols == 0 || rows == 0 || cols > 8 || rows > 8 then none
        cur := { cur with tileColumns := cols, tileRows := rows }
      else if kl == "film-grain" || kl == "film_grain" then
        let n ← v.toNat?
        if n > 50 then none
        cur := { cur with filmGrain := n }
      else if kl == "qp" || kl == "crf" then
        let n ← v.toNat?
        if n > 255 then none
        cur := { cur with qp := n }
      else if kl == "colorprim" || kl == "color-primaries" then
        let code ← LeanAV.Cli.parseColorPrimariesCicp v
        cur := { cur with colorPrimaries := some code }
      else if kl == "transfer" || kl == "transfer-characteristics" then
        let code ← LeanAV.Cli.parseColorTrcCicp v
        cur := { cur with colorTrc := some code }
      else if kl == "colormatrix" || kl == "matrix-coefficients" then
        let code ← LeanAV.Cli.parseColorspaceCicp v
        cur := { cur with colorspace := some code }
      else if kl == "hdr10" || kl == "hdr-opt" || kl == "hdr10-opt" || kl == "repeat-headers" ||
              kl == "aud" || kl == "profile" || kl == "level-idc" || kl == "high-tier" ||
              kl == "master-display" || kl == "max-cll" || kl == "dolby-vision-profile" ||
              kl == "enable-hdr" || kl == "film-grain-denoise" then
        pure ()
      else none
  some cur

def scan (args : List String) : Option Invocation := do
  let mut job : Invocation := {}
  let mut pending : Input := { path := "", format := "" }
  let mut fmt := ""
  let mut explicitVideo := false
  let mut explicitAudio := false
  let mut pendingInputOptions := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "-i" :: path :: xs =>
      if job.output != "" then none
      let inFmt := if fmt == "" then inferFormat path else if fmt == "matroska" then "mkv" else fmt
      let input := { pending with path := path, format := inFmt }
      job := { job with inputs := job.inputs.push input }
      pending := { path := "", format := "" }
      pendingInputOptions := false
      fmt := ""
      rest := xs
    | "-f" :: value :: xs =>
      fmt := if value == "matroska" then "mkv" else value
      rest := xs
    | "-s" :: value :: xs =>
      if job.output != "" then none
      let [w, h] := value.splitOn "x" | none
      let w ← w.toNat?
      let h ← h.toNat?
      pending := { pending with width := w, height := h }
      pendingInputOptions := true
      rest := xs
    | "-pix_fmt" :: value :: xs =>
      let pf ← PixelFormat.parse value
      let pfC := pf.toString
      if job.inputs.isEmpty then
        pending := { pending with pixFmt := pfC }
        pendingInputOptions := true
      else
        job := { job with options := { job.options with pixFmt := pfC } }
      rest := xs
    | "-color_primaries" :: value :: xs =>
      let code ← LeanAV.Cli.parseColorPrimariesCicp value
      job := { job with options := { job.options with colorPrimaries := some code } }
      rest := xs
    | "-color_trc" :: value :: xs =>
      let code ← LeanAV.Cli.parseColorTrcCicp value
      job := { job with options := { job.options with colorTrc := some code } }
      rest := xs
    | "-colorspace" :: value :: xs =>
      let code ← LeanAV.Cli.parseColorspaceCicp value
      job := { job with options := { job.options with colorspace := some code } }
      rest := xs
    | "-film-grain" :: value :: xs =>
      let n ← value.toNat?
      if n > 50 then none
      job := { job with options := { job.options with filmGrain := n } }
      rest := xs
    | "-c:v" :: value :: xs =>
      let norm := match value with
        | "libx264" | "h264" => "h264"
        | "libx265" | "hevc" => "hevc"
        | "libaom-av1" | "libsvtav1" | "av1" => "av1"
        | other => other
      if !["h264", "hevc", "av1", "prores", "ffv1", "rawvideo", "wrapped_avframe"].contains norm then none
      explicitVideo := true
      job := { job with options := { job.options with videoCodec := norm, explicitVideoCodec := true } }
      rest := xs
    | "-c:a" :: value :: xs =>
      let norm := match value with
        | "libopus" => "opus"
        | other => other
      if !["aac", "opus", "flac", "pcm_u8", "pcm_s16le", "pcm_s24le", "pcm_s32le", "copy"].contains norm then none
      explicitAudio := true
      job := { job with options := { job.options with audioCodec := norm } }
      rest := xs
    | "-filter_complex" :: value :: xs =>
      if job.options.filterComplex != "" then none
      job := { job with options := { job.options with filterComplex := value } }
      rest := xs
    | "-map" :: value :: xs =>
      job := { job with options := { job.options with maps := job.options.maps.push value } }
      rest := xs
    | "-vf" :: value :: xs =>
      job := { job with options := { job.options with videoFilter := value } }
      rest := xs
    | "-af" :: value :: xs =>
      job := { job with options := { job.options with audioFilter := value } }
      rest := xs
    | "-r" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 1000 then none
      rest := xs
    | "-framerate" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 1000 then none
      rest := xs
    | "-frames:v" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 then none
      job := { job with options := { job.options with maxFrames := some n } }
      rest := xs
    | "-crf" :: value :: xs =>
      let n ← value.toNat?
      if n > 63 then none
      job := { job with options := { job.options with qp := n } }
      rest := xs
    | "-qp" :: value :: xs =>
      let n ← value.toNat?
      if n > 255 then none
      job := { job with options := { job.options with qp := n } }
      rest := xs
    | "-ar" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 192000 || job.output != "" then none
      pending := { pending with sampleRate := n.toUInt32 }
      pendingInputOptions := true
      rest := xs
    | "-ac" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 8 || job.output != "" then none
      pending := { pending with channels := n }
      pendingInputOptions := true
      rest := xs
    | "-tile-columns" :: value :: xs =>
      let n ← value.toNat?
      if n > 6 then none
      job := { job with options := { job.options with av1TileColumns := n } }
      rest := xs
    | "-tile-rows" :: value :: xs =>
      let n ← value.toNat?
      if n > 6 then none
      job := { job with options := { job.options with av1TileRows := n } }
      rest := xs
    | "-x264-params" :: value :: xs =>
      let updated ← parseEncoderKVParams value job.options
      job := { job with options := updated }
      rest := xs
    | "-x265-params" :: value :: xs =>
      let updated ← parseEncoderKVParams value job.options
      job := { job with options := updated }
      rest := xs
    | "-svtav1-params" :: value :: xs =>
      let updated ← parseEncoderKVParams value job.options
      job := { job with options := updated }
      rest := xs
    | "-aom-params" :: value :: xs =>
      let updated ← parseEncoderKVParams value job.options
      job := { job with options := updated }
      rest := xs
    | "-an" :: xs =>
      job := { job with options := { job.options with noAudio := true } }
      rest := xs
    | "-vn" :: xs =>
      job := { job with options := { job.options with noVideo := true } }
      rest := xs
    | flag :: value :: xs =>
      if flag == "-loglevel" || flag == "-v" then
        if !LeanAV.Cli.supportedLogLevel value then none
        rest := xs
      else if ["-y", "-n", "-json", "-hide_banner", "-nostdin"].contains flag then
        rest := value :: xs
      else if flag.startsWith "-" && flag != "-" then none
      else
        if job.output != "" then none
        job := { job with output := flag }
        rest := value :: xs
    | [flag] =>
      if ["-y", "-n", "-json", "-hide_banner", "-nostdin"].contains flag then rest := []
      else if flag.startsWith "-" && flag != "-" then none
      else
        if job.output != "" then none
        job := { job with output := flag }
        rest := []
    | [] => pure ()
  if job.inputs.isEmpty || job.output == "" || pendingInputOptions then none
  if (job.inputs.size > 1 || !job.options.maps.isEmpty) && job.options.filterComplex == "" then none
  let rawOutFmt := if fmt == "" then inferFormat job.output else fmt
  let outputFormat := if rawOutFmt == "matroska" then "mkv" else rawOutFmt
  if outputFormat == "unknown" || (job.output == "-" && outputFormat != "null") then none
  if !explicitVideo && (job.options.videoFilter != "" || job.options.filterComplex != "") &&
     outputFormat != "null" && outputFormat != "rawvideo" && outputFormat != "md5" && outputFormat != "framemd5" &&
     outputFormat != "ogg" && outputFormat != "opus" && outputFormat != "wav" && outputFormat != "s16le" &&
     outputFormat != "s24le" && outputFormat != "s32le" && outputFormat != "flac" && outputFormat != "adts" then none
  let defaultVCodec :=
    if explicitVideo then job.options.videoCodec
    else if outputFormat == "rawvideo" || outputFormat == "null" || outputFormat == "md5" || outputFormat == "framemd5" then "rawvideo"
    else if outputFormat == "hevc" then "hevc"
    else if outputFormat == "ivf" || outputFormat == "obu" || outputFormat == "webm" then "av1"
    else job.options.videoCodec
  let options := { job.options with
    format := outputFormat
    videoCodec := defaultVCodec
    explicitVideoCodec := explicitVideo
    audioCodec := if explicitAudio then job.options.audioCodec
      else if outputFormat == "ogg" || outputFormat == "opus" || outputFormat == "webm" then "opus"
      else if outputFormat == "wav" then ""
      else if outputFormat == "s16le" || outputFormat == "null" then "pcm_s16le"
      else if outputFormat == "s24le" then "pcm_s24le"
      else if outputFormat == "s32le" then "pcm_s32le"
      else if outputFormat == "flac" then "flac" else job.options.audioCodec }
  some { job with options := options }

example : rawVideoGateSpec.gate (2, 2, 6) = true := by decide
example : rawVideoGateSpec.gate (2, 2, 7) = false := by decide
example : rawVideoGateSpec.gate (0, 2, 6) = false := by decide
example : rawVideoGateSpec.gate (3, 2, 9) = false := by decide
example : rawVideoGateSpec.gate (2, 2, 0) = false := by decide
example : p11UnifiedHdrGateSpec.gate (16, 16, 10, 1) = true := by decide
example : p11UnifiedHdrGateSpec.gate (15, 16, 10, 1) = false := by decide

end LeanAV.UnifiedPipeline
