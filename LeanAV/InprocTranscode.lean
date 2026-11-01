import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.Format
import LeanAV.Scale
import LeanAV.Encoder
import LeanAV.H264Syntax
import LeanAV.H264Entropy
import LeanAV.H264IntraTransform
import LeanAV.H264InterDeblockDpb
import LeanAV.AacLc
import LeanAV.IO

namespace LeanAV.InprocTranscode

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream
open LeanAV.Format
open LeanAV.Scale
open LeanAV.Encoder

inductive InprocAudioMode where
  | none
  | copy
  | reencodeAacLc
  deriving Repr, DecidableEq, Inhabited

structure InprocTranscodeScope where
  srcW            : Nat
  srcH            : Nat
  dstW            : Nat
  dstH            : Nat
  chromaFormatIdc : Nat
  bitDepthLuma8   : Nat
  bitDepthChroma8 : Nat
  frameMbsOnly    : Bool
  hasFmo          : Bool
  hasScalingLists : Bool
  qpprimeBypass   : Bool
  profileIdc      : Nat
  audioChannels   : Nat
  ringCap         : Nat
  deriving Repr, DecidableEq, Inhabited

def InprocTranscodeScopeSafe (s : InprocTranscodeScope) : Prop :=
  0 < s.srcW ∧ s.srcW % 2 = 0 ∧
  0 < s.srcH ∧ s.srcH % 2 = 0 ∧
  0 < s.dstW ∧ s.dstW % 2 = 0 ∧
  0 < s.dstH ∧ s.dstH % 2 = 0 ∧
  s.chromaFormatIdc = 1 ∧
  s.bitDepthLuma8 = 0 ∧
  s.bitDepthChroma8 = 0 ∧
  s.frameMbsOnly = true ∧
  s.hasFmo = false ∧
  s.hasScalingLists = false ∧
  s.qpprimeBypass = false ∧
  s.profileIdc ≠ 135 ∧
  (s.audioChannels = 0 ∨ s.audioChannels = 1 ∨ s.audioChannels = 2) ∧
  0 < s.ringCap

instance (s : InprocTranscodeScope) : Decidable (InprocTranscodeScopeSafe s) :=
  inferInstanceAs (Decidable
    (0 < s.srcW ∧ s.srcW % 2 = 0 ∧
     0 < s.srcH ∧ s.srcH % 2 = 0 ∧
     0 < s.dstW ∧ s.dstW % 2 = 0 ∧
     0 < s.dstH ∧ s.dstH % 2 = 0 ∧
     s.chromaFormatIdc = 1 ∧
     s.bitDepthLuma8 = 0 ∧
     s.bitDepthChroma8 = 0 ∧
     s.frameMbsOnly = true ∧
     s.hasFmo = false ∧
     s.hasScalingLists = false ∧
     s.qpprimeBypass = false ∧
     s.profileIdc ≠ 135 ∧
     (s.audioChannels = 0 ∨ s.audioChannels = 1 ∨ s.audioChannels = 2) ∧
     0 < s.ringCap))

def inprocTranscodeGate (s : InprocTranscodeScope) : Bool :=
  decide (InprocTranscodeScopeSafe s)

def inprocTranscodeGateSpec : AVGateSpec InprocTranscodeScope InprocTranscodeScopeSafe where
  gate := inprocTranscodeGate
  sound := by
    intro s h
    exact of_decide_eq_true h
  complete := by
    intro s h
    exact decide_eq_true h
  posWitness := {
    srcW := 16, srcH := 16, dstW := 16, dstH := 16,
    chromaFormatIdc := 1, bitDepthLuma8 := 0, bitDepthChroma8 := 0,
    frameMbsOnly := true, hasFmo := false,
    hasScalingLists := false, qpprimeBypass := false, profileIdc := 100,
    audioChannels := 2, ringCap := 64
  }
  negWitness := {
    srcW := 15, srcH := 16, dstW := 16, dstH := 16,
    chromaFormatIdc := 1, bitDepthLuma8 := 0, bitDepthChroma8 := 0,
    frameMbsOnly := true, hasFmo := false,
    hasScalingLists := false, qpprimeBypass := false, profileIdc := 100,
    audioChannels := 2, ringCap := 64
  }
  nonVacuous := rfl
  tight := rfl

theorem inprocTranscodeGateSpec_iff (s : InprocTranscodeScope) :
    inprocTranscodeGateSpec.gate s = true ↔ InprocTranscodeScopeSafe s :=
  inprocTranscodeGateSpec.iff_safe s

structure InprocDecodedBlk4 where
  sliceId      : Nat := 0
  isIntra      : Bool := false
  hasCoeff     : Bool := false
  refIdxL0     : Int := -1
  mvL0         : LeanAV.H264InterDeblockDpb.MotionVec := ⟨0, 0⟩
  refPicUidL0  : Option Nat := none
  refIdxL1     : Int := -1
  mvL1         : LeanAV.H264InterDeblockDpb.MotionVec := ⟨0, 0⟩
  refPicUidL1  : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

structure InprocStoredPic where
  uid          : Nat
  poc          : Int
  isLongTerm   : Bool
  yPlane       : Plane2D
  uPlane       : Plane2D
  vPlane       : Plane2D
  cropLeft     : Nat
  cropTop      : Nat
  cropWidth    : Nat
  cropHeight   : Nat
  gridW4       : Nat
  gridH4       : Nat
  colGrid      : Array InprocDecodedBlk4
  deriving Inhabited

structure InprocPocState where
  prevPocMsb         : Int := 0
  prevPocLsb         : Int := 0
  prevFrameNum       : Nat := 0
  prevFrameNumOffset : Nat := 0
  prevHasMmco5       : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure InprocSpsPair where
  syn : LeanAV.H264Syntax.H264SpsFull
  ent : LeanAV.H264Entropy.SpsFull
  deriving Inhabited

structure InprocPpsPair where
  syn : LeanAV.H264Syntax.H264PpsFull
  ent : LeanAV.H264Entropy.PpsFull
  deriving Inhabited

structure InprocDecoderState where
  spsTable    : Array (Option InprocSpsPair) := Array.replicate 32 none
  ppsTable    : Array (Option InprocPpsPair) := Array.replicate 256 none
  dpb         : LeanAV.H264InterDeblockDpb.H264Dpb := {}
  dpbInit     : Bool := false
  storedPics  : Array InprocStoredPic := #[]
  emittedUids : Array Nat := #[]
  pocState    : InprocPocState := {}
  deriving Inhabited

structure InprocMp4Probe where
  videoTrack   : NativeMp4Track
  avcc         : LeanAV.H264Syntax.AvcDecoderConfigRecord
  nalLenSize   : Nat
  initSps      : LeanAV.H264Syntax.H264SpsFull
  initPps      : LeanAV.H264Syntax.H264PpsFull
  srcW         : Nat
  srcH         : Nat
  dstW         : Nat
  dstH         : Nat
  audioTrack?  : Option NativeMp4Track
  audioAsc?    : Option LeanAV.AacLc.AacLcAsc
  audioMode    : InprocAudioMode
  scope        : InprocTranscodeScope
  deriving Inhabited

private def buildScopeForSpsPps
    (sps : LeanAV.H264Syntax.H264SpsFull)
    (pps : LeanAV.H264Syntax.H264PpsFull)
    (dstW dstH audioCh ringCap : Nat) : InprocTranscodeScope :=
  let hasScaling :=
    sps.seqScalingMatrixPresentFlag || pps.picScalingMatrixPresentFlag
  let hasFmo :=
    pps.numSliceGroupsMinus1 != 0 || sps.separateColourPlaneFlag
  {
    srcW := sps.widthPx.toNat
    srcH := sps.heightPx.toNat
    dstW := dstW
    dstH := dstH
    chromaFormatIdc := sps.chromaFormatIdc.toNat
    bitDepthLuma8 := sps.bitDepthLumaMinus8.toNat
    bitDepthChroma8 := sps.bitDepthChromaMinus8.toNat
    frameMbsOnly := sps.frameMbsOnlyFlag && !sps.mbAdaptiveFrameFieldFlag
    hasFmo := hasFmo
    hasScalingLists := hasScaling
    qpprimeBypass := sps.qpprimeYZeroTransformBypass
    profileIdc := sps.profileIdc.toNat
    audioChannels := audioCh
    ringCap := ringCap
  }

private def registerSpsNalu (st : InprocDecoderState) (nal : ByteArray) : Option InprocDecoderState := do
  let syn ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray nal)
  let ent ← LeanAV.H264Entropy.parseSpsFull nal
  let idx := syn.spsId.toNat
  if idx ≥ 32 || ent.spsId != idx then none
  else
    some { st with spsTable := st.spsTable.set! idx (some { syn := syn, ent := ent }) }

private def registerPpsNalu (st : InprocDecoderState) (nal : ByteArray) : Option InprocDecoderState := do
  let rbsp := LeanAV.H264Entropy.stripNalEmulationBytes nal
  if rbsp.data.size < 2 then none
  else do
    let r0 : BitReader := { slice := ByteSlice.ofByteArray rbsp, bitOffset := 8 }
    let (ppsId64, r1) ← r0.readUE
    let (spsId64, _) ← r1.readUE
    let ppsIdx := ppsId64.toNat
    let spsIdx := spsId64.toNat
    if ppsIdx ≥ 256 || spsIdx ≥ 32 then none
    else do
      let spsPair ← (st.spsTable.getD spsIdx none)
      let syn ← LeanAV.H264Syntax.parseH264PpsFull (ByteSlice.ofByteArray nal) (some spsPair.syn)
      let entSpsArr := st.spsTable.map (fun o => o.map (·.ent))
      let ent ← LeanAV.H264Entropy.parsePpsFull nal entSpsArr
      if syn.ppsId.toNat != ppsIdx || ent.ppsId != ppsIdx then none
      else
        some { st with ppsTable := st.ppsTable.set! ppsIdx (some { syn := syn, ent := ent }) }

private def findStoredPic (pics : Array InprocStoredPic) (uid : Nat) : Option InprocStoredPic :=
  pics.find? (fun p => p.uid == uid)

private def cropPlane2D (src : Plane2D) (x0 y0 w h : Nat) : Option Plane2D := do
  if w == 0 || h == 0 || x0 + w > src.width || y0 + h > src.height then none
  else Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h)
    for r in [:h] do
      for c in [:w] do
        out := out.push (src.getPixel (y0 + r) (x0 + c))
    return some { data := out, width := w, height := h, stride := w }

private def storedPicToVideoFrame (pic : InprocStoredPic) : Option VideoFrame := do
  if pic.cropWidth % 2 != 0 || pic.cropHeight % 2 != 0 then none
  else
    let yCropped ←
      if pic.cropLeft == 0 && pic.cropTop == 0 &&
         pic.cropWidth == pic.yPlane.width && pic.cropHeight == pic.yPlane.height &&
         pic.yPlane.stride == pic.yPlane.width then
        some pic.yPlane
      else
        cropPlane2D pic.yPlane pic.cropLeft pic.cropTop pic.cropWidth pic.cropHeight
    let uCropped ←
      if pic.cropLeft == 0 && pic.cropTop == 0 &&
         pic.cropWidth / 2 == pic.uPlane.width && pic.cropHeight / 2 == pic.uPlane.height &&
         pic.uPlane.stride == pic.uPlane.width then
        some pic.uPlane
      else
        cropPlane2D pic.uPlane (pic.cropLeft / 2) (pic.cropTop / 2) (pic.cropWidth / 2) (pic.cropHeight / 2)
    let vCropped ←
      if pic.cropLeft == 0 && pic.cropTop == 0 &&
         pic.cropWidth / 2 == pic.vPlane.width && pic.cropHeight / 2 == pic.vPlane.height &&
         pic.vPlane.stride == pic.vPlane.width then
        some pic.vPlane
      else
        cropPlane2D pic.vPlane (pic.cropLeft / 2) (pic.cropTop / 2) (pic.cropWidth / 2) (pic.cropHeight / 2)
    some {
      width := pic.cropWidth
      height := pic.cropHeight
      pixFmt := .yuv420p
      colorMatrix := .bt709
      pts := 0
      duration := 1
      timeBase := AVRational.tb90kHz
      planes := #[yCropped, uCropped, vCropped]
    }

/-! ## Plane, Scan, and Intra Mode Helpers -/

@[inline]
private def planeGetXY (p : Plane2D) (x y : Nat) : UInt8 :=
  if x < p.width && y < p.height then p.getPixel y x else 128

@[inline]
private def planeSetXY (p : Plane2D) (x y : Nat) (v : UInt8) : Plane2D :=
  if x < p.width && y < p.height then p.setPixel y x v else p

private def extractMbYFromPlane (p : Plane2D) (mbX mbY : Nat) : Array UInt8 :=
  let maxX := if p.width > 0 then p.width - 1 else 0
  let maxY := if p.height > 0 then p.height - 1 else 0
  Array.ofFn fun i : Fin 256 =>
    let sx := Nat.min maxX (mbX * 16 + i.val % 16)
    let sy := Nat.min maxY (mbY * 16 + i.val / 16)
    p.getPixel sy sx

private def extractMbCFromPlane (p : Plane2D) (mbX mbY : Nat) : Array UInt8 :=
  let maxX := if p.width > 0 then p.width - 1 else 0
  let maxY := if p.height > 0 then p.height - 1 else 0
  Array.ofFn fun i : Fin 64 =>
    let sx := Nat.min maxX (mbX * 8 + i.val % 8)
    let sy := Nat.min maxY (mbY * 8 + i.val / 8)
    p.getPixel sy sx

private def writeMbYToPlane (p : Plane2D) (mbX mbY : Nat) (y256 : Array UInt8) : Plane2D := Id.run do
  let mut dst := p
  for r in [:16] do
    for c in [:16] do
      dst := planeSetXY dst (mbX * 16 + c) (mbY * 16 + r) (y256.getD (r * 16 + c) 0)
  return dst

private def writeMbCToPlane (p : Plane2D) (mbX mbY : Nat) (c64 : Array UInt8) : Plane2D := Id.run do
  let mut dst := p
  for r in [:8] do
    for c in [:8] do
      dst := planeSetXY dst (mbX * 8 + c) (mbY * 8 + r) (c64.getD (r * 8 + c) 0)
  return dst

private def ac15ScanToRaster16 (scan15 : Array Int) : Array Int := Id.run do
  let mut scan16 := Array.replicate 16 (0 : Int)
  for k in [:15] do
    scan16 := scan16.set! (k + 1) (scan15.getD k 0)
  return LeanAV.H264Entropy.zigzagToRaster4x4 scan16

private def raster16ToAc15Scan (raster16 : Array Int) : Array Int :=
  (LeanAV.H264Entropy.rasterToZigzag4x4 raster16).extract 1 16

private def anyNonZeroInt (arr : Array Int) (limit : Nat) : Bool := Id.run do
  let n := Nat.min limit arr.size
  for i in [:n] do
    if arr.getD i 0 != 0 then return true
  return false

private def buildIntraMbNeighbors
    (pY pU pV : Plane2D)
    (mbSliceIds : Array Int) (mbIsIntra : Array Bool)
    (mbsW mbX mbY : Nat) (curSliceId : Int) (constrainedIntra : Bool)
    : LeanAV.H264IntraTransform.H264IntraMbNeighbors :=
  let mbAvail (nx ny : Nat) : Bool :=
    let idx := ny * mbsW + nx
    mbSliceIds.getD idx (-1) == curSliceId &&
      (!constrainedIntra || mbIsIntra.getD idx false)
  let leftAv := mbX > 0 && mbAvail (mbX - 1) mbY
  let topAv  := mbY > 0 && mbAvail mbX (mbY - 1)
  let tlAv   := mbX > 0 && mbY > 0 && mbAvail (mbX - 1) (mbY - 1)
  let trAv   := mbY > 0 && mbX + 1 < mbsW && mbAvail (mbX + 1) (mbY - 1)
  let leftY := Array.ofFn fun i : Fin 16 =>
    if leftAv then planeGetXY pY (mbX * 16 - 1) (mbY * 16 + i.val) else 128
  let topY := Array.ofFn fun i : Fin 16 =>
    if topAv then planeGetXY pY (mbX * 16 + i.val) (mbY * 16 - 1) else 128
  let trFallback := topY.getD 15 128
  let topRightY := Array.ofFn fun i : Fin 8 =>
    if trAv then planeGetXY pY ((mbX + 1) * 16 + i.val) (mbY * 16 - 1) else trFallback
  let topLeftY : UInt8 :=
    if tlAv then planeGetXY pY (mbX * 16 - 1) (mbY * 16 - 1) else 128
  let leftU := Array.ofFn fun i : Fin 8 =>
    if leftAv then planeGetXY pU (mbX * 8 - 1) (mbY * 8 + i.val) else 128
  let topU := Array.ofFn fun i : Fin 8 =>
    if topAv then planeGetXY pU (mbX * 8 + i.val) (mbY * 8 - 1) else 128
  let topLeftU : UInt8 :=
    if tlAv then planeGetXY pU (mbX * 8 - 1) (mbY * 8 - 1) else 128
  let leftV := Array.ofFn fun i : Fin 8 =>
    if leftAv then planeGetXY pV (mbX * 8 - 1) (mbY * 8 + i.val) else 128
  let topV := Array.ofFn fun i : Fin 8 =>
    if topAv then planeGetXY pV (mbX * 8 + i.val) (mbY * 8 - 1) else 128
  let topLeftV : UInt8 :=
    if tlAv then planeGetXY pV (mbX * 8 - 1) (mbY * 8 - 1) else 128
  { leftAvail := leftAv, topAvail := topAv, topRightAvail := trAv, topLeftAvail := tlAv,
    leftY := leftY, topY := topY, topRightY := topRightY, topLeftY := topLeftY,
    leftU := leftU, topU := topU, topLeftU := topLeftU,
    leftV := leftV, topV := topV, topLeftV := topLeftV }

private def deriveMostProbableIntraMode
    (intraModeGrid : Array Nat) (blkSliceIds : Array Int) (blkIsIntra : Array Bool)
    (gridW4 gx gy : Nat) (curSliceId : Int) (constrainedIntra : Bool) : Nat :=
  let dcOutside : Bool :=
    gx == 0 || gy == 0 ||
    blkSliceIds.getD (gy * gridW4 + (gx - 1)) (-1) != curSliceId ||
    blkSliceIds.getD ((gy - 1) * gridW4 + gx) (-1) != curSliceId ||
    (constrainedIntra &&
      (!blkIsIntra.getD (gy * gridW4 + (gx - 1)) false ||
       !blkIsIntra.getD ((gy - 1) * gridW4 + gx) false))
  if dcOutside then 2
  else
    let mA := intraModeGrid.getD (gy * gridW4 + (gx - 1)) 2
    let mB := intraModeGrid.getD ((gy - 1) * gridW4 + gx) 2
    Nat.min mA mB

private def syntaxToActualIntraMode (mpm pf rem : Nat) : Nat :=
  if pf != 0 then mpm
  else if rem < mpm then rem else rem + 1

private def actualToSyntaxIntraMode (mpm actual : Nat) : Nat × Nat :=
  if actual == mpm then (1, 0)
  else if actual < mpm then (0, actual) else (0, actual - 1)

/-! ## Intra Reconstruction & Inter Motion Compensation -/

private def reconstructDecodedIntraMb
    (mb : LeanAV.H264Entropy.MbSyntax)
    (nbrs : LeanAV.H264IntraTransform.H264IntraMbNeighbors)
    (intraModeGrid0 : Array Nat) (blkSliceIds : Array Int) (blkIsIntra : Array Bool)
    (gridW4 mbX mbY : Nat) (curSliceId : Int) (constrainedIntra : Bool)
    (qpY : Nat) (cqpOff secCqpOff : Int)
    : Option (LeanAV.H264IntraTransform.H264Yuv420pMb × Array Nat × Array Bool) := do
  if mb.kind == .iPcm then
    let pcm ← LeanAV.H264IntraTransform.decodeIpcmMb420 mb.pcmBytes.data
    let mut modes := intraModeGrid0
    for ry in [:4] do
      for rx in [:4] do
        modes := modes.set! ((mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)) 2
    some (pcm, modes, Array.replicate 16 true)
  else
    let qp := LeanAV.H264IntraTransform.clampQp qpY
    let qpcCb := LeanAV.H264IntraTransform.qpcFromQpy qp cqpOff
    let qpcCr := LeanAV.H264IntraTransform.qpcFromQpy qp secCqpOff
    let mut modes := intraModeGrid0
    let mut hasCoeff := Array.replicate 16 false
    let mut canvasY := Array.replicate 256 (0 : UInt8)
    if mb.kind == .i16x16 then
      let i16Mode := (mb.intraIdx - 1) % 4
      let pred256 := LeanAV.H264IntraTransform.pred16x16 i16Mode
        nbrs.leftY nbrs.topY nbrs.topLeftY nbrs.leftAvail nbrs.topAvail
      let dcRaster := LeanAV.H264Entropy.zigzagToRaster4x4 mb.i16Dc
      let hasDc := anyNonZeroInt mb.i16Dc 16
      let mut ac16 : Array (Array Int) := Array.emptyWithCapacity 16
      for b in [:16] do
        let (xO, yO) := LeanAV.H264IntraTransform.zScan4BlkCoord b
        let rx := xO / 4
        let ry := yO / 4
        modes := modes.set! ((mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)) 2
        let scanAc := (mb.lumaAcOr4x4.getD b #[]).extract 0 15
        let hasAc := (mb.cbp &&& 0xF) != 0 && anyNonZeroInt scanAc 15
        hasCoeff := hasCoeff.set! (ry * 4 + rx) (hasDc || hasAc)
        ac16 := ac16.push (if (mb.cbp &&& 0xF) != 0 then ac15ScanToRaster16 scanAc else Array.replicate 16 0)
      canvasY := LeanAV.H264IntraTransform.reconstructIntra16x16LumaLossy pred256 dcRaster ac16 qp
    else if mb.transform8x8 != 0 then
      let sched := LeanAV.H264IntraTransform.zScan8Schedule nbrs.topAvail nbrs.topRightAvail
      for i8 in [:4] do
        let (xO, yO, trAv) := sched.getD i8 (0, 0, false)
        let gx0 := mbX * 4 + xO / 4
        let gy0 := mbY * 4 + yO / 4
        let mpm := deriveMostProbableIntraMode modes blkSliceIds blkIsIntra gridW4 gx0 gy0 curSliceId constrainedIntra
        let (pf, rem) := mb.intraPred.getD i8 (1, 0)
        let m := syntaxToActualIntraMode mpm pf rem
        for dy in [:2] do
          for dx in [:2] do
            modes := modes.set! ((gy0 + dy) * gridW4 + (gx0 + dx)) m
        let n := LeanAV.H264IntraTransform.mbSubblockNeighbors 8 canvasY nbrs xO yO trAv
        let pred64 := LeanAV.H264IntraTransform.pred8x8 m n
        let scan64 :=
          if (mb.cbp &&& (1 <<< i8)) != 0 then mb.luma8x8.getD i8 (Array.replicate 64 0)
          else Array.replicate 64 0
        let nz := (mb.cbp &&& (1 <<< i8)) != 0 && anyNonZeroInt scan64 64
        for dy in [:2] do
          for dx in [:2] do
            hasCoeff := hasCoeff.set! ((yO / 4 + dy) * 4 + (xO / 4 + dx)) nz
        let rec64 :=
          if nz then
            LeanAV.H264IntraTransform.reconstructSubblock8Idct pred64
              (LeanAV.H264Entropy.zigzagToRaster8x8 scan64) qp
          else pred64
        canvasY := LeanAV.H264IntraTransform.writeMbBlock8 canvasY xO yO rec64
    else
      let sched := LeanAV.H264IntraTransform.zScan4Schedule nbrs.topAvail nbrs.topRightAvail
      for b in [:16] do
        let (xO, yO, trAv) := sched.getD b (0, 0, false)
        let rx := xO / 4
        let ry := yO / 4
        let gx := mbX * 4 + rx
        let gy := mbY * 4 + ry
        let mpm := deriveMostProbableIntraMode modes blkSliceIds blkIsIntra gridW4 gx gy curSliceId constrainedIntra
        let (pf, rem) := mb.intraPred.getD b (1, 0)
        let m := syntaxToActualIntraMode mpm pf rem
        modes := modes.set! (gy * gridW4 + gx) m
        let n := LeanAV.H264IntraTransform.mbSubblockNeighbors 4 canvasY nbrs xO yO trAv
        let pred16 := LeanAV.H264IntraTransform.pred4x4 m n
        let i8 := b / 4
        let scan16 :=
          if (mb.cbp &&& (1 <<< i8)) != 0 then mb.lumaAcOr4x4.getD b (Array.replicate 16 0)
          else Array.replicate 16 0
        let nz := (mb.cbp &&& (1 <<< i8)) != 0 && anyNonZeroInt scan16 16
        hasCoeff := hasCoeff.set! (ry * 4 + rx) nz
        let rec16 :=
          if nz then
            LeanAV.H264IntraTransform.reconstructSubblock4Idct pred16
              (LeanAV.H264Entropy.zigzagToRaster4x4 scan16) qp
          else pred16
        canvasY := LeanAV.H264IntraTransform.writeMbBlock4 canvasY xO yO rec16
    let predU := LeanAV.H264IntraTransform.predChroma mb.chromaPredMode
      nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail
    let predV := LeanAV.H264IntraTransform.predChroma mb.chromaPredMode
      nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail
    let hasCdc := (mb.cbp &&& 0x30) != 0
    let hasCac := (mb.cbp &&& 0x20) != 0
    let uDc4 := if hasCdc then mb.chromaDc.getD 0 (Array.replicate 4 0) else Array.replicate 4 0
    let vDc4 := if hasCdc then mb.chromaDc.getD 1 (Array.replicate 4 0) else Array.replicate 4 0
    let uAc4 := Array.ofFn fun i : Fin 4 =>
      if hasCac then ac15ScanToRaster16 (mb.chromaAc.getD i.val #[]) else Array.replicate 16 0
    let vAc4 := Array.ofFn fun i : Fin 4 =>
      if hasCac then ac15ScanToRaster16 (mb.chromaAc.getD (4 + i.val) #[]) else Array.replicate 16 0
    let recU := LeanAV.H264IntraTransform.reconstructChroma8x8Lossy predU uDc4 uAc4 qpcCb
    let recV := LeanAV.H264IntraTransform.reconstructChroma8x8Lossy predV vDc4 vAc4 qpcCr
    some ({ y := canvasY, u := recU, v := recV }, modes, hasCoeff)

/-! ## Inter Neighbor MV Lookup, Direct Mode & Motion Compensation -/

private def lookupNeighborMv
    (colGrid : Array InprocDecodedBlk4) (blkSliceIds : Array Int)
    (gridW4 gridH4 : Nat) (curSliceId : Int) (listIdx : Nat)
    (gx gy : Int) : LeanAV.H264InterDeblockDpb.NeighborMv :=
  if gx < 0 || gy < 0 || gx.toNat ≥ gridW4 || gy.toNat ≥ gridH4 then
    { avail := false, refIdx := -1, mv := ⟨0, 0⟩ }
  else
    let idx := gy.toNat * gridW4 + gx.toNat
    if blkSliceIds.getD idx (-1) != curSliceId then
      { avail := false, refIdx := -1, mv := ⟨0, 0⟩ }
    else
      let b := colGrid.getD idx {}
      if b.isIntra then
        { avail := true, refIdx := -1, mv := ⟨0, 0⟩ }
      else if listIdx == 0 then
        { avail := true, refIdx := b.refIdxL0, mv := b.mvL0 }
      else
        { avail := true, refIdx := b.refIdxL1, mv := b.mvL1 }

private def partNeighborsABC
    (colGrid : Array InprocDecodedBlk4) (blkSliceIds : Array Int)
    (gridW4 gridH4 : Nat) (curSliceId : Int) (listIdx : Nat)
    (gx0 gy0 pw4 : Nat)
    : LeanAV.H264InterDeblockDpb.NeighborMv ×
      LeanAV.H264InterDeblockDpb.NeighborMv ×
      LeanAV.H264InterDeblockDpb.NeighborMv :=
  let igx := Int.ofNat gx0
  let igy := Int.ofNat gy0
  let nbA := lookupNeighborMv colGrid blkSliceIds gridW4 gridH4 curSliceId listIdx (igx - 1) igy
  let nbB := lookupNeighborMv colGrid blkSliceIds gridW4 gridH4 curSliceId listIdx igx (igy - 1)
  let rx := gx0 % 4
  let ry := gy0 % 4
  let trBlockedInMb : Bool :=
    (rx + pw4 == 4 && (ry == 1 || ry == 2 || ry == 3)) ||
    (rx + pw4 == 2 && (ry == 1 || ry == 3))
  let nbCRaw :=
    if trBlockedInMb then { avail := false, refIdx := -1, mv := ⟨0, 0⟩ }
    else lookupNeighborMv colGrid blkSliceIds gridW4 gridH4 curSliceId listIdx (igx + Int.ofNat pw4) (igy - 1)
  let nbC :=
    if nbCRaw.avail then nbCRaw
    else lookupNeighborMv colGrid blkSliceIds gridW4 gridH4 curSliceId listIdx (igx - 1) (igy - 1)
  (nbA, nbB, nbC)

private def setRectMvInGrid
    (colGrid : Array InprocDecodedBlk4) (gridW4 gx0 gy0 pw4 ph4 : Nat)
    (listIdx : Nat) (refIdx : Int) (mv : LeanAV.H264InterDeblockDpb.MotionVec)
    (refUid? : Option Nat) : Array InprocDecodedBlk4 := Id.run do
  let mut g := colGrid
  for dy in [:ph4] do
    for dx in [:pw4] do
      let idx := (gy0 + dy) * gridW4 + (gx0 + dx)
      let cur := g.getD idx {}
      let upd :=
        if listIdx == 0 then { cur with refIdxL0 := refIdx, mvL0 := mv, refPicUidL0 := refUid? }
        else { cur with refIdxL1 := refIdx, mvL1 := mv, refPicUidL1 := refUid? }
      g := g.set! idx upd
  return g

private def resolveCollocatedMotion
    (l0Pics l1Pics : Array InprocStoredPic)
    (direct8x8Inference : Bool) (gx gy : Nat)
    : Bool × Int × LeanAV.H264InterDeblockDpb.MotionVec × Int × Int :=
  if l1Pics.size == 0 then
    (false, 0, ⟨0, 0⟩, 0, 0)
  else
    let colPic := l1Pics[0]!
    let rx := gx % 4
    let ry := gy % 4
    let cgx :=
      if direct8x8Inference then (gx - rx) + (if rx ≥ 2 then 3 else 0) else gx
    let cgy :=
      if direct8x8Inference then (gy - ry) + (if ry ≥ 2 then 3 else 0) else gy
    let colBlk :=
      if cgx < colPic.gridW4 && cgy < colPic.gridH4 then
        colPic.colGrid.getD (cgy * colPic.gridW4 + cgx) {}
      else {}
    if colBlk.isIntra then
      (false, 0, ⟨0, 0⟩, (l0Pics.getD 0 colPic).poc, colPic.poc)
    else
      let useColL0 := colBlk.refIdxL0 ≥ 0
      let mvCol := if useColL0 then colBlk.mvL0 else colBlk.mvL1
      let refCol := if useColL0 then colBlk.refIdxL0 else colBlk.refIdxL1
      let uidCol? := if useColL0 then colBlk.refPicUidL0 else colBlk.refPicUidL1
      let mappedL0 : Int :=
        match uidCol? with
        | some u =>
          match l0Pics.findIdx? (fun p => p.uid == u) with
          | some i => Int.ofNat i
          | none => 0
        | none => 0
      let colZero : Bool :=
        !colPic.isLongTerm && refCol == 0 && mvCol.x.natAbs ≤ 1 && mvCol.y.natAbs ≤ 1
      let poc0 :=
        if mappedL0 ≥ 0 && mappedL0.toNat < l0Pics.size then (l0Pics.getD mappedL0.toNat colPic).poc
        else colPic.poc
      (colZero, mappedL0, mvCol, poc0, colPic.poc)

private def deriveDirectSubMb8x8
    (colGrid0 : Array InprocDecodedBlk4) (blkSliceIds : Array Int)
    (gridW4 gridH4 : Nat) (curSliceId : Int) (currPoc : Int)
    (directSpatialFlag direct8x8Inference : Bool)
    (l0Pics l1Pics : Array InprocStoredPic)
    (mbGx mbGy subIdx : Nat)
    (spatialBase? : Option (LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv))
    : Array InprocDecodedBlk4 := Id.run do
  let mut g := colGrid0
  let sx0 := (subIdx % 2) * 2
  let sy0 := (subIdx / 2) * 2
  let (nb0A, nb0B, nb0C, nb1A, nb1B, nb1C) :=
    match spatialBase? with
    | some base => base
    | none =>
      let (a0, b0, c0) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 0 mbGx mbGy 4
      let (a1, b1, c1) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 1 mbGx mbGy 4
      (a0, b0, c0, a1, b1, c1)
  for dy in [:2] do
    for dx in [:2] do
      let gx := mbGx + sx0 + dx
      let gy := mbGy + sy0 + dy
      let (colZero, mappedL0, mvCol, poc0, poc1) :=
        resolveCollocatedMotion l0Pics l1Pics direct8x8Inference gx gy
      let dp :=
        if directSpatialFlag then
          LeanAV.H264InterDeblockDpb.bDirectSpatial nb0A nb0B nb0C nb1A nb1B nb1C colZero
        else
          LeanAV.H264InterDeblockDpb.bDirectTemporal mvCol mappedL0 currPoc poc0 poc1
      let r0 := if dp.predFlagL0 then dp.refIdxL0 else -1
      let r1 := if dp.predFlagL1 then dp.refIdxL1 else -1
      let uid0? := if r0 ≥ 0 && r0.toNat < l0Pics.size then some (l0Pics[r0.toNat]!.uid) else none
      let uid1? := if r1 ≥ 0 && r1.toNat < l1Pics.size then some (l1Pics[r1.toNat]!.uid) else none
      let cur := g.getD (gy * gridW4 + gx) {}
      g := g.set! (gy * gridW4 + gx) {
        cur with
        refIdxL0 := r0
        mvL0 := if dp.predFlagL0 then dp.mvL0 else ⟨0, 0⟩
        refPicUidL0 := uid0?
        refIdxL1 := r1
        mvL1 := if dp.predFlagL1 then dp.mvL1 else ⟨0, 0⟩
        refPicUidL1 := uid1?
      }
  return g

private def deriveInterMbMotionGrid
    (mb : LeanAV.H264Entropy.MbSyntax)
    (sliceKind : LeanAV.H264Syntax.H264SliceKind)
    (colGrid0 : Array InprocDecodedBlk4) (blkSliceIds : Array Int)
    (gridW4 gridH4 mbX mbY : Nat) (curSliceId : Int) (currPoc : Int)
    (directSpatialFlag direct8x8Inference : Bool)
    (l0Pics l1Pics : Array InprocStoredPic)
    : Option (Array InprocDecodedBlk4) := Id.run do
  let mbGx := mbX * 4
  let mbGy := mbY * 4
  let mut g := colGrid0
  if mb.isSkip then
    if sliceKind == .P then
      if l0Pics.size == 0 then return none
      let (nbA, nbB, nbC) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 0 mbGx mbGy 4
      let atLeftOrTop := !nbA.avail || !nbB.avail
      let mv := LeanAV.H264InterDeblockDpb.pSkipMv atLeftOrTop nbA nbB nbC
      let uid0? := some (l0Pics[0]!.uid)
      g := setRectMvInGrid g gridW4 mbGx mbGy 4 4 0 0 mv uid0?
      return some g
    else if sliceKind == .B then
      let (a0, b0, c0) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 0 mbGx mbGy 4
      let (a1, b1, c1) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 1 mbGx mbGy 4
      let spBase := some (a0, b0, c0, a1, b1, c1)
      for i8 in [:4] do
        g := deriveDirectSubMb8x8 g blkSliceIds gridW4 gridH4 curSliceId currPoc
               directSpatialFlag direct8x8Inference l0Pics l1Pics mbGx mbGy i8 spBase
      return some g
    else
      return none
  let (info, numLists) :=
    if mb.kind == .pInter then (LeanAV.H264Entropy.pMbInfoTable.getD mb.interIdx {}, 1)
    else if mb.kind == .bInter then (LeanAV.H264Entropy.bMbInfoTable.getD mb.interIdx {}, 2)
    else ({}, 0)
  if numLists == 0 then return none
  if info.shape == .direct then
    let (a0, b0, c0) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 0 mbGx mbGy 4
    let (a1, b1, c1) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 1 mbGx mbGy 4
    let spBase := some (a0, b0, c0, a1, b1, c1)
    for i8 in [:4] do
      g := deriveDirectSubMb8x8 g blkSliceIds gridW4 gridH4 curSliceId currPoc
             directSpatialFlag direct8x8Inference l0Pics l1Pics mbGx mbGy i8 spBase
    return some g
  let refsSrc := #[mb.refL0, mb.refL1]
  let mvdsSrc := #[mb.mvdL0, mb.mvdL1]
  let useLists := #[info.useL0, info.useL1]
  let picsLists := #[l0Pics, l1Pics]
  if info.shape == .p8x8 then
    let (a0, b0, c0) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 0 mbGx mbGy 4
    let (a1, b1, c1) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId 1 mbGx mbGy 4
    let spBase := some (a0, b0, c0, a1, b1, c1)
    let mut rc0 := 0
    let mut rc1 := 0
    let mut mc0 := 0
    let mut mc1 := 0
    for i8 in [:4] do
      let st := mb.subMbTypes.getD i8 0
      let sub :=
        if mb.kind == .pInter then LeanAV.H264Entropy.pSubInfoTable.getD st {}
        else LeanAV.H264Entropy.bSubInfoTable.getD st {}
      if sub.shape == .direct then
        g := deriveDirectSubMb8x8 g blkSliceIds gridW4 gridH4 curSliceId currPoc
               directSpatialFlag direct8x8Inference l0Pics l1Pics mbGx mbGy i8 spBase
      else
        for lst in [:numLists] do
          let sUse := if lst == 0 then sub.useL0 else sub.useL1
          if sUse then
            let rc := if lst == 0 then rc0 else rc1
            let rvNat : Nat :=
              if mb.kind == .pInter && mb.interIdx == 4 then 0
              else (refsSrc.getD lst #[]).getD rc 0
            if !(mb.kind == .pInter && mb.interIdx == 4) then
              if lst == 0 then rc0 := rc0 + 1 else rc1 := rc1 + 1
            let refPics := picsLists.getD lst #[]
            if rvNat ≥ refPics.size then return none
            let rv := Int.ofNat rvNat
            let uid? := some (refPics[rvNat]!.uid)
            for j in [:sub.subCnt] do
              let (off, bw, bh) := LeanAV.H264Entropy.subPartGeom sub.shape j
              let blkIdx := 4 * i8 + off
              let (xO, yO) := LeanAV.H264IntraTransform.zScan4BlkCoord blkIdx
              let gx0 := mbGx + xO / 4
              let gy0 := mbGy + yO / 4
              let (nbA, nbB, nbC) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId lst gx0 gy0 bw
              let mvp := LeanAV.H264InterDeblockDpb.mvpMedian rv nbA nbB nbC .p8x8 j
              let mc := if lst == 0 then mc0 else mc1
              let (dx, dy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
              if lst == 0 then mc0 := mc0 + 1 else mc1 := mc1 + 1
              let mv : LeanAV.H264InterDeblockDpb.MotionVec := ⟨mvp.x + dx, mvp.y + dy⟩
              g := setRectMvInGrid g gridW4 gx0 gy0 bw bh lst rv mv uid?
    return some g
  else
    let dpbShape : LeanAV.H264InterDeblockDpb.H264PartShape :=
      match info.shape with
      | .p16x16 => .p16x16
      | .p16x8  => .p16x8
      | .p8x16  => .p8x16
      | _       => .p16x16
    let nPart := info.useL0.size
    for lst in [:numLists] do
      let mut rc := 0
      let mut mc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (gx0, gy0, bw, bh) :=
            if info.shape == .p16x16 then (mbGx, mbGy, 4, 4)
            else if info.shape == .p16x8 then (mbGx, mbGy + 2 * pi, 4, 2)
            else (mbGx + 2 * pi, mbGy, 2, 4)
          let rvNat := (refsSrc.getD lst #[]).getD rc 0
          let refPics := picsLists.getD lst #[]
          if rvNat ≥ refPics.size then return none
          let rv := Int.ofNat rvNat
          let uid? := some (refPics[rvNat]!.uid)
          let (nbA, nbB, nbC) := partNeighborsABC g blkSliceIds gridW4 gridH4 curSliceId lst gx0 gy0 bw
          let mvp := LeanAV.H264InterDeblockDpb.mvpMedian rv nbA nbB nbC dpbShape pi
          let (dx, dy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
          rc := rc + 1
          mc := mc + 1
          let mv : LeanAV.H264InterDeblockDpb.MotionVec := ⟨mvp.x + dx, mvp.y + dy⟩
          g := setRectMvInGrid g gridW4 gx0 gy0 bw bh lst rv mv uid?
    return some g

def clipWeightedU8 (v : Int) : UInt8 :=
  if v ≤ 0 then 0 else if v ≥ 255 then 255 else v.toNat.toUInt8

def evalExplicitUniWeight (s : UInt8) (logWD : Nat) (w o : Int) : UInt8 :=
  let v :=
    if logWD ≥ 1 then
      ((s.toNat : Int) * w + (2 ^ (logWD - 1) : Int)) / (2 ^ logWD : Int) + o
    else
      (s.toNat : Int) * w + o
  clipWeightedU8 v

def evalExplicitBiWeight (s0 s1 : UInt8) (logWD : Nat) (w0 o0 w1 o1 : Int) : UInt8 :=
  let sh := logWD + 1
  let v :=
    (((s0.toNat : Int) * w0 + (s1.toNat : Int) * w1 + (2 ^ logWD : Int)) / (2 ^ sh : Int)) +
    ((o0 + o1 + 1) / (2 : Int))
  clipWeightedU8 v

theorem clipWeightedU8_bounds (v : Int) : (clipWeightedU8 v).toNat ≤ 255 := by
  unfold clipWeightedU8
  split
  · decide
  · split
    · decide
    · have h0 : 0 < v := by omega
      have h255 : v.toNat < 255 := by omega
      have hMod : v.toNat % 256 = v.toNat := Nat.mod_eq_of_lt (by omega)
      change v.toNat % 256 ≤ 255
      omega

theorem clipWeightedU8_id (s : UInt8) : clipWeightedU8 (s.toNat : Int) = s := by
  have hs : s.toNat < 256 := s.toBitVec.isLt
  unfold clipWeightedU8
  by_cases h0 : (s.toNat : Int) ≤ 0
  · simp only [h0, ↓reduceIte]
    have hEq0 : s.toNat = 0 := by omega
    apply UInt8.toNat_inj.mp
    simpa using hEq0.symm
  · simp only [h0, ↓reduceIte]
    by_cases h255 : (s.toNat : Int) ≥ 255
    · simp only [h255, ↓reduceIte]
      have hEq255 : s.toNat = 255 := by omega
      apply UInt8.toNat_inj.mp
      simpa using hEq255.symm
    · simp only [h255, ↓reduceIte, Int.toNat_natCast]
      exact UInt8.ofNat_toNat

theorem evalExplicitUniWeight_bounds (s : UInt8) (logWD : Nat) (w o : Int) :
    (evalExplicitUniWeight s logWD w o).toNat ≤ 255 := by
  unfold evalExplicitUniWeight
  exact clipWeightedU8_bounds _

theorem evalExplicitBiWeight_bounds (s0 s1 : UInt8) (logWD : Nat) (w0 o0 w1 o1 : Int) :
    (evalExplicitBiWeight s0 s1 logWD w0 o0 w1 o1).toNat ≤ 255 := by
  unfold evalExplicitBiWeight
  exact clipWeightedU8_bounds _

private theorem two_pow_int_pos (n : Nat) : (0 : Int) < (2 ^ n : Int) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    omega

theorem evalExplicitUniWeight_default_identity (s : UInt8) (logWD : Nat) :
    evalExplicitUniWeight s logWD (2 ^ logWD : Int) 0 = s := by
  dsimp [evalExplicitUniWeight]
  cases logWD with
  | zero =>
    have hGe : ¬ (0 ≥ 1) := by decide
    simp only [hGe, ↓reduceIte]
    have hSimp : (s.toNat : Int) * (2 ^ 0 : Int) + 0 = (s.toNat : Int) := by
      change (s.toNat : Int) * 1 + 0 = (s.toNat : Int)
      omega
    rw [hSimp]
    exact clipWeightedU8_id s
  | succ k =>
    have hGe : k + 1 ≥ 1 := by omega
    simp only [hGe, ↓reduceIte, Nat.add_sub_cancel]
    have hPos : (0 : Int) < (2 ^ k : Int) := two_pow_int_pos k
    have hPow : (2 ^ (k + 1) : Int) = (2 ^ k : Int) * 2 := Int.pow_succ 2 k
    have hSub : (2 ^ k : Int) < (2 ^ (k + 1) : Int) := by omega
    have hRem : ((2 ^ k : Int)) / (2 ^ (k + 1) : Int) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) hSub
    have hDenNe : (2 ^ (k + 1) : Int) ≠ 0 := by omega
    have hDiv : ((s.toNat : Int) * (2 ^ (k + 1) : Int) + (2 ^ k : Int)) / (2 ^ (k + 1) : Int) + 0 = (s.toNat : Int) := by
      rw [Int.mul_comm (s.toNat : Int) (2 ^ (k + 1) : Int)]
      rw [Int.mul_add_ediv_left _ _ hDenNe, hRem]
      omega
    rw [hDiv]
    exact clipWeightedU8_id s

theorem evalExplicitBiWeight_default_eq_biPredSample (s0 s1 : UInt8) (logWD : Nat) :
    evalExplicitBiWeight s0 s1 logWD (2 ^ logWD : Int) 0 (2 ^ logWD : Int) 0 =
    LeanAV.H264InterDeblockDpb.biPredSample s0 s1 := by
  dsimp [evalExplicitBiWeight, LeanAV.H264InterDeblockDpb.biPredSample, LeanAV.Video.mcBiPredPixel]
  have hdPos : (0 : Int) < (2 ^ logWD : Int) := two_pow_int_pos logWD
  have hSh : (2 ^ (logWD + 1) : Int) = (2 ^ logWD : Int) * 2 := Int.pow_succ 2 logWD
  have hAvg :
      (((s0.toNat : Int) * (2 ^ logWD : Int) +
        (s1.toNat : Int) * (2 ^ logWD : Int) +
        (2 ^ logWD : Int)) / (2 ^ (logWD + 1) : Int)) + 0 =
      (((s0.toNat + s1.toNat + 1) / 2 : Nat) : Int) := by
    rw [hSh]
    have hMul : (s0.toNat : Int) * (2 ^ logWD : Int) + (s1.toNat : Int) * (2 ^ logWD : Int) + (2 ^ logWD : Int) =
        (2 ^ logWD : Int) * ((s0.toNat : Int) + (s1.toNat : Int) + 1) := by
      rw [Int.mul_add, Int.mul_add, Int.mul_one,
          Int.mul_comm (2 ^ logWD : Int) (s0.toNat : Int),
          Int.mul_comm (2 ^ logWD : Int) (s1.toNat : Int)]
    rw [hMul, Int.mul_ediv_mul_of_pos _ _ hdPos]
    omega
  rw [hAvg]
  have hs0 : s0.toNat < 256 := s0.toBitVec.isLt
  have hs1 : s1.toNat < 256 := s1.toBitVec.isLt
  have hAvgLt : (s0.toNat + s1.toNat + 1) / 2 < 256 := by omega
  let avgU8 : UInt8 := ((s0.toNat + s1.toNat + 1) / 2).toUInt8
  have hToNat : avgU8.toNat = (s0.toNat + s1.toNat + 1) / 2 := Nat.mod_eq_of_lt hAvgLt
  rw [← hToNat, clipWeightedU8_id avgU8]
  apply UInt8.toNat_inj.mp
  rw [hToNat]
  have hU16 : ((s0.toUInt16 + s1.toUInt16 + 1) >>> 1).toUInt8.toNat = (s0.toNat + s1.toNat + 1) / 2 := by
    have hSumLt : s0.toNat + s1.toNat + 1 < 65536 := by omega
    have h1 : (s0.toUInt16 + s1.toUInt16 + 1).toNat = s0.toNat + s1.toNat + 1 := by
      simp [UInt16.toNat_add, UInt8.toNat_toUInt16]
      omega
    have h2 : ((s0.toUInt16 + s1.toUInt16 + 1) >>> 1).toNat = (s0.toNat + s1.toNat + 1) / 2 := by
      rw [UInt16.toNat_shiftRight, h1]
      exact Nat.shiftRight_eq_div_pow _ 1
    simp [UInt16.toNat_toUInt8, h2, Nat.mod_eq_of_lt hAvgLt]
  exact hU16.symm

private def lookupLumaWeightOffset
    (arr : Array LeanAV.H264Syntax.PredWeightEntry) (refIdx : Nat) (logWD : Nat) : Int × Int :=
  let defW : Int := (2 ^ logWD : Int)
  match arr[refIdx]? with
  | some e => if e.lumaWeightFlag then (e.lumaWeight.toInt, e.lumaOffset.toInt) else (defW, 0)
  | none => (defW, 0)

private def lookupChromaWeightOffset
    (arr : Array LeanAV.H264Syntax.PredWeightEntry) (refIdx : Nat) (logWD : Nat) : (Int × Int) × (Int × Int) :=
  let defW : Int := (2 ^ logWD : Int)
  match arr[refIdx]? with
  | some e =>
    if e.chromaWeightFlag then
      ((e.cbWeight.toInt, e.cbOffset.toInt), (e.crWeight.toInt, e.crOffset.toInt))
    else
      ((defW, 0), (defW, 0))
  | none => ((defW, 0), (defW, 0))

private def reconstructDecodedInterMb
    (mb : LeanAV.H264Entropy.MbSyntax)
    (colGrid : Array InprocDecodedBlk4)
    (gridW4 mbX mbY : Nat)
    (l0Pics l1Pics : Array InprocStoredPic)
    (currPoc : Int) (weightedBipredIdc : UInt8)
    (hasPredWeightTable : Bool) (pwt : LeanAV.H264Syntax.PredWeightTable)
    (qpY : Nat) (cqpOff secCqpOff : Int)
    : Option (LeanAV.H264IntraTransform.H264Yuv420pMb × Array Bool) := do
  let mbGx := mbX * 4
  let mbGy := mbY * 4
  let mut predY := Array.replicate 256 (0 : UInt8)
  let mut predU := Array.replicate 64 (0 : UInt8)
  let mut predV := Array.replicate 64 (0 : UInt8)
  let mut predOk : Bool := true
  let lLogWD := pwt.lumaLog2WeightDenom.toNat
  let cLogWD := pwt.chromaLog2WeightDenom.toNat
  for ry in [:4] do
    for rx in [:4] do
      let b := colGrid.getD ((mbGy + ry) * gridW4 + (mbGx + rx)) {}
      let use0 := b.refIdxL0 ≥ 0 && b.refIdxL0.toNat < l0Pics.size
      let use1 := b.refIdxL1 ≥ 0 && b.refIdxL1.toNat < l1Pics.size
      if !use0 && !use1 then
        predOk := false
      else do
        let x0L := mbX * 16 + rx * 4
        let y0L := mbY * 16 + ry * 4
        let x0C := mbX * 8 + rx * 2
        let y0C := mbY * 8 + ry * 2
        let useImpBi := !hasPredWeightTable && use0 && use1 && weightedBipredIdc == 2 &&
          !(l0Pics[b.refIdxL0.toNat]!.isLongTerm || l1Pics[b.refIdxL1.toNat]!.isLongTerm)
        for dy in [:4] do
          for dx in [:4] do
            let vL : UInt8 :=
              if use0 && use1 then
                let r0 := b.refIdxL0.toNat
                let r1 := b.refIdxL1.toNat
                let p0Pic := l0Pics[r0]!
                let p1Pic := l1Pics[r1]!
                let s0 := LeanAV.H264InterDeblockDpb.h264LumaQpel p0Pic.yPlane
                  (4 * Int.ofNat (x0L + dx) + b.mvL0.x) (4 * Int.ofNat (y0L + dy) + b.mvL0.y)
                let s1 := LeanAV.H264InterDeblockDpb.h264LumaQpel p1Pic.yPlane
                  (4 * Int.ofNat (x0L + dx) + b.mvL1.x) (4 * Int.ofNat (y0L + dy) + b.mvL1.y)
                if hasPredWeightTable then
                  let (w0, o0) := lookupLumaWeightOffset pwt.l0Weights r0 lLogWD
                  let (w1, o1) := lookupLumaWeightOffset pwt.l1Weights r1 lLogWD
                  evalExplicitBiWeight s0 s1 lLogWD w0 o0 w1 o1
                else if useImpBi then
                  LeanAV.H264InterDeblockDpb.implicitWeightedBiPredPixel s0 s1 currPoc p0Pic.poc p1Pic.poc
                else
                  LeanAV.H264InterDeblockDpb.biPredSample s0 s1
              else if use0 then
                let r0 := b.refIdxL0.toNat
                let p0Pic := l0Pics[r0]!
                let s0 := LeanAV.H264InterDeblockDpb.h264LumaQpel p0Pic.yPlane
                  (4 * Int.ofNat (x0L + dx) + b.mvL0.x) (4 * Int.ofNat (y0L + dy) + b.mvL0.y)
                if hasPredWeightTable then
                  let (w0, o0) := lookupLumaWeightOffset pwt.l0Weights r0 lLogWD
                  evalExplicitUniWeight s0 lLogWD w0 o0
                else s0
              else
                let r1 := b.refIdxL1.toNat
                let p1Pic := l1Pics[r1]!
                let s1 := LeanAV.H264InterDeblockDpb.h264LumaQpel p1Pic.yPlane
                  (4 * Int.ofNat (x0L + dx) + b.mvL1.x) (4 * Int.ofNat (y0L + dy) + b.mvL1.y)
                if hasPredWeightTable then
                  let (w1, o1) := lookupLumaWeightOffset pwt.l1Weights r1 lLogWD
                  evalExplicitUniWeight s1 lLogWD w1 o1
                else s1
            predY := predY.set! ((ry * 4 + dy) * 16 + (rx * 4 + dx)) vL
        for dy in [:2] do
          for dx in [:2] do
            let cx := Int.ofNat (x0C + dx)
            let cy := Int.ofNat (y0C + dy)
            let (vU, vV) : UInt8 × UInt8 :=
              if use0 && use1 then
                let r0 := b.refIdxL0.toNat
                let r1 := b.refIdxL1.toNat
                let p0Pic := l0Pics[r0]!
                let p1Pic := l1Pics[r1]!
                let u0 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p0Pic.uPlane cx cy b.mvL0.x b.mvL0.y
                let u1 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p1Pic.uPlane cx cy b.mvL1.x b.mvL1.y
                let v0 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p0Pic.vPlane cx cy b.mvL0.x b.mvL0.y
                let v1 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p1Pic.vPlane cx cy b.mvL1.x b.mvL1.y
                if hasPredWeightTable then
                  let ((wu0, ou0), (wv0, ov0)) := lookupChromaWeightOffset pwt.l0Weights r0 cLogWD
                  let ((wu1, ou1), (wv1, ov1)) := lookupChromaWeightOffset pwt.l1Weights r1 cLogWD
                  (evalExplicitBiWeight u0 u1 cLogWD wu0 ou0 wu1 ou1,
                   evalExplicitBiWeight v0 v1 cLogWD wv0 ov0 wv1 ov1)
                else if useImpBi then
                  (LeanAV.H264InterDeblockDpb.implicitWeightedBiPredPixel u0 u1 currPoc p0Pic.poc p1Pic.poc,
                   LeanAV.H264InterDeblockDpb.implicitWeightedBiPredPixel v0 v1 currPoc p0Pic.poc p1Pic.poc)
                else
                  (LeanAV.H264InterDeblockDpb.biPredSample u0 u1,
                   LeanAV.H264InterDeblockDpb.biPredSample v0 v1)
              else if use0 then
                let r0 := b.refIdxL0.toNat
                let p0Pic := l0Pics[r0]!
                let u0 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p0Pic.uPlane cx cy b.mvL0.x b.mvL0.y
                let v0 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p0Pic.vPlane cx cy b.mvL0.x b.mvL0.y
                if hasPredWeightTable then
                  let ((wu0, ou0), (wv0, ov0)) := lookupChromaWeightOffset pwt.l0Weights r0 cLogWD
                  (evalExplicitUniWeight u0 cLogWD wu0 ou0, evalExplicitUniWeight v0 cLogWD wv0 ov0)
                else (u0, v0)
              else
                let r1 := b.refIdxL1.toNat
                let p1Pic := l1Pics[r1]!
                let u1 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p1Pic.uPlane cx cy b.mvL1.x b.mvL1.y
                let v1 := LeanAV.H264InterDeblockDpb.h264ChromaOpel420 p1Pic.vPlane cx cy b.mvL1.x b.mvL1.y
                if hasPredWeightTable then
                  let ((wu1, ou1), (wv1, ov1)) := lookupChromaWeightOffset pwt.l1Weights r1 cLogWD
                  (evalExplicitUniWeight u1 cLogWD wu1 ou1, evalExplicitUniWeight v1 cLogWD wv1 ov1)
                else (u1, v1)
            let cOff := (ry * 2 + dy) * 8 + (rx * 2 + dx)
            predU := predU.set! cOff vU
            predV := predV.set! cOff vV
  guard predOk
  if mb.isSkip || mb.cbp == 0 then
    some ({ y := predY, u := predU, v := predV }, Array.replicate 16 false)
  else
    let qp := LeanAV.H264IntraTransform.clampQp qpY
    let qpcCb := LeanAV.H264IntraTransform.qpcFromQpy qp cqpOff
    let qpcCr := LeanAV.H264IntraTransform.qpcFromQpy qp secCqpOff
    let mut recY := predY
    let mut hasCoeff := Array.replicate 16 false
    if mb.transform8x8 != 0 then
      for i8 in [:4] do
        let xO := (i8 % 2) * 8
        let yO := (i8 / 2) * 8
        let scan64 :=
          if (mb.cbp &&& (1 <<< i8)) != 0 then mb.luma8x8.getD i8 (Array.replicate 64 0)
          else Array.replicate 64 0
        let nz := (mb.cbp &&& (1 <<< i8)) != 0 && anyNonZeroInt scan64 64
        for dy in [:2] do
          for dx in [:2] do
            hasCoeff := hasCoeff.set! ((yO / 4 + dy) * 4 + (xO / 4 + dx)) nz
        if nz then
          let p64 := LeanAV.H264IntraTransform.extractMbBlock8 recY xO yO
          let r64 := LeanAV.H264IntraTransform.reconstructSubblock8Idct p64
            (LeanAV.H264Entropy.zigzagToRaster8x8 scan64) qp
          recY := LeanAV.H264IntraTransform.writeMbBlock8 recY xO yO r64
    else
      for b in [:16] do
        let (xO, yO) := LeanAV.H264IntraTransform.zScan4BlkCoord b
        let i8 := b / 4
        let scan16 :=
          if (mb.cbp &&& (1 <<< i8)) != 0 then mb.lumaAcOr4x4.getD b (Array.replicate 16 0)
          else Array.replicate 16 0
        let nz := (mb.cbp &&& (1 <<< i8)) != 0 && anyNonZeroInt scan16 16
        hasCoeff := hasCoeff.set! ((yO / 4) * 4 + (xO / 4)) nz
        if nz then
          let p16 := LeanAV.H264IntraTransform.extractMbBlock4 recY xO yO
          let r16 := LeanAV.H264IntraTransform.reconstructSubblock4Idct p16
            (LeanAV.H264Entropy.zigzagToRaster4x4 scan16) qp
          recY := LeanAV.H264IntraTransform.writeMbBlock4 recY xO yO r16
    let hasCdc := (mb.cbp &&& 0x30) != 0
    let hasCac := (mb.cbp &&& 0x20) != 0
    let uDc4 := if hasCdc then mb.chromaDc.getD 0 (Array.replicate 4 0) else Array.replicate 4 0
    let vDc4 := if hasCdc then mb.chromaDc.getD 1 (Array.replicate 4 0) else Array.replicate 4 0
    let uAc4 := Array.ofFn fun i : Fin 4 =>
      if hasCac then ac15ScanToRaster16 (mb.chromaAc.getD i.val #[]) else Array.replicate 16 0
    let vAc4 := Array.ofFn fun i : Fin 4 =>
      if hasCac then ac15ScanToRaster16 (mb.chromaAc.getD (4 + i.val) #[]) else Array.replicate 16 0
    let recU :=
      if hasCdc || hasCac then LeanAV.H264IntraTransform.reconstructChroma8x8Lossy predU uDc4 uAc4 qpcCb
      else predU
    let recV :=
      if hasCdc || hasCac then LeanAV.H264IntraTransform.reconstructChroma8x8Lossy predV vDc4 vAc4 qpcCr
      else predV
    some ({ y := recY, u := recU, v := recV }, hasCoeff)

/-! ## Normative Macroblock Deblocking Filter (Luma + Chroma 4:2:0) -/

private def blkRefMvDiffGe4 (pBlk qBlk : InprocDecodedBlk4) : Bool :=
  let u0P := pBlk.refPicUidL0
  let u1P := pBlk.refPicUidL1
  let u0Q := qBlk.refPicUidL0
  let u1Q := qBlk.refPicUidL1
  let mvDiff (a b : LeanAV.H264InterDeblockDpb.MotionVec) : Bool :=
    (a.x - b.x).natAbs ≥ 4 || (a.y - b.y).natAbs ≥ 4
  if u0P == u0Q && u1P == u1Q then
    if u0P.isSome && u0P == u1P then
      (mvDiff pBlk.mvL0 qBlk.mvL0 || mvDiff pBlk.mvL1 qBlk.mvL1) &&
      (mvDiff pBlk.mvL0 qBlk.mvL1 || mvDiff pBlk.mvL1 qBlk.mvL0)
    else
      (u0P.isSome && mvDiff pBlk.mvL0 qBlk.mvL0) ||
      (u1P.isSome && mvDiff pBlk.mvL1 qBlk.mvL1)
  else if u0P == u1Q && u1P == u0Q then
    (u0P.isSome && mvDiff pBlk.mvL0 qBlk.mvL1) ||
    (u1P.isSome && mvDiff pBlk.mvL1 qBlk.mvL0)
  else
    true

private def computeBlkEdgeBs (isMbEdge : Bool) (pBlk qBlk : InprocDecodedBlk4) : Nat :=
  LeanAV.H264InterDeblockDpb.bSFromFlags
    isMbEdge pBlk.isIntra qBlk.isIntra pBlk.hasCoeff qBlk.hasCoeff
    (blkRefMvDiffGe4 pBlk qBlk)

private def deblockChromaVertEdge2
    (p : Plane2D) (edgeXC yStartC count bS : Nat) (qPavC aOff bOff : Int) : Plane2D := Id.run do
  if edgeXC < 2 || edgeXC + 2 > p.width then return p
  let mut dst := p
  for i in [:count] do
    let y := yStartC + i
    if y < dst.height then
      let p1 := dst.getPixel y (edgeXC - 2)
      let p0 := dst.getPixel y (edgeXC - 1)
      let q0 := dst.getPixel y edgeXC
      let q1 := dst.getPixel y (edgeXC + 1)
      let (np0, nq0) := LeanAV.H264InterDeblockDpb.filterChromaSamples4 p1 p0 q0 q1 bS qPavC aOff bOff
      dst := dst.setPixel y (edgeXC - 1) np0
      dst := dst.setPixel y edgeXC nq0
  return dst

private def deblockChromaHorizEdge2
    (p : Plane2D) (xStartC edgeYC count bS : Nat) (qPavC aOff bOff : Int) : Plane2D := Id.run do
  if edgeYC < 2 || edgeYC + 2 > p.height then return p
  let mut dst := p
  for i in [:count] do
    let x := xStartC + i
    if x < dst.width then
      let p1 := dst.getPixel (edgeYC - 2) x
      let p0 := dst.getPixel (edgeYC - 1) x
      let q0 := dst.getPixel edgeYC x
      let q1 := dst.getPixel (edgeYC + 1) x
      let (np0, nq0) := LeanAV.H264InterDeblockDpb.filterChromaSamples4 p1 p0 q0 q1 bS qPavC aOff bOff
      dst := dst.setPixel (edgeYC - 1) x np0
      dst := dst.setPixel edgeYC x nq0
  return dst

structure InprocMbDeblockMeta where
  sliceId      : Int := -1
  qpY          : Nat := 26
  is8x8        : Bool := false
  disableIdc   : Nat := 1
  alphaOffDiv2 : Int := 0
  betaOffDiv2  : Int := 0
  cqpOff       : Int := 0
  secCqpOff    : Int := 0
  deriving Repr, DecidableEq, Inhabited

private def deblockDecodedPicture
    (pY0 pU0 pV0 : Plane2D)
    (colGrid : Array InprocDecodedBlk4)
    (mbMeta : Array InprocMbDeblockMeta)
    (mbsW mbsH : Nat) : Plane2D × Plane2D × Plane2D := Id.run do
  let gridW4 := mbsW * 4
  let mut pY := pY0
  let mut pU := pU0
  let mut pV := pV0
  for mbY in [:mbsH] do
    for mbX in [:mbsW] do
      let curIdx := mbY * mbsW + mbX
      let mQ := mbMeta.getD curIdx {}
      if mQ.sliceId ≥ 0 && mQ.disableIdc != 1 && mQ.disableIdc < 3 then
        let aOff := mQ.alphaOffDiv2
        let bOff := mQ.betaOffDiv2
        for kx in ([0, 4, 8, 12] : List Nat) do
          let edgeX := mbX * 16 + kx
          let isMb := kx == 0
          let mP := if isMb && mbX > 0 then mbMeta.getD (mbY * mbsW + (mbX - 1)) mQ else mQ
          let isSlice := isMb && (mbX == 0 || mP.sliceId != mQ.sliceId)
          if edgeX > 0 && !(mQ.disableIdc == 2 && isSlice) &&
             !(LeanAV.H264InterDeblockDpb.skipInternalEdge8x8 mQ.is8x8 kx) then
            let qPavL : Int := Int.ofNat ((mP.qpY + mQ.qpY + 1) / 2)
            let qpCbP := LeanAV.H264IntraTransform.qpcFromQpy mP.qpY mP.cqpOff
            let qpCbQ := LeanAV.H264IntraTransform.qpcFromQpy mQ.qpY mQ.cqpOff
            let qpCrP := LeanAV.H264IntraTransform.qpcFromQpy mP.qpY mP.secCqpOff
            let qpCrQ := LeanAV.H264IntraTransform.qpcFromQpy mQ.qpY mQ.secCqpOff
            let qPavCb : Int := Int.ofNat ((qpCbP + qpCbQ + 1) / 2)
            let qPavCr : Int := Int.ofNat ((qpCrP + qpCrQ + 1) / 2)
            let gxQ := mbX * 4 + kx / 4
            for blkRow in [:4] do
              let gy := mbY * 4 + blkRow
              let pBlk := colGrid.getD (gy * gridW4 + (gxQ - 1)) {}
              let qBlk := colGrid.getD (gy * gridW4 + gxQ) {}
              let bS := computeBlkEdgeBs isMb pBlk qBlk
              if bS > 0 then
                pY := LeanAV.H264InterDeblockDpb.deblockVertEdge4
                        pY edgeX (mbY * 16 + blkRow * 4) 4 bS qPavL aOff bOff
                if kx == 0 || kx == 8 then
                  let edgeXC := mbX * 8 + kx / 2
                  pU := deblockChromaVertEdge2 pU edgeXC (mbY * 8 + blkRow * 2) 2 bS qPavCb aOff bOff
                  pV := deblockChromaVertEdge2 pV edgeXC (mbY * 8 + blkRow * 2) 2 bS qPavCr aOff bOff
        for ky in ([0, 4, 8, 12] : List Nat) do
          let edgeY := mbY * 16 + ky
          let isMb := ky == 0
          let mP := if isMb && mbY > 0 then mbMeta.getD ((mbY - 1) * mbsW + mbX) mQ else mQ
          let isSlice := isMb && (mbY == 0 || mP.sliceId != mQ.sliceId)
          if edgeY > 0 && !(mQ.disableIdc == 2 && isSlice) &&
             !(LeanAV.H264InterDeblockDpb.skipInternalEdge8x8 mQ.is8x8 ky) then
            let qPavL : Int := Int.ofNat ((mP.qpY + mQ.qpY + 1) / 2)
            let qpCbP := LeanAV.H264IntraTransform.qpcFromQpy mP.qpY mP.cqpOff
            let qpCbQ := LeanAV.H264IntraTransform.qpcFromQpy mQ.qpY mQ.cqpOff
            let qpCrP := LeanAV.H264IntraTransform.qpcFromQpy mP.qpY mP.secCqpOff
            let qpCrQ := LeanAV.H264IntraTransform.qpcFromQpy mQ.qpY mQ.secCqpOff
            let qPavCb : Int := Int.ofNat ((qpCbP + qpCbQ + 1) / 2)
            let qPavCr : Int := Int.ofNat ((qpCrP + qpCrQ + 1) / 2)
            let gyQ := mbY * 4 + ky / 4
            for blkCol in [:4] do
              let gx := mbX * 4 + blkCol
              let pBlk := colGrid.getD ((gyQ - 1) * gridW4 + gx) {}
              let qBlk := colGrid.getD (gyQ * gridW4 + gx) {}
              let bS := computeBlkEdgeBs isMb pBlk qBlk
              if bS > 0 then
                pY := LeanAV.H264InterDeblockDpb.deblockHorizEdge4
                        pY (mbX * 16 + blkCol * 4) edgeY 4 bS qPavL aOff bOff
                if ky == 0 || ky == 8 then
                  let edgeYC := mbY * 8 + ky / 2
                  pU := deblockChromaHorizEdge2 pU (mbX * 8 + blkCol * 2) edgeYC 2 bS qPavCb aOff bOff
                  pV := deblockChromaHorizEdge2 pV (mbX * 8 + blkCol * 2) edgeYC 2 bS qPavCr aOff bOff
  return (pY, pU, pV)

/-! ## POC, Reference List Modification, MMCO & Access-Unit Picture Decoder -/

private def syntaxModOpsToDpb
    (ops : Array LeanAV.H264Syntax.RefPicListModOp)
    : List LeanAV.H264InterDeblockDpb.RefListModOp :=
  (ops.toList.map fun op =>
    match op.modificationOfPicNumsIdc.toNat with
    | 0 => LeanAV.H264InterDeblockDpb.RefListModOp.subPicNum op.param.toNat
    | 1 => LeanAV.H264InterDeblockDpb.RefListModOp.addPicNum op.param.toNat
    | 2 => LeanAV.H264InterDeblockDpb.RefListModOp.longTermPic op.param.toNat
    | _ => LeanAV.H264InterDeblockDpb.RefListModOp.endLoop) ++
  [LeanAV.H264InterDeblockDpb.RefListModOp.endLoop]

private def syntaxMmcoOpsToDpb
    (ops : Array LeanAV.H264Syntax.MmcoOp)
    : Option (List LeanAV.H264InterDeblockDpb.MmcoOp) := do
  let mut out : List LeanAV.H264InterDeblockDpb.MmcoOp := []
  for op in ops do
    match op.opcode.toNat with
    | 1 => out := out ++ [.markShortUnused op.arg0.toNat]
    | 2 => out := out ++ [.markLongUnused op.arg0.toNat]
    | 3 => out := out ++ [.assignLongTermIdx op.arg0.toNat op.arg1.toNat]
    | 4 => out := out ++ [.setMaxLongTermIdxPlus1 op.arg0.toNat]
    | 5 => out := out ++ [.markAllUnused]
    | 6 => out := out ++ [.markCurrLongTerm op.arg0.toNat]
    | _ => none
  some out

private def computePicturePoc
    (sps : LeanAV.H264Syntax.H264SpsFull)
    (sh : LeanAV.H264Syntax.H264SliceHeaderFull)
    (ps : InprocPocState) : Int × InprocPocState :=
  let isIdr := sh.nalUnitType == 5
  let isRef := sh.nalRefIdc != 0
  let hasMmco5 :=
    isRef && !isIdr && sh.adaptiveRefPicMarkingModeFlag &&
    sh.mmcoOps.any (fun op => op.opcode == 5)
  let log2MaxFn := sps.log2MaxFrameNumMinus4.toNat + 4
  let fn := sh.frameNum.toNat
  if sps.picOrderCntType == 0 then
    let log2MaxLsb := sps.log2MaxPicOrderCntLsbMinus4.toNat + 4
    let lsb := sh.picOrderCntLsb.toNat
    let (poc, msb, _) :=
      LeanAV.H264InterDeblockDpb.derivePocType0
        isIdr ps.prevHasMmco5 false false false
        lsb log2MaxLsb sh.deltaPicOrderCntBottom.toInt
        ps.prevPocMsb ps.prevPocLsb
    let nextPs : InprocPocState :=
      if isRef then
        { prevPocMsb := if hasMmco5 then 0 else msb
          prevPocLsb := if hasMmco5 then 0 else Int.ofNat lsb
          prevFrameNum := if hasMmco5 then 0 else fn
          prevFrameNumOffset := 0
          prevHasMmco5 := hasMmco5 }
      else
        { ps with prevFrameNum := fn, prevHasMmco5 := false }
    (poc, nextPs)
  else if sps.picOrderCntType == 1 then
    let offArr := sps.offsetForRefFrame.map (fun v => v.toInt)
    let (poc, fnOff) :=
      LeanAV.H264InterDeblockDpb.derivePocType1
        isIdr isRef ps.prevHasMmco5 false false
        fn log2MaxFn ps.prevFrameNumOffset ps.prevFrameNum
        sps.offsetForNonRefPic.toInt sps.offsetForTopToBottomField.toInt
        offArr sh.deltaPicOrderCnt0.toInt sh.deltaPicOrderCnt1.toInt
    let nextPs : InprocPocState :=
      { ps with
        prevFrameNum := if hasMmco5 then 0 else fn
        prevFrameNumOffset := if hasMmco5 then 0 else fnOff
        prevHasMmco5 := hasMmco5 }
    (poc, nextPs)
  else
    let (poc, fnOff) :=
      LeanAV.H264InterDeblockDpb.derivePocType2
        isIdr isRef ps.prevHasMmco5 fn log2MaxFn
        ps.prevFrameNumOffset ps.prevFrameNum
    let nextPs : InprocPocState :=
      { ps with
        prevFrameNum := if hasMmco5 then 0 else fn
        prevFrameNumOffset := if hasMmco5 then 0 else fnOff
        prevHasMmco5 := hasMmco5 }
    (poc, nextPs)

private def collectEmittedAndPrune
    (dpbBefore dpbAfter : LeanAV.H264InterDeblockDpb.H264Dpb)
    (storedPics : Array InprocStoredPic)
    (emittedUids0 : Array Nat)
    : Option (Array VideoFrame × Array InprocStoredPic × Array Nat) := do
  let newLogCount := dpbAfter.outputPocLog.length - dpbBefore.outputPocLog.length
  let mut frames : Array VideoFrame := #[]
  let mut emitted := emittedUids0
  if newLogCount > 0 then
    let mut cands : List InprocStoredPic := []
    for sp in storedPics do
      if !emitted.contains sp.uid then
        let stillNeedsOut := dpbAfter.entries.any (fun e => e.uid == sp.uid && e.neededForOut)
        if !stillNeedsOut then
          cands := cands ++ [sp]
    let sortedCands :=
      (cands.toArray.qsort (fun a b =>
        if a.poc != b.poc then a.poc < b.poc else a.uid < b.uid)).toList
    for sp in sortedCands.take newLogCount do
      let vf ← storedPicToVideoFrame sp
      frames := frames.push vf
      emitted := emitted.push sp.uid
  let liveStored := storedPics.filter fun sp =>
    dpbAfter.entries.any (fun e => e.uid == sp.uid &&
      (LeanAV.H264InterDeblockDpb.isUsedForRef e || e.neededForOut))
  some (frames, liveStored, emitted)

private def resolveDpbRefsToStored
    (refEntries : List LeanAV.H264InterDeblockDpb.DpbPicture)
    (storedPics : Array InprocStoredPic) : Option (Array InprocStoredPic) := do
  let mut out : Array InprocStoredPic := Array.mkEmpty refEntries.length
  for e in refEntries do
    let sp ← findStoredPic storedPics e.uid
    let isLt := LeanAV.H264InterDeblockDpb.isLongTermRef e
    out := out.push { sp with poc := e.poc, isLongTerm := isLt }
  some out

private def decodeAccessUnitNalus
    (st0 : InprocDecoderState) (nalus : Array ByteArray) (dstW dstH audioCh : Nat)
    : Option (InprocDecoderState × Array VideoFrame) := do
  let mut st := st0
  let mut vclNals : Array ByteArray := #[]
  for nal in nalus do
    guard (nal.data.size > 0)
    let hdr := nal.data.getD 0 0
    guard ((hdr &&& 0x80) == 0)
    let nalType := (hdr &&& 0x1F).toNat
    if nalType == 7 then
      let stNext ← registerSpsNalu st nal
      st := stNext
    else if nalType == 8 then
      let stNext ← registerPpsNalu st nal
      st := stNext
    else if nalType == 1 || nalType == 5 then
      vclNals := vclNals.push nal
    else
      guard (nalType != 2 && nalType != 3 && nalType != 4 && nalType != 19)
  if vclNals.isEmpty then
    some (st, #[])
  else
    let firstNal := vclNals[0]!
    let rbsp0 := LeanAV.H264Entropy.stripNalEmulationBytes firstNal
    let entSpsArr := st.spsTable.map (fun o => o.map (·.ent))
    let entPpsArr := st.ppsTable.map (fun o => o.map (·.ent))
    let (shEnt0, _) ← LeanAV.H264Entropy.parseSliceHeaderFull rbsp0 entSpsArr entPpsArr
    let ppsPair0 ← st.ppsTable.getD shEnt0.ppsId none
    let spsPair0 ← st.spsTable.getD ppsPair0.syn.spsId.toNat none
    let sps := spsPair0.syn
    let scope := buildScopeForSpsPps sps ppsPair0.syn dstW dstH audioCh LeanAV.Encoder.inprocRingDefaultCap
    if !inprocTranscodeGateSpec.gate scope then
      none
    else
      let shSyn0 ← LeanAV.H264Syntax.parseH264SliceHeaderFull (ByteSlice.ofByteArray firstNal) sps ppsPair0.syn
      if shSyn0.redundantPicCnt != 0 then
        none
      else
        let mbsW := sps.picWidthInMbsMinus1.toNat + 1
        let mbsH := sps.picHeightInMapUnitsMinus1.toNat + 1
        let totalMbs := mbsW * mbsH
        let gridW4 := mbsW * 4
        let gridH4 := mbsH * 4
        let maxFn := 1 <<< (sps.log2MaxFrameNumMinus4.toNat + 4)
        let maxRefs := Nat.max 1 sps.maxNumRefFrames.toNat
        if !st.dpbInit then
          st := {
            st with
            dpb := {
              maxRefFrames := sps.maxNumRefFrames.toNat
              maxDpbCapacity := Nat.max 16 (maxRefs + 2)
              maxFrameNum := maxFn
            }
            dpbInit := true
          }
        let (currPoc, nextPocState) := computePicturePoc sps shSyn0 st.pocState
        let mut pY := Plane2D.alloc (mbsW * 16) (mbsH * 16) (mbsW * 16) 128
        let mut pU := Plane2D.alloc (mbsW * 8) (mbsH * 8) (mbsW * 8) 128
        let mut pV := Plane2D.alloc (mbsW * 8) (mbsH * 8) (mbsW * 8) 128
        let mut colGrid : Array InprocDecodedBlk4 := Array.replicate (gridW4 * gridH4) {}
        let mut intraModeGrid : Array Nat := Array.replicate (gridW4 * gridH4) 2
        let mut blkSliceIds : Array Int := Array.replicate (gridW4 * gridH4) (-1)
        let mut blkIsIntra : Array Bool := Array.replicate (gridW4 * gridH4) false
        let mut mbSliceIds : Array Int := Array.replicate totalMbs (-1)
        let mut mbIsIntra : Array Bool := Array.replicate totalMbs false
        let mut mbMeta : Array InprocMbDeblockMeta := Array.replicate totalMbs {}
        let mut coveredMbs : Nat := 0
        for sIdx in [:vclNals.size] do
          let sNal := vclNals[sIdx]!
          let sRbsp := LeanAV.H264Entropy.stripNalEmulationBytes sNal
          let (shEnt, bitStart) ← LeanAV.H264Entropy.parseSliceHeaderFull sRbsp entSpsArr entPpsArr
          let ppsPair ← st.ppsTable.getD shEnt.ppsId none
          guard (ppsPair.syn.spsId == sps.spsId)
          let pps := ppsPair.syn
          let sliceScope := buildScopeForSpsPps sps pps dstW dstH audioCh LeanAV.Encoder.inprocRingDefaultCap
          guard (inprocTranscodeGateSpec.gate sliceScope)
          let shSyn ← LeanAV.H264Syntax.parseH264SliceHeaderFull (ByteSlice.ofByteArray sNal) sps pps
          if shSyn.redundantPicCnt != 0 then
            pure ()
          else
            guard ((shSyn.nalUnitType == 5) == (shSyn0.nalUnitType == 5) &&
                   shSyn.frameNum == shSyn0.frameNum)
            let mbs ←
              if pps.entropyCodingModeFlag then
                LeanAV.H264Entropy.decodeSliceCabac sRbsp shEnt bitStart spsPair0.ent ppsPair.ent
              else
                LeanAV.H264Entropy.decodeSliceCavlc sRbsp shEnt bitStart spsPair0.ent ppsPair.ent
            let firstMb := shEnt.firstMbInSlice
            guard (firstMb + mbs.size ≤ totalMbs)
            let numL0 := shSyn.numRefIdxL0ActiveMinus1.toNat + 1
            let numL1 := shSyn.numRefIdxL1ActiveMinus1.toNat + 1
            let currFn := shSyn.frameNum.toNat
            let (l0Dpb, l1Dpb) :=
              if shSyn.sliceKind == .P then
                let init0 := LeanAV.H264InterDeblockDpb.buildRefPicListP0 st.dpb currFn
                  (Nat.max numL0 (st.dpb.entries.length + 1))
                let mod0 :=
                  if shSyn.refPicListModFlagL0 then
                    LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb init0 currFn numL0
                      (syntaxModOpsToDpb shSyn.refPicListModL0)
                  else init0.take numL0
                (mod0, [])
              else if shSyn.sliceKind == .B then
                let maxPool := Nat.max (Nat.max numL0 numL1) (st.dpb.entries.length + 1)
                let (init0, init1) :=
                  LeanAV.H264InterDeblockDpb.buildRefPicListsB st.dpb currFn currPoc maxPool maxPool
                let mod0 :=
                  if shSyn.refPicListModFlagL0 then
                    LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb init0 currFn numL0
                      (syntaxModOpsToDpb shSyn.refPicListModL0)
                  else init0.take numL0
                let mod1 :=
                  if shSyn.refPicListModFlagL1 then
                    LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb init1 currFn numL1
                      (syntaxModOpsToDpb shSyn.refPicListModL1)
                  else init1.take numL1
                (mod0, mod1)
              else
                ([], [])
            let l0Pics ← resolveDpbRefsToStored l0Dpb st.storedPics
            let l1Pics ← resolveDpbRefsToStored l1Dpb st.storedPics
            let curSliceId := Int.ofNat sIdx
            let mut curQpY : Int := shSyn.sliceQpY.toInt
            for i in [:mbs.size] do
              let mbIdx := firstMb + i
              guard (mbSliceIds.getD mbIdx (-1) == -1)
              let mb := mbs[i]!
              let mbX := mbIdx % mbsW
              let mbY := mbIdx / mbsW
              let isIntraMb := mb.kind.isIntra
              if mb.kind == .iPcm then
                curQpY := 0
              else if !mb.isSkip && (mb.kind == .i16x16 || mb.cbp != 0) then
                curQpY := (curQpY + mb.mbQpDelta + 52).emod 52
              let qpNat := curQpY.toNat
              mbSliceIds := mbSliceIds.set! mbIdx curSliceId
              mbIsIntra := mbIsIntra.set! mbIdx isIntraMb
              for ry in [:4] do
                for rx in [:4] do
                  let gIdx := (mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)
                  blkSliceIds := blkSliceIds.set! gIdx curSliceId
                  blkIsIntra := blkIsIntra.set! gIdx isIntraMb
              let cqpOff := pps.chromaQpIndexOffset.toInt
              let secCqpOff := pps.secondChromaQpIndexOffset.toInt
              let (recMb, hasCoeff16) ←
                if isIntraMb then do
                  let nbrs := buildIntraMbNeighbors pY pU pV mbSliceIds mbIsIntra
                    mbsW mbX mbY curSliceId pps.constrainedIntraPredFlag
                  let (rm, modes', hc) ← reconstructDecodedIntraMb mb nbrs intraModeGrid
                    blkSliceIds blkIsIntra gridW4 mbX mbY curSliceId
                    pps.constrainedIntraPredFlag qpNat cqpOff secCqpOff
                  intraModeGrid := modes'
                  some (rm, hc)
                else do
                  for ry in [:4] do
                    for rx in [:4] do
                      intraModeGrid := intraModeGrid.set! ((mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)) 2
                  let cg' ← deriveInterMbMotionGrid mb shSyn.sliceKind colGrid blkSliceIds
                    gridW4 gridH4 mbX mbY curSliceId currPoc
                    shSyn.directSpatialMvPredFlag sps.direct8x8InferenceFlag l0Pics l1Pics
                  colGrid := cg'
                  reconstructDecodedInterMb mb colGrid gridW4 mbX mbY l0Pics l1Pics
                    currPoc pps.weightedBipredIdc shSyn.hasPredWeightTable shSyn.predWeightTable
                    qpNat cqpOff secCqpOff
              pY := writeMbYToPlane pY mbX mbY recMb.y
              pU := writeMbCToPlane pU mbX mbY recMb.u
              pV := writeMbCToPlane pV mbX mbY recMb.v
              for ry in [:4] do
                for rx in [:4] do
                  let gIdx := (mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)
                  let prevB := colGrid.getD gIdx {}
                  colGrid := colGrid.set! gIdx {
                    prevB with
                    sliceId := sIdx
                    isIntra := isIntraMb
                    hasCoeff := hasCoeff16.getD (ry * 4 + rx) false
                    refIdxL0 := if isIntraMb then -1 else prevB.refIdxL0
                    mvL0 := if isIntraMb then ⟨0, 0⟩ else prevB.mvL0
                    refPicUidL0 := if isIntraMb then none else prevB.refPicUidL0
                    refIdxL1 := if isIntraMb then -1 else prevB.refIdxL1
                    mvL1 := if isIntraMb then ⟨0, 0⟩ else prevB.mvL1
                    refPicUidL1 := if isIntraMb then none else prevB.refPicUidL1
                  }
              mbMeta := mbMeta.set! mbIdx {
                sliceId := curSliceId
                qpY := qpNat
                is8x8 := mb.transform8x8 != 0
                disableIdc := shSyn.disableDeblockingFilterIdc.toNat
                alphaOffDiv2 := shSyn.sliceAlphaC0OffsetDiv2.toInt
                betaOffDiv2 := shSyn.sliceBetaOffsetDiv2.toInt
                cqpOff := cqpOff
                secCqpOff := secCqpOff
              }
              coveredMbs := coveredMbs + 1
        guard (coveredMbs == totalMbs)
        let (dY, dU, dV) := deblockDecodedPicture pY pU pV colGrid mbMeta mbsW mbsH
        let (cropUnitX, cropUnitY) :=
          LeanAV.H264Syntax.h264CropUnits sps.chromaFormatIdc sps.separateColourPlaneFlag sps.frameMbsOnlyFlag
        let cropL := if sps.frameCroppingFlag then sps.frameCropLeftOffset.toNat * cropUnitX else 0
        let cropT := if sps.frameCroppingFlag then sps.frameCropTopOffset.toNat * cropUnitY else 0
        let picUid := st.dpb.nextUid
        let hasMmco5 :=
          shSyn0.nalRefIdc != 0 && shSyn0.nalUnitType != 5 &&
          shSyn0.adaptiveRefPicMarkingModeFlag &&
          shSyn0.mmcoOps.any (fun op => op.opcode == 5)
        let effPoc := if hasMmco5 then 0 else currPoc
        let mmcoList ← syntaxMmcoOpsToDpb shSyn0.mmcoOps
        let storedPic : InprocStoredPic := {
          uid := picUid
          poc := effPoc
          isLongTerm := shSyn0.nalUnitType == 5 && shSyn0.longTermReferenceFlag
          yPlane := dY
          uPlane := dU
          vPlane := dV
          cropLeft := cropL
          cropTop := cropT
          cropWidth := sps.widthPx.toNat
          cropHeight := sps.heightPx.toNat
          gridW4 := gridW4
          gridH4 := gridH4
          colGrid := colGrid
        }
        let storedWithCurr := st.storedPics.push storedPic
        let dpbBefore := st.dpb
        let dpbAfter :=
          LeanAV.H264InterDeblockDpb.insertDecodedPicture
            dpbBefore
            (shSyn0.nalUnitType == 5)
            shSyn0.noOutputOfPriorPicsFlag
            shSyn0.longTermReferenceFlag
            (shSyn0.nalRefIdc != 0)
            shSyn0.frameNum.toNat
            currPoc
            shSyn0.adaptiveRefPicMarkingModeFlag
            mmcoList
            0
        let (emittedFrames, liveStored, emittedUids') ←
          collectEmittedAndPrune dpbBefore dpbAfter storedWithCurr st.emittedUids
        let stNext : InprocDecoderState := {
          st with
          dpb := dpbAfter
          storedPics := liveStored
          emittedUids := emittedUids'
          pocState := nextPocState
        }
        some (stNext, emittedFrames)

private def flushDecoderFrames (st : InprocDecoderState) : Option (InprocDecoderState × Array VideoFrame) := do
  if !st.dpbInit then
    some (st, #[])
  else
    let dpbBefore := st.dpb
    let dpbAfter := LeanAV.H264InterDeblockDpb.flushDpb dpbBefore
    let (frames, liveStored, emittedUids') ←
      collectEmittedAndPrune dpbBefore dpbAfter st.storedPics st.emittedUids
    some ({ st with dpb := dpbAfter, storedPics := liveStored, emittedUids := emittedUids' }, frames)

/-! ## CAVLC All-Intra H.264 Frame Re-Encoder -/

private def bitWriterToBitArray (w : BitWriter) : Array UInt8 := Id.run do
  let totalBits := w.bytes.size * 8 + w.bitsUsed
  let bytes := (w.alignToByte).toByteArray
  return LeanAV.H264Entropy.extractBitArray bytes 0 totalBits

private def chooseEncoderLevelIdc (mbsW mbsH : Nat) (srcLevel : UInt8) : UInt8 :=
  let mbs := mbsW * mbsH
  let minLvl : UInt8 :=
    if mbs ≤ 99 then 12
    else if mbs ≤ 396 then 20
    else if mbs ≤ 1620 then 30
    else if mbs ≤ 3600 then 31
    else if mbs ≤ 8192 then 40
    else 51
  if srcLevel > minLvl then srcLevel else minLvl

private def buildEncoderSpsPps
    (dstW dstH : Nat) (srcLevel : UInt8)
    : Option (LeanAV.H264Syntax.H264SpsFull × LeanAV.H264Syntax.H264PpsFull ×
              LeanAV.H264Entropy.SpsFull × LeanAV.H264Entropy.PpsFull ×
              ByteArray × ByteArray × ByteArray) := do
  if dstW == 0 || dstH == 0 || dstW % 2 != 0 || dstH % 2 != 0 then
    none
  else
    let mbsW := (dstW + 15) / 16
    let mbsH := (dstH + 15) / 16
    let padW := mbsW * 16 - dstW
    let padH := mbsH * 16 - dstH
    let needCrop := padW > 0 || padH > 0
    let lvl := chooseEncoderLevelIdc mbsW mbsH srcLevel
    let spsSyn : LeanAV.H264Syntax.H264SpsFull := {
      nalRefIdc := 3
      profileIdc := 66
      constraintSet0Flag := true
      constraintSet1Flag := true
      levelIdc := lvl
      spsId := 0
      chromaFormatIdc := 1
      separateColourPlaneFlag := false
      bitDepthLumaMinus8 := 0
      bitDepthChromaMinus8 := 0
      qpprimeYZeroTransformBypass := false
      seqScalingMatrixPresentFlag := false
      log2MaxFrameNumMinus4 := 0
      picOrderCntType := 0
      log2MaxPicOrderCntLsbMinus4 := 4
      maxNumRefFrames := 1
      gapsInFrameNumValueAllowedFlag := false
      picWidthInMbsMinus1 := (mbsW - 1).toUInt16
      picHeightInMapUnitsMinus1 := (mbsH - 1).toUInt16
      frameMbsOnlyFlag := true
      mbAdaptiveFrameFieldFlag := false
      direct8x8InferenceFlag := true
      frameCroppingFlag := needCrop
      frameCropLeftOffset := 0
      frameCropRightOffset := (padW / 2).toUInt16
      frameCropTopOffset := 0
      frameCropBottomOffset := (padH / 2).toUInt16
      widthPx := dstW.toUInt32
      heightPx := dstH.toUInt32
      vuiParametersPresentFlag := false
    }
    let ppsSyn : LeanAV.H264Syntax.H264PpsFull := {
      nalRefIdc := 3
      ppsId := 0
      spsId := 0
      entropyCodingModeFlag := false
      bottomFieldPicOrderInFramePresent := false
      numSliceGroupsMinus1 := 0
      numRefIdxL0DefaultActiveMinus1 := 0
      numRefIdxL1DefaultActiveMinus1 := 0
      weightedPredFlag := false
      weightedBipredIdc := 0
      picInitQpMinus26 := 0
      picInitQsMinus26 := 0
      chromaQpIndexOffset := 0
      deblockingFilterControlPresentFlag := true
      constrainedIntraPredFlag := false
      redundantPicCntPresentFlag := false
      hasMoreRbspDataExt := false
      transform8x8ModeFlag := false
      picScalingMatrixPresentFlag := false
      secondChromaQpIndexOffset := 0
    }
    let spsNal ← LeanAV.H264Syntax.serializeH264SpsFull spsSyn
    let ppsNal ← LeanAV.H264Syntax.serializeH264PpsFull ppsSyn 1 0
    let spsEnt ← LeanAV.H264Entropy.parseSpsFull spsNal
    let spsArr : Array (Option LeanAV.H264Entropy.SpsFull) :=
      (Array.replicate 32 none).set! 0 (some spsEnt)
    let ppsEnt ← LeanAV.H264Entropy.parsePpsFull ppsNal spsArr
    let avccRec : LeanAV.H264Syntax.AvcDecoderConfigRecord := {
      configurationVersion := 1
      avcProfileIndication := 66
      profileCompatibility := spsSyn.constraintByte
      avcLevelIndication := lvl
      lengthSizeMinusOne := 3
      spsNalus := #[spsNal]
      ppsNalus := #[ppsNal]
      hasHighExt := false
    }
    let avccBody ← LeanAV.H264Syntax.serializeAvcDecoderConfigRecord avccRec
    some (spsSyn, ppsSyn, spsEnt, ppsEnt, spsNal, ppsNal, avccBody)

private def encodeVideoFrameIdrCavlc
    (vf : VideoFrame) (frameIdx : Nat)
    (spsEnt : LeanAV.H264Entropy.SpsFull)
    (ppsEnt : LeanAV.H264Entropy.PpsFull)
    (qpY : Nat := 20) : Option ByteArray := do
  if vf.planes.size < 3 || vf.width == 0 || vf.height == 0 then
    none
  else
    let mbsW := spsEnt.picWidthInMbs
    let mbsH := spsEnt.picHeightInMapUnits
    let totalMbs := mbsW * mbsH
    let gridW4 := mbsW * 4
    let gridH4 := mbsH * 4
    let srcY := vf.planes[0]!
    let srcU := vf.planes[1]!
    let srcV := vf.planes[2]!
    let mut recY := Plane2D.alloc (mbsW * 16) (mbsH * 16) (mbsW * 16) 128
    let mut recU := Plane2D.alloc (mbsW * 8) (mbsH * 8) (mbsW * 8) 128
    let mut recV := Plane2D.alloc (mbsW * 8) (mbsH * 8) (mbsW * 8) 128
    let mut intraModeGrid : Array Nat := Array.replicate (gridW4 * gridH4) 2
    let mut blkSliceIds : Array Int := Array.replicate (gridW4 * gridH4) (-1)
    let mut blkIsIntra : Array Bool := Array.replicate (gridW4 * gridH4) false
    let mut mbSliceIds : Array Int := Array.replicate totalMbs (-1)
    let mut mbIsIntra : Array Bool := Array.replicate totalMbs false
    let mut mbsOut : Array LeanAV.H264Entropy.MbSyntax := Array.mkEmpty totalMbs
    for mbY in [:mbsH] do
      for mbX in [:mbsW] do
        let mbIdx := mbY * mbsW + mbX
        let srcMb : LeanAV.H264IntraTransform.H264Yuv420pMb := {
          y := extractMbYFromPlane srcY mbX mbY
          u := extractMbCFromPlane srcU mbX mbY
          v := extractMbCFromPlane srcV mbX mbY
        }
        let nbrs := buildIntraMbNeighbors recY recU recV mbSliceIds mbIsIntra mbsW mbX mbY 0 false
        let coded := LeanAV.H264IntraTransform.encodeLossyIntraMb srcMb nbrs 0 qpY 0
        mbSliceIds := mbSliceIds.set! mbIdx 0
        mbIsIntra := mbIsIntra.set! mbIdx true
        for ry in [:4] do
          for rx in [:4] do
            let gIdx := (mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)
            blkSliceIds := blkSliceIds.set! gIdx 0
            blkIsIntra := blkIsIntra.set! gIdx true
        let intraModesBeforeMb := intraModeGrid
        let mut predSyntax : Array (Nat × Nat) := Array.mkEmpty 16
        let mut lumaBlocks : Array (Array Int) := Array.mkEmpty 16
        for b in [:16] do
          let (xO, yO) := LeanAV.H264IntraTransform.zScan4BlkCoord b
          let gx := mbX * 4 + xO / 4
          let gy := mbY * 4 + yO / 4
          let mpm := deriveMostProbableIntraMode intraModeGrid blkSliceIds blkIsIntra gridW4 gx gy 0 false
          let actual := coded.lumaModes.getD b 2
          predSyntax := predSyntax.push (actualToSyntaxIntraMode mpm actual)
          intraModeGrid := intraModeGrid.set! (gy * gridW4 + gx) actual
          let lv16 := coded.yBlocks.getD b (Array.replicate 16 0)
          lumaBlocks := lumaBlocks.push (LeanAV.H264Entropy.rasterToZigzag4x4 lv16)
        let mut cbpLuma : Nat := 0
        for i8 in [:4] do
          let mut subNz := false
          for s in [:4] do
            if anyNonZeroInt (lumaBlocks.getD (4 * i8 + s) #[]) 16 then
              subNz := true
          if subNz then
            cbpLuma := cbpLuma ||| (1 <<< i8)
        let mut cAc : Array (Array Int) := Array.mkEmpty 8
        let mut hasChromaAc := false
        for ci in [:4] do
          let u15 := raster16ToAc15Scan (coded.uAc4.getD ci (Array.replicate 16 0))
          if anyNonZeroInt u15 15 then hasChromaAc := true
          cAc := cAc.push u15
        for ci in [:4] do
          let v15 := raster16ToAc15Scan (coded.vAc4.getD ci (Array.replicate 16 0))
          if anyNonZeroInt v15 15 then hasChromaAc := true
          cAc := cAc.push v15
        let hasChromaDc := anyNonZeroInt coded.uDc4 4 || anyNonZeroInt coded.vDc4 4
        let cbpChroma : Nat := if hasChromaAc then 2 else if hasChromaDc then 1 else 0
        let finalChromaDc :=
          if cbpChroma == 0 then #[Array.replicate 4 0, Array.replicate 4 0]
          else #[coded.uDc4, coded.vDc4]
        let finalChromaAc :=
          if cbpChroma < 2 then Array.replicate 8 (Array.replicate 15 0)
          else cAc
        let mbSyn : LeanAV.H264Entropy.MbSyntax := {
          isSkip := false
          kind := .iNxN
          intraIdx := 0
          transform8x8 := 0
          intraPred := predSyntax
          chromaPredMode := coded.chromaMode
          cbp := cbpLuma ||| (cbpChroma <<< 4)
          mbQpDelta := 0
          lumaAcOr4x4 := lumaBlocks
          chromaDc := finalChromaDc
          chromaAc := finalChromaAc
        }
        let (recDecMb, modesAfter, _) ←
          reconstructDecodedIntraMb mbSyn nbrs intraModesBeforeMb blkSliceIds blkIsIntra
            gridW4 mbX mbY 0 false qpY 0 0
        intraModeGrid := modesAfter
        recY := writeMbYToPlane recY mbX mbY recDecMb.y
        recU := writeMbCToPlane recU mbX mbY recDecMb.u
        recV := writeMbCToPlane recV mbX mbY recDecMb.v
        mbsOut := mbsOut.push mbSyn
    let idrPicId := frameIdx % 2
    let wPre :=
      let w0 := LeanAV.H264Entropy.writeUNat BitWriter.empty 0 4
      let w1 := LeanAV.H264Entropy.writeUENat w0 idrPicId
      let w2 := LeanAV.H264Entropy.writeUNat w1 0 8
      let w3 := LeanAV.H264Entropy.writeU1Nat w2 0
      LeanAV.H264Entropy.writeU1Nat w3 0
    let wSuf :=
      let w0 := LeanAV.H264Entropy.writeUENat BitWriter.empty 0
      let w1 := LeanAV.H264Entropy.writeSEInt w0 0
      LeanAV.H264Entropy.writeSEInt w1 0
    let qpDelta : Int := Int.ofNat qpY - 26
    let shEnt : LeanAV.H264Entropy.SliceHeaderFull := {
      nalHdr := 0x65
      firstMbInSlice := 0
      sliceType := 7
      sliceTypeNos := 2
      ppsId := 0
      prefixBits := bitWriterToBitArray wPre
      cabacInitIdc := 0
      sliceQpDelta := qpDelta
      suffixBits := bitWriterToBitArray wSuf
      numRefL0 := 1
      numRefL1 := 1
      sliceQpY := Int.ofNat qpY
    }
    let sliceNal ← LeanAV.H264Entropy.encodeSliceCavlc shEnt mbsOut spsEnt ppsEnt
    LeanAV.H264Syntax.packAvccPacket #[sliceNal] 4

/-! ## MP4 Probe & Bounded-Ring In-Process Transcode Pipeline -/

private def samplesInBounds (rawSize : Nat) (samples : Array NativeMp4Sample) : Bool := Id.run do
  if samples.isEmpty then return false
  for s in samples do
    if s.byteLen == 0 || s.dur == 0 || s.fileOff + s.byteLen > rawSize then
      return false
  return true

private def deriveOutputVideoDurations
    (srcSamples : Array NativeMp4Sample) (outCount : Nat) : Array Nat := Id.run do
  if outCount == 0 then return #[]
  if srcSamples.isEmpty then return Array.replicate outCount 1
  let totalDur := srcSamples.foldl (fun acc s => acc + s.dur) 0
  let defaultSample : NativeMp4Sample :=
    { dur := 1, fileOff := 0, byteLen := 1, dts := 0, cttsOff := 0, isSync := true }
  let fallbackDur := Nat.max 1 (srcSamples.getD (srcSamples.size - 1) defaultSample).dur
  if !srcSamples.any (fun s => s.cttsOff != 0) then
    return Array.ofFn fun i : Fin outCount =>
      if i.val < srcSamples.size then Nat.max 1 srcSamples[i.val]!.dur else fallbackDur
  let ptsPairs : Array (Int × Nat × Nat) :=
    Array.ofFn fun i : Fin srcSamples.size =>
      let s := srcSamples[i.val]!
      (Int.ofNat s.dts + s.cttsOff, i.val, s.dur)
  let sorted := ptsPairs.qsort fun a b =>
    if a.1 != b.1 then a.1 < b.1 else a.2.1 < b.2.1
  if outCount == sorted.size then
    let mut durs : Array Nat := Array.mkEmpty outCount
    let mut sumPrev : Nat := 0
    let mut strictlyInc := true
    for k in [:outCount] do
      if k + 1 < outCount then
        let p0 := sorted[k]!.1
        let p1 := sorted[k + 1]!.1
        if p1 ≤ p0 then strictlyInc := false
        let d := if p1 > p0 then (p1 - p0).toNat else Nat.max 1 sorted[k]!.2.2
        durs := durs.push (Nat.max 1 d)
        sumPrev := sumPrev + Nat.max 1 d
      else
        let rem := if totalDur > sumPrev then totalDur - sumPrev else sorted[k]!.2.2
        durs := durs.push (Nat.max 1 rem)
    if strictlyInc then return durs
  return Array.ofFn fun i : Fin outCount =>
    if i.val < sorted.size then Nat.max 1 sorted[i.val]!.2.2 else fallbackDur

def probeInprocMp4Bytes
    (raw : ByteArray) (dstWOpt dstHOpt : Nat)
    (wantAudio : Bool) (copyAudio : Bool)
    (ringCap : Nat := LeanAV.Encoder.inprocRingDefaultCap)
    : Option InprocMp4Probe := do
  let tracks ← LeanAV.Format.demuxNativeMp4ContainerTracks (ByteSlice.ofByteArray raw)
  let videoTracks := tracks.filter (fun t => t.kind == .video)
  if videoTracks.size != 1 then none
  else
    let video := videoTracks[0]!
    if (video.stsdFourcc != "avc1" && video.stsdFourcc != "avc3") ||
       video.hasEncrypted || video.multiStsd || video.timescale == 0 ||
       !samplesInBounds raw.size video.samples then
      none
    else
      let avccBody ← LeanAV.Format.extractMp4StsdAvcCBody video.stsdBox
      let avcc ← LeanAV.H264Syntax.parseAvcDecoderConfigRecord avccBody
      let nalLenSize := avcc.lengthSizeMinusOne.toNat + 1
      let spsNal ← avcc.spsNalus[0]?
      let ppsNal ← avcc.ppsNalus[0]?
      let sps ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray spsNal)
      let pps ← LeanAV.H264Syntax.parseH264PpsFull (ByteSlice.ofByteArray ppsNal) (some sps)
      let srcW := sps.widthPx.toNat
      let srcH := sps.heightPx.toNat
      let dstW := if dstWOpt == 0 then srcW else dstWOpt
      let dstH := if dstHOpt == 0 then srcH else dstHOpt
      let audioTracks := tracks.filter (fun t => t.kind == .audio)
      if wantAudio && audioTracks.size > 1 then
        none
      else
        let (audioMode, audioTrk?, asc?, audioCh) ←
          if !wantAudio || audioTracks.isEmpty then
            some (InprocAudioMode.none, none, none, 0)
          else
            let aTrk := audioTracks[0]!
            if aTrk.stsdFourcc != "mp4a" || aTrk.hasEncrypted || aTrk.multiStsd ||
               aTrk.timescale == 0 || !samplesInBounds raw.size aTrk.samples then
              none
            else
              let esds ← LeanAV.Format.extractMp4StsdMp4aEsdsBox aTrk.stsdBox
              let asc ← LeanAV.AacLc.parseMp4EsdsAsc (ByteSlice.ofByteArray esds)
              let ch := asc.channelConfiguration.toNat
              let mode := if copyAudio then InprocAudioMode.copy else InprocAudioMode.reencodeAacLc
              some (mode, some aTrk, some asc, ch)
        let scope := buildScopeForSpsPps sps pps dstW dstH audioCh ringCap
        if !inprocTranscodeGateSpec.gate scope then
          none
        else
          some {
            videoTrack := video
            avcc := avcc
            nalLenSize := nalLenSize
            initSps := sps
            initPps := pps
            srcW := srcW
            srcH := srcH
            dstW := dstW
            dstH := dstH
            audioTrack? := audioTrk?
            audioAsc? := asc?
            audioMode := audioMode
            scope := scope
          }

private def runInprocAudioStageIO
    (raw : ByteArray) (probe : InprocMp4Probe)
    : IO (Except String (Option SynthMp4Track)) := do
  let cap := probe.scope.ringCap
  match probe.audioMode, probe.audioTrack?, probe.audioAsc? with
  | .none, _, _ =>
    return .ok none
  | .copy, some tr, some asc =>
    let rawRes ← LeanAV.Encoder.runBoundedRingStageIO tr.samples cap fun s => do
      let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
      if pkt.size == 0 then
        return .error "inproc_aac_empty_packet"
      return .ok ({ data := pkt, dur := s.dur, cttsOff := 0, isSync := true } : SynthMp4Sample)
    match rawRes with
    | .error e => return .error e
    | .ok copied =>
      let some entry := LeanAV.AacLc.buildMp4aSampleEntryBox asc
        | return .error "inproc_aac_stsd_build_failed"
      let trk : SynthMp4Track := {
        kind := .audio
        timescale := tr.timescale
        width := 0
        height := 0
        stsdBox := LeanAV.Format.buildMp4aStsdBoxFromEntry entry
        samples := copied
      }
      return .ok (some trk)
  | .reencodeAacLc, some tr, some asc =>
    let adtsRes ← LeanAV.Encoder.runBoundedRingStageIO tr.samples cap fun s => do
      let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
      match LeanAV.AacLc.muxAdtsFrame asc.samplingFrequencyIndex asc.channelConfiguration pkt false with
      | none => return .error "inproc_aac_adts_mux_failed"
      | some f => return .ok f
    match adtsRes with
    | .error e => return .error e
    | .ok adtsFrames =>
      let adtsStream := Id.run do
        let total := adtsFrames.foldl (fun acc b => acc + b.size) 0
        let mut buf := ByteArray.emptyWithCapacity total
        for b in adtsFrames do
          buf := buf ++ b
        return buf
      let some (pcmChans, sampleRate, bps) :=
        LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray adtsStream) false
        | return .error "inproc_aac_decode_failed"
      let some encAdts :=
        LeanAV.AacLc.aacEncodeAdtsStream pcmChans sampleRate bps 128000 true
        | return .error "inproc_aac_encode_failed"
      let some (_, rawSlices) :=
        LeanAV.AacLc.demuxAdtsStream (ByteSlice.ofByteArray encAdts) false
        | return .error "inproc_aac_adts_demux_failed"
      let synthRes ← LeanAV.Encoder.runBoundedRingStageIO rawSlices cap fun sl => do
        let b := sl.toByteArray
        if b.size == 0 then
          return .error "inproc_aac_encoded_empty"
        return .ok ({ data := b, dur := 1024, cttsOff := 0, isSync := true } : SynthMp4Sample)
      match synthRes with
      | .error e => return .error e
      | .ok outSamples =>
        let outAsc : LeanAV.AacLc.AacLcAsc := {
          audioObjectType := 2
          samplingFrequencyIndex := asc.samplingFrequencyIndex
          channelConfiguration := pcmChans.size.toUInt8
          frameLengthFlag := false
          dependsOnCoreCoder := false
          extensionFlag := false
        }
        let some entry := LeanAV.AacLc.buildMp4aSampleEntryBox outAsc
          | return .error "inproc_aac_stsd_build_failed"
        let trk : SynthMp4Track := {
          kind := .audio
          timescale := sampleRate.toNat
          width := 0
          height := 0
          stsdBox := LeanAV.Format.buildMp4aStsdBoxFromEntry entry
          samples := outSamples
        }
        return .ok (some trk)
  | _, _, _ =>
    return .error "inproc_aac_invalid_probe_state"

def runInprocTranscodeWithProbeStatsIO
    (raw : ByteArray) (probe : InprocMp4Probe) (qpY : Nat := 20)
    : IO (Except String (ByteArray × Nat × Bool)) := do
  if !inprocTranscodeGateSpec.gate probe.scope then
    return .error "inproc_scope_gate_rejected"
  let cap := probe.scope.ringCap
  let audioCh := probe.scope.audioChannels
  let mut decInit : InprocDecoderState := {}
  for spsNal in probe.avcc.spsNalus do
    match registerSpsNalu decInit spsNal with
    | none => return .error "inproc_avcc_sps_parse_failed"
    | some st' => decInit := st'
  for ppsNal in probe.avcc.ppsNalus do
    match registerPpsNalu decInit ppsNal with
    | none => return .error "inproc_avcc_pps_parse_failed"
    | some st' => decInit := st'
  let some (_, _, encSpsEnt, encPpsEnt, _, _, encAvccBody) :=
    buildEncoderSpsPps probe.dstW probe.dstH probe.initSps.levelIdc
    | return .error "inproc_encoder_sps_pps_failed"
  -- Stage 1: Bounded ring demux of AVCC access-unit NALU arrays
  let auRes ← LeanAV.Encoder.runBoundedRingStageIO probe.videoTrack.samples cap fun s => do
    let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
    match LeanAV.H264Syntax.splitAvccPacket pkt probe.nalLenSize with
    | none => return .error "inproc_avcc_packet_split_failed"
    | some nalus =>
      if nalus.isEmpty then
        return .error "inproc_empty_access_unit"
      return .ok nalus
  let auList ← match auRes with
    | .error e => return .error e
    | .ok v => pure v
  -- Stage 2: Bounded ring H.264 decode + DPB reorder + optional yuv420p scale
  let decStateRef ← IO.mkRef decInit
  let needScale := probe.dstW != probe.srcW || probe.dstH != probe.srcH
  let decChunksRes ← LeanAV.Encoder.runBoundedRingStageIO auList cap fun nalus => do
    let stCur ← decStateRef.get
    match decodeAccessUnitNalus stCur nalus probe.dstW probe.dstH audioCh with
    | none => return .error "inproc_h264_decode_failed"
    | some (stNext, emitted) =>
      decStateRef.set stNext
      let scaled :=
        if needScale then
          emitted.map (fun vf => LeanAV.Scale.scaleVideoFrameYuv420p vf probe.dstW probe.dstH)
        else
          emitted
      return .ok scaled
  let decChunks ← match decChunksRes with
    | .error e => return .error e
    | .ok v => pure v
  let stAfterLoop ← decStateRef.get
  let some (_, flushedFrames) := flushDecoderFrames stAfterLoop
    | return .error "inproc_h264_dpb_flush_failed"
  let flushedScaled :=
    if needScale then
      flushedFrames.map (fun vf => LeanAV.Scale.scaleVideoFrameYuv420p vf probe.dstW probe.dstH)
    else
      flushedFrames
  let allFrames := Id.run do
    let mut acc : Array VideoFrame := #[]
    for chunk in decChunks do
      for f in chunk do
        acc := acc.push f
    for f in flushedScaled do
      acc := acc.push f
    return acc
  if allFrames.isEmpty then
    return .error "inproc_zero_decoded_frames"
  let outDurs := deriveOutputVideoDurations probe.videoTrack.samples allFrames.size
  let indexedFrames : Array (Nat × VideoFrame) :=
    Array.ofFn fun i : Fin allFrames.size => (i.val, allFrames[i.val]!)
  -- Stage 3: Bounded ring CAVLC all-intra H.264 re-encode
  let encSamplesRes ← LeanAV.Encoder.runBoundedRingStageIO indexedFrames cap fun (idx, vf) => do
    match encodeVideoFrameIdrCavlc vf idx encSpsEnt encPpsEnt qpY with
    | none => return .error "inproc_h264_cavlc_encode_failed"
    | some avccPkt =>
      let dur := outDurs.getD idx 1
      return .ok ({ data := avccPkt, dur := dur, cttsOff := 0, isSync := true } : SynthMp4Sample)
  let videoSamples ← match encSamplesRes with
    | .error e => return .error e
    | .ok v => pure v
  let videoSynthTrack : SynthMp4Track := {
    kind := .video
    timescale := probe.videoTrack.timescale
    width := probe.dstW
    height := probe.dstH
    stsdBox := LeanAV.Format.buildAvc1StsdBox probe.dstW probe.dstH encAvccBody
    samples := videoSamples
  }
  -- Stages 4 & 5: Optional AAC-LC bounded ring demux / decode / re-encode
  let audioSynthOpt ← match (← runInprocAudioStageIO raw probe) with
    | .error e => return .error e
    | .ok a => pure a
  let outTracks : Array SynthMp4Track :=
    match audioSynthOpt with
    | none => #[videoSynthTrack]
    | some aTrk => #[videoSynthTrack, aTrk]
  match LeanAV.Format.muxSynthMp4Container outTracks with
  | none => return .error "inproc_mp4_mux_failed"
  | some mp4Bytes => return .ok (mp4Bytes, allFrames.size, audioSynthOpt.isSome)

def runInprocTranscodeWithProbeIO
    (raw : ByteArray) (probe : InprocMp4Probe) (qpY : Nat := 20)
    : IO (Except String ByteArray) := do
  match (← runInprocTranscodeWithProbeStatsIO raw probe qpY) with
  | .ok (mp4Bytes, _, _) => return .ok mp4Bytes
  | .error e => return .error e

def inprocTranscodeMp4BytesIO
    (raw : ByteArray) (dstWOpt dstHOpt : Nat)
    (wantAudio : Bool) (copyAudio : Bool := false) (qpY : Nat := 20)
    : IO (Except String ByteArray) := do
  let some probe := probeInprocMp4Bytes raw dstWOpt dstHOpt wantAudio copyAudio
    | return .error "inproc_mp4_probe_rejected"
  runInprocTranscodeWithProbeIO raw probe qpY

def inprocTranscodeMp4FileIO
    (inPath outPath : String) (dstWOpt dstHOpt : Nat)
    (wantAudio : Bool) (copyAudio : Bool := false) (qpY : Nat := 20)
    : IO (Except String UInt64) := do
  let raw ← try
      IO.FS.readBinFile inPath
    catch e =>
      return .error s!"inproc_read_failed:{e.toString}"
  let mp4Out ← match (← inprocTranscodeMp4BytesIO raw dstWOpt dstHOpt wantAudio copyAudio qpY) with
    | .ok b => pure b
    | .error e => return .error e
  match (← LeanAV.IO.writeMediaFileAtomic outPath mp4Out) with
  | .ok digest => return .ok digest
  | .error e => return .error s!"inproc_write_failed:{reprStr e}"

end LeanAV.InprocTranscode
