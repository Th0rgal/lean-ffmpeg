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
  0 < s.srcW ∧ 0 < s.srcH ∧ 0 < s.dstW ∧ 0 < s.dstH ∧
  s.dstW % 2 = 0 ∧ s.dstH % 2 = 0 ∧
  (s.chromaFormatIdc = 0 ∨ s.chromaFormatIdc = 1 ∨ s.chromaFormatIdc = 2 ∨ s.chromaFormatIdc = 3) ∧
  (s.chromaFormatIdc ≠ 1 ∨ (s.srcW % 2 = 0 ∧ s.srcH % 2 = 0)) ∧
  (s.chromaFormatIdc ≠ 2 ∨ s.srcW % 2 = 0) ∧
  (s.bitDepthLuma8 = 0 ∨ s.bitDepthLuma8 = 2 ∨ s.bitDepthLuma8 = 4) ∧
  (s.bitDepthChroma8 = 0 ∨ s.bitDepthChroma8 = 2 ∨ s.bitDepthChroma8 = 4) ∧
  s.frameMbsOnly = true ∧
  s.hasFmo = false ∧
  s.profileIdc ≠ 135 ∧
  (s.audioChannels = 0 ∨ s.audioChannels = 1 ∨ s.audioChannels = 2) ∧
  0 < s.ringCap

instance (s : InprocTranscodeScope) : Decidable (InprocTranscodeScopeSafe s) :=
  inferInstanceAs (Decidable
    (0 < s.srcW ∧ 0 < s.srcH ∧ 0 < s.dstW ∧ 0 < s.dstH ∧
     s.dstW % 2 = 0 ∧ s.dstH % 2 = 0 ∧
     (s.chromaFormatIdc = 0 ∨ s.chromaFormatIdc = 1 ∨ s.chromaFormatIdc = 2 ∨ s.chromaFormatIdc = 3) ∧
     (s.chromaFormatIdc ≠ 1 ∨ (s.srcW % 2 = 0 ∧ s.srcH % 2 = 0)) ∧
     (s.chromaFormatIdc ≠ 2 ∨ s.srcW % 2 = 0) ∧
     (s.bitDepthLuma8 = 0 ∨ s.bitDepthLuma8 = 2 ∨ s.bitDepthLuma8 = 4) ∧
     (s.bitDepthChroma8 = 0 ∨ s.bitDepthChroma8 = 2 ∨ s.bitDepthChroma8 = 4) ∧
     s.frameMbsOnly = true ∧
     s.hasFmo = false ∧
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
    pps.numSliceGroupsMinus1 != 0
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

/-! ## Access-Unit HBD Picture Decoder Bridge -/

private def picsHbdToVideoFrames
    (pics : Array LeanAV.H264InterDeblockDpb.H264PictureHbd) : Option (Array VideoFrame) := do
  let mut out : Array VideoFrame := Array.mkEmpty pics.size
  for p in pics do
    let vf ← LeanAV.H264IntraTransform.pictureHbdToYuv420pVideoFrame p
    out := out.push vf
  some out

private def decodeAccessUnitNalusHbd
    (st0 : LeanAV.H264IntraTransform.HbdDecoderState) (nalus : Array ByteArray) (dstW dstH audioCh : Nat)
    : Option (LeanAV.H264IntraTransform.HbdDecoderState × Array VideoFrame) := do
  let chk := fun sps pps =>
    let scope := buildScopeForSpsPps sps pps dstW dstH audioCh LeanAV.Encoder.inprocRingDefaultCap
    inprocTranscodeGateSpec.gate scope
  let (stNext, emittedPics) ← LeanAV.H264IntraTransform.decodeHbdAccessUnitNalusChecked st0 nalus (some chk)
  let emittedFrames ← picsHbdToVideoFrames emittedPics
  some (stNext, emittedFrames)

private def flushDecoderFramesHbd
    (st : LeanAV.H264IntraTransform.HbdDecoderState)
    : Option (LeanAV.H264IntraTransform.HbdDecoderState × Array VideoFrame) := do
  let (stNext, flushedPics) ← LeanAV.H264IntraTransform.flushHbdDecoderPictures st
  let flushedFrames ← picsHbdToVideoFrames flushedPics
  some (stNext, flushedFrames)

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
  let mut decInit : LeanAV.H264IntraTransform.HbdDecoderState := {}
  for spsNal in probe.avcc.spsNalus do
    match LeanAV.H264IntraTransform.registerHbdSps decInit spsNal with
    | none => return .error "inproc_avcc_sps_parse_failed"
    | some st' => decInit := st'
  for ppsNal in probe.avcc.ppsNalus do
    match LeanAV.H264IntraTransform.registerHbdPps decInit ppsNal with
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
    match decodeAccessUnitNalusHbd stCur nalus probe.dstW probe.dstH audioCh with
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
  let some (_, flushedFrames) := flushDecoderFramesHbd stAfterLoop
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

/-! ## Unified Pipeline H.264 & AAC-LC Codec Entrypoints -/

/-- Decode an ISOBMFF `avc1`/`avc3` video track into display-ordered `yuv420p` `VideoFrame`s
along with output frame durations (in `video.timescale` units) and source SPS level. -/
def decodeMp4AvcTrackToFrames
    (raw : ByteArray) (video : NativeMp4Track) : Option (Array VideoFrame × Array Nat × UInt8) := do
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
    if srcW % 2 != 0 || srcH % 2 != 0 then
      none
    else
      let scope := buildScopeForSpsPps sps pps srcW srcH 0 LeanAV.Encoder.inprocRingDefaultCap
      if !inprocTranscodeGateSpec.gate scope then
        none
      else
        let mut decSt : LeanAV.H264IntraTransform.HbdDecoderState := {}
        for sN in avcc.spsNalus do
          let st' ← LeanAV.H264IntraTransform.registerHbdSps decSt sN
          decSt := st'
        for pN in avcc.ppsNalus do
          let st' ← LeanAV.H264IntraTransform.registerHbdPps decSt pN
          decSt := st'
        let mut allFrames : Array VideoFrame := #[]
        for s in video.samples do
          let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
          let nalus ← LeanAV.H264Syntax.splitAvccPacket pkt nalLenSize
          if nalus.isEmpty then none
          let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt nalus srcW srcH 0
          decSt := stNext
          for vf in emitted do
            allFrames := allFrames.push vf
        let (_, flushed) ← flushDecoderFramesHbd decSt
        for vf in flushed do
          allFrames := allFrames.push vf
        if allFrames.isEmpty then none
        else
          let durs := deriveOutputVideoDurations video.samples allFrames.size
          some (allFrames, durs, sps.levelIdc)

/-- Decode an Annex-B H.264 byte stream (`.h264`/`.264` or MPEG-TS PES payloads) into `yuv420p` `VideoFrame`s. -/
def decodeAnnexBH264StreamToFrames (annexB : ByteArray) : Option (Array VideoFrame) := do
  let nals := LeanAV.H264Entropy.splitAnnexB annexB
  if nals.isEmpty then none
  else
    let mut decSt : LeanAV.H264IntraTransform.HbdDecoderState := {}
    let mut allFrames : Array VideoFrame := #[]
    let mut curVcl : Array ByteArray := #[]
    for nal in nals do
      if nal.size > 0 then
        let hdr := nal.data.getD 0 0
        if (hdr &&& 0x80) != 0 then none
        let nalType := (hdr &&& 0x1F).toNat
        if nalType == 7 then
          if !curVcl.isEmpty then
            let sps0 ← (decSt.spsTable.findSome? id)
            let w := sps0.syn.widthPx.toNat
            let h := sps0.syn.heightPx.toNat
            let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt curVcl w h 0
            decSt := stNext
            for vf in emitted do allFrames := allFrames.push vf
            curVcl := #[]
          let st' ← LeanAV.H264IntraTransform.registerHbdSps decSt nal
          decSt := st'
        else if nalType == 8 then
          if !curVcl.isEmpty then
            let sps0 ← (decSt.spsTable.findSome? id)
            let w := sps0.syn.widthPx.toNat
            let h := sps0.syn.heightPx.toNat
            let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt curVcl w h 0
            decSt := stNext
            for vf in emitted do allFrames := allFrames.push vf
            curVcl := #[]
          let st' ← LeanAV.H264IntraTransform.registerHbdPps decSt nal
          decSt := st'
        else if nalType == 9 then
          if !curVcl.isEmpty then
            let sps0 ← (decSt.spsTable.findSome? id)
            let w := sps0.syn.widthPx.toNat
            let h := sps0.syn.heightPx.toNat
            let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt curVcl w h 0
            decSt := stNext
            for vf in emitted do allFrames := allFrames.push vf
            curVcl := #[]
        else if nalType == 1 || nalType == 5 then
          let rbsp := LeanAV.H264Entropy.stripNalEmulationBytes nal
          let entSpsArr := decSt.spsTable.map (fun o => o.map (·.ent))
          let entPpsArr := decSt.ppsTable.map (fun o => o.map (·.ent))
          let (shEnt, _) ← LeanAV.H264Entropy.parseSliceHeaderFull rbsp entSpsArr entPpsArr
          if shEnt.firstMbInSlice == 0 && !curVcl.isEmpty then
            let sps0 ← (decSt.spsTable.findSome? id)
            let w := sps0.syn.widthPx.toNat
            let h := sps0.syn.heightPx.toNat
            let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt curVcl w h 0
            decSt := stNext
            for vf in emitted do allFrames := allFrames.push vf
            curVcl := #[nal]
          else
            curVcl := curVcl.push nal
        else if nalType == 2 || nalType == 3 || nalType == 4 || nalType == 19 then
          none
    if !curVcl.isEmpty then
      let sps0 ← (decSt.spsTable.findSome? id)
      let w := sps0.syn.widthPx.toNat
      let h := sps0.syn.heightPx.toNat
      let (stNext, emitted) ← decodeAccessUnitNalusHbd decSt curVcl w h 0
      decSt := stNext
      for vf in emitted do allFrames := allFrames.push vf
    let (_, flushed) ← flushDecoderFramesHbd decSt
    for vf in flushed do allFrames := allFrames.push vf
    if allFrames.isEmpty then none else some allFrames

/-- Encode `yuv420p` `VideoFrame`s into CAVLC all-intra H.264: returns `(avccBody, spsNal, ppsNal, avccPackets)`. -/
def encodeFramesToH264Cavlc
    (frames : Array VideoFrame) (qpY : Nat := 20) (srcLevel : UInt8 := 31)
    : Option (ByteArray × ByteArray × ByteArray × Array ByteArray) := do
  if frames.isEmpty then none
  else
    let vf0 := frames[0]!
    let (_, _, spsEnt, ppsEnt, spsNal, ppsNal, avccBody) ← buildEncoderSpsPps vf0.width vf0.height srcLevel
    let mut pkts : Array ByteArray := Array.mkEmpty frames.size
    for idx in [:frames.size] do
      let pkt ← encodeVideoFrameIdrCavlc frames[idx]! idx spsEnt ppsEnt qpY
      pkts := pkts.push pkt
    some (avccBody, spsNal, ppsNal, pkts)

/-- Encode `yuv420p` `VideoFrame`s into Annex-B H.264 access units (with SPS/PPS prepended to frame 0). -/
def encodeFramesToH264AnnexBPackets
    (frames : Array VideoFrame) (qpY : Nat := 20) (srcLevel : UInt8 := 31)
    : Option (Array ByteArray) := do
  let (_, spsNal, ppsNal, avccPkts) ← encodeFramesToH264Cavlc frames qpY srcLevel
  let mut aus : Array ByteArray := Array.mkEmpty avccPkts.size
  for i in [:avccPkts.size] do
    let sliceNals ← LeanAV.H264Syntax.splitAvccPacket avccPkts[i]! 4
    let nals := if i == 0 then #[spsNal, ppsNal] ++ sliceNals else sliceNals
    aus := aus.push (LeanAV.H264Entropy.joinAnnexB nals)
  some aus

/-- Decode an ISOBMFF `mp4a` AAC-LC audio track into `(pcmChannels, sampleRate, bps)`. -/
def decodeMp4AacTrackToChannels
    (raw : ByteArray) (aTrk : NativeMp4Track) : Option (Array (Array Int32) × UInt32 × Nat) := do
  if aTrk.stsdFourcc != "mp4a" || aTrk.hasEncrypted || aTrk.multiStsd ||
     aTrk.timescale == 0 || !samplesInBounds raw.size aTrk.samples then
    none
  else
    let esds ← LeanAV.Format.extractMp4StsdMp4aEsdsBox aTrk.stsdBox
    let asc ← LeanAV.AacLc.parseMp4EsdsAsc (ByteSlice.ofByteArray esds)
    if asc.channelConfiguration.toNat == 0 || asc.channelConfiguration.toNat > 2 then
      none
    else
      let mut adtsStream := ByteArray.empty
      for s in aTrk.samples do
        let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
        let f ← LeanAV.AacLc.muxAdtsFrame asc.samplingFrequencyIndex asc.channelConfiguration pkt false
        adtsStream := adtsStream ++ f
      LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray adtsStream) false

/-- Copy an ISOBMFF `mp4a` AAC-LC audio track into a `SynthMp4Track` (`-c:a copy`). -/
def copyMp4AacTrackToSynth (raw : ByteArray) (tr : NativeMp4Track) : Option SynthMp4Track := do
  if tr.stsdFourcc != "mp4a" || tr.hasEncrypted || tr.multiStsd ||
     tr.timescale == 0 || !samplesInBounds raw.size tr.samples then
    none
  else
    let esds ← LeanAV.Format.extractMp4StsdMp4aEsdsBox tr.stsdBox
    let asc ← LeanAV.AacLc.parseMp4EsdsAsc (ByteSlice.ofByteArray esds)
    let entry ← LeanAV.AacLc.buildMp4aSampleEntryBox asc
    let mut copied : Array SynthMp4Sample := Array.mkEmpty tr.samples.size
    for s in tr.samples do
      let pkt := raw.extract s.fileOff (s.fileOff + s.byteLen)
      if pkt.size == 0 then none
      copied := copied.push { data := pkt, dur := s.dur, cttsOff := 0, isSync := true }
    some {
      kind := .audio
      timescale := tr.timescale
      width := 0
      height := 0
      stsdBox := LeanAV.Format.buildMp4aStsdBoxFromEntry entry
      samples := copied
    }

/-- Encode per-channel 16-bit PCM into an ISOBMFF `mp4a` `SynthMp4Track`. -/
def encodeChannelsToMp4AacTrack
    (pcmChans : Array (Array Int32)) (sampleRate : UInt32) (bitrateBps : Nat := 128000)
    : Option SynthMp4Track := do
  if pcmChans.isEmpty || pcmChans.size > 2 then none
  else
    let srIdx ← LeanAV.AacLc.aacSampleRateToIndex sampleRate
    let encAdts ← LeanAV.AacLc.aacEncodeAdtsStream pcmChans sampleRate 16 bitrateBps true
    let (_, rawSlices) ← LeanAV.AacLc.demuxAdtsStream (ByteSlice.ofByteArray encAdts) false
    if rawSlices.isEmpty then none
    else
      let mut outSamples : Array SynthMp4Sample := Array.mkEmpty rawSlices.size
      for sl in rawSlices do
        let b := sl.toByteArray
        if b.size == 0 then none
        outSamples := outSamples.push { data := b, dur := 1024, cttsOff := 0, isSync := true }
      let outAsc : LeanAV.AacLc.AacLcAsc := {
        audioObjectType := 2
        samplingFrequencyIndex := srIdx
        channelConfiguration := pcmChans.size.toUInt8
        frameLengthFlag := false
        dependsOnCoreCoder := false
        extensionFlag := false
      }
      let entry ← LeanAV.AacLc.buildMp4aSampleEntryBox outAsc
      some {
        kind := .audio
        timescale := sampleRate.toNat
        width := 0
        height := 0
        stsdBox := LeanAV.Format.buildMp4aStsdBoxFromEntry entry
        samples := outSamples
      }

end LeanAV.InprocTranscode
