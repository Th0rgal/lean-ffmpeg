import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.Video
import LeanAV.Encoder

namespace LeanAV.H264InterDeblockDpb

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream
open LeanAV.Video
open LeanAV.Encoder

@[inline]
def clip3 (lo hi x : Int) : Int :=
  if x < lo then lo else if x > hi then hi else x

@[inline]
def clip1Y (x : Int) : UInt8 :=
  (clip3 0 255 x).toNat.toUInt8

@[inline]
def sampleExt (p : Plane2D) (x y : Int) : Int :=
  if p.width == 0 || p.height == 0 then 0
  else
    let cx := (clip3 0 (Int.ofNat p.width - 1) x).toNat
    let cy := (clip3 0 (Int.ofNat p.height - 1) y).toNat
    Int.ofNat (planePixelD p cy cx).toNat

@[inline]
def h264Tap6 (e f g h i j : Int) : Int :=
  e - 5 * f + 20 * g + 20 * h - 5 * i + j

@[inline]
def h264Round5 (b1 : Int) : Int :=
  clip3 0 255 ((b1 + 16) / 32)

@[inline]
def h264Round6 (j1 : Int) : Int :=
  clip3 0 255 ((j1 + 512) / 1024)

@[inline]
def avgRound (p0 p1 : Int) : Int :=
  (p0 + p1 + 1) / 2

@[inline]
def h264HorizB1 (p : Plane2D) (xInt y : Int) : Int :=
  h264Tap6
    (sampleExt p (xInt - 2) y) (sampleExt p (xInt - 1) y)
    (sampleExt p xInt y)       (sampleExt p (xInt + 1) y)
    (sampleExt p (xInt + 2) y) (sampleExt p (xInt + 3) y)

@[inline]
def h264VertH1 (p : Plane2D) (x yInt : Int) : Int :=
  h264Tap6
    (sampleExt p x (yInt - 2)) (sampleExt p x (yInt - 1))
    (sampleExt p x yInt)       (sampleExt p x (yInt + 1))
    (sampleExt p x (yInt + 2)) (sampleExt p x (yInt + 3))

@[inline]
def h264CenterJ1 (p : Plane2D) (xInt yInt : Int) : Int :=
  h264Tap6
    (h264HorizB1 p xInt (yInt - 2)) (h264HorizB1 p xInt (yInt - 1))
    (h264HorizB1 p xInt yInt)       (h264HorizB1 p xInt (yInt + 1))
    (h264HorizB1 p xInt (yInt + 2)) (h264HorizB1 p xInt (yInt + 3))

def h264CenterJ1Vert (p : Plane2D) (xInt yInt : Int) : Int :=
  h264Tap6
    (h264VertH1 p (xInt - 2) yInt) (h264VertH1 p (xInt - 1) yInt)
    (h264VertH1 p xInt yInt)       (h264VertH1 p (xInt + 1) yInt)
    (h264VertH1 p (xInt + 2) yInt) (h264VertH1 p (xInt + 3) yInt)

def h264LumaFracInt (p : Plane2D) (xInt yInt : Int) (xFracL yFracL : Nat) : Int :=
  let g  := sampleExt p xInt yInt
  let m  := sampleExt p (xInt + 1) yInt
  let s0 := sampleExt p xInt (yInt + 1)
  let b  := h264Round5 (h264HorizB1 p xInt yInt)
  let s  := h264Round5 (h264HorizB1 p xInt (yInt + 1))
  let h  := h264Round5 (h264VertH1 p xInt yInt)
  let mV := h264Round5 (h264VertH1 p (xInt + 1) yInt)
  let j  := h264Round6 (h264CenterJ1 p xInt yInt)
  match xFracL % 4, yFracL % 4 with
  | 0, 0 => g
  | 1, 0 => avgRound g b
  | 2, 0 => b
  | 3, 0 => avgRound b m
  | 0, 1 => avgRound g h
  | 1, 1 => avgRound b h
  | 2, 1 => avgRound b j
  | 3, 1 => avgRound b mV
  | 0, 2 => h
  | 1, 2 => avgRound h j
  | 2, 2 => j
  | 3, 2 => avgRound j mV
  | 0, 3 => avgRound h s0
  | 1, 3 => avgRound h s
  | 2, 3 => avgRound j s
  | _, _ => avgRound s mV

@[inline]
def h264LumaFrac (p : Plane2D) (xInt yInt : Int) (xFracL yFracL : Nat) : UInt8 :=
  let xf := xFracL % 4
  let yf := yFracL % 4
  if xf == 2 && yf == 0 then
    h264HalfPel6Tap
      (clip1Y (sampleExt p (xInt - 2) yInt)) (clip1Y (sampleExt p (xInt - 1) yInt))
      (clip1Y (sampleExt p xInt yInt))       (clip1Y (sampleExt p (xInt + 1) yInt))
      (clip1Y (sampleExt p (xInt + 2) yInt)) (clip1Y (sampleExt p (xInt + 3) yInt))
  else if xf == 0 && yf == 2 then
    h264HalfPel6Tap
      (clip1Y (sampleExt p xInt (yInt - 2))) (clip1Y (sampleExt p xInt (yInt - 1)))
      (clip1Y (sampleExt p xInt yInt))       (clip1Y (sampleExt p xInt (yInt + 1)))
      (clip1Y (sampleExt p xInt (yInt + 2))) (clip1Y (sampleExt p xInt (yInt + 3)))
  else
    clip1Y (h264LumaFracInt p xInt yInt xf yf)

@[inline]
def h264LumaQpel (p : Plane2D) (xQ yQ : Int) : UInt8 :=
  let xInt := xQ / 4
  let yInt := yQ / 4
  let xFrac := (xQ - 4 * xInt).toNat
  let yFrac := (yQ - 4 * yInt).toNat
  h264LumaFrac p xInt yInt xFrac yFrac

@[inline]
def h264ChromaFracInt (p : Plane2D) (xIntC yIntC : Int) (xFracC yFracC : Nat) : Int :=
  let xf := Int.ofNat (xFracC % 8)
  let yf := Int.ofNat (yFracC % 8)
  let a := sampleExt p xIntC yIntC
  let b := sampleExt p (xIntC + 1) yIntC
  let c := sampleExt p xIntC (yIntC + 1)
  let d := sampleExt p (xIntC + 1) (yIntC + 1)
  ((8 - xf) * (8 - yf) * a + xf * (8 - yf) * b +
   (8 - xf) * yf * c + xf * yf * d + 32) / 64

@[inline]
def h264ChromaFrac (p : Plane2D) (xIntC yIntC : Int) (xFracC yFracC : Nat) : UInt8 :=
  clip1Y (h264ChromaFracInt p xIntC yIntC xFracC yFracC)

@[inline]
def h264ChromaOpel420 (p : Plane2D) (xC yC mvX mvY : Int) : UInt8 :=
  let posX := 8 * xC + mvX
  let posY := 8 * yC + mvY
  let xIntC := posX / 8
  let yIntC := posY / 8
  h264ChromaFrac p xIntC yIntC (posX - 8 * xIntC).toNat (posY - 8 * yIntC).toNat

inductive H264PartShape where
  | p16x16
  | p16x8
  | p8x16
  | p8x8
  | p8x4
  | p4x8
  | p4x4
  deriving Repr, DecidableEq, Inhabited

def partSize : H264PartShape → Nat × Nat
  | .p16x16 => (16, 16)
  | .p16x8  => (16, 8)
  | .p8x16  => (8, 16)
  | .p8x8   => (8, 8)
  | .p8x4   => (8, 4)
  | .p4x8   => (4, 8)
  | .p4x4   => (4, 4)

def predL0LumaBlock (refP : Plane2D) (x0 y0 : Nat) (shape : H264PartShape) (mvX mvY : Int) : Plane2D := Id.run do
  let (bw, bh) := partSize shape
  let mut out := Plane2D.alloc bw bh bw 0
  for r in [:bh] do
    for c in [:bw] do
      let xQ := 4 * Int.ofNat (x0 + c) + mvX
      let yQ := 4 * Int.ofNat (y0 + r) + mvY
      out := out.setPixel r c (h264LumaQpel refP xQ yQ)
  return out

def predL0ChromaBlock420 (refP : Plane2D) (x0C y0C : Nat) (shape : H264PartShape) (mvX mvY : Int) : Plane2D := Id.run do
  let (bwL, bhL) := partSize shape
  let bw := Nat.max 1 (bwL / 2)
  let bh := Nat.max 1 (bhL / 2)
  let mut out := Plane2D.alloc bw bh bw 0
  for r in [:bh] do
    for c in [:bw] do
      out := out.setPixel r c (h264ChromaOpel420 refP (Int.ofNat (x0C + c)) (Int.ofNat (y0C + r)) mvX mvY)
  return out

@[inline]
def biPredSample (pL0 pL1 : UInt8) : UInt8 :=
  mcBiPredPixel pL0 pL1

def biPredBlock (b0 b1 : Plane2D) : Plane2D := Id.run do
  let bw := Nat.min b0.width b1.width
  let bh := Nat.min b0.height b1.height
  let mut out := Plane2D.alloc bw bh bw 0
  for r in [:bh] do
    for c in [:bw] do
      out := out.setPixel r c (mcBiPredPixel (b0.getPixel r c) (b1.getPixel r c))
  return out

@[inline]
def weightedUniPredPixel (p0 : UInt8) (w0 o0 : Int) (log2Wd : Nat) : UInt8 :=
  let val :=
    if log2Wd >= 1 then
      let round : Int := Int.ofNat (1 <<< (log2Wd - 1))
      ((Int.ofNat p0.toNat * w0 + round) / Int.ofNat (1 <<< log2Wd)) + o0
    else
      Int.ofNat p0.toNat * w0 + o0
  clip1Y val

@[inline]
def weightedBiPredPixelSpec (p0 p1 : UInt8) (w0 w1 o0 o1 : Int) (log2Wd : Nat) : UInt8 :=
  mcWeightedBiPredPixel p0 p1 (Int32.ofInt w0) (Int32.ofInt w1) (Int32.ofInt o0) (Int32.ofInt o1) log2Wd

def implicitBiWeightScaleFactor (pocCur poc0 poc1 : Int) : Option (Int × Int) :=
  let tb := clip3 (-128) 127 (pocCur - poc0)
  let td := clip3 (-128) 127 (poc1 - poc0)
  if td == 0 then none
  else
    let tx := (Int.ofNat (16384 + td.natAbs / 2)).tdiv td
    let dsf := clip3 (-1024) 1023 ((tb * tx + 32) / 64)
    let w1 := dsf / 4
    if w1 < -64 || w1 > 128 then none
    else some (64 - w1, w1)

def implicitWeightedBiPredPixel (p0 p1 : UInt8) (pocCur poc0 poc1 : Int) : UInt8 :=
  match implicitBiWeightScaleFactor pocCur poc0 poc1 with
  | none => mcBiPredPixel p0 p1
  | some (w0, w1) =>
    clip1Y ((Int.ofNat p0.toNat * w0 + Int.ofNat p1.toNat * w1 + 32) / 64)

structure MotionVec where
  x : Int
  y : Int
  deriving Repr, DecidableEq, Inhabited

structure NeighborMv where
  avail  : Bool
  refIdx : Int
  mv     : MotionVec
  deriving Repr, DecidableEq, Inhabited

@[inline]
def median3 (a b c : Int) : Int :=
  a + b + c - min a (min b c) - max a (max b c)

def mvpMedian (targetRef : Int) (nbA nbB nbC : NeighborMv) (shape : H264PartShape := .p16x16)
    (partIdx : Nat := 0) : MotionVec :=
  let rA := if nbA.avail then nbA.refIdx else -1
  let rB := if nbB.avail then nbB.refIdx else -1
  let rC := if nbC.avail then nbC.refIdx else -1
  let mA := if nbA.avail then nbA.mv else ⟨0, 0⟩
  let mB := if nbB.avail then nbB.mv else ⟨0, 0⟩
  let mC := if nbC.avail then nbC.mv else ⟨0, 0⟩
  if shape == .p16x8 && partIdx == 0 && rB == targetRef then mB
  else if shape == .p16x8 && partIdx == 1 && rA == targetRef then mA
  else if shape == .p8x16 && partIdx == 0 && rA == targetRef then mA
  else if shape == .p8x16 && partIdx == 1 && rC == targetRef then mC
  else if !nbB.avail && !nbC.avail && nbA.avail then mA
  else
    let matchA := rA == targetRef
    let matchB := rB == targetRef
    let matchC := rC == targetRef
    if matchA && !matchB && !matchC then mA
    else if !matchA && matchB && !matchC then mB
    else if !matchA && !matchB && matchC then mC
    else ⟨median3 mA.x mB.x mC.x, median3 mA.y mB.y mC.y⟩

def pSkipMv (atLeftOrTopSliceEdge : Bool) (nbA nbB nbC : NeighborMv) : MotionVec :=
  if atLeftOrTopSliceEdge then ⟨0, 0⟩
  else if !nbA.avail || !nbB.avail then ⟨0, 0⟩
  else if (nbA.refIdx == 0 && nbA.mv == ⟨0, 0⟩) || (nbB.refIdx == 0 && nbB.mv == ⟨0, 0⟩) then ⟨0, 0⟩
  else mvpMedian 0 nbA nbB nbC .p16x16 0

def selectMinPosRef (rA rB rC : Int) : Int :=
  let cands := [rA, rB, rC].filter (· >= 0)
  match cands with
  | [] => -1
  | r :: rs => rs.foldl min r

structure DirectPredResult where
  refIdxL0 : Int
  refIdxL1 : Int
  mvL0     : MotionVec
  mvL1     : MotionVec
  predFlagL0 : Bool
  predFlagL1 : Bool
  deriving Repr, DecidableEq, Inhabited

def bDirectSpatial (nbL0A nbL0B nbL0C nbL1A nbL1B nbL1C : NeighborMv)
    (colZeroFlag : Bool) : DirectPredResult :=
  let r0 := selectMinPosRef
    (if nbL0A.avail then nbL0A.refIdx else -1)
    (if nbL0B.avail then nbL0B.refIdx else -1)
    (if nbL0C.avail then nbL0C.refIdx else -1)
  let r1 := selectMinPosRef
    (if nbL1A.avail then nbL1A.refIdx else -1)
    (if nbL1B.avail then nbL1B.refIdx else -1)
    (if nbL1C.avail then nbL1C.refIdx else -1)
  if r0 < 0 && r1 < 0 then
    { refIdxL0 := 0, refIdxL1 := 0, mvL0 := ⟨0, 0⟩, mvL1 := ⟨0, 0⟩,
      predFlagL0 := true, predFlagL1 := true }
  else
    let mv0Base := if r0 >= 0 then mvpMedian r0 nbL0A nbL0B nbL0C .p16x16 0 else ⟨0, 0⟩
    let mv1Base := if r1 >= 0 then mvpMedian r1 nbL1A nbL1B nbL1C .p16x16 0 else ⟨0, 0⟩
    let mv0 := if r0 == 0 && colZeroFlag && mv0Base.x.natAbs ≤ 1 && mv0Base.y.natAbs ≤ 1 then ⟨0, 0⟩ else mv0Base
    let mv1 := if r1 == 0 && colZeroFlag && mv1Base.x.natAbs ≤ 1 && mv1Base.y.natAbs ≤ 1 then ⟨0, 0⟩ else mv1Base
    { refIdxL0 := r0, refIdxL1 := r1, mvL0 := mv0, mvL1 := mv1,
      predFlagL0 := r0 >= 0, predFlagL1 := r1 >= 0 }

def bDirectTemporal (mvCol : MotionVec) (refIdxL0 : Int) (pocCur poc0 poc1 : Int) : DirectPredResult :=
  let tb := clip3 (-128) 127 (pocCur - poc0)
  let td := clip3 (-128) 127 (poc1 - poc0)
  if td == 0 then
    { refIdxL0 := refIdxL0, refIdxL1 := 0, mvL0 := mvCol, mvL1 := ⟨0, 0⟩,
      predFlagL0 := true, predFlagL1 := true }
  else
    let tx := (Int.ofNat (16384 + td.natAbs / 2)).tdiv td
    let dsf := clip3 (-1024) 1023 ((tb * tx + 32) / 64)
    let mvL0X := (dsf * mvCol.x + 128) / 256
    let mvL0Y := (dsf * mvCol.y + 128) / 256
    let mvL0 : MotionVec := ⟨mvL0X, mvL0Y⟩
    let mvL1 : MotionVec := ⟨mvL0X - mvCol.x, mvL0Y - mvCol.y⟩
    { refIdxL0 := refIdxL0, refIdxL1 := 0, mvL0 := mvL0, mvL1 := mvL1,
      predFlagL0 := true, predFlagL1 := true }

def expGolombSignedBits (v : Int) : Nat :=
  let codeNum : Nat := if v == 0 then 0 else if v > 0 then 2 * v.natAbs - 1 else 2 * v.natAbs
  let val1 := codeNum + 1
  let rec bitLen (n acc : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 => if n ≤ 1 then acc else bitLen (n / 2) (acc + 1) f
  let lz := bitLen val1 0 32
  2 * lz + 1

def mvdRateBits (mv mvp : MotionVec) : Nat :=
  expGolombSignedBits (mv.x - mvp.x) + expGolombSignedBits (mv.y - mvp.y)

def qpelBlockSad (src refP : Plane2D) (x0 y0 bw bh : Nat) (mvX mvY : Int) : Nat :=
  (List.range bh).foldl (fun accR r =>
    (List.range bw).foldl (fun accC c =>
      let sPx := (src.getPixel (y0 + r) (x0 + c)).toNat
      let rPx := (h264LumaQpel refP (4 * Int.ofNat (x0 + c) + mvX) (4 * Int.ofNat (y0 + r) + mvY)).toNat
      accC + absDiffNat sPx rPx) accR) 0

structure MotionEstResult where
  mv       : MotionVec
  sad      : Nat
  rdCost   : Nat
  deriving Repr, DecidableEq, Inhabited

def subpelNeighborOffsets (step : Int) : List (Int × Int) :=
  [(-step, -step), (0, -step), (step, -step),
   (-step, 0),                 (step, 0),
   (-step, step),  (0, step),  (step, step)]

def refineMotionSubpel (src refP : Plane2D) (x0 y0 bw bh : Nat) (intDx intDy : Int)
    (mvp : MotionVec := ⟨0, 0⟩) (lambda : Nat := 1) : MotionEstResult :=
  let initMv : MotionVec := ⟨4 * intDx, 4 * intDy⟩
  let initSad := qpelBlockSad src refP x0 y0 bw bh initMv.x initMv.y
  let initRes : MotionEstResult := {
    mv := initMv, sad := initSad,
    rdCost := rdoSelectModeCost initSad lambda (mvdRateBits initMv mvp)
  }
  let halfRes := (subpelNeighborOffsets 2).foldl (fun best (dx, dy) =>
    let cand : MotionVec := ⟨initRes.mv.x + dx, initRes.mv.y + dy⟩
    let sad := qpelBlockSad src refP x0 y0 bw bh cand.x cand.y
    let cost := rdoSelectModeCost sad lambda (mvdRateBits cand mvp)
    if cost < best.rdCost then { mv := cand, sad := sad, rdCost := cost } else best) initRes
  (subpelNeighborOffsets 1).foldl (fun best (dx, dy) =>
    let cand : MotionVec := ⟨halfRes.mv.x + dx, halfRes.mv.y + dy⟩
    let sad := qpelBlockSad src refP x0 y0 bw bh cand.x cand.y
    let cost := rdoSelectModeCost sad lambda (mvdRateBits cand mvp)
    if cost < best.rdCost then { mv := cand, sad := sad, rdCost := cost } else best) halfRes

def estimateMotionSubpel (src refP : Plane2D) (x0 y0 bw bh radius : Nat)
    (mvp : MotionVec := ⟨0, 0⟩) (lambda : Nat := 1) : MotionEstResult :=
  let (intDx, intDy, _) := searchDiamondMotionVector src refP x0 y0 bw bh radius
  refineMotionSubpel src refP x0 y0 bw bh intDx intDy mvp lambda

def estimateMotionP16x16 (src refP : Plane2D) (x0 y0 : Nat) (radius : Nat := 8)
    (mvp : MotionVec := ⟨0, 0⟩) (lambda : Nat := 1) : MotionEstResult :=
  estimateMotionSubpel src refP x0 y0 16 16 radius mvp lambda

def estimateMotionP8x8 (src refP : Plane2D) (x0 y0 : Nat) (radius : Nat := 8)
    (mvp : MotionVec := ⟨0, 0⟩) (lambda : Nat := 1) : MotionEstResult :=
  estimateMotionSubpel src refP x0 y0 8 8 radius mvp lambda

def h264AlphaTable : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  4, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 17, 20, 22, 25, 28,
  32, 36, 40, 45, 50, 56, 63, 71, 80, 90, 101, 113, 127, 144, 162, 182,
  203, 226, 255, 255
]

def h264BetaTable : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 6, 6, 7, 7, 8, 8,
  9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16,
  17, 17, 18, 18
]

def h264Tc0Table1 : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8,
  9, 10, 11, 13
]

def h264Tc0Table2 : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
  2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 7, 8, 8, 10, 11,
  12, 13, 15, 17
]

def h264Tc0Table3 : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3,
  3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 10, 11, 13, 14, 16,
  18, 20, 23, 25
]

@[inline]
def deblockIndexA (qPav : Int) (alphaOffsetDiv2 : Int) : Nat :=
  (clip3 0 51 (qPav + 2 * alphaOffsetDiv2)).toNat

@[inline]
def deblockIndexB (qPav : Int) (betaOffsetDiv2 : Int) : Nat :=
  (clip3 0 51 (qPav + 2 * betaOffsetDiv2)).toNat

@[inline]
def lookupAlpha (idxA : Nat) : Int :=
  h264AlphaTable.getD (Nat.min 51 idxA) 0

@[inline]
def lookupBeta (idxB : Nat) : Int :=
  h264BetaTable.getD (Nat.min 51 idxB) 0

@[inline]
def lookupTc0 (idxA bS : Nat) : Int :=
  let i := Nat.min 51 idxA
  match bS with
  | 1 => h264Tc0Table1.getD i 0
  | 2 => h264Tc0Table2.getD i 0
  | 3 => h264Tc0Table3.getD i 0
  | _ => 0

def bSFromFlags (isMbEdge intraP intraQ codedP codedQ refDiffOrMvDiffGe4 : Bool) : Nat :=
  if intraP || intraQ then
    if isMbEdge then 4 else 3
  else if codedP || codedQ then 2
  else if refDiffOrMvDiffGe4 then 1
  else 0

def skipInternalEdge8x8 (transformSize8x8 : Bool) (localCoord : Nat) : Bool :=
  transformSize8x8 && (localCoord % 16 == 4 || localCoord % 16 == 12)

def shouldFilterEdge (disableDeblockingFilterIdc : Nat) (isSliceBoundary : Bool)
    (transformSize8x8 : Bool) (localCoord : Nat) (bS : Nat) : Bool :=
  if disableDeblockingFilterIdc == 1 then false
  else if disableDeblockingFilterIdc >= 3 then false
  else if disableDeblockingFilterIdc == 2 && isSliceBoundary then false
  else if bS == 0 || bS > 4 then false
  else if skipInternalEdge8x8 transformSize8x8 localCoord then false
  else true

structure DeblockSamples8 where
  p3 : UInt8
  p2 : UInt8
  p1 : UInt8
  p0 : UInt8
  q0 : UInt8
  q1 : UInt8
  q2 : UInt8
  q3 : UInt8
  deriving Repr, DecidableEq, Inhabited

def filterLumaSamples8 (s : DeblockSamples8) (bS : Nat) (qPav alphaOffDiv2 betaOffDiv2 : Int) : DeblockSamples8 :=
  if bS == 0 || bS > 4 then s
  else
    let idxA := deblockIndexA qPav alphaOffDiv2
    let idxB := deblockIndexB qPav betaOffDiv2
    let alpha := lookupAlpha idxA
    let beta  := lookupBeta idxB
    let p3 := Int.ofNat s.p3.toNat
    let p2 := Int.ofNat s.p2.toNat
    let p1 := Int.ofNat s.p1.toNat
    let p0 := Int.ofNat s.p0.toNat
    let q0 := Int.ofNat s.q0.toNat
    let q1 := Int.ofNat s.q1.toNat
    let q2 := Int.ofNat s.q2.toNat
    let q3 := Int.ofNat s.q3.toNat
    let ap := Int.ofNat (p2 - p0).natAbs
    let aq := Int.ofNat (q2 - q0).natAbs
    if !(Int.ofNat (p0 - q0).natAbs < alpha &&
         Int.ofNat (p1 - p0).natAbs < beta &&
         Int.ofNat (q1 - q0).natAbs < beta) then s
    else if bS == 4 then
      let smallGap := Int.ofNat (p0 - q0).natAbs < (alpha / 4) + 2
      let (np0, np1, np2) :=
        if ap < beta && smallGap then
          ((p2 + 2 * p1 + 2 * p0 + 2 * q0 + q1 + 4) / 8,
           (p2 + p1 + p0 + q0 + 2) / 4,
           (2 * p3 + 3 * p2 + p1 + p0 + q0 + 4) / 8)
        else
          ((2 * p1 + p0 + q1 + 2) / 4, p1, p2)
      let (nq0, nq1, nq2) :=
        if aq < beta && smallGap then
          ((p1 + 2 * p0 + 2 * q0 + 2 * q1 + q2 + 4) / 8,
           (p0 + q0 + q1 + q2 + 2) / 4,
           (2 * q3 + 3 * q2 + q1 + q0 + p0 + 4) / 8)
        else
          ((2 * q1 + q0 + p1 + 2) / 4, q1, q2)
      { s with p2 := clip1Y np2, p1 := clip1Y np1, p0 := clip1Y np0,
               q0 := clip1Y nq0, q1 := clip1Y nq1, q2 := clip1Y nq2 }
    else
      let tc0 := lookupTc0 idxA bS
      let tc := tc0 + (if ap < beta then 1 else 0) + (if aq < beta then 1 else 0)
      let delta := clip3 (-tc) tc ((4 * (q0 - p0) + (p1 - q1) + 4) / 8)
      let np0 := clip1Y (p0 + delta)
      let nq0 := clip1Y (q0 - delta)
      let np1 :=
        if ap < beta then
          let dp1 := clip3 (-tc0) tc0 ((p2 + ((p0 + q0 + 1) / 2) - 2 * p1) / 2)
          clip1Y (p1 + dp1)
        else s.p1
      let nq1 :=
        if aq < beta then
          let dq1 := clip3 (-tc0) tc0 ((q2 + ((p0 + q0 + 1) / 2) - 2 * q1) / 2)
          clip1Y (q1 + dq1)
        else s.q1
      { s with p1 := np1, p0 := np0, q0 := nq0, q1 := nq1 }

def filterChromaSamples4 (p1u p0u q0u q1u : UInt8) (bS : Nat) (qPav alphaOffDiv2 betaOffDiv2 : Int) :
    UInt8 × UInt8 :=
  if bS == 0 || bS > 4 then (p0u, q0u)
  else
    let idxA := deblockIndexA qPav alphaOffDiv2
    let idxB := deblockIndexB qPav betaOffDiv2
    let alpha := lookupAlpha idxA
    let beta  := lookupBeta idxB
    let p1 := Int.ofNat p1u.toNat
    let p0 := Int.ofNat p0u.toNat
    let q0 := Int.ofNat q0u.toNat
    let q1 := Int.ofNat q1u.toNat
    if !(Int.ofNat (p0 - q0).natAbs < alpha &&
         Int.ofNat (p1 - p0).natAbs < beta &&
         Int.ofNat (q1 - q0).natAbs < beta) then (p0u, q0u)
    else if bS == 4 then
      (clip1Y ((2 * p1 + p0 + q1 + 2) / 4), clip1Y ((2 * q1 + q0 + p1 + 2) / 4))
    else
      let tc := lookupTc0 idxA bS + 1
      let delta := clip3 (-tc) tc ((4 * (q0 - p0) + (p1 - q1) + 4) / 8)
      (clip1Y (p0 + delta), clip1Y (q0 - delta))

structure DeblockMbConfig where
  disableIdc       : Nat := 0
  alphaOffDiv2     : Int := 0
  betaOffDiv2      : Int := 0
  qPav             : Int := 26
  transformSize8x8 : Bool := false
  bSInternal       : Nat := 2
  bSMbEdge         : Nat := 4
  deriving Repr, DecidableEq, Inhabited

def deblockVertEdge4 (p : Plane2D) (edgeX yStart count bS : Nat) (qPav aOff bOff : Int) : Plane2D := Id.run do
  if edgeX < 4 || edgeX + 4 > p.width then return p
  let mut dst := p
  for i in [:count] do
    let y := yStart + i
    if y < dst.height then
      let sIn : DeblockSamples8 := {
        p3 := dst.getPixel y (edgeX - 4), p2 := dst.getPixel y (edgeX - 3),
        p1 := dst.getPixel y (edgeX - 2), p0 := dst.getPixel y (edgeX - 1),
        q0 := dst.getPixel y edgeX,       q1 := dst.getPixel y (edgeX + 1),
        q2 := dst.getPixel y (edgeX + 2), q3 := dst.getPixel y (edgeX + 3)
      }
      let sOut := filterLumaSamples8 sIn bS qPav aOff bOff
      dst := dst.setPixel y (edgeX - 3) sOut.p2
      dst := dst.setPixel y (edgeX - 2) sOut.p1
      dst := dst.setPixel y (edgeX - 1) sOut.p0
      dst := dst.setPixel y edgeX       sOut.q0
      dst := dst.setPixel y (edgeX + 1) sOut.q1
      dst := dst.setPixel y (edgeX + 2) sOut.q2
  return dst

def deblockHorizEdge4 (p : Plane2D) (xStart edgeY count bS : Nat) (qPav aOff bOff : Int) : Plane2D := Id.run do
  if edgeY < 4 || edgeY + 4 > p.height then return p
  let mut dst := p
  for i in [:count] do
    let x := xStart + i
    if x < dst.width then
      let sIn : DeblockSamples8 := {
        p3 := dst.getPixel (edgeY - 4) x, p2 := dst.getPixel (edgeY - 3) x,
        p1 := dst.getPixel (edgeY - 2) x, p0 := dst.getPixel (edgeY - 1) x,
        q0 := dst.getPixel edgeY       x, q1 := dst.getPixel (edgeY + 1) x,
        q2 := dst.getPixel (edgeY + 2) x, q3 := dst.getPixel (edgeY + 3) x
      }
      let sOut := filterLumaSamples8 sIn bS qPav aOff bOff
      dst := dst.setPixel (edgeY - 3) x sOut.p2
      dst := dst.setPixel (edgeY - 2) x sOut.p1
      dst := dst.setPixel (edgeY - 1) x sOut.p0
      dst := dst.setPixel edgeY       x sOut.q0
      dst := dst.setPixel (edgeY + 1) x sOut.q1
      dst := dst.setPixel (edgeY + 2) x sOut.q2
  return dst

def deblockMacroblockLuma (p : Plane2D) (mbX mbY : Nat) (cfg : DeblockMbConfig)
    (leftSliceBoundary : Bool := false) (topSliceBoundary : Bool := false) : Plane2D := Id.run do
  if cfg.disableIdc == 1 || cfg.disableIdc >= 3 then return p
  let x0 := mbX * 16
  let y0 := mbY * 16
  let mut cur := p
  for kx in ([0, 4, 8, 12] : List Nat) do
    let edgeX := x0 + kx
    let isMb := kx == 0
    let isSlice := isMb && leftSliceBoundary
    let bS := if isMb then cfg.bSMbEdge else cfg.bSInternal
    if edgeX > 0 && shouldFilterEdge cfg.disableIdc isSlice cfg.transformSize8x8 kx bS then
      cur := deblockVertEdge4 cur edgeX y0 16 bS cfg.qPav cfg.alphaOffDiv2 cfg.betaOffDiv2
  for ky in ([0, 4, 8, 12] : List Nat) do
    let edgeY := y0 + ky
    let isMb := ky == 0
    let isSlice := isMb && topSliceBoundary
    let bS := if isMb then cfg.bSMbEdge else cfg.bSInternal
    if edgeY > 0 && shouldFilterEdge cfg.disableIdc isSlice cfg.transformSize8x8 ky bS then
      cur := deblockHorizEdge4 cur x0 edgeY 16 bS cfg.qPav cfg.alphaOffDiv2 cfg.betaOffDiv2
  return cur

def deblockFrameLumaRaster (p : Plane2D) (cfg : DeblockMbConfig) : Plane2D := Id.run do
  if cfg.disableIdc == 1 || cfg.disableIdc >= 3 then return p
  let mbsW := p.width / 16
  let mbsH := p.height / 16
  let mut cur := p
  for mbY in [:mbsH] do
    for mbX in [:mbsW] do
      cur := deblockMacroblockLuma cur mbX mbY cfg false false
  return cur

inductive DpbRefMark where
  | unused
  | shortTerm (picNum : Int)
  | longTerm (longTermPicIdx : Nat)
  deriving Repr, DecidableEq, Inhabited

structure DpbPicture where
  uid           : Nat
  frameNum      : Nat
  picNum        : Int
  poc           : Int
  mark          : DpbRefMark
  neededForOut  : Bool
  lumaDigest    : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

structure H264Dpb where
  maxRefFrames     : Nat := 4
  maxDpbCapacity   : Nat := 16
  maxFrameNum      : Nat := 16
  maxLongTermIdx   : Int := -1
  nextUid          : Nat := 0
  entries          : List DpbPicture := []
  outputPocLog     : List Int := []
  currCvsPocLog    : List Int := []
  priorCvsMonitor  : Bool := true
  deriving Repr, DecidableEq, Inhabited

@[inline]
def isShortTermRef (pic : DpbPicture) : Bool :=
  match pic.mark with
  | .shortTerm _ => true
  | _ => false

@[inline]
def isLongTermRef (pic : DpbPicture) : Bool :=
  match pic.mark with
  | .longTerm _ => true
  | _ => false

@[inline]
def isUsedForRef (pic : DpbPicture) : Bool :=
  isShortTermRef pic || isLongTermRef pic

def dpbRefCount (dpb : H264Dpb) : Nat :=
  (dpb.entries.filter isUsedForRef).length

def dpbCapacityValid (dpb : H264Dpb) : Bool :=
  decide (dpb.maxDpbCapacity ≥ 1 ∧ dpb.maxDpbCapacity ≤ 16 ∧
          dpb.maxRefFrames ≤ dpb.maxDpbCapacity ∧
          dpb.entries.length ≤ dpb.maxDpbCapacity ∧
          dpbRefCount dpb ≤ dpb.maxRefFrames)

def wrapPicNum (frameNum currFrameNum maxFrameNum : Nat) : Int :=
  let m := if maxFrameNum == 0 then 16 else maxFrameNum
  let fw := if frameNum > currFrameNum then Int.ofNat frameNum - Int.ofNat m else Int.ofNat frameNum
  fw

def refreshShortTermPicNums (entries : List DpbPicture) (currFrameNum maxFrameNum : Nat) : List DpbPicture :=
  entries.map fun p =>
    match p.mark with
    | .shortTerm _ =>
      let pn := wrapPicNum p.frameNum currFrameNum maxFrameNum
      { p with picNum := pn, mark := .shortTerm pn }
    | _ => p

def insertSortedDescPicNum (x : DpbPicture) : List DpbPicture → List DpbPicture
  | [] => [x]
  | y :: ys => if x.picNum >= y.picNum then x :: y :: ys else y :: insertSortedDescPicNum x ys

def insertSortedAscLtIdx (x : DpbPicture) : List DpbPicture → List DpbPicture
  | [] => [x]
  | y :: ys =>
    let ix := match x.mark with | .longTerm i => i | _ => 0
    let iy := match y.mark with | .longTerm i => i | _ => 0
    if ix <= iy then x :: y :: ys else y :: insertSortedAscLtIdx x ys

def insertSortedAscPoc (x : DpbPicture) : List DpbPicture → List DpbPicture
  | [] => [x]
  | y :: ys => if x.poc <= y.poc then x :: y :: ys else y :: insertSortedAscPoc x ys

def insertSortedDescPoc (x : DpbPicture) : List DpbPicture → List DpbPicture
  | [] => [x]
  | y :: ys => if x.poc >= y.poc then x :: y :: ys else y :: insertSortedDescPoc x ys

def buildRefPicListP0 (dpb : H264Dpb) (currFrameNum : Nat) (numActive : Nat) : List DpbPicture :=
  let refreshed := refreshShortTermPicNums dpb.entries currFrameNum dpb.maxFrameNum
  let st := (refreshed.filter isShortTermRef).foldl (fun acc p => insertSortedDescPicNum p acc) []
  let lt := (refreshed.filter isLongTermRef).foldl (fun acc p => insertSortedAscLtIdx p acc) []
  (st ++ lt).take numActive

def buildRefPicListsB (dpb : H264Dpb) (currFrameNum : Nat) (currPoc : Int)
    (numActiveL0 numActiveL1 : Nat) : List DpbPicture × List DpbPicture :=
  let refreshed := refreshShortTermPicNums dpb.entries currFrameNum dpb.maxFrameNum
  let stAll := refreshed.filter isShortTermRef
  let stLe := (stAll.filter (fun p => p.poc <= currPoc)).foldl (fun acc p => insertSortedDescPoc p acc) []
  let stGt := (stAll.filter (fun p => p.poc > currPoc)).foldl (fun acc p => insertSortedAscPoc p acc) []
  let stLt := (stAll.filter (fun p => p.poc < currPoc)).foldl (fun acc p => insertSortedDescPoc p acc) []
  let stGe := (stAll.filter (fun p => p.poc >= currPoc)).foldl (fun acc p => insertSortedAscPoc p acc) []
  let lt := (refreshed.filter isLongTermRef).foldl (fun acc p => insertSortedAscLtIdx p acc) []
  let baseL0 := stLe ++ stGt ++ lt
  let rawL1 := stGe ++ stLt ++ lt
  let swappedL1 :=
    if rawL1.length >= 2 && (rawL1.map DpbPicture.uid == baseL0.map DpbPicture.uid) then
      match rawL1 with
      | a :: b :: rest => b :: a :: rest
      | _ => rawL1
    else rawL1
  (baseL0.take numActiveL0, swappedL1.take numActiveL1)

inductive RefListModOp where
  | subPicNum (absDiffMinus1 : Nat)
  | addPicNum (absDiffMinus1 : Nat)
  | longTermPic (longTermPicNum : Nat)
  | endLoop
  deriving Repr, DecidableEq, Inhabited

def placeRefAtIdx (refList : List DpbPicture) (refIdx : Nat) (target : DpbPicture)
    (numActive : Nat) : List DpbPicture :=
  let prefixL := refList.take refIdx
  let suffixL := (refList.drop refIdx).filter (fun p => p.uid != target.uid)
  (prefixL ++ (target :: suffixL)).take numActive

def applyRefPicListMod (dpb : H264Dpb) (initList : List DpbPicture) (currFrameNum : Nat)
    (numActive : Nat) (ops : List RefListModOp) : List DpbPicture :=
  let maxPic := Int.ofNat (if dpb.maxFrameNum == 0 then 16 else dpb.maxFrameNum)
  let refreshed := refreshShortTermPicNums dpb.entries currFrameNum dpb.maxFrameNum
  let rec go (rem : List RefListModOp) (cur : List DpbPicture) (refIdx : Nat) (predPn : Int) : List DpbPicture :=
    match rem with
    | [] => cur.take numActive
    | .endLoop :: _ => cur.take numActive
    | .subPicNum adm1 :: rest =>
      let diff := Int.ofNat adm1 + 1
      let pnNoWrap := if predPn - diff < 0 then predPn - diff + maxPic else predPn - diff
      let pn := if pnNoWrap > Int.ofNat currFrameNum then pnNoWrap - maxPic else pnNoWrap
      match refreshed.find? (fun p => isShortTermRef p && p.picNum == pn) with
      | some tgt => go rest (placeRefAtIdx cur refIdx tgt numActive) (refIdx + 1) pnNoWrap
      | none     => go rest cur (refIdx + 1) pnNoWrap
    | .addPicNum adm1 :: rest =>
      let diff := Int.ofNat adm1 + 1
      let pnNoWrap := if predPn + diff >= maxPic then predPn + diff - maxPic else predPn + diff
      let pn := if pnNoWrap > Int.ofNat currFrameNum then pnNoWrap - maxPic else pnNoWrap
      match refreshed.find? (fun p => isShortTermRef p && p.picNum == pn) with
      | some tgt => go rest (placeRefAtIdx cur refIdx tgt numActive) (refIdx + 1) pnNoWrap
      | none     => go rest cur (refIdx + 1) pnNoWrap
    | .longTermPic ltNum :: rest =>
      match refreshed.find? (fun p => p.mark == .longTerm ltNum) with
      | some tgt => go rest (placeRefAtIdx cur refIdx tgt numActive) (refIdx + 1) predPn
      | none     => go rest cur (refIdx + 1) predPn
  go ops initList 0 (Int.ofNat currFrameNum)

inductive MmcoOp where
  | markShortUnused (diffPicNumsMinus1 : Nat)
  | markLongUnused (longTermPicNum : Nat)
  | assignLongTermIdx (diffPicNumsMinus1 : Nat) (longTermFrameIdx : Nat)
  | setMaxLongTermIdxPlus1 (maxIdxPlus1 : Nat)
  | markAllUnused
  | markCurrLongTerm (longTermFrameIdx : Nat)
  deriving Repr, DecidableEq, Inhabited

def isPocListMonotone : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a <= b) && isPocListMonotone (b :: rest)

def bumpOneDpb (dpb : H264Dpb) : H264Dpb :=
  let outCands := (dpb.entries.filter DpbPicture.neededForOut).foldl (fun acc p => insertSortedAscPoc p acc) []
  match outCands with
  | [] =>
    let pruned := dpb.entries.filter (fun p => isUsedForRef p || p.neededForOut)
    { dpb with entries := pruned }
  | lowest :: _ =>
    let updated := dpb.entries.map (fun p => if p.uid == lowest.uid then { p with neededForOut := false } else p)
    let pruned := updated.filter (fun p => isUsedForRef p || p.neededForOut)
    { dpb with
      entries := pruned,
      outputPocLog := dpb.outputPocLog ++ [lowest.poc],
      currCvsPocLog := dpb.currCvsPocLog ++ [lowest.poc] }

def bumpToCapacity (dpb : H264Dpb) (fuel : Nat := 32) : H264Dpb :=
  match fuel with
  | 0 => dpb
  | f + 1 =>
    if dpb.entries.length < dpb.maxDpbCapacity then dpb
    else
      let next := bumpOneDpb dpb
      if next.entries.length >= dpb.entries.length &&
         !(next.entries.any DpbPicture.neededForOut) then next
      else bumpToCapacity next f

def bumpLowerPocUntilSpace (dpb : H264Dpb) (currPoc : Int) (fuel : Nat := 32) : H264Dpb :=
  match fuel with
  | 0 => dpb
  | f + 1 =>
    if dpb.entries.length < dpb.maxDpbCapacity then dpb
    else
      let outCands := (dpb.entries.filter DpbPicture.neededForOut).foldl (fun acc p => insertSortedAscPoc p acc) []
      match outCands with
      | [] =>
        let pruned := dpb.entries.filter (fun p => isUsedForRef p || p.neededForOut)
        { dpb with entries := pruned }
      | lowest :: _ =>
        if lowest.poc < currPoc then
          bumpLowerPocUntilSpace (bumpOneDpb dpb) currPoc f
        else
          dpb

def flushDpb (dpb : H264Dpb) : H264Dpb :=
  let outCands := (dpb.entries.filter DpbPicture.neededForOut).foldl (fun acc p => insertSortedAscPoc p acc) []
  let outPocs := outCands.map DpbPicture.poc
  let finalCvs := dpb.currCvsPocLog ++ outPocs
  { dpb with
    entries := [],
    maxLongTermIdx := -1,
    outputPocLog := dpb.outputPocLog ++ outPocs,
    currCvsPocLog := [],
    priorCvsMonitor := dpb.priorCvsMonitor && isPocListMonotone finalCvs }

def clearIdrDpb (dpb : H264Dpb) (noOutputOfPriorPics : Bool) (longTermRefFlag : Bool)
    (idrPoc : Int := 0) (lumaDigest : UInt64 := 0) : H264Dpb :=
  let base :=
    if noOutputOfPriorPics then
      { dpb with
        entries := [],
        maxLongTermIdx := if longTermRefFlag && dpb.maxRefFrames > 0 then 0 else -1,
        currCvsPocLog := [],
        priorCvsMonitor := dpb.priorCvsMonitor && isPocListMonotone dpb.currCvsPocLog }
    else
      let fl := flushDpb dpb
      { fl with maxLongTermIdx := if longTermRefFlag && dpb.maxRefFrames > 0 then 0 else -1 }
  let mark : DpbRefMark :=
    if base.maxRefFrames == 0 then .unused
    else if longTermRefFlag then .longTerm 0 else .shortTerm 0
  let idrPic : DpbPicture := {
    uid := base.nextUid, frameNum := 0, picNum := 0, poc := idrPoc,
    mark := mark, neededForOut := true, lumaDigest := lumaDigest
  }
  { base with nextUid := base.nextUid + 1, entries := [idrPic].take base.maxDpbCapacity }

def slidingWindowMark (dpb : H264Dpb) (currFrameNum : Nat) : H264Dpb :=
  let refreshed := refreshShortTermPicNums dpb.entries currFrameNum dpb.maxFrameNum
  let numShort := (refreshed.filter isShortTermRef).length
  let numLong  := (refreshed.filter isLongTermRef).length
  if dpb.maxRefFrames == 0 || numShort + numLong < dpb.maxRefFrames || numShort == 0 then
    { dpb with entries := refreshed }
  else
    let stSorted := (refreshed.filter isShortTermRef).foldl (fun acc p => insertSortedDescPicNum p acc) []
    match stSorted.reverse with
    | [] => { dpb with entries := refreshed }
    | smallest :: _ =>
      let marked := refreshed.map fun p =>
        if p.uid == smallest.uid then { p with mark := .unused } else p
      let pruned := marked.filter (fun p => isUsedForRef p || p.neededForOut)
      { dpb with entries := pruned }

def applySingleMmco (dpb : H264Dpb) (currFrameNum : Nat) (currMark : DpbRefMark)
    (mmco5Seen : Bool) (op : MmcoOp) : H264Dpb × DpbRefMark × Bool :=
  let refreshed := refreshShortTermPicNums dpb.entries currFrameNum dpb.maxFrameNum
  let currPn := Int.ofNat currFrameNum
  match op with
  | .markShortUnused dpm1 =>
    let tgtPn := currPn - (Int.ofNat dpm1 + 1)
    let ents := (refreshed.map fun p =>
      if isShortTermRef p && p.picNum == tgtPn then { p with mark := .unused } else p).filter
      (fun p => isUsedForRef p || p.neededForOut)
    ({ dpb with entries := ents }, currMark, mmco5Seen)
  | .markLongUnused ltPn =>
    let ents := (refreshed.map fun p =>
      if p.mark == .longTerm ltPn then { p with mark := .unused } else p).filter
      (fun p => isUsedForRef p || p.neededForOut)
    ({ dpb with entries := ents }, currMark, mmco5Seen)
  | .assignLongTermIdx dpm1 ltIdx =>
    if Int.ofNat ltIdx > dpb.maxLongTermIdx then
      ({ dpb with entries := refreshed }, currMark, mmco5Seen)
    else
      let tgtPn := currPn - (Int.ofNat dpm1 + 1)
      let cleared := refreshed.map fun p =>
        if p.mark == .longTerm ltIdx then { p with mark := .unused } else p
      let assigned := cleared.map fun p =>
        if isShortTermRef p && p.picNum == tgtPn then { p with mark := .longTerm ltIdx } else p
      let ents := assigned.filter (fun p => isUsedForRef p || p.neededForOut)
      ({ dpb with entries := ents }, currMark, mmco5Seen)
  | .setMaxLongTermIdxPlus1 mPlus1 =>
    let newMax : Int := if mPlus1 == 0 then -1 else Int.ofNat mPlus1 - 1
    let ents := (refreshed.map fun p =>
      match p.mark with
      | .longTerm idx => if Int.ofNat idx > newMax then { p with mark := .unused } else p
      | _ => p).filter (fun p => isUsedForRef p || p.neededForOut)
    ({ dpb with entries := ents, maxLongTermIdx := newMax }, currMark, mmco5Seen)
  | .markAllUnused =>
    let ents := (refreshed.map fun p => { p with mark := .unused }).filter DpbPicture.neededForOut
    let newCurrMark := match currMark with
      | .shortTerm _ => .shortTerm 0
      | other => other
    ({ dpb with entries := ents, maxLongTermIdx := -1 }, newCurrMark, true)
  | .markCurrLongTerm ltIdx =>
    if Int.ofNat ltIdx > dpb.maxLongTermIdx then
      ({ dpb with entries := refreshed }, currMark, mmco5Seen)
    else
      let ents := (refreshed.map fun p =>
        if p.mark == .longTerm ltIdx then { p with mark := .unused } else p).filter
        (fun p => isUsedForRef p || p.neededForOut)
      ({ dpb with entries := ents }, .longTerm ltIdx, mmco5Seen)

def insertDecodedPicture (dpb : H264Dpb) (isIdr noOutputPrior longTermIdr isRef : Bool)
    (frameNum : Nat) (poc : Int) (adaptiveMode : Bool) (mmcoOps : List MmcoOp)
    (lumaDigest : UInt64 := 0) : H264Dpb :=
  if isIdr then
    clearIdrDpb dpb noOutputPrior longTermIdr poc lumaDigest
  else
    let pruned0 := dpb.entries.filter (fun p => isUsedForRef p || p.neededForOut)
    let dpb0 := { dpb with entries := pruned0 }
    if !isRef || dpb0.maxRefFrames == 0 then
      let dpb1 := bumpLowerPocUntilSpace dpb0 poc (dpb0.entries.length + 1)
      if dpb1.entries.length < dpb1.maxDpbCapacity then
        let nonRefPic : DpbPicture := {
          uid := dpb1.nextUid, frameNum := frameNum, picNum := Int.ofNat frameNum,
          poc := poc, mark := .unused, neededForOut := true, lumaDigest := lumaDigest
        }
        { dpb1 with nextUid := dpb1.nextUid + 1, entries := dpb1.entries ++ [nonRefPic] }
      else
        { dpb1 with
          nextUid := dpb1.nextUid + 1,
          outputPocLog := dpb1.outputPocLog ++ [poc],
          currCvsPocLog := dpb1.currCvsPocLog ++ [poc] }
    else if !adaptiveMode then
      let dpb2 := slidingWindowMark dpb0 frameNum
      let dpb3 := bumpToCapacity dpb2 (dpb2.entries.length + 1)
      let stPic : DpbPicture := {
        uid := dpb3.nextUid, frameNum := frameNum, picNum := Int.ofNat frameNum,
        poc := poc, mark := .shortTerm (Int.ofNat frameNum), neededForOut := true, lumaDigest := lumaDigest
      }
      { dpb3 with nextUid := dpb3.nextUid + 1, entries := dpb3.entries ++ [stPic] }
    else
      let initMark : DpbRefMark := .shortTerm (Int.ofNat frameNum)
      let (dpb2, finalMark, mmco5) := mmcoOps.foldl
        (fun (st, cm, m5) op => applySingleMmco st frameNum cm m5 op)
        (dpb0, initMark, false)
      let dpb3 :=
        if mmco5 then
          let fl := flushDpb dpb2
          { fl with maxLongTermIdx := dpb2.maxLongTermIdx }
        else bumpToCapacity dpb2 (dpb2.entries.length + 1)
      let effFn := if mmco5 then 0 else frameNum
      let effPoc := if mmco5 then 0 else poc
      let pic : DpbPicture := {
        uid := dpb3.nextUid, frameNum := effFn, picNum := Int.ofNat effFn,
        poc := effPoc, mark := finalMark, neededForOut := true, lumaDigest := lumaDigest
      }
      { dpb3 with nextUid := dpb3.nextUid + 1, entries := dpb3.entries ++ [pic] }

structure AnnexBSpsInfo where
  spsId                     : Nat := 0
  log2MaxFrameNum           : Nat := 4
  picOrderCntType           : Nat := 0
  log2MaxPicOrderCntLsb     : Nat := 4
  deltaPicOrderAlwaysZero   : Bool := false
  offsetForNonRefPic        : Int := 0
  offsetForTopToBottomField : Int := 0
  offsetForRefFrame         : Array Int := #[]
  maxNumRefFrames           : Nat := 4
  frameMbsOnly              : Bool := true
  separateColourPlane       : Bool := false
  chromaArrayType           : Nat := 1
  deriving Repr, DecidableEq, Inhabited

def skipH264ScalingList (r : BitReader) (remaining : Nat) (lastScale nextScale : Int) : Option BitReader :=
  match remaining with
  | 0 => some r
  | k + 1 =>
    if nextScale != 0 then do
      let (deltaScale, r1) ← r.readSE
      let ns := (lastScale + deltaScale.toInt + 256).emod 256
      let ls := if ns == 0 then lastScale else ns
      skipH264ScalingList r1 k ls ns
    else
      skipH264ScalingList r k lastScale 0

def skipSeqScalingMatrixLoop (r : BitReader) (idx remaining : Nat) : Option BitReader :=
  match remaining with
  | 0 => some r
  | k + 1 => do
    let (presentFlag, r1) ← r.readBit
    let r2 ←
      if presentFlag == 1 then
        let listSize := if idx < 6 then 16 else 64
        skipH264ScalingList r1 listSize 8 8
      else
        some r1
    skipSeqScalingMatrixLoop r2 (idx + 1) k

def skipSeqScalingMatrix (r : BitReader) (idx total : Nat) : Option BitReader :=
  skipSeqScalingMatrixLoop r idx (total - idx)

def readOffsetForRefFrameLoop (r : BitReader) (remaining : Nat) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  match remaining with
  | 0 => some (acc, r)
  | k + 1 => do
    let (v, r1) ← r.readSE
    readOffsetForRefFrameLoop r1 k (acc.push v.toInt)

structure AnnexBPpsInfo where
  ppsId                         : Nat := 0
  spsId                         : Nat := 0
  entropyCodingCabac            : Bool := true
  bottomFieldPicOrder           : Bool := false
  numSliceGroupsMinus1          : Nat := 0
  numRefIdxL0DefaultActive      : Nat := 1
  numRefIdxL1DefaultActive      : Nat := 1
  weightedPredFlag              : Bool := false
  weightedBipredIdc             : Nat := 0
  deblockingFilterControlPresent : Bool := true
  redundantPicCntPresent        : Bool := false
  deriving Repr, DecidableEq, Inhabited

def parseAnnexBSpsFull (nalPayload : ByteSlice) : Option AnnexBSpsInfo := do
  let rbsp := stripRbspEmulationBytes nalPayload
  if rbsp.size < 4 then none
  else if (rbsp.data.getD 0 0 &&& 0x1F) != 7 then none
  else
    let profileIdc := rbsp.data.getD 1 0
    let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 32 }
    let (spsId, r1) ← r0.readUE
    let (rAfterHigh, sepCol, cArr) ←
      if profileIdc == 100 || profileIdc == 110 || profileIdc == 122 || profileIdc == 244 ||
         profileIdc == 44  || profileIdc == 83  || profileIdc == 86  || profileIdc == 118 || profileIdc == 128 then do
        let (chromaIdc, rA) ← r1.readUE
        let (sep, rSep) ←
          if chromaIdc == 3 then do
            let (b, rN) ← rA.readBit
            pure (b == 1, rN)
          else pure (false, rA)
        let (_, rB) ← rSep.readUE
        let (_, rC) ← rB.readUE
        let (_, rD) ← rC.readBit
        let (seqScalePresent, rE) ← rD.readBit
        let rF ←
          if seqScalePresent == 1 then
            skipSeqScalingMatrix rE 0 (if chromaIdc != 3 then 8 else 12)
          else
            pure rE
        let cat := if sep then 0 else chromaIdc.toNat
        pure (rF, sep, cat)
      else pure (r1, false, 1)
    let (log2FnM4, r2) ← rAfterHigh.readUE
    let (pocType, r3) ← r2.readUE
    let (log2PocLsb, deltaZero, offNonRef, offTopBot, offRefArr, rAfterPoc) ←
      if pocType == 0 then do
        let (l4, rP) ← r3.readUE
        pure (l4.toNat + 4, false, (0 : Int), (0 : Int), #[], rP)
      else if pocType == 1 then do
        let (dz, rP1) ← r3.readBit
        let (onr, rP2) ← rP1.readSE
        let (otb, rP3) ← rP2.readSE
        let (nCycle, rP4) ← rP3.readUE
        if nCycle.toNat > 255 then none
        else
          let (arr, rP5) ← readOffsetForRefFrameLoop rP4 nCycle.toNat #[]
          pure (4, dz == 1, onr.toInt, otb.toInt, arr, rP5)
      else pure (4, false, (0 : Int), (0 : Int), #[], r3)
    let (maxRefs, r4) ← rAfterPoc.readUE
    let (_, r5) ← r4.readBit
    let (_, r6) ← r5.readUE
    let (_, r7) ← r6.readUE
    let (fmo, _) ← r7.readBit
    some {
      spsId := spsId.toNat
      log2MaxFrameNum := log2FnM4.toNat + 4
      picOrderCntType := pocType.toNat
      log2MaxPicOrderCntLsb := log2PocLsb
      deltaPicOrderAlwaysZero := deltaZero
      offsetForNonRefPic := offNonRef
      offsetForTopToBottomField := offTopBot
      offsetForRefFrame := offRefArr
      maxNumRefFrames := maxRefs.toNat
      frameMbsOnly := fmo == 1
      separateColourPlane := sepCol
      chromaArrayType := cArr
    }

def parseAnnexBPpsFull (nalPayload : ByteSlice) : Option AnnexBPpsInfo := do
  let rbsp := stripRbspEmulationBytes nalPayload
  if rbsp.size < 2 then none
  else if (rbsp.data.getD 0 0 &&& 0x1F) != 8 then none
  else
    let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 8 }
    let (ppsId, r1) ← r0.readUE
    let (spsId, r2) ← r1.readUE
    let (cabacBit, r3) ← r2.readBit
    let (bfpoBit, r4) ← r3.readBit
    let (numSg, r5) ← r4.readUE
    if numSg > 0 then none
    else
      let (l0DefM1, r6) ← r5.readUE
      let (l1DefM1, r7) ← r6.readUE
      let (wpBit, r8) ← r7.readBit
      let (wbIdc, r9) ← r8.readBitsMSB 2
      let (_, r10) ← r9.readSE
      let (_, r11) ← r10.readSE
      let (_, r12) ← r11.readSE
      let (dbfCtrl, r13) ← r12.readBit
      let (_, r14) ← r13.readBit
      let (redPic, _) ← r14.readBit
      some {
        ppsId := ppsId.toNat
        spsId := spsId.toNat
        entropyCodingCabac := cabacBit == 1
        bottomFieldPicOrder := bfpoBit == 1
        numSliceGroupsMinus1 := 0
        numRefIdxL0DefaultActive := l0DefM1.toNat + 1
        numRefIdxL1DefaultActive := l1DefM1.toNat + 1
        weightedPredFlag := wpBit == 1
        weightedBipredIdc := wbIdc.toNat
        deblockingFilterControlPresent := dbfCtrl == 1
        redundantPicCntPresent := redPic == 1
      }

def parseRefListModLoop (r : BitReader) (fuel : Nat) (acc : List RefListModOp) :
    Option (List RefListModOp × BitReader) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (idc, r1) ← r.readUE
    if idc == 3 then
      some ((RefListModOp.endLoop :: acc).reverse, r1)
    else if idc == 0 then
      let (adm1, r2) ← r1.readUE
      parseRefListModLoop r2 f (RefListModOp.subPicNum adm1.toNat :: acc)
    else if idc == 1 then
      let (adm1, r2) ← r1.readUE
      parseRefListModLoop r2 f (RefListModOp.addPicNum adm1.toNat :: acc)
    else if idc == 2 then
      let (ltpn, r2) ← r1.readUE
      parseRefListModLoop r2 f (RefListModOp.longTermPic ltpn.toNat :: acc)
    else none

def skipPredWeightList (r : BitReader) (count : Nat) (hasChroma : Bool) : Option BitReader :=
  match count with
  | 0 => some r
  | k + 1 => do
    let (lFlag, r1) ← r.readBit
    let r2 ←
      if lFlag == 1 then do
        let (_, ra) ← r1.readSE
        let (_, rb) ← ra.readSE
        pure rb
      else pure r1
    let r3 ←
      if hasChroma then do
        let (cFlag, rc0) ← r2.readBit
        if cFlag == 1 then do
          let (_, rc1) ← rc0.readSE
          let (_, rc2) ← rc1.readSE
          let (_, rc3) ← rc2.readSE
          let (_, rc4) ← rc3.readSE
          pure rc4
        else pure rc0
      else pure r2
    skipPredWeightList r3 k hasChroma

def parseMmcoLoop (r : BitReader) (fuel : Nat) (acc : List MmcoOp) :
    Option (List MmcoOp × BitReader) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (op, r1) ← r.readUE
    if op == 0 then
      some (acc.reverse, r1)
    else if op == 1 then
      let (d, r2) ← r1.readUE
      parseMmcoLoop r2 f (MmcoOp.markShortUnused d.toNat :: acc)
    else if op == 2 then
      let (lt, r2) ← r1.readUE
      parseMmcoLoop r2 f (MmcoOp.markLongUnused lt.toNat :: acc)
    else if op == 3 then
      let (d, r2) ← r1.readUE
      let (idx, r3) ← r2.readUE
      parseMmcoLoop r3 f (MmcoOp.assignLongTermIdx d.toNat idx.toNat :: acc)
    else if op == 4 then
      let (m1, r2) ← r1.readUE
      parseMmcoLoop r2 f (MmcoOp.setMaxLongTermIdxPlus1 m1.toNat :: acc)
    else if op == 5 then
      parseMmcoLoop r1 f (MmcoOp.markAllUnused :: acc)
    else if op == 6 then
      let (idx, r2) ← r1.readUE
      parseMmcoLoop r2 f (MmcoOp.markCurrLongTerm idx.toNat :: acc)
    else none

structure ParsedSliceHeaderDpb where
  isIdr               : Bool
  nalRefIdc           : Nat
  firstMbInSlice      : Nat
  sliceTypeMod5       : Nat
  frameNum            : Nat
  fieldPicFlag        : Bool := false
  bottomFieldFlag     : Bool := false
  pocLsb              : Nat
  deltaPocBottom      : Int
  deltaPoc0           : Int := 0
  deltaPoc1           : Int := 0
  directSpatialMvPred : Bool
  numRefIdxL0Active   : Nat
  numRefIdxL1Active   : Nat
  rplmL0              : List RefListModOp
  rplmL1              : List RefListModOp
  noOutputPriorPics   : Bool
  longTermRefFlag     : Bool
  adaptiveMarking     : Bool
  mmcoOps             : List MmcoOp
  disableDeblockIdc   : Nat
  alphaOffsetDiv2     : Int
  betaOffsetDiv2      : Int
  deriving Repr, DecidableEq, Inhabited

def parseAnnexBSliceHeader (nalPayload : ByteSlice) (sps : AnnexBSpsInfo) (pps : AnnexBPpsInfo) :
    Option ParsedSliceHeaderDpb := do
  let rbsp := stripRbspEmulationBytes nalPayload
  if rbsp.size < 2 then none
  else
    let hdr := rbsp.data.getD 0 0
    let nalRefIdc := ((hdr >>> 5) &&& 0x03).toNat
    let nalType := (hdr &&& 0x1F).toNat
    if nalType != 1 && nalType != 5 then none
    else
      let isIdr := nalType == 5
      let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 8 }
      let (firstMb, r1) ← r0.readUE
      let (rawSliceType, r2) ← r1.readUE
      let stMod := rawSliceType.toNat % 5
      let (_, r3) ← r2.readUE
      let r3c ← if sps.separateColourPlane then r3.readBitsMSB 2 |>.map Prod.snd else some r3
      let (fnBits, r4) ← r3c.readBitsMSB sps.log2MaxFrameNum
      let (fieldPic, botField, r5) ←
        if !sps.frameMbsOnly then do
          let (fpFlag, rf1) ← r4.readBit
          if fpFlag == 1 then do
            let (bfFlag, rf2) ← rf1.readBit
            pure (true, bfFlag == 1, rf2)
          else pure (false, false, rf1)
        else pure (false, false, r4)
      let r6 ← if isIdr then r5.readUE.map Prod.snd else some r5
      let (pocLsb, deltaBot, delta0, delta1, r7) ←
        if sps.picOrderCntType == 0 then do
          let (lsb, rp1) ← r6.readBitsMSB sps.log2MaxPicOrderCntLsb
          if pps.bottomFieldPicOrder && !fieldPic then do
            let (db, rp2) ← rp1.readSE
            pure (lsb.toNat, db.toInt, (0 : Int), (0 : Int), rp2)
          else pure (lsb.toNat, (0 : Int), (0 : Int), (0 : Int), rp1)
        else if sps.picOrderCntType == 1 && !sps.deltaPicOrderAlwaysZero then do
          let (d0, rp1) ← r6.readSE
          if pps.bottomFieldPicOrder && !fieldPic then do
            let (d1, rp2) ← rp1.readSE
            pure (0, (0 : Int), d0.toInt, d1.toInt, rp2)
          else pure (0, (0 : Int), d0.toInt, (0 : Int), rp1)
        else pure (0, (0 : Int), (0 : Int), (0 : Int), r6)
      let r8 ← if pps.redundantPicCntPresent then r7.readUE.map Prod.snd else some r7
      let (dirSpatial, r9) ←
        if stMod == 1 then do
          let (b, rd) ← r8.readBit
          pure (b == 1, rd)
        else pure (true, r8)
      let isPOrSp := stMod == 0 || stMod == 3
      let isB := stMod == 1
      let (nL0, nL1, r10) ←
        if isPOrSp || isB then do
          let (ovFlag, ro1) ← r9.readBit
          if ovFlag == 1 then do
            let (l0m1, ro2) ← ro1.readUE
            if isB then do
              let (l1m1, ro3) ← ro2.readUE
              pure (l0m1.toNat + 1, l1m1.toNat + 1, ro3)
            else pure (l0m1.toNat + 1, pps.numRefIdxL1DefaultActive, ro2)
          else pure (pps.numRefIdxL0DefaultActive, pps.numRefIdxL1DefaultActive, ro1)
        else pure (0, 0, r9)
      let (opsL0, r11) ←
        if stMod != 2 && stMod != 4 then do
          let (f0, rm0) ← r10.readBit
          if f0 == 1 then parseRefListModLoop rm0 32 [] else pure ([], rm0)
        else pure ([], r10)
      let (opsL1, r12) ←
        if isB then do
          let (f1, rm1) ← r11.readBit
          if f1 == 1 then parseRefListModLoop rm1 32 [] else pure ([], rm1)
        else pure ([], r11)
      let hasWeightTable :=
        (pps.weightedPredFlag && isPOrSp) || (pps.weightedBipredIdc == 1 && isB)
      let hasChroma := sps.chromaArrayType != 0
      let r13 ←
        if hasWeightTable then do
          let (_, rw1) ← r12.readUE
          let rw2 ← if hasChroma then rw1.readUE.map Prod.snd else pure rw1
          let rw3 ← skipPredWeightList rw2 nL0 hasChroma
          if isB then skipPredWeightList rw3 nL1 hasChroma else pure rw3
        else pure r12
      let (noOut, ltIdr, adaptMark, mmco, r14) ←
        if nalRefIdc != 0 then
          if isIdr then do
            let (noP, ri1) ← r13.readBit
            let (ltF, ri2) ← ri1.readBit
            pure (noP == 1, ltF == 1, false, [], ri2)
          else do
            let (am, rn1) ← r13.readBit
            if am == 1 then do
              let (ops, rn2) ← parseMmcoLoop rn1 32 []
              pure (false, false, true, ops, rn2)
            else pure (false, false, false, [], rn1)
        else pure (false, false, false, [], r13)
      let r15 ←
        if pps.entropyCodingCabac && stMod != 2 && stMod != 4 then r14.readUE.map Prod.snd
        else pure r14
      let (_, r16) ← r15.readSE
      let (disIdc, aOff, bOff) ←
        if pps.deblockingFilterControlPresent then do
          let (dIdc, rd1) ← r16.readUE
          if dIdc != 1 then do
            let (ao, rd2) ← rd1.readSE
            let (bo, _) ← rd2.readSE
            pure (dIdc.toNat, ao.toInt, bo.toInt)
          else pure (1, 0, 0)
        else pure (0, 0, 0)
      some {
        isIdr := isIdr, nalRefIdc := nalRefIdc, firstMbInSlice := firstMb.toNat,
        sliceTypeMod5 := stMod, frameNum := fnBits.toNat,
        fieldPicFlag := fieldPic, bottomFieldFlag := botField,
        pocLsb := pocLsb, deltaPocBottom := deltaBot,
        deltaPoc0 := delta0, deltaPoc1 := delta1,
        directSpatialMvPred := dirSpatial,
        numRefIdxL0Active := nL0, numRefIdxL1Active := nL1,
        rplmL0 := opsL0, rplmL1 := opsL1,
        noOutputPriorPics := noOut, longTermRefFlag := ltIdr,
        adaptiveMarking := adaptMark, mmcoOps := mmco,
        disableDeblockIdc := disIdc, alphaOffsetDiv2 := aOff, betaOffsetDiv2 := bOff
      }

def derivePocType0 (isIdr prevHasMmco5 prevBottomField fieldPic bottomField : Bool)
    (pocLsb log2MaxPocLsb : Nat) (deltaPocBottom prevPocMsb prevPocLsb : Int) : Int × Int × Int :=
  if isIdr then (0, 0, 0)
  else
    let effPrevMsb : Int := if prevHasMmco5 then 0 else prevPocMsb
    let effPrevLsb : Int :=
      if prevHasMmco5 then
        if prevBottomField then 0 else prevPocLsb
      else prevPocLsb
    let maxLsb : Int := Int.ofNat (1 <<< log2MaxPocLsb)
    let lsb : Int := Int.ofNat pocLsb
    let msb : Int :=
      if lsb < effPrevLsb && (effPrevLsb - lsb) >= (maxLsb / 2) then
        effPrevMsb + maxLsb
      else if lsb > effPrevLsb && (lsb - effPrevLsb) > (maxLsb / 2) then
        effPrevMsb - maxLsb
      else effPrevMsb
    let topPoc := msb + lsb
    let botPoc := if !fieldPic then topPoc + deltaPocBottom else msb + lsb
    let poc :=
      if !fieldPic then min topPoc botPoc
      else if bottomField then botPoc
      else topPoc
    (poc, msb, topPoc)

def sumRefFrameOffsets (offsets : Array Int) (limit : Nat) : Int :=
  (List.range (Nat.min limit offsets.size)).foldl (fun acc i => acc + offsets.getD i 0) 0

def derivePocType1 (isIdr isRef prevHasMmco5 fieldPic bottomField : Bool)
    (frameNum log2MaxFrameNum prevFrameNumOffset prevFrameNum : Nat)
    (offsetForNonRefPic offsetForTopToBottomField : Int)
    (offsetForRefFrame : Array Int) (deltaPoc0 deltaPoc1 : Int) : Int × Nat :=
  if isIdr then (0, 0)
  else
    let maxFn := 1 <<< log2MaxFrameNum
    let effPrevFnOff := if prevHasMmco5 then 0 else prevFrameNumOffset
    let fnOff :=
      if prevHasMmco5 then 0
      else if prevFrameNum > frameNum then effPrevFnOff + maxFn
      else effPrevFnOff
    let numRefCycle := offsetForRefFrame.size
    let absFnBase : Int :=
      if numRefCycle != 0 then Int.ofNat (fnOff + frameNum) else 0
    let absFn : Int :=
      if !isRef && absFnBase > 0 then absFnBase - 1 else absFnBase
    let expectedPoc : Int :=
      if absFn > 0 && numRefCycle > 0 then
        let nCy : Int := Int.ofNat numRefCycle
        let pocCycleCnt := (absFn - 1).tdiv nCy
        let fnInCycle := ((absFn - 1).tmod nCy).toNat
        let expectedDeltaPerCycle := sumRefFrameOffsets offsetForRefFrame numRefCycle
        pocCycleCnt * expectedDeltaPerCycle + sumRefFrameOffsets offsetForRefFrame (fnInCycle + 1)
      else 0
    let expectedPocAdj := if !isRef then expectedPoc + offsetForNonRefPic else expectedPoc
    let topPoc := expectedPocAdj + deltaPoc0
    let botPoc :=
      if !fieldPic then topPoc + offsetForTopToBottomField + deltaPoc1
      else expectedPocAdj + offsetForTopToBottomField + deltaPoc0
    let poc :=
      if !fieldPic then min topPoc botPoc
      else if bottomField then botPoc
      else topPoc
    (poc, fnOff)

def derivePocType2 (isIdr isRef prevHasMmco5 : Bool) (frameNum log2MaxFrameNum : Nat)
    (prevFrameNumOffset prevFrameNum : Nat) : Int × Nat :=
  if isIdr then (0, 0)
  else
    let maxFn := 1 <<< log2MaxFrameNum
    let effPrevFnOff := if prevHasMmco5 then 0 else prevFrameNumOffset
    let fnOff :=
      if prevHasMmco5 then 0
      else if prevFrameNum > frameNum then effPrevFnOff + maxFn
      else effPrevFnOff
    let tempPoc : Int :=
      if !isRef then 2 * Int.ofNat (fnOff + frameNum) - 1
      else 2 * Int.ofNat (fnOff + frameNum)
    (tempPoc, fnOff)

structure AnnexBDpbTraceEntry where
  sliceIdx   : Nat
  sliceType  : Nat
  isIdr      : Bool
  isRef      : Bool
  frameNum   : Nat
  poc        : Int
  refL0Pocs  : List Int
  refL1Pocs  : List Int
  disableDbf : Nat
  deriving Repr, DecidableEq, Inhabited

structure AnnexBDpbSimReport where
  framesDecoded : Nat
  outputPocOrder : List Int
  pocMonotone    : Bool
  capacityAllOk  : Bool
  traces         : List AnnexBDpbTraceEntry
  deriving Repr, DecidableEq, Inhabited

def isIntListMonotone : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a <= b) && isIntListMonotone (b :: rest)

def simulateAnnexBDpbStream (annexB : ByteSlice) : AnnexBDpbSimReport := Id.run do
  let nals := scanAnnexBNalUnitsFast annexB false
  let mut spsOpt : Option AnnexBSpsInfo := none
  let mut ppsOpt : Option AnnexBPpsInfo := none
  let mut dpb : H264Dpb := { maxRefFrames := 4, maxDpbCapacity := 16, maxFrameNum := 16 }
  let mut prevPocMsb : Int := 0
  let mut prevPocLsb : Int := 0
  let mut prevFnOff  : Nat := 0
  let mut prevFn     : Nat := 0
  let mut prevHasMmco5 : Bool := false
  let mut prevBotField : Bool := false
  let mut traces : Array AnnexBDpbTraceEntry := #[]
  let mut capOk : Bool := true
  let mut sliceIdx : Nat := 0
  for nal in nals do
    if nal.nalType == 7 then
      if let some sps := parseAnnexBSpsFull nal.payload then
        spsOpt := some sps
        let maxFn := 1 <<< sps.log2MaxFrameNum
        let maxRef := Nat.min 16 sps.maxNumRefFrames
        let cap := Nat.min 16 (Nat.max 1 (Nat.max maxRef 8))
        dpb := { dpb with maxRefFrames := maxRef, maxDpbCapacity := cap, maxFrameNum := maxFn }
    else if nal.nalType == 8 then
      if let some pps := parseAnnexBPpsFull nal.payload then
        ppsOpt := some pps
    else if nal.nalType == 1 || nal.nalType == 5 then
      match spsOpt, ppsOpt with
      | some sps, some pps =>
        if let some sh := parseAnnexBSliceHeader nal.payload sps pps then
          if sh.firstMbInSlice == 0 then
            let isRef := sh.nalRefIdc != 0
            let hasMmco5 := isRef && !sh.isIdr && sh.adaptiveMarking && sh.mmcoOps.any (· == .markAllUnused)
            let mut poc : Int := 0
            if sps.picOrderCntType == 0 then
              let (p, msb, topPoc) := derivePocType0 sh.isIdr prevHasMmco5 prevBotField
                sh.fieldPicFlag sh.bottomFieldFlag sh.pocLsb sps.log2MaxPicOrderCntLsb
                sh.deltaPocBottom prevPocMsb prevPocLsb
              if isRef then
                prevPocMsb := if hasMmco5 then 0 else msb
                prevPocLsb :=
                  if hasMmco5 then
                    if sh.fieldPicFlag && sh.bottomFieldFlag then 0
                    else topPoc - p
                  else Int.ofNat sh.pocLsb
                prevHasMmco5 := hasMmco5
                prevBotField := sh.fieldPicFlag && sh.bottomFieldFlag
              prevFnOff := if hasMmco5 then 0 else if sh.isIdr then 0 else prevFnOff
              prevFn := if hasMmco5 || sh.isIdr then 0 else sh.frameNum
              poc := p
            else if sps.picOrderCntType == 1 then
              let (p, fnOff) := derivePocType1 sh.isIdr isRef prevHasMmco5
                sh.fieldPicFlag sh.bottomFieldFlag sh.frameNum sps.log2MaxFrameNum
                prevFnOff prevFn sps.offsetForNonRefPic sps.offsetForTopToBottomField
                sps.offsetForRefFrame sh.deltaPoc0 sh.deltaPoc1
              prevFnOff := if hasMmco5 then 0 else fnOff
              prevFn := if hasMmco5 then 0 else sh.frameNum
              prevHasMmco5 := hasMmco5
              poc := p
            else
              let (p, fnOff) := derivePocType2 sh.isIdr isRef prevHasMmco5
                sh.frameNum sps.log2MaxFrameNum prevFnOff prevFn
              prevFnOff := if hasMmco5 then 0 else fnOff
              prevFn := if hasMmco5 then 0 else sh.frameNum
              prevHasMmco5 := hasMmco5
              poc := p
            let effPoc := if hasMmco5 then 0 else poc
            let effFrameNum := if hasMmco5 then 0 else sh.frameNum
            let (l0Init, l1Init) :=
              if sh.sliceTypeMod5 == 0 || sh.sliceTypeMod5 == 3 then
                (buildRefPicListP0 dpb sh.frameNum sh.numRefIdxL0Active, [])
              else if sh.sliceTypeMod5 == 1 then
                buildRefPicListsB dpb sh.frameNum poc sh.numRefIdxL0Active sh.numRefIdxL1Active
              else ([], [])
            let l0Mod := if sh.rplmL0.isEmpty then l0Init else applyRefPicListMod dpb l0Init sh.frameNum sh.numRefIdxL0Active sh.rplmL0
            let l1Mod := if sh.rplmL1.isEmpty then l1Init else applyRefPicListMod dpb l1Init sh.frameNum sh.numRefIdxL1Active sh.rplmL1
            dpb := insertDecodedPicture dpb sh.isIdr sh.noOutputPriorPics sh.longTermRefFlag isRef
              sh.frameNum poc sh.adaptiveMarking sh.mmcoOps (UInt64.ofNat sliceIdx)
            capOk := capOk && dpbCapacityValid dpb
            traces := traces.push {
              sliceIdx := sliceIdx, sliceType := sh.sliceTypeMod5, isIdr := sh.isIdr,
              isRef := isRef, frameNum := effFrameNum, poc := effPoc,
              refL0Pocs := l0Mod.map DpbPicture.poc, refL1Pocs := l1Mod.map DpbPicture.poc,
              disableDbf := sh.disableDeblockIdc
            }
            sliceIdx := sliceIdx + 1
      | _, _ => pure ()
  let dpbFinal := flushDpb dpb
  return {
    framesDecoded := traces.size
    outputPocOrder := dpbFinal.outputPocLog
    pocMonotone := dpbFinal.priorCvsMonitor
    capacityAllOk := capOk
    traces := traces.toList
  }

def h264TraceToJson (t : AnnexBDpbTraceEntry) : String :=
  let l0Str := String.intercalate "," (t.refL0Pocs.map toString)
  let l1Str := String.intercalate "," (t.refL1Pocs.map toString)
  let p0 := s!"\{\"slice_idx\":{t.sliceIdx},\"slice_type\":{t.sliceType},\"is_idr\":{t.isIdr},"
  let p1 := s!"\"is_ref\":{t.isRef},\"frame_num\":{t.frameNum},\"poc\":{t.poc},"
  let p2 := s!"\"ref_l0_pocs\":[{l0Str}],\"ref_l1_pocs\":[{l1Str}],\"disable_dbf\":{t.disableDbf}}"
  p0 ++ p1 ++ p2

def h264DpbReportToJson (rep : AnnexBDpbSimReport) : String :=
  let pocs := String.intercalate "," (rep.outputPocOrder.map toString)
  let trs := String.intercalate "," (rep.traces.map h264TraceToJson)
  let okFlag := rep.pocMonotone && rep.capacityAllOk && rep.framesDecoded > 0
  let p0 := s!"\{\"ok\":{okFlag},\"frames_decoded\":{rep.framesDecoded},"
  let p1 := s!"\"poc_monotone\":{rep.pocMonotone},\"capacity_all_ok\":{rep.capacityAllOk},"
  let p2 := s!"\"output_poc_order\":[{pocs}],\"traces\":[{trs}]}"
  p0 ++ p1 ++ p2

def h264Sample8ToJson (s : DeblockSamples8) : String :=
  let vals := [s.p3, s.p2, s.p1, s.p0, s.q0, s.q1, s.q2, s.q3].map (fun v => toString v.toNat)
  "[" ++ String.intercalate "," vals ++ "]"

def h264KernelVectorsJson : String :=
  let refP : Plane2D := {
    width := 8, height := 8, stride := 8,
    data := ⟨((List.range 64).map fun idx =>
      let r := idx / 8
      let c := idx % 8
      UInt8.ofNat ((17 * r + 31 * c + 5 * r * c + 23) % 256)).toArray⟩
  }
  let qpel16 : List Nat := (List.range 4).foldl (fun acc yf =>
    (List.range 4).foldl (fun acc2 xf =>
      acc2 ++ [(h264LumaFrac refP 3 3 xf yf).toNat]) acc) []
  let chrP : Plane2D := {
    width := 4, height := 4, stride := 4,
    data := ⟨#[40, 120, 200, 90,
               60, 140, 180, 110,
               80, 160, 150, 130,
               50, 100, 170, 70]⟩
  }
  let chr64 : List Nat := (List.range 8).foldl (fun acc yf =>
    (List.range 8).foldl (fun acc2 xf =>
      acc2 ++ [(h264ChromaFrac chrP 1 1 xf yf).toNat]) acc) []
  let dbfStrong := filterLumaSamples8 ⟨100, 100, 100, 100, 108, 108, 108, 108⟩ 4 30 0 0
  let dbfNorm   := filterLumaSamples8 ⟨90, 96, 98, 100, 108, 110, 114, 120⟩ 2 30 0 0
  let (cP0, cQ0) := filterChromaSamples4 100 100 108 108 4 30 0 0
  let qStr := String.intercalate "," (qpel16.map toString)
  let cStr := String.intercalate "," (chr64.map toString)
  let sStr := h264Sample8ToJson dbfStrong
  let nStr := h264Sample8ToJson dbfNorm
  let iwp :=
    match implicitBiWeightScaleFactor 2 0 6 with
    | some (w0, w1) => s!"[{w0},{w1}]"
    | none => "[32,32]"
  let iwpPx := (implicitWeightedBiPredPixel 60 180 2 0 6).toNat
  let ewpPx := (weightedBiPredPixelSpec 60 180 43 21 2 (-2) 5).toNat
  let mvp16x8 := mvpMedian 0 ⟨true, 0, ⟨8, -4⟩⟩ ⟨true, 0, ⟨12, 16⟩⟩ ⟨true, 1, ⟨-20, 4⟩⟩ .p16x8 0
  let psk := pSkipMv false ⟨true, 0, ⟨0, 0⟩⟩ ⟨true, 0, ⟨12, 8⟩⟩ ⟨true, 0, ⟨4, 4⟩⟩
  let bdt := bDirectTemporal ⟨16, -8⟩ 0 2 0 4
  let srcMe := predL0LumaBlock refP 2 2 .p4x4 (-1) 2
  let srcFull := Id.run do
    let mut dst := refP
    for r in [:4] do
      for c in [:4] do
        dst := dst.setPixel (2 + r) (2 + c) (srcMe.getPixel r c)
    return dst
  let meRes := refineMotionSubpel srcFull refP 2 2 4 4 0 0 ⟨-1, 2⟩ 1
  let v0 := s!"\{\"ok\":true,\"qpel16\":[{qStr}],\"chroma64\":[{cStr}],"
  let v1 := s!"\"deblock_strong\":{sStr},\"deblock_normal\":{nStr},"
  let v2 := s!"\"deblock_chroma\":[{cP0.toNat},{cQ0.toNat}],\"implicit_weights_2_0_6\":{iwp},"
  let v3 := s!"\"implicit_bipred_px\":{iwpPx},\"explicit_bipred_px\":{ewpPx},"
  let v4 := s!"\"mvp_16x8_top\":[{mvp16x8.x},{mvp16x8.y}],\"pskip_zero_mv\":[{psk.x},{psk.y}],"
  let v5 := s!"\"bdirect_temporal\":[{bdt.mvL0.x},{bdt.mvL0.y},{bdt.mvL1.x},{bdt.mvL1.y}],"
  let v6 := s!"\"subpel_me_mv\":[{meRes.mv.x},{meRes.mv.y},{meRes.sad}]}"
  v0 ++ v1 ++ v2 ++ v3 ++ v4 ++ v5 ++ v6

end LeanAV.H264InterDeblockDpb

