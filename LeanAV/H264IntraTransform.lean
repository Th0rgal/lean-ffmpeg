import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.Format
import LeanAV.H264Syntax
import LeanAV.H264Entropy
import LeanAV.H264InterDeblockDpb

namespace LeanAV.H264IntraTransform

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream

@[inline] def asrInt (x : Int) (n : Nat) : Int :=
  Int.fdiv x ((2 : Int) ^ n)

@[inline] def shlInt (x : Int) (n : Nat) : Int :=
  x * ((2 : Int) ^ n)

@[inline] def clip3 (lo hi v : Int) : Int :=
  if v < lo then lo else if v > hi then hi else v

@[inline] def clip1 (v : Int) : Int :=
  clip3 0 255 v

@[inline] def clipU8 (v : Int) : UInt8 :=
  (clip1 v).toNat.toUInt8

def isValidQp (qp : Int) : Bool :=
  decide (0 ≤ qp ∧ qp ≤ 51)

def isValidChromaQpOffset (off : Int) : Bool :=
  decide (-12 ≤ off ∧ off ≤ 12)

def isValidPixelInt (v : Int) : Bool :=
  decide (0 ≤ v ∧ v ≤ 255)

def isValidIntraNxNMode (m : Nat) : Bool :=
  decide (m ≤ 8)

def isValidIntra16x16Mode (m : Nat) : Bool :=
  decide (m ≤ 3)

def isValidIntraChromaMode (m : Nat) : Bool :=
  decide (m ≤ 3)

@[inline] def qpMod6 (qp : Nat) : Nat := qp % 6
@[inline] def qpDiv6 (qp : Nat) : Nat := qp / 6

def qpcTable30 : Array Nat :=
  #[29, 30, 31, 32, 32, 33, 34, 34, 35, 35, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 39]

def qpcFromQpy (qpy : Nat) (chromaOffset : Int) : Nat :=
  let qpi := (clip3 0 51 ((qpy : Int) + chromaOffset)).toNat
  if qpi < 30 then qpi else qpcTable30.getD (qpi - 30) 39

def posClass4x4 (i j : Nat) : Nat :=
  if i % 2 == 0 && j % 2 == 0 then 0
  else if i % 2 == 1 && j % 2 == 1 then 1
  else 2

def posClass8x8 (i j : Nat) : Nat :=
  let im := i % 4
  let jm := j % 4
  if im == 0 && jm == 0 then 0
  else if i % 2 == 1 && j % 2 == 1 then 1
  else if im == 2 && jm == 2 then 2
  else if (im == 0 && j % 2 == 1) || (i % 2 == 1 && jm == 0) then 3
  else if (im == 0 && jm == 2) || (im == 2 && jm == 0) then 4
  else 5

def v4x4Table (m posClass : Nat) : Int :=
  let row : Array Int := match m % 6 with
    | 0 => #[10, 16, 13] | 1 => #[11, 18, 14] | 2 => #[13, 20, 16]
    | 3 => #[14, 23, 18] | 4 => #[16, 25, 20] | _ => #[18, 29, 23]
  row.getD posClass 16

def v8x8Table (m posClass : Nat) : Int :=
  let row : Array Int := match m % 6 with
    | 0 => #[20, 18, 32, 19, 25, 24]
    | 1 => #[22, 19, 35, 21, 28, 26]
    | 2 => #[26, 23, 42, 24, 33, 31]
    | 3 => #[28, 25, 45, 26, 36, 33]
    | 4 => #[32, 28, 51, 30, 40, 38]
    | _ => #[36, 32, 58, 34, 46, 43]
  row.getD posClass 32

def levelScale4x4 (qp i j : Nat) (weightScale : Int := 16) : Int :=
  weightScale * v4x4Table (qpMod6 qp) (posClass4x4 i j)

def levelScale8x8 (qp i j : Nat) (weightScale : Int := 16) : Int :=
  weightScale * v8x8Table (qpMod6 qp) (posClass8x8 i j)

def mf4x4Table (m posClass : Nat) : Int :=
  let row : Array Int := match m % 6 with
    | 0 => #[13107, 5243, 8066] | 1 => #[11916, 4660, 7490] | 2 => #[10082, 4194, 6554]
    | 3 => #[9362, 3647, 5825]  | 4 => #[8192, 3355, 5243]  | _ => #[7282, 2893, 4559]
  row.getD posClass 8192

def mf8x8Table (m posClass : Nat) : Int :=
  let row : Array Int := match m % 6 with
    | 0 => #[13107, 11428, 20972, 12222, 16777, 15481]
    | 1 => #[11916, 10826, 19174, 11058, 14980, 14290]
    | 2 => #[10082, 8943, 15978, 9670, 12710, 11985]
    | 3 => #[9362, 8228, 14913, 8931, 11984, 11259]
    | 4 => #[8192, 7346, 13159, 7740, 10486, 9777]
    | _ => #[7282, 6428, 11570, 6830, 9118, 8640]
  row.getD posClass 8192

@[inline] def idct4Butterfly1D (d0 d1 d2 d3 : Int) : Int × Int × Int × Int :=
  let e0 := d0 + d2
  let e1 := d0 - d2
  let e2 := asrInt d1 1 - d3
  let e3 := d1 + asrInt d3 1
  (e0 + e3, e1 + e2, e1 - e2, e0 - e3)

@[inline] def fdct4Butterfly1D (s0 s1 s2 s3 : Int) : Int × Int × Int × Int :=
  let a := s0 + s3
  let b := s1 + s2
  let c := s1 - s2
  let d := s0 - s3
  (a + b, 2 * d + c, a - b, d - 2 * c)

@[inline] def hadamard4Butterfly1D (a b d e : Int) : Int × Int × Int × Int :=
  (a + b + d + e, a + b - d - e, a - b - d + e, a - b + d - e)

@[inline] def hadamard2x2 (c00 c01 c10 c11 : Int) : Int × Int × Int × Int :=
  (c00 + c01 + c10 + c11, c00 - c01 + c10 - c11,
   c00 + c01 - c10 - c11, c00 - c01 - c10 + c11)

@[inline] def idct8Butterfly1D (d0 d1 d2 d3 d4 d5 d6 d7 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int :=
  let a0 := d0 + d4
  let a2 := d0 - d4
  let a4 := asrInt d2 1 - d6
  let a6 := d2 + asrInt d6 1
  let b0 := a0 + a6
  let b2 := a2 + a4
  let b4 := a2 - a4
  let b6 := a0 - a6
  let a1 := -d3 + d5 - d7 - asrInt d7 1
  let a3 := d1 + d7 - d3 - asrInt d3 1
  let a5 := -d1 + d7 + d5 + asrInt d5 1
  let a7 := d3 + d5 + d1 + asrInt d1 1
  let b1 := a1 + asrInt a7 2
  let b7 := -asrInt a1 2 + a7
  let b3 := a3 + asrInt a5 2
  let b5 := asrInt a3 2 - a5
  (b0 + b7, b2 + b5, b4 + b3, b6 + b1, b6 - b1, b4 - b3, b2 - b5, b0 - b7)

@[inline] def fdct8Butterfly1D (s0 s1 s2 s3 s4 s5 s6 s7 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int :=
  let a0 := s0 + s7
  let a1 := s1 + s6
  let a2 := s2 + s5
  let a3 := s3 + s4
  let a4 := s0 - s7
  let a5 := s1 - s6
  let a6 := s2 - s5
  let a7 := s3 - s4
  let b0 := a0 + a3
  let b1 := a1 + a2
  let b2 := a0 - a3
  let b3 := a1 - a2
  let b4 := a5 + a6 + a4 + asrInt a4 1
  let b5 := a4 - a7 - a6 - asrInt a6 1
  let b6 := a4 + a7 - a5 - asrInt a5 1
  let b7 := a5 - a6 + a7 + asrInt a7 1
  (b0 + b1, b4 + asrInt b7 2, b2 + asrInt b3 1, b5 + asrInt b6 2,
   b0 - b1, b6 - asrInt b5 2, asrInt b2 1 - b3, asrInt b4 2 - b7)

def hadamard4x4 (c : Array Int) : Array Int :=
  let (t00, t01, t02, t03) := hadamard4Butterfly1D (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)
  let (t10, t11, t12, t13) := hadamard4Butterfly1D (c.getD 4 0) (c.getD 5 0) (c.getD 6 0) (c.getD 7 0)
  let (t20, t21, t22, t23) := hadamard4Butterfly1D (c.getD 8 0) (c.getD 9 0) (c.getD 10 0) (c.getD 11 0)
  let (t30, t31, t32, t33) := hadamard4Butterfly1D (c.getD 12 0) (c.getD 13 0) (c.getD 14 0) (c.getD 15 0)
  let (y00, y10, y20, y30) := hadamard4Butterfly1D t00 t10 t20 t30
  let (y01, y11, y21, y31) := hadamard4Butterfly1D t01 t11 t21 t31
  let (y02, y12, y22, y32) := hadamard4Butterfly1D t02 t12 t22 t32
  let (y03, y13, y23, y33) := hadamard4Butterfly1D t03 t13 t23 t33
  #[y00, y01, y02, y03, y10, y11, y12, y13, y20, y21, y22, y23, y30, y31, y32, y33]

def forwardHadamard4x4 (dc : Array Int) : Array Int :=
  (hadamard4x4 dc).map (fun v => asrInt v 1)

def forwardDct4x4 (res : Array Int) : Array Int :=
  let (t00, t01, t02, t03) := fdct4Butterfly1D (res.getD 0 0) (res.getD 1 0) (res.getD 2 0) (res.getD 3 0)
  let (t10, t11, t12, t13) := fdct4Butterfly1D (res.getD 4 0) (res.getD 5 0) (res.getD 6 0) (res.getD 7 0)
  let (t20, t21, t22, t23) := fdct4Butterfly1D (res.getD 8 0) (res.getD 9 0) (res.getD 10 0) (res.getD 11 0)
  let (t30, t31, t32, t33) := fdct4Butterfly1D (res.getD 12 0) (res.getD 13 0) (res.getD 14 0) (res.getD 15 0)
  let (y00, y10, y20, y30) := fdct4Butterfly1D t00 t10 t20 t30
  let (y01, y11, y21, y31) := fdct4Butterfly1D t01 t11 t21 t31
  let (y02, y12, y22, y32) := fdct4Butterfly1D t02 t12 t22 t32
  let (y03, y13, y23, y33) := fdct4Butterfly1D t03 t13 t23 t33
  #[y00, y01, y02, y03, y10, y11, y12, y13, y20, y21, y22, y23, y30, y31, y32, y33]

def idct4x4FromScaled (d : Array Int) : Array Int :=
  let (t00, t01, t02, t03) := idct4Butterfly1D (d.getD 0 0) (d.getD 1 0) (d.getD 2 0) (d.getD 3 0)
  let (t10, t11, t12, t13) := idct4Butterfly1D (d.getD 4 0) (d.getD 5 0) (d.getD 6 0) (d.getD 7 0)
  let (t20, t21, t22, t23) := idct4Butterfly1D (d.getD 8 0) (d.getD 9 0) (d.getD 10 0) (d.getD 11 0)
  let (t30, t31, t32, t33) := idct4Butterfly1D (d.getD 12 0) (d.getD 13 0) (d.getD 14 0) (d.getD 15 0)
  let (z00, z10, z20, z30) := idct4Butterfly1D t00 t10 t20 t30
  let (z01, z11, z21, z31) := idct4Butterfly1D t01 t11 t21 t31
  let (z02, z12, z22, z32) := idct4Butterfly1D t02 t12 t22 t32
  let (z03, z13, z23, z33) := idct4Butterfly1D t03 t13 t23 t33
  let r6 (v : Int) := asrInt (v + 32) 6
  #[r6 z00, r6 z01, r6 z02, r6 z03, r6 z10, r6 z11, r6 z12, r6 z13,
    r6 z20, r6 z21, r6 z22, r6 z23, r6 z30, r6 z31, r6 z32, r6 z33]

def dequant4x4 (levels : Array Int) (qp : Nat) (dcOverride : Option Int := none) : Array Int := Id.run do
  let q := qpDiv6 qp
  let mut out := Array.replicate 16 (0 : Int)
  for i in [:4] do
    for j in [:4] do
      let ls := levelScale4x4 qp i j
      let c := levels.getD (i * 4 + j) 0
      let v := if qp ≥ 24 then shlInt (c * ls) (q - 4)
               else asrInt (c * ls + shlInt 1 (3 - q)) (4 - q)
      out := out.set! (i * 4 + j) v
  match dcOverride with
  | some dc => out := out.set! 0 dc
  | none => pure ()
  return out

def inverseResidual4x4 (levels : Array Int) (qp : Nat) (dcOverride : Option Int := none) : Array Int :=
  idct4x4FromScaled (dequant4x4 levels qp dcOverride)

def quant4x4 (coeff : Array Int) (qp : Nat) (intra : Bool) : Array Int := Id.run do
  let q := qpDiv6 qp
  let qbits := 15 + q
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  let mut out := Array.replicate 16 (0 : Int)
  for i in [:4] do
    for j in [:4] do
      let c := coeff.getD (i * 4 + j) 0
      let sign : Int := if c < 0 then -1 else 1
      let mag := asrInt (sign * c * mf4x4Table (qpMod6 qp) (posClass4x4 i j) + f) qbits
      out := out.set! (i * 4 + j) (sign * mag)
  return out

def lumaDcDequant (dc : Array Int) (qp : Nat) : Array Int :=
  let h := hadamard4x4 dc
  let q := qpDiv6 qp
  let ls := levelScale4x4 qp 0 0
  h.map fun v =>
    if qp ≥ 36 then shlInt (v * ls) (q - 6)
    else asrInt (v * ls + shlInt 1 (5 - q)) (6 - q)

def chromaDcDequant (c00 c01 c10 c11 : Int) (qpc : Nat) : Int × Int × Int × Int :=
  let (h00, h01, h10, h11) := hadamard2x2 c00 c01 c10 c11
  let q := qpDiv6 qpc
  let ls := levelScale4x4 qpc 0 0
  let scale (v : Int) : Int :=
    if qpc ≥ 30 then shlInt (v * ls) (q - 5) else asrInt (v * ls) (5 - q)
  (scale h00, scale h01, scale h10, scale h11)

def forwardDct8x8 (res : Array Int) : Array Int :=
  let row (r : Nat) :=
    fdct8Butterfly1D (res.getD (r * 8) 0) (res.getD (r * 8 + 1) 0) (res.getD (r * 8 + 2) 0)
      (res.getD (r * 8 + 3) 0) (res.getD (r * 8 + 4) 0) (res.getD (r * 8 + 5) 0)
      (res.getD (r * 8 + 6) 0) (res.getD (r * 8 + 7) 0)
  let (t00, t01, t02, t03, t04, t05, t06, t07) := row 0
  let (t10, t11, t12, t13, t14, t15, t16, t17) := row 1
  let (t20, t21, t22, t23, t24, t25, t26, t27) := row 2
  let (t30, t31, t32, t33, t34, t35, t36, t37) := row 3
  let (t40, t41, t42, t43, t44, t45, t46, t47) := row 4
  let (t50, t51, t52, t53, t54, t55, t56, t57) := row 5
  let (t60, t61, t62, t63, t64, t65, t66, t67) := row 6
  let (t70, t71, t72, t73, t74, t75, t76, t77) := row 7
  let col (a b c d e f g h : Int) := fdct8Butterfly1D a b c d e f g h
  let (y00, y10, y20, y30, y40, y50, y60, y70) := col t00 t10 t20 t30 t40 t50 t60 t70
  let (y01, y11, y21, y31, y41, y51, y61, y71) := col t01 t11 t21 t31 t41 t51 t61 t71
  let (y02, y12, y22, y32, y42, y52, y62, y72) := col t02 t12 t22 t32 t42 t52 t62 t72
  let (y03, y13, y23, y33, y43, y53, y63, y73) := col t03 t13 t23 t33 t43 t53 t63 t73
  let (y04, y14, y24, y34, y44, y54, y64, y74) := col t04 t14 t24 t34 t44 t54 t64 t74
  let (y05, y15, y25, y35, y45, y55, y65, y75) := col t05 t15 t25 t35 t45 t55 t65 t75
  let (y06, y16, y26, y36, y46, y56, y66, y76) := col t06 t16 t26 t36 t46 t56 t66 t76
  let (y07, y17, y27, y37, y47, y57, y67, y77) := col t07 t17 t27 t37 t47 t57 t67 t77
  #[y00, y01, y02, y03, y04, y05, y06, y07,
    y10, y11, y12, y13, y14, y15, y16, y17,
    y20, y21, y22, y23, y24, y25, y26, y27,
    y30, y31, y32, y33, y34, y35, y36, y37,
    y40, y41, y42, y43, y44, y45, y46, y47,
    y50, y51, y52, y53, y54, y55, y56, y57,
    y60, y61, y62, y63, y64, y65, y66, y67,
    y70, y71, y72, y73, y74, y75, y76, y77]

def dequant8x8 (levels : Array Int) (qp : Nat) : Array Int := Id.run do
  let q := qpDiv6 qp
  let mut out := Array.replicate 64 (0 : Int)
  for i in [:8] do
    for j in [:8] do
      let ls := levelScale8x8 qp i j
      let c := levels.getD (i * 8 + j) 0
      let v := if qp ≥ 36 then shlInt (c * ls) (q - 6)
               else asrInt (c * ls + shlInt 1 (5 - q)) (6 - q)
      out := out.set! (i * 8 + j) v
  return out

def idct8x8FromScaled (d : Array Int) : Array Int :=
  let row (r : Nat) :=
    idct8Butterfly1D (d.getD (r * 8) 0) (d.getD (r * 8 + 1) 0) (d.getD (r * 8 + 2) 0)
      (d.getD (r * 8 + 3) 0) (d.getD (r * 8 + 4) 0) (d.getD (r * 8 + 5) 0)
      (d.getD (r * 8 + 6) 0) (d.getD (r * 8 + 7) 0)
  let (t00, t01, t02, t03, t04, t05, t06, t07) := row 0
  let (t10, t11, t12, t13, t14, t15, t16, t17) := row 1
  let (t20, t21, t22, t23, t24, t25, t26, t27) := row 2
  let (t30, t31, t32, t33, t34, t35, t36, t37) := row 3
  let (t40, t41, t42, t43, t44, t45, t46, t47) := row 4
  let (t50, t51, t52, t53, t54, t55, t56, t57) := row 5
  let (t60, t61, t62, t63, t64, t65, t66, t67) := row 6
  let (t70, t71, t72, t73, t74, t75, t76, t77) := row 7
  let col (a b c e f g h k : Int) := idct8Butterfly1D a b c e f g h k
  let (z00, z10, z20, z30, z40, z50, z60, z70) := col t00 t10 t20 t30 t40 t50 t60 t70
  let (z01, z11, z21, z31, z41, z51, z61, z71) := col t01 t11 t21 t31 t41 t51 t61 t71
  let (z02, z12, z22, z32, z42, z52, z62, z72) := col t02 t12 t22 t32 t42 t52 t62 t72
  let (z03, z13, z23, z33, z43, z53, z63, z73) := col t03 t13 t23 t33 t43 t53 t63 t73
  let (z04, z14, z24, z34, z44, z54, z64, z74) := col t04 t14 t24 t34 t44 t54 t64 t74
  let (z05, z15, z25, z35, z45, z55, z65, z75) := col t05 t15 t25 t35 t45 t55 t65 t75
  let (z06, z16, z26, z36, z46, z56, z66, z76) := col t06 t16 t26 t36 t46 t56 t66 t76
  let (z07, z17, z27, z37, z47, z57, z67, z77) := col t07 t17 t27 t37 t47 t57 t67 t77
  let r6 (v : Int) := asrInt (v + 32) 6
  #[r6 z00, r6 z01, r6 z02, r6 z03, r6 z04, r6 z05, r6 z06, r6 z07,
    r6 z10, r6 z11, r6 z12, r6 z13, r6 z14, r6 z15, r6 z16, r6 z17,
    r6 z20, r6 z21, r6 z22, r6 z23, r6 z24, r6 z25, r6 z26, r6 z27,
    r6 z30, r6 z31, r6 z32, r6 z33, r6 z34, r6 z35, r6 z36, r6 z37,
    r6 z40, r6 z41, r6 z42, r6 z43, r6 z44, r6 z45, r6 z46, r6 z47,
    r6 z50, r6 z51, r6 z52, r6 z53, r6 z54, r6 z55, r6 z56, r6 z57,
    r6 z60, r6 z61, r6 z62, r6 z63, r6 z64, r6 z65, r6 z66, r6 z67,
    r6 z70, r6 z71, r6 z72, r6 z73, r6 z74, r6 z75, r6 z76, r6 z77]

def inverseResidual8x8 (levels : Array Int) (qp : Nat) : Array Int :=
  idct8x8FromScaled (dequant8x8 levels qp)

def quant8x8 (coeff : Array Int) (qp : Nat) (intra : Bool) : Array Int := Id.run do
  let q := qpDiv6 qp
  let qbits := 16 + q
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  let mut out := Array.replicate 64 (0 : Int)
  for i in [:8] do
    for j in [:8] do
      let c := coeff.getD (i * 8 + j) 0
      let sign : Int := if c < 0 then -1 else 1
      let mag := asrInt (sign * c * mf8x8Table (qpMod6 qp) (posClass8x8 i j) + f) qbits
      out := out.set! (i * 8 + j) (sign * mag)
  return out

def reconstructBlock4x4Idct (pred : Plane2D) (row0 col0 : Nat) (levels16 : Array Int)
    (qp : Nat := 0) (dcOverride : Option Int := none) : Plane2D := Id.run do
  let res := inverseResidual4x4 levels16 qp dcOverride
  let mut out := pred
  for r in [:4] do
    for c in [:4] do
      let p : Int := (out.getPixel (row0 + r) (col0 + c)).toNat
      out := out.setPixel (row0 + r) (col0 + c) (clipU8 (p + res.getD (r * 4 + c) 0))
  return out

def reconstructBlock8x8Idct (pred : Plane2D) (row0 col0 : Nat) (levels64 : Array Int)
    (qp : Nat) : Plane2D := Id.run do
  let res := inverseResidual8x8 levels64 qp
  let mut out := pred
  for r in [:8] do
    for c in [:8] do
      let p : Int := (out.getPixel (row0 + r) (col0 + c)).toNat
      out := out.setPixel (row0 + r) (col0 + c) (clipU8 (p + res.getD (r * 8 + c) 0))
  return out

@[inline] def losslessSampleResidual (sample pred : UInt8) : Int :=
  (sample.toNat : Int) - (pred.toNat : Int)

@[inline] def losslessSampleReconstruct (pred : UInt8) (res : Int) : UInt8 :=
  clipU8 ((pred.toNat : Int) + res)

@[inline] def dpcmLine4 (r0 r1 r2 r3 : Int) : Int × Int × Int × Int :=
  (r0, r1 - r0, r2 - r1, r3 - r2)

@[inline] def undpcmLine4 (c0 c1 c2 c3 : Int) : Int × Int × Int × Int :=
  (c0, c0 + c1, c0 + c1 + c2, c0 + c1 + c2 + c3)

@[inline] def dpcmLine8 (r0 r1 r2 r3 r4 r5 r6 r7 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int :=
  (r0, r1 - r0, r2 - r1, r3 - r2, r4 - r3, r5 - r4, r6 - r5, r7 - r6)

@[inline] def undpcmLine8 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int :=
  (c0, c0 + c1, c0 + c1 + c2, c0 + c1 + c2 + c3,
   c0 + c1 + c2 + c3 + c4, c0 + c1 + c2 + c3 + c4 + c5,
   c0 + c1 + c2 + c3 + c4 + c5 + c6, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)

def encodeResidualDpcm4x4 (mode : Nat) (res : Array Int) : Array Int :=
  let g (i : Nat) := res.getD i 0
  if mode == 0 then
    let (a0, a1, a2, a3) := dpcmLine4 (g 0) (g 4) (g 8) (g 12)
    let (b0, b1, b2, b3) := dpcmLine4 (g 1) (g 5) (g 9) (g 13)
    let (c0, c1, c2, c3) := dpcmLine4 (g 2) (g 6) (g 10) (g 14)
    let (d0, d1, d2, d3) := dpcmLine4 (g 3) (g 7) (g 11) (g 15)
    #[a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3]
  else if mode == 1 then
    let (a0, a1, a2, a3) := dpcmLine4 (g 0) (g 1) (g 2) (g 3)
    let (b0, b1, b2, b3) := dpcmLine4 (g 4) (g 5) (g 6) (g 7)
    let (c0, c1, c2, c3) := dpcmLine4 (g 8) (g 9) (g 10) (g 11)
    let (d0, d1, d2, d3) := dpcmLine4 (g 12) (g 13) (g 14) (g 15)
    #[a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3]
  else
    #[g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11, g 12, g 13, g 14, g 15]

def decodeResidualDpcm4x4 (mode : Nat) (levels : Array Int) : Array Int :=
  let g (i : Nat) := levels.getD i 0
  if mode == 0 then
    let (a0, a1, a2, a3) := undpcmLine4 (g 0) (g 4) (g 8) (g 12)
    let (b0, b1, b2, b3) := undpcmLine4 (g 1) (g 5) (g 9) (g 13)
    let (c0, c1, c2, c3) := undpcmLine4 (g 2) (g 6) (g 10) (g 14)
    let (d0, d1, d2, d3) := undpcmLine4 (g 3) (g 7) (g 11) (g 15)
    #[a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3]
  else if mode == 1 then
    let (a0, a1, a2, a3) := undpcmLine4 (g 0) (g 1) (g 2) (g 3)
    let (b0, b1, b2, b3) := undpcmLine4 (g 4) (g 5) (g 6) (g 7)
    let (c0, c1, c2, c3) := undpcmLine4 (g 8) (g 9) (g 10) (g 11)
    let (d0, d1, d2, d3) := undpcmLine4 (g 12) (g 13) (g 14) (g 15)
    #[a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3]
  else
    #[g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11, g 12, g 13, g 14, g 15]

def encodeResidualDpcm8x8 (mode : Nat) (res : Array Int) : Array Int :=
  Array.ofFn fun idx : Fin 64 =>
    let r := idx.val / 8
    let c := idx.val % 8
    if mode == 0 then
      if r == 0 then res.getD c 0 else res.getD (r * 8 + c) 0 - res.getD ((r - 1) * 8 + c) 0
    else if mode == 1 then
      if c == 0 then res.getD (r * 8) 0 else res.getD (r * 8 + c) 0 - res.getD (r * 8 + c - 1) 0
    else res.getD idx.val 0

def dpcmPrefixSum : Nat → (Nat → Int) → Int
  | 0, g => g 0
  | k + 1, g => dpcmPrefixSum k g + g (k + 1)

def decodeResidualDpcm8x8 (mode : Nat) (levels : Array Int) : Array Int :=
  Array.ofFn fun idx : Fin 64 =>
    let r := idx.val / 8
    let c := idx.val % 8
    if mode == 0 then
      dpcmPrefixSum r (fun k => levels.getD (k * 8 + c) 0)
    else if mode == 1 then
      dpcmPrefixSum c (fun k => levels.getD (r * 8 + k) 0)
    else levels.getD idx.val 0

structure IntraNeighbors where
  leftAvail     : Bool
  topAvail      : Bool
  topRightAvail : Bool
  topLeftAvail  : Bool
  left          : Array UInt8
  top           : Array UInt8
  topRight      : Array UInt8
  topLeft       : UInt8
  deriving Repr, DecidableEq, Inhabited

def sampleAt (p : Plane2D) (x y : Int) : Option UInt8 :=
  if x ≥ 0 && y ≥ 0 && x.toNat < p.width && y.toNat < p.height then
    some (p.getPixel y.toNat x.toNat)
  else none

def neighborsNxN (nSz : Nat) (p : Plane2D) (x y : Nat) (allowTopRight : Bool := true) : IntraNeighbors := Id.run do
  let xi : Int := x
  let yi : Int := y
  let leftAv := (sampleAt p (xi - 1) yi).isSome
  let topAv := (sampleAt p xi (yi - 1)).isSome
  let tlAv := (sampleAt p (xi - 1) (yi - 1)).isSome
  let tr0 := sampleAt p (xi + (nSz : Int)) (yi - 1)
  let trAv := allowTopRight && tr0.isSome
  let mut left := Array.replicate nSz (128 : UInt8)
  let mut top := Array.replicate nSz (128 : UInt8)
  for i in [:nSz] do
    left := left.set! i ((sampleAt p (xi - 1) (yi + (i : Int))).getD 128)
    top := top.set! i ((sampleAt p (xi + (i : Int)) (yi - 1)).getD 128)
  let rep := top.getD (nSz - 1) 128
  let mut topRight := Array.replicate nSz rep
  if trAv then
    for i in [:nSz] do
      topRight := topRight.set! i ((sampleAt p (xi + (nSz : Int) + (i : Int)) (yi - 1)).getD rep)
  return { leftAvail := leftAv, topAvail := topAv, topRightAvail := trAv, topLeftAvail := tlAv,
           left := left, top := top, topRight := topRight,
           topLeft := (sampleAt p (xi - 1) (yi - 1)).getD 128 }

def neighbors4 (p : Plane2D) (x y : Nat) (allowTopRight : Bool := true) : IntraNeighbors :=
  neighborsNxN 4 p x y allowTopRight

def neighbors8 (p : Plane2D) (x y : Nat) (allowTopRight : Bool := true) : IntraNeighbors :=
  neighborsNxN 8 p x y allowTopRight

def isLegalIntraNxNMode (mode : Nat) (n : IntraNeighbors) : Bool :=
  match mode with
  | 0 | 3 | 7 => n.topAvail
  | 1 | 8 => n.leftAvail
  | 2 => true
  | 4 | 5 | 6 => n.topAvail && n.leftAvail && n.topLeftAvail
  | _ => false

def isLegalIntra16x16Mode (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) : Bool :=
  match mode with
  | 0 => topAvail | 1 => leftAvail | 2 => true
  | 3 => topAvail && leftAvail && topLeftAvail | _ => false

def isLegalIntraChromaMode (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) : Bool :=
  match mode with
  | 0 => true | 1 => leftAvail | 2 => topAvail
  | 3 => topAvail && leftAvail && topLeftAvail | _ => false

@[inline] def avg2U8 (a b : UInt8) : UInt8 :=
  ((a.toNat + b.toNat + 1) / 2).toUInt8

@[inline] def filt3U8 (a b c : UInt8) : UInt8 :=
  ((a.toNat + 2 * b.toNat + c.toNat + 2) / 4).toUInt8

def pred4x4 (mode : Nat) (n : IntraNeighbors) : Array UInt8 :=
  let raw : Array UInt8 := (Id.run do
  let pT := (n.top.extract 0 4) ++ (if n.topRightAvail then n.topRight.extract 0 4
    else Array.replicate 4 (n.top.getD 3 128))
  let pL := n.left
  let tl := n.topLeft
  let mut out := Array.replicate 16 (128 : UInt8)
  match mode with
  | 0 =>
    for y in [:4] do for x in [:4] do out := out.set! (y * 4 + x) (pT.getD x 128)
  | 1 =>
    for y in [:4] do for x in [:4] do out := out.set! (y * 4 + x) (pL.getD y 128)
  | 2 =>
    let mut s : Nat := 0
    if n.topAvail then for i in [:4] do s := s + (pT.getD i 0).toNat
    if n.leftAvail then for i in [:4] do s := s + (pL.getD i 0).toNat
    let dc : UInt8 :=
      if n.topAvail && n.leftAvail then ((s + 4) / 8).toUInt8
      else if n.topAvail || n.leftAvail then ((s + 2) / 4).toUInt8
      else 128
    for i in [:16] do out := out.set! i dc
  | 3 =>
    for y in [:4] do for x in [:4] do
      let v := if x == 3 && y == 3 then filt3U8 (pT.getD 6 0) (pT.getD 7 0) (pT.getD 7 0)
               else filt3U8 (pT.getD (x + y) 0) (pT.getD (x + y + 1) 0) (pT.getD (x + y + 2) 0)
      out := out.set! (y * 4 + x) v
  | 4 =>
    for y in [:4] do for x in [:4] do
      let v :=
        if x > y then
          let d := x - y
          filt3U8 (if d == 1 then tl else pT.getD (d - 2) 0) (pT.getD (d - 1) 0) (pT.getD d 0)
        else if x < y then
          let d := y - x
          filt3U8 (if d == 1 then tl else pL.getD (d - 2) 0) (pL.getD (d - 1) 0) (pL.getD d 0)
        else filt3U8 (pT.getD 0 0) tl (pL.getD 0 0)
      out := out.set! (y * 4 + x) v
  | 5 =>
    for y in [:4] do for x in [:4] do
      let zVR : Int := 2 * (x : Int) - (y : Int)
      let i := x - y / 2
      let v :=
        if zVR == 0 || zVR == 2 || zVR == 4 || zVR == 6 then
          avg2U8 (if i == 0 then tl else pT.getD (i - 1) 0) (pT.getD i 0)
        else if zVR == 1 || zVR == 3 || zVR == 5 then
          let a := if i == 0 then tl else pT.getD (i - 1) 0
          let b := if i == 1 then tl else if i == 0 then pL.getD 0 0 else pT.getD (i - 2) 0
          filt3U8 b a (pT.getD i 0)
        else if zVR == -1 then filt3U8 (pL.getD 0 0) tl (pT.getD 0 0)
        else if zVR == -2 then filt3U8 (pL.getD 1 0) (pL.getD 0 0) tl
        else filt3U8 (pL.getD 2 0) (pL.getD 1 0) (pL.getD 0 0)
      out := out.set! (y * 4 + x) v
  | 6 =>
    for y in [:4] do for x in [:4] do
      let zHD : Int := 2 * (y : Int) - (x : Int)
      let i := y - x / 2
      let v :=
        if zHD == 0 || zHD == 2 || zHD == 4 || zHD == 6 then
          avg2U8 (if i == 0 then tl else pL.getD (i - 1) 0) (pL.getD i 0)
        else if zHD == 1 || zHD == 3 || zHD == 5 then
          let a := if i == 0 then tl else pL.getD (i - 1) 0
          let b := if i == 1 then tl else if i == 0 then pT.getD 0 0 else pL.getD (i - 2) 0
          filt3U8 b a (pL.getD i 0)
        else if zHD == -1 then filt3U8 (pL.getD 0 0) tl (pT.getD 0 0)
        else if zHD == -2 then filt3U8 (pT.getD 1 0) (pT.getD 0 0) tl
        else filt3U8 (pT.getD 2 0) (pT.getD 1 0) (pT.getD 0 0)
      out := out.set! (y * 4 + x) v
  | 7 =>
    for y in [:4] do for x in [:4] do
      let i := x + y / 2
      let v := if y % 2 == 0 then avg2U8 (pT.getD i 0) (pT.getD (i + 1) 0)
               else filt3U8 (pT.getD i 0) (pT.getD (i + 1) 0) (pT.getD (i + 2) 0)
      out := out.set! (y * 4 + x) v
  | _ =>
    for y in [:4] do for x in [:4] do
      let zHU := x + 2 * y
      let i := y + x / 2
      let v :=
        if zHU == 0 || zHU == 2 || zHU == 4 then avg2U8 (pL.getD i 0) (pL.getD (i + 1) 0)
        else if zHU == 1 || zHU == 3 then filt3U8 (pL.getD i 0) (pL.getD (i + 1) 0) (pL.getD (i + 2) 0)
        else if zHU == 5 then filt3U8 (pL.getD 2 0) (pL.getD 3 0) (pL.getD 3 0)
        else pL.getD 3 0
      out := out.set! (y * 4 + x) v
  return out)
  Array.ofFn fun i : Fin 16 => raw.getD i.val 128

def filterIntra8x8Refs (n : IntraNeighbors) : IntraNeighbors := Id.run do
  let pT := (n.top.extract 0 8) ++ (if n.topRightAvail then n.topRight.extract 0 8
    else Array.replicate 8 (n.top.getD 7 128))
  let mut fT := Array.replicate 16 (128 : UInt8)
  let mut fL := Array.replicate 8 (128 : UInt8)
  let mut fTL := n.topLeft
  if n.topAvail then
    let a0 := if n.topLeftAvail then n.topLeft else pT.getD 0 128
    fT := fT.set! 0 (filt3U8 a0 (pT.getD 0 128) (pT.getD 1 128))
    for x in [1:15] do
      fT := fT.set! x (filt3U8 (pT.getD (x - 1) 128) (pT.getD x 128) (pT.getD (x + 1) 128))
    fT := fT.set! 15 (filt3U8 (pT.getD 14 128) (pT.getD 15 128) (pT.getD 15 128))
  if n.topLeftAvail then
    fTL :=
      if n.topAvail && n.leftAvail then filt3U8 (n.left.getD 0 128) n.topLeft (pT.getD 0 128)
      else if n.topAvail then filt3U8 n.topLeft n.topLeft (pT.getD 0 128)
      else if n.leftAvail then filt3U8 n.topLeft n.topLeft (n.left.getD 0 128)
      else n.topLeft
  if n.leftAvail then
    let b0 := if n.topLeftAvail then n.topLeft else n.left.getD 0 128
    fL := fL.set! 0 (filt3U8 b0 (n.left.getD 0 128) (n.left.getD 1 128))
    for y in [1:7] do
      fL := fL.set! y (filt3U8 (n.left.getD (y - 1) 128) (n.left.getD y 128) (n.left.getD (y + 1) 128))
    fL := fL.set! 7 (filt3U8 (n.left.getD 6 128) (n.left.getD 7 128) (n.left.getD 7 128))
  return { n with left := fL, top := fT.extract 0 8, topRight := fT.extract 8 16,
                  topRightAvail := true, topLeft := fTL }

def pred8x8 (mode : Nat) (raw : IntraNeighbors) : Array UInt8 :=
  let res : Array UInt8 := (Id.run do
  let n := filterIntra8x8Refs raw
  let pT := n.top ++ n.topRight
  let fL := n.left
  let fTL := n.topLeft
  let mut out := Array.replicate 64 (128 : UInt8)
  match mode with
  | 0 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (pT.getD x 128)
  | 1 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (fL.getD y 128)
  | 2 =>
    let mut s : Nat := 0
    if n.topAvail then for i in [:8] do s := s + (pT.getD i 0).toNat
    if n.leftAvail then for i in [:8] do s := s + (fL.getD i 0).toNat
    let dc : UInt8 :=
      if n.topAvail && n.leftAvail then ((s + 8) / 16).toUInt8
      else if n.topAvail || n.leftAvail then ((s + 4) / 8).toUInt8
      else 128
    for i in [:64] do out := out.set! i dc
  | 3 =>
    for y in [:8] do for x in [:8] do
      let v := if x == 7 && y == 7 then filt3U8 (pT.getD 14 0) (pT.getD 15 0) (pT.getD 15 0)
               else filt3U8 (pT.getD (x + y) 0) (pT.getD (x + y + 1) 0) (pT.getD (x + y + 2) 0)
      out := out.set! (y * 8 + x) v
  | 4 =>
    for y in [:8] do for x in [:8] do
      let v :=
        if x > y then
          let d := x - y
          filt3U8 (if d == 1 then fTL else pT.getD (d - 2) 0) (pT.getD (d - 1) 0) (pT.getD d 0)
        else if x < y then
          let d := y - x
          filt3U8 (if d == 1 then fTL else fL.getD (d - 2) 0) (fL.getD (d - 1) 0) (fL.getD d 0)
        else filt3U8 (pT.getD 0 0) fTL (fL.getD 0 0)
      out := out.set! (y * 8 + x) v
  | 5 =>
    for y in [:8] do for x in [:8] do
      let zVR : Int := 2 * (x : Int) - (y : Int)
      let i := x - y / 2
      let v :=
        if zVR ≥ 0 && zVR % 2 == 0 then
          avg2U8 (if i == 0 then fTL else pT.getD (i - 1) 0) (pT.getD i 0)
        else if zVR > 0 then
          let a := if i == 0 then fTL else pT.getD (i - 1) 0
          let b := if i == 1 then fTL else if i == 0 then fL.getD 0 0 else pT.getD (i - 2) 0
          filt3U8 b a (pT.getD i 0)
        else if zVR == -1 then filt3U8 (fL.getD 0 0) fTL (pT.getD 0 0)
        else
          let k := y - 2 * x
          filt3U8 (fL.getD (k - 1) 0) (fL.getD (k - 2) 0) (if k == 2 then fTL else fL.getD (k - 3) 0)
      out := out.set! (y * 8 + x) v
  | 6 =>
    for y in [:8] do for x in [:8] do
      let zHD : Int := 2 * (y : Int) - (x : Int)
      let i := y - x / 2
      let v :=
        if zHD ≥ 0 && zHD % 2 == 0 then
          avg2U8 (if i == 0 then fTL else fL.getD (i - 1) 0) (fL.getD i 0)
        else if zHD > 0 then
          let a := if i == 0 then fTL else fL.getD (i - 1) 0
          let b := if i == 1 then fTL else if i == 0 then pT.getD 0 0 else fL.getD (i - 2) 0
          filt3U8 b a (fL.getD i 0)
        else if zHD == -1 then filt3U8 (fL.getD 0 0) fTL (pT.getD 0 0)
        else
          let k := x - 2 * y
          filt3U8 (pT.getD (k - 1) 0) (pT.getD (k - 2) 0) (if k == 2 then fTL else pT.getD (k - 3) 0)
      out := out.set! (y * 8 + x) v
  | 7 =>
    for y in [:8] do for x in [:8] do
      let i := x + y / 2
      let v := if y % 2 == 0 then avg2U8 (pT.getD i 0) (pT.getD (i + 1) 0)
               else filt3U8 (pT.getD i 0) (pT.getD (i + 1) 0) (pT.getD (i + 2) 0)
      out := out.set! (y * 8 + x) v
  | _ =>
    for y in [:8] do for x in [:8] do
      let zHU := x + 2 * y
      let i := y + x / 2
      let v :=
        if zHU ≤ 12 && zHU % 2 == 0 then avg2U8 (fL.getD i 0) (fL.getD (i + 1) 0)
        else if zHU ≤ 11 then filt3U8 (fL.getD i 0) (fL.getD (i + 1) 0) (fL.getD (i + 2) 0)
        else if zHU == 13 then filt3U8 (fL.getD 6 0) (fL.getD 7 0) (fL.getD 7 0)
        else fL.getD 7 0
      out := out.set! (y * 8 + x) v
  return out)
  Array.ofFn fun i : Fin 64 => res.getD i.val 128

def pred16x16 (mode : Nat) (left top : Array UInt8) (topLeft : UInt8)
    (leftAvail topAvail : Bool) : Array UInt8 :=
  let res : Array UInt8 := (Id.run do
  let mut out := Array.replicate 256 (128 : UInt8)
  match mode with
  | 0 => for y in [:16] do for x in [:16] do out := out.set! (y * 16 + x) (top.getD x 128)
  | 1 => for y in [:16] do for x in [:16] do out := out.set! (y * 16 + x) (left.getD y 128)
  | 2 =>
    let mut s : Nat := 0
    if topAvail then for i in [:16] do s := s + (top.getD i 0).toNat
    if leftAvail then for i in [:16] do s := s + (left.getD i 0).toNat
    let dc : UInt8 :=
      if topAvail && leftAvail then ((s + 16) / 32).toUInt8
      else if topAvail || leftAvail then ((s + 8) / 16).toUInt8
      else 128
    for i in [:256] do out := out.set! i dc
  | _ =>
    let mut hSum : Int := 0
    let mut vSum : Int := 0
    for k in [:8] do
      let pHNeg : Int := if k == 7 then topLeft.toNat else (top.getD (6 - k) 0).toNat
      let pVNeg : Int := if k == 7 then topLeft.toNat else (left.getD (6 - k) 0).toNat
      hSum := hSum + ((k + 1 : Nat) : Int) * (((top.getD (8 + k) 0).toNat : Int) - pHNeg)
      vSum := vSum + ((k + 1 : Nat) : Int) * (((left.getD (8 + k) 0).toNat : Int) - pVNeg)
    let a : Int := 16 * (((left.getD 15 0).toNat : Int) + ((top.getD 15 0).toNat : Int))
    let b := asrInt (5 * hSum + 32) 6
    let c := asrInt (5 * vSum + 32) 6
    for y in [:16] do for x in [:16] do
      let v := asrInt (a + b * ((x : Int) - 7) + c * ((y : Int) - 7) + 16) 5
      out := out.set! (y * 16 + x) (clipU8 v)
  return out)
  Array.ofFn fun i : Fin 256 => res.getD i.val 128

def predChroma (mode : Nat) (left top : Array UInt8) (topLeft : UInt8)
    (leftAvail topAvail : Bool) : Array UInt8 :=
  let res : Array UInt8 := (Id.run do
  let mut out := Array.replicate 64 (128 : UInt8)
  match mode with
  | 0 =>
    let sumT0 := (top.getD 0 0).toNat + (top.getD 1 0).toNat + (top.getD 2 0).toNat + (top.getD 3 0).toNat
    let sumT1 := (top.getD 4 0).toNat + (top.getD 5 0).toNat + (top.getD 6 0).toNat + (top.getD 7 0).toNat
    let sumL0 := (left.getD 0 0).toNat + (left.getD 1 0).toNat + (left.getD 2 0).toNat + (left.getD 3 0).toNat
    let sumL1 := (left.getD 4 0).toNat + (left.getD 5 0).toNat + (left.getD 6 0).toNat + (left.getD 7 0).toNat
    let dc00 : UInt8 := if topAvail && leftAvail then ((sumT0 + sumL0 + 4) / 8).toUInt8
                        else if topAvail then ((sumT0 + 2) / 4).toUInt8
                        else if leftAvail then ((sumL0 + 2) / 4).toUInt8 else 128
    let dc01 : UInt8 := if topAvail then ((sumT1 + 2) / 4).toUInt8
                        else if leftAvail then ((sumL0 + 2) / 4).toUInt8 else 128
    let dc10 : UInt8 := if leftAvail then ((sumL1 + 2) / 4).toUInt8
                        else if topAvail then ((sumT0 + 2) / 4).toUInt8 else 128
    let dc11 : UInt8 := if topAvail && leftAvail then ((sumT1 + sumL1 + 4) / 8).toUInt8
                        else if topAvail then ((sumT1 + 2) / 4).toUInt8
                        else if leftAvail then ((sumL1 + 2) / 4).toUInt8 else 128
    let dcs := #[dc00, dc01, dc10, dc11]
    for byy in [:2] do for bxx in [:2] do
      let dc := dcs.getD (byy * 2 + bxx) 128
      for y in [:4] do for x in [:4] do out := out.set! ((byy * 4 + y) * 8 + bxx * 4 + x) dc
  | 1 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (left.getD y 128)
  | 2 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (top.getD x 128)
  | _ =>
    let mut hSum : Int := 0
    let mut vSum : Int := 0
    for k in [:4] do
      let pHNeg : Int := if k == 3 then topLeft.toNat else (top.getD (2 - k) 0).toNat
      let pVNeg : Int := if k == 3 then topLeft.toNat else (left.getD (2 - k) 0).toNat
      hSum := hSum + ((k + 1 : Nat) : Int) * (((top.getD (4 + k) 0).toNat : Int) - pHNeg)
      vSum := vSum + ((k + 1 : Nat) : Int) * (((left.getD (4 + k) 0).toNat : Int) - pVNeg)
    let a : Int := 16 * (((left.getD 7 0).toNat : Int) + ((top.getD 7 0).toNat : Int))
    let b := asrInt (17 * hSum + 16) 5
    let c := asrInt (17 * vSum + 16) 5
    for y in [:8] do for x in [:8] do
      let v := asrInt (a + b * ((x : Int) - 3) + c * ((y : Int) - 3) + 16) 5
      out := out.set! (y * 8 + x) (clipU8 v)
  return out)
  Array.ofFn fun i : Fin 64 => res.getD i.val 128

def sadBlock (a b : Array UInt8) : Nat := Id.run do
  let n := Nat.min a.size b.size
  let mut acc : Nat := 0
  for i in [:n] do
    acc := acc + Int.natAbs (((a.getD i 0).toNat : Int) - ((b.getD i 0).toNat : Int))
  return acc

def satd4x4 (src pred : Array UInt8) : Nat := Id.run do
  let mut diff := Array.replicate 16 (0 : Int)
  for i in [:16] do
    diff := diff.set! i (((src.getD i 0).toNat : Int) - ((pred.getD i 0).toNat : Int))
  let h := hadamard4x4 diff
  let mut acc : Nat := 0
  for i in [:16] do acc := acc + (h.getD i 0).natAbs
  return acc / 2

def chooseIntra4x4 (src16 : Array UInt8) (n : IntraNeighbors) : Nat × Array UInt8 := Id.run do
  let mut bestMode := 2
  let mut bestPred := pred4x4 2 n
  let mut bestCost := satd4x4 src16 bestPred
  for m in [:9] do
    if isLegalIntraNxNMode m n then
      let p := pred4x4 m n
      let cost := satd4x4 src16 p
      if cost < bestCost then
        bestMode := m; bestPred := p; bestCost := cost
  return (bestMode, bestPred)

def chooseIntra8x8 (src64 : Array UInt8) (n : IntraNeighbors) : Nat × Array UInt8 := Id.run do
  let mut bestMode := 2
  let mut bestPred := pred8x8 2 n
  let mut bestCost := sadBlock src64 bestPred
  for m in [:9] do
    if isLegalIntraNxNMode m n then
      let p := pred8x8 m n
      let cost := sadBlock src64 p
      if cost < bestCost then
        bestMode := m; bestPred := p; bestCost := cost
  return (bestMode, bestPred)

def chooseIntra16x16 (src256 left top : Array UInt8) (tl : UInt8)
    (leftAv topAv tlAv : Bool) : Nat × Array UInt8 := Id.run do
  let mut bestMode := 2
  let mut bestPred := pred16x16 2 left top tl leftAv topAv
  let mut bestCost := sadBlock src256 bestPred
  for m in [:4] do
    if isLegalIntra16x16Mode m leftAv topAv tlAv then
      let p := pred16x16 m left top tl leftAv topAv
      let cost := sadBlock src256 p
      if cost < bestCost then
        bestMode := m; bestPred := p; bestCost := cost
  return (bestMode, bestPred)

def chooseIntraChroma (srcU srcV leftU topU leftV topV : Array UInt8) (tlU tlV : UInt8)
    (leftAv topAv tlAv : Bool) : Nat × Array UInt8 × Array UInt8 := Id.run do
  let mut bestMode := 0
  let mut bestU := predChroma 0 leftU topU tlU leftAv topAv
  let mut bestV := predChroma 0 leftV topV tlV leftAv topAv
  let mut bestCost := sadBlock srcU bestU + sadBlock srcV bestV
  for m in [:4] do
    if isLegalIntraChromaMode m leftAv topAv tlAv then
      let pu := predChroma m leftU topU tlU leftAv topAv
      let pv := predChroma m leftV topV tlV leftAv topAv
      let cost := sadBlock srcU pu + sadBlock srcV pv
      if cost < bestCost then
        bestMode := m
        bestU := pu
        bestV := pv
        bestCost := cost
  return (bestMode, bestU, bestV)

def encodeSamplesLosslessList : List UInt8 → List UInt8 → List Int
  | s :: ss, p :: ps => losslessSampleResidual s p :: encodeSamplesLosslessList ss ps
  | _, _ => []

def decodeSamplesLosslessList : List UInt8 → List Int → List UInt8
  | p :: ps, r :: rs => losslessSampleReconstruct p r :: decodeSamplesLosslessList ps rs
  | _, _ => []

def encodeSamplesLossless (samples preds : Array UInt8) : Array Int :=
  (encodeSamplesLosslessList samples.toList preds.toList).toArray

def decodeSamplesLossless (preds : Array UInt8) (res : Array Int) : Array UInt8 :=
  (decodeSamplesLosslessList preds.toList res.toList).toArray

structure H264IntraMbNeighbors where
  leftAvail     : Bool
  topAvail      : Bool
  topRightAvail : Bool
  topLeftAvail  : Bool
  leftY         : Array UInt8
  topY          : Array UInt8
  topRightY     : Array UInt8
  topLeftY      : UInt8
  leftU         : Array UInt8
  topU          : Array UInt8
  topLeftU      : UInt8
  leftV         : Array UInt8
  topV          : Array UInt8
  topLeftV      : UInt8
  deriving Repr, DecidableEq, Inhabited

structure H264Yuv420pMb where
  y : Array UInt8
  u : Array UInt8
  v : Array UInt8
  deriving Repr, DecidableEq, Inhabited

def H264Yuv420pMb.valid (mb : H264Yuv420pMb) : Bool :=
  mb.y.size == 256 && mb.u.size == 64 && mb.v.size == 64

structure LosslessIntraMbCoded where
  partitionKind : Nat
  lumaModes     : List Nat
  chromaMode    : Nat
  yBlocks       : List (Array Int)
  uLevels       : Array Int
  vLevels       : Array Int
  deriving Repr, DecidableEq, Inhabited

def zScan4BlkIdx (bx byy : Nat) : Nat :=
  (byy / 2) * 8 + (bx / 2) * 4 + (byy % 2) * 2 + (bx % 2)

def zScan4BlkCoord (blkIdx : Nat) : Nat × Nat :=
  (((blkIdx / 4) % 2) * 8 + (blkIdx % 2) * 4, (blkIdx / 8) * 8 + ((blkIdx / 2) % 2) * 4)

def zScan4AllowTopRight (blkIdx : Nat) (mbTopAvail mbTopRightAvail : Bool) : Bool :=
  if blkIdx == 3 || blkIdx == 7 || blkIdx == 11 || blkIdx == 13 || blkIdx == 15 then false
  else if blkIdx == 5 then mbTopRightAvail
  else if blkIdx == 0 || blkIdx == 1 || blkIdx == 4 then mbTopAvail
  else true

def extractMbBlock4 (y256 : Array UInt8) (xO yO : Nat) : Array UInt8 :=
  Array.ofFn fun idx : Fin 16 =>
    y256.getD ((yO + idx.val / 4) * 16 + (xO + idx.val % 4)) 0

def writeMbBlock4 (canvas256 : Array UInt8) (xO yO : Nat) (blk16 : Array UInt8) : Array UInt8 :=
  Array.ofFn fun idx : Fin 256 =>
    let y := idx.val / 16
    let x := idx.val % 16
    if xO ≤ x && x < xO + 4 && yO ≤ y && y < yO + 4 then
      blk16.getD ((y - yO) * 4 + (x - xO)) 0
    else canvas256.getD idx.val 0

def assembleMbBlocks4 (blks : List (Array UInt8)) : Array UInt8 :=
  let arr := blks.toArray
  Array.ofFn fun idx : Fin 256 =>
    let y := idx.val / 16
    let x := idx.val % 16
    let b := zScan4BlkIdx (x / 4) (y / 4)
    (arr.getD b #[]).getD ((y % 4) * 4 + (x % 4)) 0

def extractMbBlock8 (y256 : Array UInt8) (xO yO : Nat) : Array UInt8 :=
  Array.ofFn fun idx : Fin 64 =>
    y256.getD ((yO + idx.val / 8) * 16 + (xO + idx.val % 8)) 0

def writeMbBlock8 (canvas256 : Array UInt8) (xO yO : Nat) (blk64 : Array UInt8) : Array UInt8 :=
  Array.ofFn fun idx : Fin 256 =>
    let y := idx.val / 16
    let x := idx.val % 16
    if xO ≤ x && x < xO + 8 && yO ≤ y && y < yO + 8 then
      blk64.getD ((y - yO) * 8 + (x - xO)) 0
    else canvas256.getD idx.val 0

def assembleMbBlocks8 (blks : List (Array UInt8)) : Array UInt8 :=
  let arr := blks.toArray
  Array.ofFn fun idx : Fin 256 =>
    let y := idx.val / 16
    let x := idx.val % 16
    let b := (y / 8) * 2 + (x / 8)
    (arr.getD b #[]).getD ((y % 8) * 8 + (x % 8)) 0

def mbSubblockNeighbors (nSz : Nat) (canvas256 : Array UInt8) (nbrs : H264IntraMbNeighbors)
    (xO yO : Nat) (trAvail : Bool) : IntraNeighbors :=
  let leftAv := if xO == 0 then nbrs.leftAvail else true
  let topAv := if yO == 0 then nbrs.topAvail else true
  let tlAv := if xO == 0 && yO == 0 then nbrs.topLeftAvail
              else if yO == 0 then nbrs.topAvail
              else if xO == 0 then nbrs.leftAvail else true
  let left := Array.ofFn fun i : Fin nSz =>
    if xO == 0 then nbrs.leftY.getD (yO + i.val) 128
    else canvas256.getD ((yO + i.val) * 16 + (xO - 1)) 128
  let top := Array.ofFn fun i : Fin nSz =>
    if yO == 0 then nbrs.topY.getD (xO + i.val) 128
    else canvas256.getD ((yO - 1) * 16 + (xO + i.val)) 128
  let rep := top.getD (nSz - 1) 128
  let topRight := Array.ofFn fun i : Fin nSz =>
    if !trAvail then rep
    else if yO == 0 then
      if xO + nSz + i.val < 16 then nbrs.topY.getD (xO + nSz + i.val) rep
      else nbrs.topRightY.getD (xO + nSz + i.val - 16) rep
    else canvas256.getD ((yO - 1) * 16 + (xO + nSz + i.val)) rep
  let tl :=
    if xO == 0 && yO == 0 then nbrs.topLeftY
    else if yO == 0 then nbrs.topY.getD (xO - 1) 128
    else if xO == 0 then nbrs.leftY.getD (yO - 1) 128
    else canvas256.getD ((yO - 1) * 16 + (xO - 1)) 128
  { leftAvail := leftAv, topAvail := topAv, topRightAvail := trAvail, topLeftAvail := tlAv,
    left := left, top := top, topRight := topRight, topLeft := tl }

def zScan4Schedule (topAv topRightAv : Bool) : List (Nat × Nat × Bool) :=
  (List.range 16).map fun b =>
    let (xO, yO) := zScan4BlkCoord b
    (xO, yO, zScan4AllowTopRight b topAv topRightAv)

def zScan8Schedule (topAv topRightAv : Bool) : List (Nat × Nat × Bool) :=
  [(0, 0, topAv), (8, 0, topRightAv), (0, 8, true), (8, 8, false)]

def encodeSubblocks4x4List (srcY256 canvas256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    List (Nat × Nat × Bool) → List Nat → List (Array Int)
  | [], _ => []
  | (xO, yO, trAv) :: rest, modes =>
    let m := modes.headD 2
    let n := mbSubblockNeighbors 4 canvas256 nbrs xO yO trAv
    let pred16 := pred4x4 m n
    let blk16 := extractMbBlock4 srcY256 xO yO
    let lv16 := encodeResidualDpcm4x4 m (encodeSamplesLossless blk16 pred16)
    let canvas' := writeMbBlock4 canvas256 xO yO blk16
    lv16 :: encodeSubblocks4x4List srcY256 canvas' nbrs rest (modes.drop 1)

def decodeSubblocks4x4List (canvas256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    List (Nat × Nat × Bool) → List Nat → List (Array Int) → List (Array UInt8)
  | [], _, _ => []
  | (xO, yO, trAv) :: rest, modes, lvs =>
    let m := modes.headD 2
    let lv16 := lvs.headD (Array.replicate 16 0)
    let n := mbSubblockNeighbors 4 canvas256 nbrs xO yO trAv
    let pred16 := pred4x4 m n
    let blk16 := decodeSamplesLossless pred16 (decodeResidualDpcm4x4 m lv16)
    let canvas' := writeMbBlock4 canvas256 xO yO blk16
    blk16 :: decodeSubblocks4x4List canvas' nbrs rest (modes.drop 1) (lvs.drop 1)

def encodeSubblocks8x8List (srcY256 canvas256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    List (Nat × Nat × Bool) → List Nat → List (Array Int)
  | [], _ => []
  | (xO, yO, trAv) :: rest, modes =>
    let m := modes.headD 2
    let n := mbSubblockNeighbors 8 canvas256 nbrs xO yO trAv
    let pred64 := pred8x8 m n
    let blk64 := extractMbBlock8 srcY256 xO yO
    let lv64 := encodeResidualDpcm8x8 m (encodeSamplesLossless blk64 pred64)
    let canvas' := writeMbBlock8 canvas256 xO yO blk64
    lv64 :: encodeSubblocks8x8List srcY256 canvas' nbrs rest (modes.drop 1)

def decodeSubblocks8x8List (canvas256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    List (Nat × Nat × Bool) → List Nat → List (Array Int) → List (Array UInt8)
  | [], _, _ => []
  | (xO, yO, trAv) :: rest, modes, lvs =>
    let m := modes.headD 2
    let lv64 := lvs.headD (Array.replicate 64 0)
    let n := mbSubblockNeighbors 8 canvas256 nbrs xO yO trAv
    let pred64 := pred8x8 m n
    let blk64 := decodeSamplesLossless pred64 (decodeResidualDpcm8x8 m lv64)
    let canvas' := writeMbBlock8 canvas256 xO yO blk64
    blk64 :: decodeSubblocks8x8List canvas' nbrs rest (modes.drop 1) (lvs.drop 1)

def ipcmMbTypeI : UInt64 := 25

def ipcmBlockNonZeroCount (blkIdx : Nat) : Nat :=
  if blkIdx < 24 then 16 else 0

def encodeIpcmMb420 (mb : H264Yuv420pMb) : Array UInt8 :=
  mb.y ++ mb.u ++ mb.v

def decodeIpcmMb420 (pcm : Array UInt8) : Option H264Yuv420pMb :=
  if pcm.size == 384 then
    some {
      y := Array.ofFn fun i : Fin 256 => pcm.getD i.val 0,
      u := Array.ofFn fun i : Fin 64 => pcm.getD (256 + i.val) 0,
      v := Array.ofFn fun i : Fin 64 => pcm.getD (320 + i.val) 0 }
  else
    none

def writeIpcmMb420Bits (w : BitWriter) (mb : H264Yuv420pMb) : BitWriter :=
  let wAligned := (w.writeUE ipcmMbTypeI).alignToByte
  let raw := encodeIpcmMb420 mb
  { bytes := { data := wAligned.bytes.data ++ raw }, curByte := 0, bitsUsed := 0 }

def readIpcmBytesList (s : ByteSlice) (byteStart : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => s.getByteD byteStart 0 :: readIpcmBytesList s (byteStart + 1) k

def readIpcmMb420Bits (r : BitReader) : Option (H264Yuv420pMb × BitReader) :=
  match r.readUE 5 with
  | none => none
  | some (mbType, rAfterType) =>
    if mbType != ipcmMbTypeI then none
    else
      let rAligned := rAfterType.alignToByte
      let byteStart := rAligned.bitOffset / 8
      if rAligned.bitOffset % 8 != 0 || byteStart + 384 > rAligned.slice.len then
        none
      else
        let raw := (readIpcmBytesList rAligned.slice byteStart 384).toArray
        match decodeIpcmMb420 raw with
        | none => none
        | some mb => some (mb, { rAligned with bitOffset := (byteStart + 384) * 8 })

def encodeLosslessIntraMb (mb : H264Yuv420pMb) (nbrs : H264IntraMbNeighbors)
    (partitionKind : Nat) (lumaModes : List Nat) (chromaMode : Nat) : LosslessIntraMbCoded :=
  if partitionKind == 3 then
    { partitionKind := 3, lumaModes := [], chromaMode := 0,
      yBlocks := [mb.y.map fun s => (s.toNat : Int)],
      uLevels := mb.u.map fun s => (s.toNat : Int),
      vLevels := mb.v.map fun s => (s.toNat : Int) }
  else
    let zeroCanvas := Array.replicate 256 (0 : UInt8)
    let yBlocks :=
      if partitionKind == 0 then
        encodeSubblocks4x4List mb.y zeroCanvas nbrs (zScan4Schedule nbrs.topAvail nbrs.topRightAvail) lumaModes
      else if partitionKind == 1 then
        encodeSubblocks8x8List mb.y zeroCanvas nbrs (zScan8Schedule nbrs.topAvail nbrs.topRightAvail) lumaModes
      else
        let predY := pred16x16 (lumaModes.headD 2) nbrs.leftY nbrs.topY nbrs.topLeftY nbrs.leftAvail nbrs.topAvail
        [encodeSamplesLossless mb.y predY]
    let predU := predChroma chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail
    let predV := predChroma chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail
    { partitionKind := partitionKind, lumaModes := lumaModes, chromaMode := chromaMode,
      yBlocks := yBlocks, uLevels := encodeSamplesLossless mb.u predU,
      vLevels := encodeSamplesLossless mb.v predV }

def decodeLosslessIntraMb (coded : LosslessIntraMbCoded) (nbrs : H264IntraMbNeighbors) : H264Yuv420pMb :=
  if coded.partitionKind == 3 then
    { y := (coded.yBlocks.headD #[]).map clipU8,
      u := coded.uLevels.map clipU8,
      v := coded.vLevels.map clipU8 }
  else
    let zeroCanvas := Array.replicate 256 (0 : UInt8)
    let recY :=
      if coded.partitionKind == 0 then
        let blks := decodeSubblocks4x4List zeroCanvas nbrs
          (zScan4Schedule nbrs.topAvail nbrs.topRightAvail) coded.lumaModes coded.yBlocks
        assembleMbBlocks4 blks
      else if coded.partitionKind == 1 then
        let blks := decodeSubblocks8x8List zeroCanvas nbrs
          (zScan8Schedule nbrs.topAvail nbrs.topRightAvail) coded.lumaModes coded.yBlocks
        assembleMbBlocks8 blks
      else
        let predY := pred16x16 (coded.lumaModes.headD 2) nbrs.leftY nbrs.topY nbrs.topLeftY nbrs.leftAvail nbrs.topAvail
        decodeSamplesLossless predY (coded.yBlocks.headD (Array.replicate 256 0))
    let predU := predChroma coded.chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail
    let predV := predChroma coded.chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail
    { y := recY, u := decodeSamplesLossless predU coded.uLevels,
      v := decodeSamplesLossless predV coded.vLevels }

def reconstructChroma8x8Lossy (pred64 : Array UInt8) (dc4 : Array Int)
    (ac4x4s : Array (Array Int)) (qpc : Nat) : Array UInt8 := Id.run do
  let (d00, d01, d10, d11) := chromaDcDequant
    (dc4.getD 0 0) (dc4.getD 1 0) (dc4.getD 2 0) (dc4.getD 3 0) qpc
  let dcArr := #[d00, d01, d10, d11]
  let mut out := Array.replicate 64 (0 : UInt8)
  for idx in [:4] do
    let bxx := idx % 2
    let byy := idx / 2
    let ac := ac4x4s.getD idx (Array.replicate 16 0)
    let scaled := (dequant4x4 ac qpc).set! 0 (dcArr.getD idx 0)
    let res16 := idct4x4FromScaled scaled
    for y in [:4] do for x in [:4] do
      let pIdx := (byy * 4 + y) * 8 + bxx * 4 + x
      out := out.set! pIdx (clipU8 (((pred64.getD pIdx 0).toNat : Int) + res16.getD (y * 4 + x) 0))
  return Array.ofFn fun i : Fin 64 => out.getD i.val 0

def reconstructIntra16x16LumaLossy (pred256 : Array UInt8) (lumaDc16 : Array Int)
    (ac16 : Array (Array Int)) (qp : Nat) : Array UInt8 := Id.run do
  let dcScaled := lumaDcDequant lumaDc16 qp
  let mut out := Array.replicate 256 (0 : UInt8)
  for blkIdx in [:16] do
    let (xO, yO) := zScan4BlkCoord blkIdx
    let dcPos := (yO / 4) * 4 + (xO / 4)
    let ac := ac16.getD blkIdx (Array.replicate 16 0)
    let scaled := (dequant4x4 ac qp).set! 0 (dcScaled.getD dcPos 0)
    let res16 := idct4x4FromScaled scaled
    for y in [:4] do for x in [:4] do
      let pIdx := (yO + y) * 16 + (xO + x)
      out := out.set! pIdx (clipU8 (((pred256.getD pIdx 0).toNat : Int) + res16.getD (y * 4 + x) 0))
  return Array.ofFn fun i : Fin 256 => out.getD i.val 0

structure LossyIntraMbCoded where
  partitionKind : Nat
  qpY           : Nat
  chromaQpIdxOffset : Int
  lumaModes     : List Nat
  chromaMode    : Nat
  lumaDc16      : Array Int
  yBlocks       : List (Array Int)
  uDc4          : Array Int
  uAc4          : Array (Array Int)
  vDc4          : Array Int
  vAc4          : Array (Array Int)
  deriving Repr, DecidableEq, Inhabited

def clampQp (qp : Nat) : Nat :=
  if qp > 51 then 51 else qp

def reconstructSubblock4Idct (pred16 : Array UInt8) (levels16 : Array Int)
    (qp : Nat) (dcOverride : Option Int := none) : Array UInt8 :=
  let res := inverseResidual4x4 levels16 qp dcOverride
  Array.ofFn fun i : Fin 16 =>
    clipU8 (((pred16.getD i.val 0).toNat : Int) + res.getD i.val 0)

def reconstructSubblock8Idct (pred64 : Array UInt8) (levels64 : Array Int)
    (qp : Nat) : Array UInt8 :=
  let res := inverseResidual8x8 levels64 qp
  Array.ofFn fun i : Fin 64 =>
    clipU8 (((pred64.getD i.val 0).toNat : Int) + res.getD i.val 0)

def reconstructLossyIntraMb (coded : LossyIntraMbCoded) (nbrs : H264IntraMbNeighbors) : H264Yuv420pMb := Id.run do
  let qp := clampQp coded.qpY
  let qpc := qpcFromQpy qp coded.chromaQpIdxOffset
  let mut canvasY := Array.replicate 256 (0 : UInt8)
  if coded.partitionKind == 0 then
    let sched := zScan4Schedule nbrs.topAvail nbrs.topRightAvail
    for b in [:16] do
      let (xO, yO, trAv) := sched.getD b (0, 0, false)
      let m := coded.lumaModes.getD b 2
      let n := mbSubblockNeighbors 4 canvasY nbrs xO yO trAv
      let pred16 := pred4x4 m n
      let lv16 := coded.yBlocks.getD b (Array.replicate 16 0)
      let rec16 := reconstructSubblock4Idct pred16 lv16 qp
      canvasY := writeMbBlock4 canvasY xO yO rec16
  else if coded.partitionKind == 1 then
    let sched := zScan8Schedule nbrs.topAvail nbrs.topRightAvail
    for b in [:4] do
      let (xO, yO, trAv) := sched.getD b (0, 0, false)
      let m := coded.lumaModes.getD b 2
      let n := mbSubblockNeighbors 8 canvasY nbrs xO yO trAv
      let pred64 := pred8x8 m n
      let lv64 := coded.yBlocks.getD b (Array.replicate 64 0)
      let rec64 := reconstructSubblock8Idct pred64 lv64 qp
      canvasY := writeMbBlock8 canvasY xO yO rec64
  else
    let pred256 := pred16x16 (coded.lumaModes.headD 2) nbrs.leftY nbrs.topY nbrs.topLeftY nbrs.leftAvail nbrs.topAvail
    canvasY := reconstructIntra16x16LumaLossy pred256 coded.lumaDc16 coded.yBlocks.toArray qp
  let predU := predChroma coded.chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail
  let predV := predChroma coded.chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail
  let recU := reconstructChroma8x8Lossy predU coded.uDc4 coded.uAc4 qpc
  let recV := reconstructChroma8x8Lossy predV coded.vDc4 coded.vAc4 qpc
  return { y := canvasY, u := recU, v := recV }

def encodeChroma8x8Lossy (src64 pred64 : Array UInt8) (qpc : Nat) :
    Array Int × Array (Array Int) := Id.run do
  let mut dcs := Array.replicate 4 (0 : Int)
  let mut acs := Array.replicate 4 (Array.replicate 16 (0 : Int))
  for idx in [:4] do
    let bxx := idx % 2
    let byy := idx / 2
    let mut res16 := Array.replicate 16 (0 : Int)
    for y in [:4] do for x in [:4] do
      let pIdx := (byy * 4 + y) * 8 + bxx * 4 + x
      res16 := res16.set! (y * 4 + x) (((src64.getD pIdx 0).toNat : Int) - ((pred64.getD pIdx 0).toNat : Int))
    let coeff := forwardDct4x4 res16
    dcs := dcs.set! idx (coeff.getD 0 0)
    acs := acs.set! idx ((quant4x4 coeff qpc true).set! 0 0)
  let (h0, h1, h2, h3) := hadamard2x2 (dcs.getD 0 0) (dcs.getD 1 0) (dcs.getD 2 0) (dcs.getD 3 0)
  let qbits := 16 + qpDiv6 qpc
  let mf := mf4x4Table (qpMod6 qpc) 0
  let f := shlInt 1 qbits / 3
  let qDc (w : Int) : Int :=
    let mag := asrInt (Int.ofNat w.natAbs * mf + f) qbits
    if w < 0 then -mag else mag
  return (#[qDc h0, qDc h1, qDc h2, qDc h3], acs)

def encodeLossyIntraMb (mb : H264Yuv420pMb) (nbrs : H264IntraMbNeighbors)
    (partitionKind qpY : Nat) (chromaQpIdxOffset : Int) : LossyIntraMbCoded := Id.run do
  let qp := clampQp qpY
  let qpc := qpcFromQpy qp chromaQpIdxOffset
  let mut canvasY := Array.replicate 256 (0 : UInt8)
  let mut lumaModes : List Nat := []
  let mut yBlocks : List (Array Int) := []
  let mut lumaDc16 := Array.replicate 16 (0 : Int)
  if partitionKind == 0 then
    let sched := zScan4Schedule nbrs.topAvail nbrs.topRightAvail
    for b in [:16] do
      let (xO, yO, trAv) := sched.getD b (0, 0, false)
      let n := mbSubblockNeighbors 4 canvasY nbrs xO yO trAv
      let src16 := extractMbBlock4 mb.y xO yO
      let (m, pred16) := chooseIntra4x4 src16 n
      let res16 := Array.ofFn fun i : Fin 16 =>
        ((src16.getD i.val 0).toNat : Int) - ((pred16.getD i.val 0).toNat : Int)
      let lv16 := quant4x4 (forwardDct4x4 res16) qp true
      let rec16 := reconstructSubblock4Idct pred16 lv16 qp
      canvasY := writeMbBlock4 canvasY xO yO rec16
      lumaModes := lumaModes ++ [m]
      yBlocks := yBlocks ++ [lv16]
  else if partitionKind == 1 then
    let sched := zScan8Schedule nbrs.topAvail nbrs.topRightAvail
    for b in [:4] do
      let (xO, yO, trAv) := sched.getD b (0, 0, false)
      let n := mbSubblockNeighbors 8 canvasY nbrs xO yO trAv
      let src64 := extractMbBlock8 mb.y xO yO
      let (m, pred64) := chooseIntra8x8 src64 n
      let res64 := Array.ofFn fun i : Fin 64 =>
        ((src64.getD i.val 0).toNat : Int) - ((pred64.getD i.val 0).toNat : Int)
      let lv64 := quant8x8 (forwardDct8x8 res64) qp true
      let rec64 := reconstructSubblock8Idct pred64 lv64 qp
      canvasY := writeMbBlock8 canvasY xO yO rec64
      lumaModes := lumaModes ++ [m]
      yBlocks := yBlocks ++ [lv64]
  else
    let (m, pred256) := chooseIntra16x16 mb.y nbrs.leftY nbrs.topY nbrs.topLeftY
      nbrs.leftAvail nbrs.topAvail nbrs.topLeftAvail
    lumaModes := [m]
    let mut rawDcs := Array.replicate 16 (0 : Int)
    for b in [:16] do
      let (xO, yO) := zScan4BlkCoord b
      let src16 := extractMbBlock4 mb.y xO yO
      let pr16 := extractMbBlock4 pred256 xO yO
      let res16 := Array.ofFn fun i : Fin 16 =>
        ((src16.getD i.val 0).toNat : Int) - ((pr16.getD i.val 0).toNat : Int)
      let coeff := forwardDct4x4 res16
      rawDcs := rawDcs.set! ((yO / 4) * 4 + (xO / 4)) (coeff.getD 0 0)
      yBlocks := yBlocks ++ [(quant4x4 coeff qp true).set! 0 0]
    let hDc := hadamard4x4 rawDcs
    let qbits := 16 + qpDiv6 qp
    let mf := mf4x4Table (qpMod6 qp) 0
    let f := shlInt 1 qbits / 3
    lumaDc16 := hDc.map fun w =>
      let mag := asrInt (Int.ofNat w.natAbs * mf + f) qbits
      if w < 0 then -mag else mag
  let (cm, predU, predV) := chooseIntraChroma mb.u mb.v nbrs.leftU nbrs.topU nbrs.leftV nbrs.topV
    nbrs.topLeftU nbrs.topLeftV nbrs.leftAvail nbrs.topAvail nbrs.topLeftAvail
  let (uDc4, uAc4) := encodeChroma8x8Lossy mb.u predU qpc
  let (vDc4, vAc4) := encodeChroma8x8Lossy mb.v predV qpc
  return { partitionKind := partitionKind, qpY := qp, chromaQpIdxOffset := chromaQpIdxOffset,
           lumaModes := lumaModes, chromaMode := cm, lumaDc16 := lumaDc16,
           yBlocks := yBlocks, uDc4 := uDc4, uAc4 := uAc4, vDc4 := vDc4, vAc4 := vAc4 }

def insertRbspEmulationBytes (rbsp : ByteArray) : ByteArray := Id.run do
  let mut out : Array UInt8 := #[]
  let mut zeroRun : Nat := 0
  for i in [:rbsp.size] do
    let b := rbsp.get! i
    if zeroRun >= 2 && b <= 3 then
      out := out.push 3
      zeroRun := 0
    out := out.push b
    zeroRun := if b == 0 then zeroRun + 1 else 0
  return { data := out }

def stripRbspEmulationList (zeroRun : Nat) : List UInt8 → List UInt8 → List UInt8
  | [], accRev => accRev.reverse
  | b :: rest, accRev =>
    if zeroRun == 2 && b == 3 then
      stripRbspEmulationList 0 rest accRev
    else
      let nextRun := if b == 0 then zeroRun + 1 else 0
      stripRbspEmulationList nextRun rest (b :: accRev)

def stripRbspBytes (ebsp : ByteSlice) : ByteArray :=
  let xs := (ebsp.ba.data.toList.drop ebsp.off).take ebsp.len
  { data := (stripRbspEmulationList 0 xs []).toArray }

def encodeAnnexBNal (nalHeader : UInt8) (rbsp : ByteArray) : ByteArray :=
  let ebsp := insertRbspEmulationBytes rbsp
  { data := #[0, 0, 0, 1, nalHeader] ++ ebsp.data }

def encodeMinimalBaselineSps16x16 : ByteArray :=
  let w0 := BitWriter.empty
  let w1 := (((w0.writeBitsMSB 66 8).writeBitsMSB 0xC0 8).writeBitsMSB 10 8).writeUE 0
  let w2 := (((w1.writeUE 0).writeUE 2).writeUE 0).writeBit 0
  let w3 := (((((w2.writeUE 0).writeUE 0).writeBit 1).writeBit 1).writeBit 0).writeBit 0
  encodeAnnexBNal 0x67 (w3.writeBit 1).toByteArray

def encodeMinimalBaselinePps : ByteArray :=
  let w0 := BitWriter.empty
  let w1 := ((((w0.writeUE 0).writeUE 0).writeBit 0).writeBit 0).writeUE 0
  let w2 := (((w1.writeUE 0).writeUE 0).writeBit 0).writeBitsMSB 0 2
  let w3 := ((((w2.writeSE 0).writeSE 0).writeSE 0).writeBit 1).writeBit 0
  encodeAnnexBNal 0x68 ((w3.writeBit 0).writeBit 1).toByteArray

def encodeAnnexBIpcmIdr16x16 (mb : H264Yuv420pMb) : ByteArray :=
  let w0 := BitWriter.empty
  let wHdr := ((((((((w0.writeUE 0).writeUE 7).writeUE 0).writeBitsMSB 0 4).writeUE 0).writeBit 0).writeBit 0).writeSE 0).writeUE 1
  let wMb := writeIpcmMb420Bits wHdr mb
  let sliceRbsp := (wMb.writeBit 1).toByteArray
  encodeMinimalBaselineSps16x16 ++ encodeMinimalBaselinePps ++ encodeAnnexBNal 0x65 sliceRbsp

def decodeAnnexBIpcmIdr16x16 (stream : ByteArray) : Option H264Yuv420pMb := Id.run do
  let s := ByteSlice.ofByteArray stream
  let mut p : Nat := 0
  let mut starts : Array (Nat × Nat) := #[]
  while p + 3 ≤ s.len do
    if p + 4 ≤ s.len && s.getByteD p 1 == 0 && s.getByteD (p + 1) 1 == 0 &&
       s.getByteD (p + 2) 1 == 0 && s.getByteD (p + 3) 0 == 1 then
      starts := starts.push (p, 4)
      p := p + 4
    else if s.getByteD p 1 == 0 && s.getByteD (p + 1) 1 == 0 && s.getByteD (p + 2) 0 == 1 then
      starts := starts.push (p, 3)
      p := p + 3
    else
      p := p + 1
  for idx in [:starts.size] do
    let (scPos, scLen) := starts[idx]!
    let endPos := if idx + 1 < starts.size then (starts[idx + 1]!).1 else s.len
    if scPos + scLen + 1 ≤ endPos then
      let hdr := s.getByteD (scPos + scLen) 0
      if (hdr &&& 0x1F) == 5 then
        if let some bodySlice := s.subSlice? (scPos + scLen + 1) (endPos - (scPos + scLen + 1)) then
          let rbsp := stripRbspBytes bodySlice
          let r0 := BitReader.ofSlice (ByteSlice.ofByteArray rbsp)
          if let some (_, r1) := r0.readUE 8 then
          if let some (_, r2) := r1.readUE 8 then
          if let some (_, r3) := r2.readUE 8 then
          if let some (_, r4) := r3.readBitsMSB 4 then
          if let some (_, r5) := r4.readUE 8 then
          if let some (_, r6) := r5.readBit then
          if let some (_, r7) := r6.readBit then
          if let some (_, r8) := r7.readSE 8 then
          if let some (disDeblock, r9) := r8.readUE 8 then
            let rMbOpt :=
              if disDeblock == 1 then some r9
              else match r9.readSE 8 with
                   | none => none
                   | some (_, rA) => rA.readSE 8 |>.map Prod.snd
            if let some rMb := rMbOpt then
              if let some (mb, _) := readIpcmMb420Bits rMb then
                return some mb
  return none

/-! ## High / High10 / High 4:2:2 / High 4:4:4 Predictive Generalization -/

/-- `(1 <<< bitDepth) - 1` sample maximum for High/High10/High422/High444 (`bitDepth ∈ {8..12}`). -/
@[inline] def h264SampleMax (bitDepth : Nat) : Nat :=
  (1 <<< bitDepth) - 1

/-- Mid-scale DC prediction default `1 <<< (bitDepth - 1)` (`128` at 8-bit, `512` at 10-bit, `2048` at 12-bit). -/
@[inline] def h264MidSample (bitDepth : Nat) : Nat :=
  1 <<< (bitDepth - 1)

/-- Clip an `Int` sample to `[0, (1 <<< bitDepth) - 1]`. -/
@[inline] def clipSampleHbd (v : Int) (bitDepth : Nat) : Nat :=
  let maxV : Int := h264SampleMax bitDepth
  (clip3 0 maxV v).toNat

@[inline] def avg2Nat (a b : Nat) : Nat :=
  (a + b + 1) / 2

@[inline] def filt3Nat (a b c : Nat) : Nat :=
  (a + 2 * b + c + 2) / 4

/-- `ISO/IEC 14496-10` Table 8-15 `qP_C` derivation generalized across `bit_depth_chroma_minus8` (`QpBdOffsetC`).
    `qPi` is clipped to `[-QpBdOffsetC, 51]`, mapped via Table 8-15 for `qPi ≥ 30` (linear for `qPi < 30`,
    including negative `qPi`), and shifted by `+QpBdOffsetC` into `[0, 51 + QpBdOffsetC]`. -/
def qpcFromQpyHbd (qpPrimeY : Nat) (chromaOffset : Int) (bitDepthC : Nat := 8) : Nat :=
  let qpBdOffsetC : Int := 6 * ((bitDepthC : Int) - 8)
  let qPi := clip3 (-qpBdOffsetC) 51 ((qpPrimeY : Int) - qpBdOffsetC + chromaOffset)
  let qPc :=
    if qPi < 30 then qPi
    else (qpcTable30.getD (qPi.toNat - 30) 39 : Int)
  (qPc + qpBdOffsetC).toNat

/-- 4:2:2 Chroma DC Hadamard dequant (`ISO/IEC 14496-10` Clause 8.5.11.2) uses `qP_C + 3`. -/
def qpc422Dc (qpc : Nat) : Nat :=
  qpc + 3

/-- Dequantize a single 4×4 coefficient using a custom `weightScale` (default flat `16`). -/
def dequantCoeff4x4 (level : Int) (qp i j : Nat) (weightScale : Int := 16) : Int :=
  let q := qpDiv6 qp
  let ls := levelScale4x4 qp i j weightScale
  if qp ≥ 24 then shlInt (level * ls) (q - 4)
  else asrInt (level * ls + shlInt 1 (3 - q)) (4 - q)

/-- Dequantize a single 8×8 coefficient using a custom `weightScale` (default flat `16`). -/
def dequantCoeff8x8 (level : Int) (qp i j : Nat) (weightScale : Int := 16) : Int :=
  let q := qpDiv6 qp
  let ls := levelScale8x8 qp i j weightScale
  if qp ≥ 36 then shlInt (level * ls) (q - 6)
  else asrInt (level * ls + shlInt 1 (5 - q)) (6 - q)

/-- Forward-quantize a single 4×4 coefficient using a custom `weightScale` (default flat `16`). -/
def quantCoeff4x4 (coeff : Int) (qp i j : Nat) (intra : Bool) (weightScale : Int := 16) : Int :=
  let q := qpDiv6 qp
  let qbits := 15 + q
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  let sign : Int := if coeff < 0 then -1 else 1
  let mf := mf4x4Table (qpMod6 qp) (posClass4x4 i j)
  let denom := if weightScale == 0 then 1 else weightScale
  let mag := asrInt (sign * coeff * mf * 16 / denom + f) qbits
  sign * mag

/-- Forward-quantize a single 8×8 coefficient using a custom `weightScale` (default flat `16`). -/
def quantCoeff8x8 (coeff : Int) (qp i j : Nat) (intra : Bool) (weightScale : Int := 16) : Int :=
  let q := qpDiv6 qp
  let qbits := 16 + q
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  let sign : Int := if coeff < 0 then -1 else 1
  let mf := mf8x8Table (qpMod6 qp) (posClass8x8 i j)
  let denom := if weightScale == 0 then 1 else weightScale
  let mag := asrInt (sign * coeff * mf * 16 / denom + f) qbits
  sign * mag

/-- `ISO/IEC 14496-10` Figure 8-7 2×4 chroma DC scan order: scan index `k ∈ 0..7` → raster `ry * 2 + rx`. -/
def chromaDcScan2x4 : Array Nat :=
  #[0, 2, 1, 4, 6, 3, 5, 7]

def chromaDcRaster2x4Inv : Array Nat :=
  #[0, 2, 1, 5, 3, 6, 4, 7]

def chromaDcScan2x4ToRaster (scan8 : Array Int) : Array Int :=
  Array.ofFn fun r : Fin 8 => scan8.getD (chromaDcRaster2x4Inv.getD r.val 0) 0

def chromaDcRasterToScan2x4 (raster8 : Array Int) : Array Int :=
  Array.ofFn fun k : Fin 8 => raster8.getD (chromaDcScan2x4.getD k.val 0) 0

/-- 4×2 (`ry ∈ 0..3, rx ∈ 0..1`) Hadamard transform (`ISO/IEC 14496-10` Clause 8.5.11.2):
    `H_4 * C * H_2` using `hadamard4Butterfly1D` vertically and 2-point `(a + b, a - b)` horizontally. -/
def hadamard2x4 (c : Array Int) : Array Int :=
  let g (i : Nat) := c.getD i 0
  let r0p := g 0 + g 1
  let r0m := g 0 - g 1
  let r1p := g 2 + g 3
  let r1m := g 2 - g 3
  let r2p := g 4 + g 5
  let r2m := g 4 - g 5
  let r3p := g 6 + g 7
  let r3m := g 6 - g 7
  let (v00, v10, v20, v30) := hadamard4Butterfly1D r0p r1p r2p r3p
  let (v01, v11, v21, v31) := hadamard4Butterfly1D r0m r1m r2m r3m
  #[v00, v01, v10, v11, v20, v21, v30, v31]

/-- Generalized 4×4 DC Hadamard dequant (`I_16x16` luma & 4:4:4 chroma) with custom `WeightScale(0,0)`. -/
def lumaDcDequantHbd (dc16 : Array Int) (qp : Nat) (weightScale0 : Int := 16) : Array Int :=
  let h := hadamard4x4 dc16
  let q := qpDiv6 qp
  let ls := levelScale4x4 qp 0 0 weightScale0
  h.map fun v =>
    if qp ≥ 36 then shlInt (v * ls) (q - 6)
    else asrInt (v * ls + shlInt 1 (5 - q)) (6 - q)

/-- Generalized 4×4 DC Hadamard forward quant (`I_16x16` luma & 4:4:4 chroma) with custom `WeightScale(0,0)`. -/
def lumaDcQuantHbd (raw16 : Array Int) (qp : Nat) (intra : Bool) (weightScale0 : Int := 16) : Array Int :=
  let h := forwardHadamard4x4 raw16
  let q := qpDiv6 qp
  let qbits := 16 + q
  let mf := mf4x4Table (qpMod6 qp) 0
  let denom := if weightScale0 == 0 then 1 else weightScale0
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  h.map fun w =>
    let mag := asrInt (Int.ofNat w.natAbs * mf * 16 / denom + f) qbits
    if w < 0 then -mag else mag

/-- Generalized 4:2:0 2×2 Chroma DC Hadamard dequant with custom `WeightScale(0,0)`. -/
def chromaDcDequant420Hbd (dc4 : Array Int) (qpc : Nat) (weightScale0 : Int := 16) : Array Int :=
  let (h00, h01, h10, h11) := hadamard2x2 (dc4.getD 0 0) (dc4.getD 1 0) (dc4.getD 2 0) (dc4.getD 3 0)
  let q := qpDiv6 qpc
  let ls := levelScale4x4 qpc 0 0 weightScale0
  let scale (v : Int) : Int :=
    if qpc ≥ 30 then shlInt (v * ls) (q - 5) else asrInt (v * ls) (5 - q)
  #[scale h00, scale h01, scale h10, scale h11]

/-- Generalized 4:2:0 2×2 Chroma DC forward quant with custom `WeightScale(0,0)`. -/
def chromaDcQuant420Hbd (raw4 : Array Int) (qpc : Nat) (intra : Bool) (weightScale0 : Int := 16) : Array Int :=
  let (h0, h1, h2, h3) := hadamard2x2 (raw4.getD 0 0) (raw4.getD 1 0) (raw4.getD 2 0) (raw4.getD 3 0)
  let qbits := 16 + qpDiv6 qpc
  let mf := mf4x4Table (qpMod6 qpc) 0
  let denom := if weightScale0 == 0 then 1 else weightScale0
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  let qDc (w : Int) : Int :=
    let mag := asrInt (Int.ofNat w.natAbs * mf * 16 / denom + f) qbits
    if w < 0 then -mag else mag
  #[qDc h0, qDc h1, qDc h2, qDc h3]

/-- 4:2:2 Chroma DC inverse Hadamard + dequant (`ISO/IEC 14496-10` Clause 8.5.11.2, raster-ordered `dc8`). -/
def chromaDcDequant422 (dc8 : Array Int) (qpc : Nat) (weightScale0 : Int := 16) : Array Int :=
  let h := hadamard2x4 dc8
  let qpcDc := qpc422Dc qpc
  let q := qpDiv6 qpcDc
  let ls := levelScale4x4 qpcDc 0 0 weightScale0
  h.map fun v =>
    if qpcDc ≥ 36 then shlInt (v * ls) (q - 6)
    else asrInt (v * ls + shlInt 1 (5 - q)) (6 - q)

/-- 4:2:2 Chroma DC forward Hadamard + quant (`ISO/IEC 14496-10` Clause 8.5.11.2, raster-ordered `raw8`). -/
def chromaDcQuant422 (raw8 : Array Int) (qpc : Nat) (intra : Bool) (weightScale0 : Int := 16) : Array Int :=
  let h := hadamard2x4 raw8
  let qpcDc := qpc422Dc qpc
  let q := qpDiv6 qpcDc
  let qbits := 16 + q
  let mf := mf4x4Table (qpMod6 qpcDc) 0
  let denom := if weightScale0 == 0 then 1 else weightScale0
  let f := (shlInt 1 qbits) / (if intra then 3 else 6)
  h.map fun w =>
    let mag := asrInt (Int.ofNat w.natAbs * mf * 16 / denom + f) qbits
    if w < 0 then -mag else mag

/-- 4:4:4 shared luma-style 4×4 Chroma DC dequant (`qP_C` via Table 8-15 + `WeightScale(0,0)`). -/
def chromaDcDequant444 (dc16 : Array Int) (qpc : Nat) (weightScale0 : Int := 16) : Array Int :=
  lumaDcDequantHbd dc16 qpc weightScale0

/-- 4:4:4 shared luma-style 4×4 Chroma DC forward quant (`qP_C` via Table 8-15 + `WeightScale(0,0)`). -/
def chromaDcQuant444 (raw16 : Array Int) (qpc : Nat) (intra : Bool) (weightScale0 : Int := 16) : Array Int :=
  lumaDcQuantHbd raw16 qpc intra weightScale0

/-- Reconstruct one 4×4 block (`bitDepth`-generalized) from raster levels and a prediction block. -/
def reconstructBlock4x4Hbd (pred : Array Nat) (levels : Array Int) (qp bitDepth : Nat)
    (weights : Array Int := Array.replicate 16 16) (dcOverride : Option Int := none) : Array Nat :=
  let scaled := Array.ofFn fun idx : Fin 16 =>
    let i := idx.val / 4
    let j := idx.val % 4
    match dcOverride with
    | some dc => if idx.val == 0 then dc else dequantCoeff4x4 (levels.getD idx.val 0) qp i j (weights.getD idx.val 16)
    | none => dequantCoeff4x4 (levels.getD idx.val 0) qp i j (weights.getD idx.val 16)
  let res := idct4x4FromScaled scaled
  Array.ofFn fun idx : Fin 16 =>
    clipSampleHbd ((pred.getD idx.val 0 : Int) + res.getD idx.val 0) bitDepth

/-- Reconstruct one 8×8 block (`bitDepth`-generalized) from raster levels and a prediction block. -/
def reconstructBlock8x8Hbd (pred : Array Nat) (levels : Array Int) (qp bitDepth : Nat)
    (weights : Array Int := Array.replicate 64 16) : Array Nat :=
  let scaled := Array.ofFn fun idx : Fin 64 =>
    let i := idx.val / 8
    let j := idx.val % 8
    dequantCoeff8x8 (levels.getD idx.val 0) qp i j (weights.getD idx.val 16)
  let res := idct8x8FromScaled scaled
  Array.ofFn fun idx : Fin 64 =>
    clipSampleHbd ((pred.getD idx.val 0 : Int) + res.getD idx.val 0) bitDepth

/-- Forward-quantize one 4×4 residual block using a custom `weights` scaling list. -/
def quantBlock4x4Hbd (res : Array Int) (qp : Nat) (intra : Bool)
    (weights : Array Int := Array.replicate 16 16) : Array Int :=
  let coeff := forwardDct4x4 res
  Array.ofFn fun idx : Fin 16 =>
    let i := idx.val / 4
    let j := idx.val % 4
    quantCoeff4x4 (coeff.getD idx.val 0) qp i j intra (weights.getD idx.val 16)

/-- Forward-quantize one 8×8 residual block using a custom `weights` scaling list. -/
def quantBlock8x8Hbd (res : Array Int) (qp : Nat) (intra : Bool)
    (weights : Array Int := Array.replicate 64 16) : Array Int :=
  let coeff := forwardDct8x8 res
  Array.ofFn fun idx : Fin 64 =>
    let i := idx.val / 8
    let j := idx.val % 8
    quantCoeff8x8 (coeff.getD idx.val 0) qp i j intra (weights.getD idx.val 16)

/-- Lossless bypass reconstruction (`qpprime_y_zero_transform_bypass_flag = 1`, `qpPrimeY = 0`):
    no transform/quant; optional vertical (`mode = 0`) or horizontal (`mode = 1`) residual DPCM. -/
def reconstructLosslessBypass (pred : Array Nat) (levels : Array Int) (mode nSz bitDepth : Nat) : Array Nat :=
  let res :=
    if nSz == 4 then decodeResidualDpcm4x4 mode levels
    else if nSz == 8 then decodeResidualDpcm8x8 mode levels
    else levels
  Array.ofFn fun idx : Fin (nSz * nSz) =>
    clipSampleHbd ((pred.getD idx.val 0 : Int) + res.getD idx.val 0) bitDepth

/-- Lossless bypass forward residual (`qpprime_y_zero_transform_bypass_flag = 1`, `qpPrimeY = 0`). -/
def encodeLosslessBypass (src pred : Array Nat) (mode nSz : Nat) : Array Int :=
  let res := Array.ofFn fun idx : Fin (nSz * nSz) =>
    (src.getD idx.val 0 : Int) - (pred.getD idx.val 0 : Int)
  if nSz == 4 then encodeResidualDpcm4x4 mode res
  else if nSz == 8 then encodeResidualDpcm8x8 mode res
  else res

/-- Map `intra_chroma_pred_mode` (`1` = Horizontal, `2` = Vertical, else none) to 4×4 lossless
    residual DPCM mode (`1` = row DPCM, `0` = column DPCM, `2` = bypass) for 4:2:0 / 4:2:2 chroma. -/
def losslessChromaDpcmMode (chromaMode : Nat) : Nat :=
  if chromaMode == 1 then 1
  else if chromaMode == 2 then 0
  else 2

/-- Bit-depth generalized neighbor samples (`Array Nat`) for 8/10/12-bit Intra 4×4 and 8×8 prediction. -/
structure IntraNeighborsHbd where
  leftAvail     : Bool := false
  topAvail      : Bool := false
  topRightAvail : Bool := false
  topLeftAvail  : Bool := false
  left          : Array Nat := #[]
  top           : Array Nat := #[]
  topRight      : Array Nat := #[]
  topLeft       : Nat := 128
  deriving Repr, DecidableEq, Inhabited

def isLegalIntraNxNModeHbd (mode : Nat) (n : IntraNeighborsHbd) : Bool :=
  match mode with
  | 0 | 3 | 7 => n.topAvail
  | 1 | 8 => n.leftAvail
  | 2 => true
  | 4 | 5 | 6 => n.topAvail && n.leftAvail && n.topLeftAvail
  | _ => false

/-- Bit-depth generalized 4×4 intra prediction (`ISO/IEC 14496-10` Clause 8.3.1). -/
def pred4x4Hbd (mode : Nat) (n : IntraNeighborsHbd) (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  let raw : Array Nat := (Id.run do
    let pT := (n.top.extract 0 4) ++ (if n.topRightAvail then n.topRight.extract 0 4
      else Array.replicate 4 (n.top.getD 3 mid))
    let pL := n.left
    let tl := n.topLeft
    let mut out := Array.replicate 16 mid
    match mode with
    | 0 => for y in [:4] do for x in [:4] do out := out.set! (y * 4 + x) (pT.getD x mid)
    | 1 => for y in [:4] do for x in [:4] do out := out.set! (y * 4 + x) (pL.getD y mid)
    | 2 =>
      let mut s : Nat := 0
      if n.topAvail then for i in [:4] do s := s + pT.getD i 0
      if n.leftAvail then for i in [:4] do s := s + pL.getD i 0
      let dc :=
        if n.topAvail && n.leftAvail then (s + 4) / 8
        else if n.topAvail || n.leftAvail then (s + 2) / 4
        else mid
      for i in [:16] do out := out.set! i dc
    | 3 =>
      for y in [:4] do for x in [:4] do
        let v := if x == 3 && y == 3 then filt3Nat (pT.getD 6 0) (pT.getD 7 0) (pT.getD 7 0)
                 else filt3Nat (pT.getD (x + y) 0) (pT.getD (x + y + 1) 0) (pT.getD (x + y + 2) 0)
        out := out.set! (y * 4 + x) v
    | 4 =>
      for y in [:4] do for x in [:4] do
        let v :=
          if x > y then
            let d := x - y
            filt3Nat (if d == 1 then tl else pT.getD (d - 2) 0) (pT.getD (d - 1) 0) (pT.getD d 0)
          else if x < y then
            let d := y - x
            filt3Nat (if d == 1 then tl else pL.getD (d - 2) 0) (pL.getD (d - 1) 0) (pL.getD d 0)
          else filt3Nat (pT.getD 0 0) tl (pL.getD 0 0)
        out := out.set! (y * 4 + x) v
    | 5 =>
      for y in [:4] do for x in [:4] do
        let zVR : Int := 2 * (x : Int) - (y : Int)
        let i := x - y / 2
        let v :=
          if zVR == 0 || zVR == 2 || zVR == 4 || zVR == 6 then
            avg2Nat (if i == 0 then tl else pT.getD (i - 1) 0) (pT.getD i 0)
          else if zVR == 1 || zVR == 3 || zVR == 5 then
            let a := if i == 0 then tl else pT.getD (i - 1) 0
            let b := if i == 1 then tl else if i == 0 then pL.getD 0 0 else pT.getD (i - 2) 0
            filt3Nat b a (pT.getD i 0)
          else if zVR == -1 then filt3Nat (pL.getD 0 0) tl (pT.getD 0 0)
          else if zVR == -2 then filt3Nat (pL.getD 1 0) (pL.getD 0 0) tl
          else filt3Nat (pL.getD 2 0) (pL.getD 1 0) (pL.getD 0 0)
        out := out.set! (y * 4 + x) v
    | 6 =>
      for y in [:4] do for x in [:4] do
        let zHD : Int := 2 * (y : Int) - (x : Int)
        let i := y - x / 2
        let v :=
          if zHD == 0 || zHD == 2 || zHD == 4 || zHD == 6 then
            avg2Nat (if i == 0 then tl else pL.getD (i - 1) 0) (pL.getD i 0)
          else if zHD == 1 || zHD == 3 || zHD == 5 then
            let a := if i == 0 then tl else pL.getD (i - 1) 0
            let b := if i == 1 then tl else if i == 0 then pT.getD 0 0 else pL.getD (i - 2) 0
            filt3Nat b a (pL.getD i 0)
          else if zHD == -1 then filt3Nat (pL.getD 0 0) tl (pT.getD 0 0)
          else if zHD == -2 then filt3Nat (pT.getD 1 0) (pT.getD 0 0) tl
          else filt3Nat (pT.getD 2 0) (pT.getD 1 0) (pT.getD 0 0)
        out := out.set! (y * 4 + x) v
    | 7 =>
      for y in [:4] do for x in [:4] do
        let i := x + y / 2
        let v := if y % 2 == 0 then avg2Nat (pT.getD i 0) (pT.getD (i + 1) 0)
                 else filt3Nat (pT.getD i 0) (pT.getD (i + 1) 0) (pT.getD (i + 2) 0)
        out := out.set! (y * 4 + x) v
    | _ =>
      for y in [:4] do for x in [:4] do
        let zHU := x + 2 * y
        let i := y + x / 2
        let v :=
          if zHU == 0 || zHU == 2 || zHU == 4 then avg2Nat (pL.getD i 0) (pL.getD (i + 1) 0)
          else if zHU == 1 || zHU == 3 then filt3Nat (pL.getD i 0) (pL.getD (i + 1) 0) (pL.getD (i + 2) 0)
          else if zHU == 5 then filt3Nat (pL.getD 2 0) (pL.getD 3 0) (pL.getD 3 0)
          else pL.getD 3 0
        out := out.set! (y * 4 + x) v
    return out)
  Array.ofFn fun i : Fin 16 => raw.getD i.val mid

/-- Bit-depth generalized 8×8 reference sample low-pass filtering (`ISO/IEC 14496-10` Clause 8.3.2.2.1). -/
def filterIntra8x8RefsHbd (n : IntraNeighborsHbd) (bitDepth : Nat := 8) : IntraNeighborsHbd := Id.run do
  let mid := h264MidSample bitDepth
  let pT := (n.top.extract 0 8) ++ (if n.topRightAvail then n.topRight.extract 0 8
    else Array.replicate 8 (n.top.getD 7 mid))
  let mut fT := Array.replicate 16 mid
  let mut fL := Array.replicate 8 mid
  let mut fTL := n.topLeft
  if n.topAvail then
    let a0 := if n.topLeftAvail then n.topLeft else pT.getD 0 mid
    fT := fT.set! 0 (filt3Nat a0 (pT.getD 0 mid) (pT.getD 1 mid))
    for x in [1:15] do
      fT := fT.set! x (filt3Nat (pT.getD (x - 1) mid) (pT.getD x mid) (pT.getD (x + 1) mid))
    fT := fT.set! 15 (filt3Nat (pT.getD 14 mid) (pT.getD 15 mid) (pT.getD 15 mid))
  if n.topLeftAvail then
    fTL :=
      if n.topAvail && n.leftAvail then filt3Nat (n.left.getD 0 mid) n.topLeft (pT.getD 0 mid)
      else if n.topAvail then filt3Nat n.topLeft n.topLeft (pT.getD 0 mid)
      else if n.leftAvail then filt3Nat n.topLeft n.topLeft (n.left.getD 0 mid)
      else n.topLeft
  if n.leftAvail then
    let b0 := if n.topLeftAvail then n.topLeft else n.left.getD 0 mid
    fL := fL.set! 0 (filt3Nat b0 (n.left.getD 0 mid) (n.left.getD 1 mid))
    for y in [1:7] do
      fL := fL.set! y (filt3Nat (n.left.getD (y - 1) mid) (n.left.getD y mid) (n.left.getD (y + 1) mid))
    fL := fL.set! 7 (filt3Nat (n.left.getD 6 mid) (n.left.getD 7 mid) (n.left.getD 7 mid))
  return { n with left := fL, top := fT.extract 0 8, topRight := fT.extract 8 16,
                  topRightAvail := true, topLeft := fTL }

/-- Bit-depth generalized 8×8 intra prediction (`ISO/IEC 14496-10` Clause 8.3.2). -/
def pred8x8Hbd (mode : Nat) (raw : IntraNeighborsHbd) (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  let res : Array Nat := (Id.run do
    let n := filterIntra8x8RefsHbd raw bitDepth
    let pT := n.top ++ n.topRight
    let fL := n.left
    let fTL := n.topLeft
    let mut out := Array.replicate 64 mid
    match mode with
    | 0 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (pT.getD x mid)
    | 1 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (fL.getD y mid)
    | 2 =>
      let mut s : Nat := 0
      if n.topAvail then for i in [:8] do s := s + pT.getD i 0
      if n.leftAvail then for i in [:8] do s := s + fL.getD i 0
      let dc :=
        if n.topAvail && n.leftAvail then (s + 8) / 16
        else if n.topAvail || n.leftAvail then (s + 4) / 8
        else mid
      for i in [:64] do out := out.set! i dc
    | 3 =>
      for y in [:8] do for x in [:8] do
        let v := if x == 7 && y == 7 then filt3Nat (pT.getD 14 0) (pT.getD 15 0) (pT.getD 15 0)
                 else filt3Nat (pT.getD (x + y) 0) (pT.getD (x + y + 1) 0) (pT.getD (x + y + 2) 0)
        out := out.set! (y * 8 + x) v
    | 4 =>
      for y in [:8] do for x in [:8] do
        let v :=
          if x > y then
            let d := x - y
            filt3Nat (if d == 1 then fTL else pT.getD (d - 2) 0) (pT.getD (d - 1) 0) (pT.getD d 0)
          else if x < y then
            let d := y - x
            filt3Nat (if d == 1 then fTL else fL.getD (d - 2) 0) (fL.getD (d - 1) 0) (fL.getD d 0)
          else filt3Nat (pT.getD 0 0) fTL (fL.getD 0 0)
        out := out.set! (y * 8 + x) v
    | 5 =>
      for y in [:8] do for x in [:8] do
        let zVR : Int := 2 * (x : Int) - (y : Int)
        let i := x - y / 2
        let v :=
          if zVR ≥ 0 && zVR % 2 == 0 then
            avg2Nat (if i == 0 then fTL else pT.getD (i - 1) 0) (pT.getD i 0)
          else if zVR > 0 then
            let a := if i == 0 then fTL else pT.getD (i - 1) 0
            let b := if i == 1 then fTL else if i == 0 then fL.getD 0 0 else pT.getD (i - 2) 0
            filt3Nat b a (pT.getD i 0)
          else if zVR == -1 then filt3Nat (fL.getD 0 0) fTL (pT.getD 0 0)
          else
            let k := y - 2 * x
            filt3Nat (fL.getD (k - 1) 0) (fL.getD (k - 2) 0) (if k == 2 then fTL else fL.getD (k - 3) 0)
        out := out.set! (y * 8 + x) v
    | 6 =>
      for y in [:8] do for x in [:8] do
        let zHD : Int := 2 * (y : Int) - (x : Int)
        let i := y - x / 2
        let v :=
          if zHD ≥ 0 && zHD % 2 == 0 then
            avg2Nat (if i == 0 then fTL else fL.getD (i - 1) 0) (fL.getD i 0)
          else if zHD > 0 then
            let a := if i == 0 then fTL else fL.getD (i - 1) 0
            let b := if i == 1 then fTL else if i == 0 then pT.getD 0 0 else fL.getD (i - 2) 0
            filt3Nat b a (fL.getD i 0)
          else if zHD == -1 then filt3Nat (fL.getD 0 0) fTL (pT.getD 0 0)
          else
            let k := x - 2 * y
            filt3Nat (pT.getD (k - 1) 0) (pT.getD (k - 2) 0) (if k == 2 then fTL else pT.getD (k - 3) 0)
        out := out.set! (y * 8 + x) v
    | 7 =>
      for y in [:8] do for x in [:8] do
        let i := x + y / 2
        let v := if y % 2 == 0 then avg2Nat (pT.getD i 0) (pT.getD (i + 1) 0)
                 else filt3Nat (pT.getD i 0) (pT.getD (i + 1) 0) (pT.getD (i + 2) 0)
        out := out.set! (y * 8 + x) v
    | _ =>
      for y in [:8] do for x in [:8] do
        let zHU := x + 2 * y
        let i := y + x / 2
        let v :=
          if zHU ≤ 12 && zHU % 2 == 0 then avg2Nat (fL.getD i 0) (fL.getD (i + 1) 0)
          else if zHU ≤ 11 then filt3Nat (fL.getD i 0) (fL.getD (i + 1) 0) (fL.getD (i + 2) 0)
          else if zHU == 13 then filt3Nat (fL.getD 6 0) (fL.getD 7 0) (fL.getD 7 0)
          else fL.getD 7 0
        out := out.set! (y * 8 + x) v
    return out)
  Array.ofFn fun i : Fin 64 => res.getD i.val mid

/-- Bit-depth generalized 16×16 intra prediction (`ISO/IEC 14496-10` Clause 8.3.3; luma & 4:4:4 chroma). -/
def pred16x16Hbd (mode : Nat) (left top : Array Nat) (topLeft : Nat)
    (leftAvail topAvail : Bool) (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  let res : Array Nat := (Id.run do
    let mut out := Array.replicate 256 mid
    match mode with
    | 0 => for y in [:16] do for x in [:16] do out := out.set! (y * 16 + x) (top.getD x mid)
    | 1 => for y in [:16] do for x in [:16] do out := out.set! (y * 16 + x) (left.getD y mid)
    | 2 =>
      let mut s : Nat := 0
      if topAvail then for i in [:16] do s := s + top.getD i 0
      if leftAvail then for i in [:16] do s := s + left.getD i 0
      let dc :=
        if topAvail && leftAvail then (s + 16) / 32
        else if topAvail || leftAvail then (s + 8) / 16
        else mid
      for i in [:256] do out := out.set! i dc
    | _ =>
      let mut hSum : Int := 0
      let mut vSum : Int := 0
      for k in [:8] do
        let pHNeg : Int := if k == 7 then (topLeft : Int) else (top.getD (6 - k) 0 : Int)
        let pVNeg : Int := if k == 7 then (topLeft : Int) else (left.getD (6 - k) 0 : Int)
        hSum := hSum + ((k + 1 : Nat) : Int) * ((top.getD (8 + k) 0 : Int) - pHNeg)
        vSum := vSum + ((k + 1 : Nat) : Int) * ((left.getD (8 + k) 0 : Int) - pVNeg)
      let a : Int := 16 * ((left.getD 15 0 : Int) + (top.getD 15 0 : Int))
      let b := asrInt (5 * hSum + 32) 6
      let c := asrInt (5 * vSum + 32) 6
      for y in [:16] do for x in [:16] do
        let v := asrInt (a + b * ((x : Int) - 7) + c * ((y : Int) - 7) + 16) 5
        out := out.set! (y * 16 + x) (clipSampleHbd v bitDepth)
    return out)
  Array.ofFn fun i : Fin 256 => res.getD i.val mid

/-- Bit-depth generalized 4:2:0 8×8 chroma intra prediction (`ISO/IEC 14496-10` Clause 8.3.4). -/
def predChroma420Hbd (mode : Nat) (left top : Array Nat) (topLeft : Nat)
    (leftAvail topAvail : Bool) (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  let res : Array Nat := (Id.run do
    let mut out := Array.replicate 64 mid
    match mode with
    | 0 =>
      let sumT0 := top.getD 0 0 + top.getD 1 0 + top.getD 2 0 + top.getD 3 0
      let sumT1 := top.getD 4 0 + top.getD 5 0 + top.getD 6 0 + top.getD 7 0
      let sumL0 := left.getD 0 0 + left.getD 1 0 + left.getD 2 0 + left.getD 3 0
      let sumL1 := left.getD 4 0 + left.getD 5 0 + left.getD 6 0 + left.getD 7 0
      let dc00 := if topAvail && leftAvail then (sumT0 + sumL0 + 4) / 8
                  else if topAvail then (sumT0 + 2) / 4
                  else if leftAvail then (sumL0 + 2) / 4 else mid
      let dc01 := if topAvail then (sumT1 + 2) / 4
                  else if leftAvail then (sumL0 + 2) / 4 else mid
      let dc10 := if leftAvail then (sumL1 + 2) / 4
                  else if topAvail then (sumT0 + 2) / 4 else mid
      let dc11 := if topAvail && leftAvail then (sumT1 + sumL1 + 4) / 8
                  else if topAvail then (sumT1 + 2) / 4
                  else if leftAvail then (sumL1 + 2) / 4 else mid
      let dcs := #[dc00, dc01, dc10, dc11]
      for byy in [:2] do for bxx in [:2] do
        let dc := dcs.getD (byy * 2 + bxx) mid
        for y in [:4] do for x in [:4] do out := out.set! ((byy * 4 + y) * 8 + bxx * 4 + x) dc
    | 1 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (left.getD y mid)
    | 2 => for y in [:8] do for x in [:8] do out := out.set! (y * 8 + x) (top.getD x mid)
    | _ =>
      let mut hSum : Int := 0
      let mut vSum : Int := 0
      for k in [:4] do
        let pHNeg : Int := if k == 3 then (topLeft : Int) else (top.getD (2 - k) 0 : Int)
        let pVNeg : Int := if k == 3 then (topLeft : Int) else (left.getD (2 - k) 0 : Int)
        hSum := hSum + ((k + 1 : Nat) : Int) * ((top.getD (4 + k) 0 : Int) - pHNeg)
        vSum := vSum + ((k + 1 : Nat) : Int) * ((left.getD (4 + k) 0 : Int) - pVNeg)
      let a : Int := 16 * ((left.getD 7 0 : Int) + (top.getD 7 0 : Int))
      let b := asrInt (17 * hSum + 16) 5
      let c := asrInt (17 * vSum + 16) 5
      for y in [:8] do for x in [:8] do
        let v := asrInt (a + b * ((x : Int) - 3) + c * ((y : Int) - 3) + 16) 5
        out := out.set! (y * 8 + x) (clipSampleHbd v bitDepth)
    return out)
  Array.ofFn fun i : Fin 64 => res.getD i.val mid

/-- 4:2:2 8×16 chroma DC prediction (`ISO/IEC 14496-10` Clause 8.3.4.1, `bitDepth`-generalized). -/
def predChroma422Dc (left : Array Nat) (top : Array Nat) (leftAvail topAvail : Bool)
    (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  let sumT (rx : Nat) := (List.range 4).foldl (fun acc x => acc + top.getD (4 * rx + x) 0) 0
  let sumL (ry : Nat) := (List.range 4).foldl (fun acc y => acc + left.getD (4 * ry + y) 0) 0
  Array.ofFn fun idx : Fin 128 =>
    let y := idx.val / 8
    let x := idx.val % 8
    let ry := y / 4
    let rx := x / 4
    if (rx == 0 && ry == 0) || (rx == 1 && ry > 0) then
      if topAvail && leftAvail then (sumT rx + sumL ry + 4) / 8
      else if topAvail then (sumT rx + 2) / 4
      else if leftAvail then (sumL ry + 2) / 4
      else mid
    else if rx == 1 && ry == 0 then
      if topAvail then (sumT 1 + 2) / 4
      else if leftAvail then (sumL 0 + 2) / 4
      else mid
    else
      if leftAvail then (sumL ry + 2) / 4
      else if topAvail then (sumT 0 + 2) / 4
      else mid

/-- 4:2:2 8×16 chroma plane prediction (`ISO/IEC 14496-10` Clause 8.3.4.4, `bitDepth`-generalized). -/
def predChroma422Plane (left : Array Nat) (top : Array Nat) (topLeft : Nat)
    (bitDepth : Nat := 8) : Array Nat :=
  let hSum := (List.range 4).foldl (fun acc x1 =>
    let pNeg := if x1 == 3 then topLeft else top.getD (2 - x1) 0
    acc + ((x1 + 1 : Nat) : Int) * (((top.getD (4 + x1) 0) : Int) - (pNeg : Int))) 0
  let vSum := (List.range 8).foldl (fun acc y1 =>
    let pNeg := if y1 == 7 then topLeft else left.getD (6 - y1) 0
    acc + ((y1 + 1 : Nat) : Int) * (((left.getD (8 + y1) 0) : Int) - (pNeg : Int))) 0
  let a : Int := 16 * (((left.getD 15 0) : Int) + ((top.getD 7 0) : Int))
  let b := asrInt (17 * hSum + 16) 5
  let c := asrInt (5 * vSum + 32) 6
  Array.ofFn fun idx : Fin 128 =>
    let y := idx.val / 8
    let x := idx.val % 8
    let v := asrInt (a + b * ((x : Int) - 3) + c * ((y : Int) - 7) + 16) 5
    clipSampleHbd v bitDepth

/-- 4:2:2 8×16 chroma intra prediction (`mode ∈ {0 DC, 1 Horizontal, 2 Vertical, 3 Plane}`). -/
def predChroma422 (mode : Nat) (left top : Array Nat) (topLeft : Nat)
    (leftAvail topAvail : Bool) (bitDepth : Nat := 8) : Array Nat :=
  let mid := h264MidSample bitDepth
  match mode with
  | 0 => predChroma422Dc left top leftAvail topAvail bitDepth
  | 1 => Array.ofFn fun idx : Fin 128 => left.getD (idx.val / 8) mid
  | 2 => Array.ofFn fun idx : Fin 128 => top.getD (idx.val % 8) mid
  | _ => predChroma422Plane left top topLeft bitDepth

/-- 4:4:4 16×16 chroma intra prediction (`bitDepth`-generalized, full sample precision). -/
def predChroma444 (mode : Nat) (left top : Array Nat) (topLeft : Nat)
    (leftAvail topAvail : Bool) (bitDepth : Nat := 8) : Array Nat :=
  pred16x16Hbd mode left top topLeft leftAvail topAvail bitDepth

/-- Reconstruct one 4:2:0 8×8 chroma plane (`bitDepth` + custom scaling-list `weights` generalized). -/
def reconstructChroma420Hbd (pred64 : Array Nat) (dc4 : Array Int) (ac4 : Array (Array Int))
    (qpc bitDepth : Nat) (weights : Array Int := Array.replicate 16 16) : Array Nat :=
  let dcScaled := chromaDcDequant420Hbd dc4 qpc (weights.getD 0 16)
  Array.ofFn fun idx : Fin 64 =>
    let y := idx.val / 8
    let x := idx.val % 8
    let blk := (y / 4) * 2 + (x / 4)
    let sub := (y % 4) * 4 + (x % 4)
    let ac := ac4.getD blk (Array.replicate 16 0)
    let scaled := Array.ofFn fun s : Fin 16 =>
      if s.val == 0 then dcScaled.getD blk 0
      else
        let i := s.val / 4
        let j := s.val % 4
        dequantCoeff4x4 (ac.getD s.val 0) qpc i j (weights.getD s.val 16)
    let res := idct4x4FromScaled scaled
    clipSampleHbd ((pred64.getD idx.val 0 : Int) + res.getD sub 0) bitDepth

/-- Reconstruct one 4:2:2 8×16 chroma plane (raster `dc8` 2×4 Hadamard + 8 AC 4×4 blocks). -/
def reconstructChroma422Hbd (pred128 : Array Nat) (dc8 : Array Int) (ac8 : Array (Array Int))
    (qpc bitDepth : Nat) (weights : Array Int := Array.replicate 16 16) : Array Nat :=
  let dcScaled := chromaDcDequant422 dc8 qpc (weights.getD 0 16)
  Array.ofFn fun idx : Fin 128 =>
    let y := idx.val / 8
    let x := idx.val % 8
    let blk := (y / 4) * 2 + (x / 4)
    let sub := (y % 4) * 4 + (x % 4)
    let ac := ac8.getD blk (Array.replicate 16 0)
    let scaled := Array.ofFn fun s : Fin 16 =>
      if s.val == 0 then dcScaled.getD blk 0
      else
        let i := s.val / 4
        let j := s.val % 4
        dequantCoeff4x4 (ac.getD s.val 0) qpc i j (weights.getD s.val 16)
    let res := idct4x4FromScaled scaled
    clipSampleHbd ((pred128.getD idx.val 0 : Int) + res.getD sub 0) bitDepth

/-- Reconstruct one 4:4:4 16×16 chroma plane (shared luma-style 4×4 DC + 16 AC 4×4 blocks). -/
def reconstructChroma444Hbd (pred256 : Array Nat) (dc16 : Array Int) (ac16 : Array (Array Int))
    (qpc bitDepth : Nat) (weights : Array Int := Array.replicate 16 16) : Array Nat :=
  let dcScaled := chromaDcDequant444 dc16 qpc (weights.getD 0 16)
  Array.ofFn fun idx : Fin 256 =>
    let y := idx.val / 16
    let x := idx.val % 16
    let blk := zScan4BlkIdx (x / 4) (y / 4)
    let sub := (y % 4) * 4 + (x % 4)
    let ac := ac16.getD blk (Array.replicate 16 0)
    let scaled := Array.ofFn fun s : Fin 16 =>
      if s.val == 0 then dcScaled.getD blk 0
      else
        let i := s.val / 4
        let j := s.val % 4
        dequantCoeff4x4 (ac.getD s.val 0) qpc i j (weights.getD s.val 16)
    let res := idct4x4FromScaled scaled
    clipSampleHbd ((pred256.getD idx.val 0 : Int) + res.getD sub 0) bitDepth

/-- MSB-first bit-packing of `I_PCM` luma + Cb + Cr samples (`ISO/IEC 14496-10` §7.3.5) for
    `chromaArrayType ∈ {0,1,2,3}` and arbitrary `bitDepthY, bitDepthC ∈ {8..12}`. -/
def packIpcmSamplesHbd (luma cb cr : Array Nat) (chromaArrayType bitDepthY bitDepthC : Nat) : Option ByteArray := Id.run do
  if luma.size != 256 || bitDepthY < 8 || bitDepthY > 14 || bitDepthC < 8 || bitDepthC > 14 then return none
  let expectedChroma :=
    if chromaArrayType == 0 then 0
    else if chromaArrayType == 1 then 64
    else if chromaArrayType == 2 then 128
    else if chromaArrayType == 3 then 256
    else 999
  if expectedChroma == 999 || cb.size != expectedChroma || cr.size != expectedChroma then return none
  let maskY : Nat := h264SampleMax bitDepthY
  let maskC : Nat := h264SampleMax bitDepthC
  let mut w := BitWriter.empty 512
  for i in [:256] do
    w := w.writeBitsMSB ((luma.getD i 0 &&& maskY).toUInt64) bitDepthY
  for i in [:expectedChroma] do
    w := w.writeBitsMSB ((cb.getD i 0 &&& maskC).toUInt64) bitDepthC
  for i in [:expectedChroma] do
    w := w.writeBitsMSB ((cr.getD i 0 &&& maskC).toUInt64) bitDepthC
  return some w.toByteArray

/-- Unpack MSB-first `I_PCM` `pcmBytes` into `(luma256, cb, cr)` for `chromaArrayType ∈ {0,1,2,3}`. -/
def unpackIpcmSamplesHbd (pcmBytes : ByteArray) (chromaArrayType bitDepthY bitDepthC : Nat) :
    Option (Array Nat × Array Nat × Array Nat) := Id.run do
  if bitDepthY < 8 || bitDepthY > 14 || bitDepthC < 8 || bitDepthC > 14 then return none
  let expectedChroma :=
    if chromaArrayType == 0 then 0
    else if chromaArrayType == 1 then 64
    else if chromaArrayType == 2 then 128
    else if chromaArrayType == 3 then 256
    else 999
  if expectedChroma == 999 then return none
  let totalBits := 256 * bitDepthY + 2 * expectedChroma * bitDepthC
  if pcmBytes.size * 8 != totalBits then return none
  let mut r : BitReader := { slice := ByteSlice.ofByteArray pcmBytes, bitOffset := 0 }
  let mut yOut := Array.emptyWithCapacity 256
  for _ in [:256] do
    let some (v, rNext) := r.readBitsMSB bitDepthY | return none
    yOut := yOut.push v.toNat
    r := rNext
  let mut cbOut := Array.emptyWithCapacity expectedChroma
  for _ in [:expectedChroma] do
    let some (v, rNext) := r.readBitsMSB bitDepthC | return none
    cbOut := cbOut.push v.toNat
    r := rNext
  let mut crOut := Array.emptyWithCapacity expectedChroma
  for _ in [:expectedChroma] do
    let some (v, rNext) := r.readBitsMSB bitDepthC | return none
    crOut := crOut.push v.toNat
    r := rNext
  return some (yOut, cbOut, crOut)

/-- High-tier extended `QP'_Y` range gate: `0 ≤ qpPrimeY ≤ 51 + 6 * (bitDepth - 8)` for `bitDepth ∈ {8..12}`. -/
def isValidHighTierQpPrime (bitDepth : Nat) (qpPrime : Int) : Bool :=
  decide (bitDepth ≥ 8 ∧ bitDepth ≤ 12 ∧ 0 ≤ qpPrime ∧ qpPrime ≤ 51 + 6 * ((bitDepth : Int) - 8))

/-- High-tier sample-range gate: `bitDepth ∈ {8,9,10,11,12}` and `v ≤ (1 <<< bitDepth) - 1`. -/
def isValidHighTierSample (bitDepth v : Nat) : Bool :=
  decide (bitDepth ≥ 8 ∧ bitDepth ≤ 12 ∧ v ≤ (1 <<< bitDepth) - 1)

/-- High-tier chroma-format gate: `chromaFormatIdc ∈ {0,1,2,3}`. -/
def isValidHighTierChroma (chromaFormatIdc : Nat) : Bool :=
  decide (chromaFormatIdc ≤ 3)

/-! ## Canonical Raw Planar HBD Pack/Unpack & HBD Picture Decoder/Encoder -/

def parseCanonicalHbdPixFmt (pixFmt : String) : Option (Nat × Nat) :=
  match pixFmt with
  | "gray"         => some (0, 8)
  | "gray10le"     => some (0, 10)
  | "gray12le"     => some (0, 12)
  | "yuv420p"      => some (1, 8)
  | "yuv420p10le"  => some (1, 10)
  | "yuv420p12le"  => some (1, 12)
  | "yuv422p"      => some (2, 8)
  | "yuv422p10le"  => some (2, 10)
  | "yuv422p12le"  => some (2, 12)
  | "yuv444p"      => some (3, 8)
  | "yuv444p10le"  => some (3, 10)
  | "yuv444p12le"  => some (3, 12)
  | _              => none

def chromaPlaneDims (chromaFormatIdc w h : Nat) : Option (Nat × Nat) :=
  if w == 0 || h == 0 then none
  else if chromaFormatIdc == 0 then some (0, 0)
  else if chromaFormatIdc == 1 then some ((w + 1) / 2, (h + 1) / 2)
  else if chromaFormatIdc == 2 then some ((w + 1) / 2, h)
  else if chromaFormatIdc == 3 then some (w, h)
  else none

def canonicalRawFrameBytes (chromaFormatIdc bitDepth w h : Nat) : Option Nat := do
  if bitDepth != 8 && bitDepth != 10 && bitDepth != 12 then none
  else
    let (cw, ch) ← chromaPlaneDims chromaFormatIdc w h
    let bps := if bitDepth == 8 then 1 else 2
    some ((w * h + 2 * cw * ch) * bps)

private def packPlaneHbdBytes (p : LeanAV.H264InterDeblockDpb.PlaneHbd) (bitDepth : Nat) : Option ByteArray :=
  if bitDepth == 8 then Id.run do
    let mut out := ByteArray.emptyWithCapacity (p.width * p.height)
    for r in [:p.height] do
      for c in [:p.width] do
        out := out.push (clipSampleHbd (Int.ofNat (p.getPixel r c)) 8).toUInt8
    return some out
  else if bitDepth == 10 || bitDepth == 12 then Id.run do
    let mut out := ByteArray.emptyWithCapacity (p.width * p.height * 2)
    for r in [:p.height] do
      for c in [:p.width] do
        let v := clipSampleHbd (Int.ofNat (p.getPixel r c)) bitDepth
        out := out.push (v &&& 0xFF).toUInt8
        out := out.push ((v >>> 8) &&& 0xFF).toUInt8
    return some out
  else none

def packPictureHbdCanonicalRaw (pic : LeanAV.H264InterDeblockDpb.H264PictureHbd) : Option ByteArray := do
  if pic.bitDepthY != pic.bitDepthC then none
  else
    let _ ← canonicalRawFrameBytes pic.chromaFormatIdc pic.bitDepthY pic.width pic.height
    let yBytes ← packPlaneHbdBytes pic.y pic.bitDepthY
    if pic.chromaFormatIdc == 0 then
      some yBytes
    else
      let uBytes ← packPlaneHbdBytes pic.u pic.bitDepthC
      let vBytes ← packPlaneHbdBytes pic.v pic.bitDepthC
      some (yBytes ++ uBytes ++ vBytes)

def packPicturesHbdCanonicalRaw (pics : Array LeanAV.H264InterDeblockDpb.H264PictureHbd) : Option ByteArray := do
  if pics.isEmpty then none
  else
    let mut out := ByteArray.empty
    for pic in pics do
      let b ← packPictureHbdCanonicalRaw pic
      out := out ++ b
    some out

private def unpackPlaneHbdBytes (raw : ByteArray) (byteOff w h bitDepth : Nat)
    : Option (LeanAV.H264InterDeblockDpb.PlaneHbd × Nat) :=
  let maxVal := h264SampleMax bitDepth
  if bitDepth == 8 then
    let n := w * h
    if byteOff + n > raw.size then none
    else Id.run do
      let mut arr := Array.emptyWithCapacity n
      for i in [:n] do
        arr := arr.push (raw.data.getD (byteOff + i) 0).toNat
      return some ({ width := w, height := h, stride := w, bitDepth := 8, data := arr }, byteOff + n)
  else if bitDepth == 10 || bitDepth == 12 then
    let n := w * h
    if byteOff + n * 2 > raw.size then none
    else Id.run do
      let mut arr := Array.emptyWithCapacity n
      for i in [:n] do
        let lo := (raw.data.getD (byteOff + 2 * i) 0).toNat
        let hi := (raw.data.getD (byteOff + 2 * i + 1) 0).toNat
        let v := lo ||| (hi <<< 8)
        if v > maxVal then return none
        arr := arr.push v
      return some ({ width := w, height := h, stride := w, bitDepth := bitDepth, data := arr }, byteOff + n * 2)
  else none

def unpackCanonicalRawPicturesHbd (raw : ByteArray) (pixFmt : String) (w h : Nat)
    : Option (Array LeanAV.H264InterDeblockDpb.H264PictureHbd) := do
  let (cfmt, bd) ← parseCanonicalHbdPixFmt pixFmt
  let frameBytes ← canonicalRawFrameBytes cfmt bd w h
  if frameBytes == 0 || raw.size == 0 || raw.size % frameBytes != 0 then none
  else
    let (cw, ch) ← chromaPlaneDims cfmt w h
    let nFrames := raw.size / frameBytes
    let mut out : Array LeanAV.H264InterDeblockDpb.H264PictureHbd := Array.mkEmpty nFrames
    let mut off : Nat := 0
    for _ in [:nFrames] do
      let (pY, off1) ← unpackPlaneHbdBytes raw off w h bd
      if cfmt == 0 then
        let emptyC := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc 0 0 bd 0
        out := out.push {
          width := w, height := h, chromaFormatIdc := 0, separateColourPlane := false,
          bitDepthY := bd, bitDepthC := bd, y := pY, u := emptyC, v := emptyC
        }
        off := off1
      else
        let (pU, off2) ← unpackPlaneHbdBytes raw off1 cw ch bd
        let (pV, off3) ← unpackPlaneHbdBytes raw off2 cw ch bd
        out := out.push {
          width := w, height := h, chromaFormatIdc := cfmt, separateColourPlane := false,
          bitDepthY := bd, bitDepthC := bd, y := pY, u := pU, v := pV
        }
        off := off3
    some out

def cropPlaneHbd (src : LeanAV.H264InterDeblockDpb.PlaneHbd) (x0 y0 w h : Nat)
    : Option LeanAV.H264InterDeblockDpb.PlaneHbd :=
  if w == 0 && h == 0 then
    some (LeanAV.H264InterDeblockDpb.PlaneHbd.alloc 0 0 src.bitDepth 0)
  else if w == 0 || h == 0 || x0 + w > src.width || y0 + h > src.height then none
  else Id.run do
    let mut arr := Array.emptyWithCapacity (w * h)
    for r in [:h] do
      for c in [:w] do
        arr := arr.push (src.getPixel (y0 + r) (x0 + c))
    return some { width := w, height := h, stride := w, bitDepth := src.bitDepth, data := arr }

def pictureHbdToYuv420pVideoFrame (pic : LeanAV.H264InterDeblockDpb.H264PictureHbd) : Option VideoFrame := do
  if pic.width == 0 || pic.height == 0 then none
  else if pic.chromaFormatIdc == 1 && (pic.width % 2 != 0 || pic.height % 2 != 0) then none
  else if pic.chromaFormatIdc == 2 && pic.width % 2 != 0 then none
  else if pic.bitDepthY < 8 || pic.bitDepthC < 8 then none
  else
    let shY := pic.bitDepthY - 8
    let shC := pic.bitDepthC - 8
    let cw := (pic.width + 1) / 2
    let ch := (pic.height + 1) / 2
    let yPlane : Plane2D := Id.run do
      let mut out := ByteArray.emptyWithCapacity (pic.width * pic.height)
      for r in [:pic.height] do
        for c in [:pic.width] do
          let v := (pic.y.getPixel r c) >>> shY
          out := out.push (clip1 (Int.ofNat v)).toNat.toUInt8
      return { data := out, width := pic.width, height := pic.height, stride := pic.width }
    let clampCoord (idx dim : Nat) : Nat :=
      if dim == 0 then 0 else if idx < dim then idx else dim - 1
    let downsampleChroma (src : LeanAV.H264InterDeblockDpb.PlaneHbd) : Plane2D := Id.run do
      let mut out := ByteArray.emptyWithCapacity (cw * ch)
      for r in [:ch] do
        for c in [:cw] do
          let v : Nat :=
            if pic.chromaFormatIdc == 0 then 128
            else if pic.chromaFormatIdc == 1 then
              (src.getPixel r c) >>> shC
            else if pic.chromaFormatIdc == 2 then
              let r0 := clampCoord (2 * r) src.height
              let r1 := clampCoord (2 * r + 1) src.height
              let c0 := clampCoord c src.width
              let s0 := src.getPixel r0 c0
              let s1 := src.getPixel r1 c0
              ((s0 + s1 + 1) / 2) >>> shC
            else
              let r0 := clampCoord (2 * r) src.height
              let r1 := clampCoord (2 * r + 1) src.height
              let c0 := clampCoord (2 * c) src.width
              let c1 := clampCoord (2 * c + 1) src.width
              let s00 := src.getPixel r0 c0
              let s01 := src.getPixel r0 c1
              let s10 := src.getPixel r1 c0
              let s11 := src.getPixel r1 c1
              ((s00 + s01 + s10 + s11 + 2) / 4) >>> shC
          out := out.push (clip1 (Int.ofNat v)).toNat.toUInt8
      return { data := out, width := cw, height := ch, stride := cw }
    let uPlane := downsampleChroma pic.u
    let vPlane := downsampleChroma pic.v
    some {
      width := pic.width
      height := pic.height
      pixFmt := .yuv420p
      colorMatrix := .bt709
      pts := 0
      duration := 1
      timeBase := AVRational.tb90kHz
      planes := #[yPlane, uPlane, vPlane]
    }

abbrev HbdPlane := LeanAV.H264InterDeblockDpb.PlaneHbd
abbrev HbdPic := LeanAV.H264InterDeblockDpb.H264PictureHbd

private def hbdGet (p : HbdPlane) (x y : Nat) (mid : Nat) : Nat :=
  if x < p.width && y < p.height then p.getPixel y x else mid

private def hbdSet (p : HbdPlane) (x y : Nat) (v : Nat) : HbdPlane :=
  if x < p.width && y < p.height then p.setPixel y x v else p

private def extractMbRect (p : HbdPlane) (x0 y0 w h : Nat) (mid : Nat) : Array Nat :=
  Array.ofFn fun i : Fin (w * h) =>
    hbdGet p (x0 + i.val % w) (y0 + i.val / w) mid

private def writeMbRect (p : HbdPlane) (x0 y0 w : Nat) (blk : Array Nat) : HbdPlane := Id.run do
  let mut dst := p
  for i in [:blk.size] do
    dst := hbdSet dst (x0 + i % w) (y0 + i / w) (blk.getD i 0)
  return dst

private def scalingWeights4 (pps : LeanAV.H264Syntax.H264PpsFull) (isIntra : Bool) (plane : Nat) : Array Int :=
  let slot := (if isIntra then 0 else 3) + plane
  let zig := pps.effectiveScaling4x4.getD slot LeanAV.H264Syntax.flatScalingList4x4
  let rast := LeanAV.H264Entropy.zigzagToRaster4x4 (zig.map fun b => (b.toNat : Int))
  Array.ofFn fun i : Fin 16 => rast.getD i.val 16

private def scalingWeights8 (pps : LeanAV.H264Syntax.H264PpsFull) (chromaFormatIdc : Nat)
    (isIntra : Bool) (plane : Nat) : Array Int :=
  let slot := if chromaFormatIdc != 3 then (if isIntra then 0 else 1) else 2 * plane + (if isIntra then 0 else 1)
  let zig := pps.effectiveScaling8x8.getD slot LeanAV.H264Syntax.flatScalingList8x8
  let rast := LeanAV.H264Entropy.zigzagToRaster8x8 (zig.map fun b => (b.toNat : Int))
  Array.ofFn fun i : Fin 64 => rast.getD i.val 16

private def anyNz (a : Array Int) (n : Nat) : Bool :=
  (List.range n).any fun i => a.getD i 0 != 0

private def ac15ToRaster16 (ac15 : Array Int) : Array Int :=
  LeanAV.H264Entropy.zigzagToRaster4x4 (#[0] ++ ac15.extract 0 15)

private def raster16ToAc15Scan (raster : Array Int) : Array Int :=
  (LeanAV.H264Entropy.rasterToZigzag4x4 raster).extract 1 16

private def syntaxToMode (mpm pf rem : Nat) : Nat :=
  if pf != 0 then mpm else if rem < mpm then rem else rem + 1

private def modeToSyntax (mpm actual : Nat) : Nat × Nat :=
  if actual == mpm then (1, 0) else if actual < mpm then (0, actual) else (0, actual - 1)

private def mpmOf (modes : Array Nat) (sliceIds : Array Int) (intraFlags : Array Bool)
    (gridW gx gy : Nat) (sliceId : Int) (constrained : Bool) : Nat :=
  let leftOk := gx > 0 &&
    sliceIds.getD (gy * gridW + (gx - 1)) (-1) == sliceId &&
    (!constrained || intraFlags.getD (gy * gridW + (gx - 1)) false)
  let topOk := gy > 0 &&
    sliceIds.getD ((gy - 1) * gridW + gx) (-1) == sliceId &&
    (!constrained || intraFlags.getD ((gy - 1) * gridW + gx) false)
  if !leftOk || !topOk then 2
  else Nat.min (modes.getD (gy * gridW + (gx - 1)) 2) (modes.getD ((gy - 1) * gridW + gx) 2)

private def hbdSubNeighbors (nSz : Nat) (canvas : Array Nat) (mbW : Nat)
    (leftCol topRow : Array Nat) (topLeft : Nat)
    (leftAv topAv topLeftAv : Bool) (xO yO : Nat) (trAvail : Bool) (mid : Nat) : IntraNeighborsHbd :=
  let leftAvail := if xO == 0 then leftAv else true
  let topAvail := if yO == 0 then topAv else true
  let tlAvail :=
    if xO == 0 && yO == 0 then topLeftAv
    else if yO == 0 then topAv
    else if xO == 0 then leftAv else true
  let left := Array.ofFn fun i : Fin nSz =>
    if xO == 0 then leftCol.getD (yO + i.val) mid else canvas.getD ((yO + i.val) * mbW + (xO - 1)) mid
  let top := Array.ofFn fun i : Fin nSz =>
    if yO == 0 then topRow.getD (xO + i.val) mid else canvas.getD ((yO - 1) * mbW + (xO + i.val)) mid
  let rep := top.getD (nSz - 1) mid
  let topRight := Array.ofFn fun i : Fin nSz =>
    if !trAvail then rep
    else if yO == 0 then topRow.getD (xO + nSz + i.val) rep
    else canvas.getD ((yO - 1) * mbW + (xO + nSz + i.val)) rep
  let tl :=
    if xO == 0 && yO == 0 then topLeft
    else if yO == 0 then topRow.getD (xO - 1) mid
    else if xO == 0 then leftCol.getD (yO - 1) mid
    else canvas.getD ((yO - 1) * mbW + (xO - 1)) mid
  { leftAvail := leftAvail, topAvail := topAvail, topRightAvail := trAvail, topLeftAvail := tlAvail,
    left := left, top := top, topRight := topRight, topLeft := tl }

private def applyDpcmBlock (pred : Array Nat) (levels : Array Int) (mode nSz bitDepth : Nat) : Array Nat :=
  reconstructLosslessBypass pred levels mode nSz bitDepth

private def dpcm16x16 (pred : Array Nat) (raw : Array Int) (mode bitDepth : Nat) : Array Nat :=
  Id.run do
    let mut recArr : Array Nat := Array.replicate 256 0
    for y in [:16] do
      for x in [:16] do
        let i := y * 16 + x
        let base : Int :=
          if mode == 0 then
            if y == 0 then (pred.getD i 0 : Int) else (recArr.getD ((y - 1) * 16 + x) 0 : Int)
          else if mode == 1 then
            if x == 0 then (pred.getD i 0 : Int) else (recArr.getD (i - 1) 0 : Int)
          else (pred.getD i 0 : Int)
        recArr := recArr.set! i (clipSampleHbd (base + raw.getD i 0) bitDepth)
    return recArr

private def dpcmRect (pred : Array Nat) (raw : Array Int) (w mode bitDepth : Nat) : Array Nat :=
  Id.run do
    let h := if w == 0 then 0 else raw.size / w
    let mut recArr : Array Nat := Array.replicate raw.size 0
    for y in [:h] do
      for x in [:w] do
        let i := y * w + x
        let base : Int :=
          if mode == 0 then
            if y == 0 then (pred.getD i 0 : Int) else (recArr.getD ((y - 1) * w + x) 0 : Int)
          else if mode == 1 then
            if x == 0 then (pred.getD i 0 : Int) else (recArr.getD (i - 1) 0 : Int)
          else (pred.getD i 0 : Int)
        recArr := recArr.set! i (clipSampleHbd (base + raw.getD i 0) bitDepth)
    return recArr

private def assembleI16Raw (dcRaster : Array Int) (ac16 : Array (Array Int)) : Array Int :=
  Array.ofFn fun i : Fin 256 =>
    let x := i.val % 16
    let y := i.val / 16
    let blk := zScan4BlkIdx (x / 4) (y / 4)
    let sub := (y % 4) * 4 + (x % 4)
    let ac := ac16.getD blk (Array.replicate 16 0)
    if sub == 0 then dcRaster.getD blk 0 else ac.getD sub 0

private def assembleChromaRaw (dc : Array Int) (ac : Array (Array Int)) (w h : Nat) : Array Int :=
  Array.ofFn fun i : Fin (w * h) =>
    let x := i.val % w
    let y := i.val / w
    let blk := (y / 4) * (w / 4) + (x / 4)
    let sub := (y % 4) * 4 + (x % 4)
    let acB := ac.getD blk (Array.replicate 16 0)
    if sub == 0 then dc.getD blk 0 else acB.getD sub 0

structure HbdDecodedBlk4 where
  sliceId     : Int := -1
  isIntra     : Bool := false
  hasCoeff    : Bool := false
  refIdxL0    : Int := -1
  mvL0        : LeanAV.H264InterDeblockDpb.MotionVec := ⟨0, 0⟩
  refPicUidL0 : Option Nat := none
  refIdxL1    : Int := -1
  mvL1        : LeanAV.H264InterDeblockDpb.MotionVec := ⟨0, 0⟩
  refPicUidL1 : Option Nat := none
  qpPrimeY    : Nat := 0
  deriving Inhabited

structure HbdStoredPic where
  uid        : Nat
  poc        : Int
  isLongTerm : Bool := false
  pic        : HbdPic
  cropLeft   : Nat := 0
  cropTop    : Nat := 0
  cropWidth  : Nat := 0
  cropHeight : Nat := 0
  gridW4     : Nat := 0
  gridH4     : Nat := 0
  colGrid    : Array HbdDecodedBlk4 := #[]
  deriving Inhabited

structure HbdPocState where
  prevPocMsb          : Int := 0
  prevPocLsb          : Int := 0
  prevFrameNum        : Nat := 0
  prevFrameNumOffset  : Nat := 0
  prevHasMmco5        : Bool := false
  deriving Inhabited

structure HbdSpsPair where
  syn : LeanAV.H264Syntax.H264SpsFull
  ent : LeanAV.H264Entropy.SpsFull

structure HbdPpsPair where
  syn : LeanAV.H264Syntax.H264PpsFull
  ent : LeanAV.H264Entropy.PpsFull

structure HbdDecoderState where
  spsTable   : Array (Option HbdSpsPair) := Array.replicate 32 none
  ppsTable   : Array (Option HbdPpsPair) := Array.replicate 256 none
  dpb        : LeanAV.H264InterDeblockDpb.H264Dpb := {}
  dpbInit    : Bool := false
  stored     : Array HbdStoredPic := #[]
  emitted    : Array Nat := #[]
  pocState   : HbdPocState := {}
  deriving Inhabited

def registerHbdSps (st : HbdDecoderState) (nal : ByteArray) : Option HbdDecoderState := do
  let syn ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray nal)
  let ent ← LeanAV.H264Entropy.parseSpsFull nal
  let idx := syn.spsId.toNat
  if idx ≥ 32 || ent.spsId != idx then none
  else some { st with spsTable := st.spsTable.set! idx (some { syn := syn, ent := ent }) }

def registerHbdPps (st : HbdDecoderState) (nal : ByteArray) : Option HbdDecoderState := do
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
      let spsPair ← st.spsTable.getD spsIdx none
      let syn ← LeanAV.H264Syntax.parseH264PpsFull (ByteSlice.ofByteArray nal) (some spsPair.syn)
      let entSps := st.spsTable.map (fun o => o.map (·.ent))
      let ent ← LeanAV.H264Entropy.parsePpsFull nal entSps
      if syn.ppsId.toNat != ppsIdx || ent.ppsId != ppsIdx then none
      else some { st with ppsTable := st.ppsTable.set! ppsIdx (some { syn := syn, ent := ent }) }

private def hbdModOps (ops : Array LeanAV.H264Syntax.RefPicListModOp)
    : List LeanAV.H264InterDeblockDpb.RefListModOp :=
  (ops.toList.map fun op =>
    match op.modificationOfPicNumsIdc.toNat with
    | 0 => LeanAV.H264InterDeblockDpb.RefListModOp.subPicNum op.param.toNat
    | 1 => LeanAV.H264InterDeblockDpb.RefListModOp.addPicNum op.param.toNat
    | 2 => LeanAV.H264InterDeblockDpb.RefListModOp.longTermPic op.param.toNat
    | _ => LeanAV.H264InterDeblockDpb.RefListModOp.endLoop) ++
  [LeanAV.H264InterDeblockDpb.RefListModOp.endLoop]

private def hbdMmcoOps (ops : Array LeanAV.H264Syntax.MmcoOp)
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

private def hbdPicturePoc (sps : LeanAV.H264Syntax.H264SpsFull)
    (sh : LeanAV.H264Syntax.H264SliceHeaderFull) (ps : HbdPocState) : Int × HbdPocState :=
  let isIdr := sh.nalUnitType == 5
  let isRef := sh.nalRefIdc != 0
  let hasMmco5 := isRef && !isIdr && sh.adaptiveRefPicMarkingModeFlag && sh.mmcoOps.any (fun op => op.opcode == 5)
  let log2MaxFn := sps.log2MaxFrameNumMinus4.toNat + 4
  let fn := sh.frameNum.toNat
  if sps.picOrderCntType == 0 then
    let log2MaxLsb := sps.log2MaxPicOrderCntLsbMinus4.toNat + 4
    let lsb := sh.picOrderCntLsb.toNat
    let (poc, msb, _) := LeanAV.H264InterDeblockDpb.derivePocType0
      isIdr ps.prevHasMmco5 false false false lsb log2MaxLsb sh.deltaPicOrderCntBottom.toInt ps.prevPocMsb ps.prevPocLsb
    let nextPs : HbdPocState :=
      if isRef then
        { prevPocMsb := if hasMmco5 then 0 else msb
          prevPocLsb := if hasMmco5 then 0 else Int.ofNat lsb
          prevFrameNum := if hasMmco5 then 0 else fn
          prevFrameNumOffset := 0
          prevHasMmco5 := hasMmco5 }
      else { ps with prevFrameNum := fn, prevHasMmco5 := false }
    (poc, nextPs)
  else if sps.picOrderCntType == 1 then
    let offArr := sps.offsetForRefFrame.map (fun v => v.toInt)
    let (poc, fnOff) := LeanAV.H264InterDeblockDpb.derivePocType1
      isIdr isRef ps.prevHasMmco5 false false fn log2MaxFn ps.prevFrameNumOffset ps.prevFrameNum
      sps.offsetForNonRefPic.toInt sps.offsetForTopToBottomField.toInt offArr
      sh.deltaPicOrderCnt0.toInt sh.deltaPicOrderCnt1.toInt
    let nextPs : HbdPocState :=
      { ps with prevFrameNum := if hasMmco5 then 0 else fn
                prevFrameNumOffset := if hasMmco5 then 0 else fnOff
                prevHasMmco5 := hasMmco5 }
    (poc, nextPs)
  else
    let (poc, fnOff) := LeanAV.H264InterDeblockDpb.derivePocType2
      isIdr isRef ps.prevHasMmco5 fn log2MaxFn ps.prevFrameNumOffset ps.prevFrameNum
    let nextPs : HbdPocState :=
      { ps with prevFrameNum := if hasMmco5 then 0 else fn
                prevFrameNumOffset := if hasMmco5 then 0 else fnOff
                prevHasMmco5 := hasMmco5 }
    (poc, nextPs)

private def reconstructLumaMbHbd
    (canvas : Array Nat) (mb : LeanAV.H264Entropy.MbSyntax)
    (leftCol topRow : Array Nat) (topLeft : Nat) (leftAv topAv topLeftAv : Bool)
    (mbW : Nat) (qpPrimeY bitDepth : Nat) (bypass : Bool)
    (w4 w8 : Array Int) (modes : Array Nat) (sliceIds : Array Int) (intraFlags : Array Bool)
    (gridW gx gy : Nat) (sliceId : Int) (constrained : Bool)
    : Option (Array Nat × Array Nat × Array Bool) := do
  let mid := h264MidSample bitDepth
  let mut out := canvas
  let mut modes' := modes
  let mut nz16 := Array.replicate 16 false
  if mb.kind == .iPcm then
    let (yArr, _, _) ← unpackIpcmSamplesHbd mb.pcmBytes 0 bitDepth bitDepth
    for b in [:16] do
      nz16 := nz16.set! b true
    some (yArr, modes', nz16)
  else if mb.kind == .i16x16 then
    let i16Mode := (mb.intraIdx - 1) % 4
    for b in [:16] do
      modes' := modes'.set! ((gy + b / 4) * gridW + (gx + b % 4)) 2
    let pred := pred16x16Hbd i16Mode leftCol topRow topLeft leftAv topAv bitDepth
    let rec256 :=
      if bypass then
        let raw := assembleI16Raw (LeanAV.H264Entropy.zigzagToRaster4x4 mb.i16Dc)
          (Array.ofFn fun b : Fin 16 => ac15ToRaster16 (mb.lumaAcOr4x4.getD b.val #[]))
        dpcm16x16 pred raw (if i16Mode == 0 then 0 else if i16Mode == 1 then 1 else 2) bitDepth
      else
        let dcRast := lumaDcDequantHbd (LeanAV.H264Entropy.zigzagToRaster4x4 mb.i16Dc) qpPrimeY (w4.getD 0 16)
        let recBlocks := Array.ofFn fun blk : Fin 16 =>
          let acScan := if (mb.cbp &&& 0xF) != 0 then mb.lumaAcOr4x4.getD blk.val #[] else Array.replicate 16 0
          let acRast := ac15ToRaster16 acScan
          let scaled := Array.ofFn fun s : Fin 16 =>
            if s.val == 0 then dcRast.getD blk.val 0
            else dequantCoeff4x4 (acRast.getD s.val 0) qpPrimeY (s.val / 4) (s.val % 4) (w4.getD s.val 16)
          idct4x4FromScaled scaled
        Array.ofFn fun i : Fin 256 =>
          let x := i.val % 16
          let y := i.val / 16
          let blk := zScan4BlkIdx (x / 4) (y / 4)
          let sub := (y % 4) * 4 + (x % 4)
          clipSampleHbd ((pred.getD i.val 0 : Int) + (recBlocks.getD blk (Array.replicate 16 0)).getD sub 0) bitDepth
    for b in [:16] do
      let acScan := mb.lumaAcOr4x4.getD b #[]
      nz16 := nz16.set! b (anyNz mb.i16Dc 16 || anyNz acScan 15)
    some (rec256, modes', nz16)
  else if mb.transform8x8 != 0 then
    for i8 in [:4] do
      let xO := (i8 % 2) * 8
      let yO := (i8 / 2) * 8
      let gx0 := gx + xO / 4
      let gy0 := gy + yO / 4
      let mpm := mpmOf modes' sliceIds intraFlags gridW gx0 gy0 sliceId constrained
      let (pf, rem) := mb.intraPred.getD i8 (1, 0)
      let mode := syntaxToMode mpm pf rem
      modes' := modes'.set! (gy0 * gridW + gx0) mode
      for dy in [:2] do
        for dx in [:2] do
          modes' := modes'.set! ((gy0 + dy) * gridW + (gx0 + dx)) mode
      let trAvail := zScan4AllowTopRight (4 * i8) topAv (topRow.size > 16)
      let nbr := hbdSubNeighbors 8 out mbW leftCol topRow topLeft leftAv topAv topLeftAv xO yO trAvail mid
      let pred := pred8x8Hbd mode nbr bitDepth
      let scan64 := if (mb.cbp &&& (1 <<< i8)) != 0 then mb.luma8x8.getD i8 #[] else Array.replicate 64 0
      let rast64 := LeanAV.H264Entropy.zigzagToRaster8x8 scan64
      let rec64 :=
        if bypass then applyDpcmBlock pred rast64 (if mode == 0 then 0 else if mode == 1 then 1 else 2) 8 bitDepth
        else reconstructBlock8x8Hbd pred rast64 qpPrimeY bitDepth w8
      for dy in [:8] do
        for dx in [:8] do
          out := out.set! ((yO + dy) * mbW + (xO + dx)) (rec64.getD (dy * 8 + dx) mid)
      let nz := anyNz scan64 64
      for dy in [:2] do
        for dx in [:2] do
          nz16 := nz16.set! ((yO / 4 + dy) * 4 + (xO / 4 + dx)) nz
    some (out, modes', nz16)
  else
    for b in [:16] do
      let (xO, yO) := zScan4BlkCoord b
      let gx0 := gx + xO / 4
      let gy0 := gy + yO / 4
      let mpm := mpmOf modes' sliceIds intraFlags gridW gx0 gy0 sliceId constrained
      let (pf, rem) := mb.intraPred.getD b (1, 0)
      let mode := syntaxToMode mpm pf rem
      modes' := modes'.set! (gy0 * gridW + gx0) mode
      let trAvail := zScan4AllowTopRight b topAv (topRow.size > 16)
      let nbr := hbdSubNeighbors 4 out mbW leftCol topRow topLeft leftAv topAv topLeftAv xO yO trAvail mid
      let pred := pred4x4Hbd mode nbr bitDepth
      let scan16 := if (mb.cbp &&& (1 <<< (b / 4))) != 0 then mb.lumaAcOr4x4.getD b #[] else Array.replicate 16 0
      let rast16 := LeanAV.H264Entropy.zigzagToRaster4x4 scan16
      let rec16 :=
        if bypass then applyDpcmBlock pred rast16 (if mode == 0 then 0 else if mode == 1 then 1 else 2) 4 bitDepth
        else reconstructBlock4x4Hbd pred rast16 qpPrimeY bitDepth w4
      for dy in [:4] do
        for dx in [:4] do
          out := out.set! ((yO + dy) * mbW + (xO + dx)) (rec16.getD (dy * 4 + dx) mid)
      nz16 := nz16.set! b (anyNz scan16 16)
    some (out, modes', nz16)

private def reconstructLumaResidualHbd
    (pred : Array Nat) (mb : LeanAV.H264Entropy.MbSyntax)
    (qpY bitDepth : Nat) (bypass : Bool) (w4 w8 : Array Int) : Array Nat :=
  if mb.isSkip || mb.cbp == 0 then pred
  else if bypass then
    if mb.transform8x8 != 0 then
      Array.ofFn fun i : Fin 256 =>
        let x := i.val % 16
        let y := i.val / 16
        let i8 := (y / 8) * 2 + (x / 8)
        let sub := (y % 8) * 8 + (x % 8)
        let scan := if (mb.cbp &&& (1 <<< i8)) != 0 then mb.luma8x8.getD i8 #[] else Array.replicate 64 0
        (applyDpcmBlock
          (Array.ofFn fun k : Fin 64 => pred.getD (((y / 8) * 8 + k.val / 8) * 16 + ((x / 8) * 8 + k.val % 8)) 0)
          (LeanAV.H264Entropy.zigzagToRaster8x8 scan) 2 8 bitDepth).getD sub 0
    else
      Array.ofFn fun i : Fin 256 =>
        let x := i.val % 16
        let y := i.val / 16
        let blk := zScan4BlkIdx (x / 4) (y / 4)
        let sub := (y % 4) * 4 + (x % 4)
        let scan := if (mb.cbp &&& (1 <<< (blk / 4))) != 0 then mb.lumaAcOr4x4.getD blk #[] else Array.replicate 16 0
        (applyDpcmBlock
          (Array.ofFn fun k : Fin 16 => pred.getD (((y / 4) * 4 + k.val / 4) * 16 + ((x / 4) * 4 + k.val % 4)) 0)
          (LeanAV.H264Entropy.zigzagToRaster4x4 scan) 2 4 bitDepth).getD sub 0
  else if mb.transform8x8 != 0 then
    Array.ofFn fun i : Fin 256 =>
      let x := i.val % 16
      let y := i.val / 16
      let i8 := (y / 8) * 2 + (x / 8)
      let sub := (y % 8) * 8 + (x % 8)
      let scan := if (mb.cbp &&& (1 <<< i8)) != 0 then mb.luma8x8.getD i8 #[] else Array.replicate 64 0
      (reconstructBlock8x8Hbd
        (Array.ofFn fun k : Fin 64 => pred.getD (((y / 8) * 8 + k.val / 8) * 16 + ((x / 8) * 8 + k.val % 8)) 0)
        (LeanAV.H264Entropy.zigzagToRaster8x8 scan) qpY bitDepth w8).getD sub 0
  else
    Array.ofFn fun i : Fin 256 =>
      let x := i.val % 16
      let y := i.val / 16
      let blk := zScan4BlkIdx (x / 4) (y / 4)
      let sub := (y % 4) * 4 + (x % 4)
      let scan := if (mb.cbp &&& (1 <<< (blk / 4))) != 0 then mb.lumaAcOr4x4.getD blk #[] else Array.replicate 16 0
      (reconstructBlock4x4Hbd
        (Array.ofFn fun k : Fin 16 => pred.getD (((y / 4) * 4 + k.val / 4) * 16 + ((x / 4) * 4 + k.val % 4)) 0)
        (LeanAV.H264Entropy.zigzagToRaster4x4 scan) qpY bitDepth w4).getD sub 0

private def reconstructChromaMbHbd
    (pred : Array Nat) (mb : LeanAV.H264Entropy.MbSyntax)
    (chType qpC bitDepth : Nat) (bypass : Bool) (w4 w8 : Array Int) (w plane : Nat) (isIntra : Bool := true) : Array Nat :=
  if chType == 0 then pred
  else if bypass then
    let dpcmMode := if isIntra then losslessChromaDpcmMode mb.chromaPredMode else 2
    if chType == 3 then
      if mb.kind == .i16x16 then
        let i16Mode := (mb.intraIdx - 1) % 4
        let raw := assembleI16Raw (LeanAV.H264Entropy.zigzagToRaster4x4 (mb.chroma444Dc.getD plane #[]))
          (Array.ofFn fun b : Fin 16 => ac15ToRaster16 (mb.chroma444AcOr4x4.getD (plane * 16 + b.val) #[]))
        dpcm16x16 pred raw (if i16Mode == 0 then 0 else if i16Mode == 1 then 1 else 2) bitDepth
      else if mb.transform8x8 != 0 then
        Array.ofFn fun i : Fin 256 =>
          let x := i.val % 16
          let y := i.val / 16
          let i8 := (y / 8) * 2 + (x / 8)
          let sub := (y % 8) * 8 + (x % 8)
          let scan := if (mb.cbp &&& (1 <<< i8)) != 0 then
            (mb.chroma444_8x8.getD plane #[]).getD i8 #[] else Array.replicate 64 0
          (applyDpcmBlock
            (Array.ofFn fun k : Fin 64 => pred.getD (((y / 8) * 8 + k.val / 8) * 16 + ((x / 8) * 8 + k.val % 8)) 0)
            (LeanAV.H264Entropy.zigzagToRaster8x8 scan) 2 8 bitDepth).getD sub 0
      else
        Array.ofFn fun i : Fin 256 =>
          let x := i.val % 16
          let y := i.val / 16
          let blk := zScan4BlkIdx (x / 4) (y / 4)
          let sub := (y % 4) * 4 + (x % 4)
          let scan := if (mb.cbp &&& (1 <<< (blk / 4))) != 0 then mb.chroma444AcOr4x4.getD (plane * 16 + blk) #[] else Array.replicate 16 0
          (applyDpcmBlock
            (Array.ofFn fun k : Fin 16 => pred.getD (((y / 4) * 4 + k.val / 4) * 16 + ((x / 4) * 4 + k.val % 4)) 0)
            (LeanAV.H264Entropy.zigzagToRaster4x4 scan) 2 4 bitDepth).getD sub 0
    else
      let blocks := if chType == 2 then 8 else 4
      let dcRast :=
        if (mb.cbp &&& 0x30) != 0 then
          if chType == 2 then chromaDcScan2x4ToRaster (mb.chromaDc.getD plane #[])
          else (mb.chromaDc.getD plane #[]).extract 0 4
        else Array.replicate blocks 0
      let acRast :=
        if (mb.cbp &&& 0x20) != 0 then
          Array.ofFn fun b : Fin blocks => ac15ToRaster16 (mb.chromaAc.getD (plane * blocks + b.val) #[])
        else Array.replicate blocks (Array.replicate 16 0)
      Array.ofFn fun i : Fin (w * (pred.size / w)) =>
        let x := i.val % w
        let y := i.val / w
        let blk := (y / 4) * (w / 4) + (x / 4)
        let sub := (y % 4) * 4 + (x % 4)
        let r16 := Array.ofFn fun k : Fin 16 =>
          if k.val == 0 then dcRast.getD blk 0 else (acRast.getD blk #[]).getD k.val 0
        let p16 := Array.ofFn fun k : Fin 16 =>
          pred.getD (((y / 4) * 4 + k.val / 4) * w + ((x / 4) * 4 + k.val % 4)) 0
        (applyDpcmBlock p16 r16 dpcmMode 4 bitDepth).getD sub 0
  else if chType == 1 then
    let dc4 := if (mb.cbp &&& 0x30) != 0 then (mb.chromaDc.getD plane #[]).extract 0 4 else Array.replicate 4 0
    let ac4 := if (mb.cbp &&& 0x20) != 0 then Array.ofFn fun b : Fin 4 => ac15ToRaster16 (mb.chromaAc.getD (plane * 4 + b.val) #[])
               else Array.replicate 4 (Array.replicate 16 0)
    reconstructChroma420Hbd pred dc4 ac4 qpC bitDepth w4
  else if chType == 2 then
    let dc8 := if (mb.cbp &&& 0x30) != 0 then chromaDcScan2x4ToRaster (mb.chromaDc.getD plane #[]) else Array.replicate 8 0
    let ac8 := if (mb.cbp &&& 0x20) != 0 then Array.ofFn fun b : Fin 8 => ac15ToRaster16 (mb.chromaAc.getD (plane * 8 + b.val) #[])
               else Array.replicate 8 (Array.replicate 16 0)
    reconstructChroma422Hbd pred dc8 ac8 qpC bitDepth w4
  else
    if mb.kind == .i16x16 then
      let dc16 := LeanAV.H264Entropy.zigzagToRaster4x4 (mb.chroma444Dc.getD plane #[])
      let ac16 := if (mb.cbp &&& 0xF) != 0 then Array.ofFn fun b : Fin 16 => ac15ToRaster16 (mb.chroma444AcOr4x4.getD (plane * 16 + b.val) #[])
                  else Array.replicate 16 (Array.replicate 16 0)
      reconstructChroma444Hbd pred dc16 ac16 qpC bitDepth w4
    else if mb.transform8x8 != 0 then
      Array.ofFn fun i : Fin 256 =>
        let x := i.val % 16
        let y := i.val / 16
        let i8 := (y / 8) * 2 + (x / 8)
        let sub := (y % 8) * 8 + (x % 8)
        let scan := if (mb.cbp &&& (1 <<< i8)) != 0 then
          (mb.chroma444_8x8.getD plane #[]).getD i8 #[] else Array.replicate 64 0
        let rec64 := reconstructBlock8x8Hbd
          (Array.ofFn fun k : Fin 64 => pred.getD (((y / 8) * 8 + k.val / 8) * 16 + ((x / 8) * 8 + k.val % 8)) 0)
          (LeanAV.H264Entropy.zigzagToRaster8x8 scan) qpC bitDepth w8
        rec64.getD sub 0
    else
      Array.ofFn fun i : Fin 256 =>
        let x := i.val % 16
        let y := i.val / 16
        let blk := zScan4BlkIdx (x / 4) (y / 4)
        let sub := (y % 4) * 4 + (x % 4)
        let scan := if (mb.cbp &&& (1 <<< (blk / 4))) != 0 then mb.chroma444AcOr4x4.getD (plane * 16 + blk) #[] else Array.replicate 16 0
        let rec16 := reconstructBlock4x4Hbd
          (Array.ofFn fun k : Fin 16 => pred.getD (((y / 4) * 4 + k.val / 4) * 16 + ((x / 4) * 4 + k.val % 4)) 0)
          (LeanAV.H264Entropy.zigzagToRaster4x4 scan) qpC bitDepth w4
        rec16.getD sub 0

private def reconstructChroma444CausalMbHbd
    (canvas : Array Nat) (mb : LeanAV.H264Entropy.MbSyntax)
    (leftCol topRow : Array Nat) (topLeft : Nat) (leftAv topAv topLeftAv : Bool)
    (qpC bitDepth : Nat) (bypass : Bool) (w4 w8 : Array Int)
    (modesAfterLuma : Array Nat) (gridW gx gy plane : Nat) : Array Nat := Id.run do
  let mid := h264MidSample bitDepth
  let mut out := canvas
  if mb.kind == .i16x16 then
    let i16Mode := (mb.intraIdx - 1) % 4
    let pred := pred16x16Hbd i16Mode leftCol topRow topLeft leftAv topAv bitDepth
    if bypass then
      let raw := assembleI16Raw (LeanAV.H264Entropy.zigzagToRaster4x4 (mb.chroma444Dc.getD plane #[]))
        (Array.ofFn fun b : Fin 16 => ac15ToRaster16 (mb.chroma444AcOr4x4.getD (plane * 16 + b.val) #[]))
      return dpcm16x16 pred raw (if i16Mode == 0 then 0 else if i16Mode == 1 then 1 else 2) bitDepth
    else
      let dc16 := LeanAV.H264Entropy.zigzagToRaster4x4 (mb.chroma444Dc.getD plane #[])
      let ac16 := if (mb.cbp &&& 0xF) != 0 then Array.ofFn fun b : Fin 16 => ac15ToRaster16 (mb.chroma444AcOr4x4.getD (plane * 16 + b.val) #[])
                  else Array.replicate 16 (Array.replicate 16 0)
      return reconstructChroma444Hbd pred dc16 ac16 qpC bitDepth w4
  else if mb.transform8x8 != 0 then
    for i8 in [:4] do
      let xO := (i8 % 2) * 8
      let yO := (i8 / 2) * 8
      let mode := modesAfterLuma.getD ((gy + yO / 4) * gridW + (gx + xO / 4)) 2
      let trAvail := zScan4AllowTopRight (4 * i8) topAv (topRow.size > 16)
      let nbr := hbdSubNeighbors 8 out 16 leftCol topRow topLeft leftAv topAv topLeftAv xO yO trAvail mid
      let pred := pred8x8Hbd mode nbr bitDepth
      let scan64 := if (mb.cbp &&& (1 <<< i8)) != 0 then (mb.chroma444_8x8.getD plane #[]).getD i8 #[] else Array.replicate 64 0
      let rast64 := LeanAV.H264Entropy.zigzagToRaster8x8 scan64
      let rec64 :=
        if bypass then applyDpcmBlock pred rast64 (if mode == 0 then 0 else if mode == 1 then 1 else 2) 8 bitDepth
        else reconstructBlock8x8Hbd pred rast64 qpC bitDepth w8
      for dy in [:8] do
        for dx in [:8] do
          out := out.set! ((yO + dy) * 16 + (xO + dx)) (rec64.getD (dy * 8 + dx) mid)
    return out
  else
    for b in [:16] do
      let (xO, yO) := zScan4BlkCoord b
      let mode := modesAfterLuma.getD ((gy + yO / 4) * gridW + (gx + xO / 4)) 2
      let trAvail := zScan4AllowTopRight b topAv (topRow.size > 16)
      let nbr := hbdSubNeighbors 4 out 16 leftCol topRow topLeft leftAv topAv topLeftAv xO yO trAvail mid
      let pred := pred4x4Hbd mode nbr bitDepth
      let scan16 := if (mb.cbp &&& (1 <<< (b / 4))) != 0 then mb.chroma444AcOr4x4.getD (plane * 16 + b) #[] else Array.replicate 16 0
      let rast16 := LeanAV.H264Entropy.zigzagToRaster4x4 scan16
      let rec16 :=
        if bypass then applyDpcmBlock pred rast16 (if mode == 0 then 0 else if mode == 1 then 1 else 2) 4 bitDepth
        else reconstructBlock4x4Hbd pred rast16 qpC bitDepth w4
      for dy in [:4] do
        for dx in [:4] do
          out := out.set! ((yO + dy) * 16 + (xO + dx)) (rec16.getD (dy * 4 + dx) mid)
    return out

private def findStoredHbd (stored : Array HbdStoredPic) (uid : Nat) : Option HbdStoredPic :=
  stored.find? fun sp => sp.uid == uid

private def resolveHbdRefs (refs : List LeanAV.H264InterDeblockDpb.DpbPicture)
    (stored : Array HbdStoredPic) : Option (Array HbdStoredPic) := do
  let mut out : Array HbdStoredPic := Array.mkEmpty refs.length
  for e in refs do
    let sp ← findStoredHbd stored e.uid
    out := out.push { sp with poc := e.poc, isLongTerm := LeanAV.H264InterDeblockDpb.isLongTermRef e }
  some out

private def lookupHbdMv (grid : Array HbdDecodedBlk4) (sliceIds : Array Int)
    (gridW gridH : Nat) (sliceId : Int) (listIdx : Nat) (gx gy : Int)
    : LeanAV.H264InterDeblockDpb.NeighborMv :=
  if gx < 0 || gy < 0 || gx.toNat ≥ gridW || gy.toNat ≥ gridH then
    { avail := false, refIdx := -1, mv := ⟨0, 0⟩ }
  else
    let idx := gy.toNat * gridW + gx.toNat
    if sliceIds.getD idx (-1) != sliceId then
      { avail := false, refIdx := -1, mv := ⟨0, 0⟩ }
    else
      let b := grid.getD idx {}
      if b.isIntra then { avail := true, refIdx := -1, mv := ⟨0, 0⟩ }
      else if listIdx == 0 then { avail := true, refIdx := b.refIdxL0, mv := b.mvL0 }
      else { avail := true, refIdx := b.refIdxL1, mv := b.mvL1 }

private def hbdNeighborsABC (grid : Array HbdDecodedBlk4) (sliceIds : Array Int)
    (gridW gridH : Nat) (sliceId : Int) (listIdx gx0 gy0 pw4 : Nat)
    : LeanAV.H264InterDeblockDpb.NeighborMv × LeanAV.H264InterDeblockDpb.NeighborMv × LeanAV.H264InterDeblockDpb.NeighborMv :=
  let igx := Int.ofNat gx0
  let igy := Int.ofNat gy0
  let nbA := lookupHbdMv grid sliceIds gridW gridH sliceId listIdx (igx - 1) igy
  let nbB := lookupHbdMv grid sliceIds gridW gridH sliceId listIdx igx (igy - 1)
  let rx := gx0 % 4
  let ry := gy0 % 4
  let trBlocked := (rx + pw4 == 4 && (ry == 1 || ry == 2 || ry == 3)) || (rx + pw4 == 2 && (ry == 1 || ry == 3))
  let nbCRaw :=
    if trBlocked then { avail := false, refIdx := -1, mv := ⟨0, 0⟩ : LeanAV.H264InterDeblockDpb.NeighborMv }
    else lookupHbdMv grid sliceIds gridW gridH sliceId listIdx (igx + Int.ofNat pw4) (igy - 1)
  let nbC := if nbCRaw.avail then nbCRaw else lookupHbdMv grid sliceIds gridW gridH sliceId listIdx (igx - 1) (igy - 1)
  (nbA, nbB, nbC)

private def setHbdRect (grid : Array HbdDecodedBlk4) (gridW gx0 gy0 pw4 ph4 listIdx : Nat)
    (refIdx : Int) (mv : LeanAV.H264InterDeblockDpb.MotionVec) (uid? : Option Nat) : Array HbdDecodedBlk4 := Id.run do
  let mut g := grid
  for dy in [:ph4] do
    for dx in [:pw4] do
      let idx := (gy0 + dy) * gridW + (gx0 + dx)
      let cur := g.getD idx {}
      let upd :=
        if listIdx == 0 then { cur with refIdxL0 := refIdx, mvL0 := mv, refPicUidL0 := uid? }
        else { cur with refIdxL1 := refIdx, mvL1 := mv, refPicUidL1 := uid? }
      g := g.set! idx upd
  return g

private def resolveHbdCollocatedMotion
    (l0 l1 : Array HbdStoredPic) (direct8x8 : Bool) (gx gy : Nat)
    : Bool × Int × LeanAV.H264InterDeblockDpb.MotionVec × Int × Int :=
  if l1.size == 0 then
    (false, 0, ⟨0, 0⟩, 0, 0)
  else
    let colPic := l1[0]!
    let rx := gx % 4
    let ry := gy % 4
    let cgx := if direct8x8 then (gx - rx) + (if rx ≥ 2 then 3 else 0) else gx
    let cgy := if direct8x8 then (gy - ry) + (if ry ≥ 2 then 3 else 0) else gy
    let colBlk :=
      if cgx < colPic.gridW4 && cgy < colPic.gridH4 then
        colPic.colGrid.getD (cgy * colPic.gridW4 + cgx) {}
      else {}
    if colBlk.isIntra then
      (false, 0, ⟨0, 0⟩, (l0.getD 0 colPic).poc, colPic.poc)
    else
      let useColL0 := colBlk.refIdxL0 ≥ 0
      let mvCol := if useColL0 then colBlk.mvL0 else colBlk.mvL1
      let refCol := if useColL0 then colBlk.refIdxL0 else colBlk.refIdxL1
      let uidCol? := if useColL0 then colBlk.refPicUidL0 else colBlk.refPicUidL1
      let mappedL0 : Int :=
        match uidCol? with
        | some u =>
          match l0.findIdx? (fun p => p.uid == u) with
          | some i => Int.ofNat i
          | none => 0
        | none => 0
      let colZero : Bool :=
        !colPic.isLongTerm && refCol == 0 && mvCol.x.natAbs ≤ 1 && mvCol.y.natAbs ≤ 1
      let poc0 :=
        if mappedL0 ≥ 0 && mappedL0.toNat < l0.size then (l0.getD mappedL0.toNat colPic).poc
        else colPic.poc
      (colZero, mappedL0, mvCol, poc0, colPic.poc)

private def deriveHbdDirectSubMb8x8
    (grid0 : Array HbdDecodedBlk4) (sliceIds : Array Int)
    (gridW gridH : Nat) (sliceId currPoc : Int)
    (spatial direct8x8 : Bool)
    (l0 l1 : Array HbdStoredPic) (mbGx mbGy subIdx : Nat)
    (spatialBase? : Option (LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv ×
                            LeanAV.H264InterDeblockDpb.NeighborMv))
    : Array HbdDecodedBlk4 := Id.run do
  let mut g := grid0
  let sx0 := (subIdx % 2) * 2
  let sy0 := (subIdx / 2) * 2
  let (nb0A, nb0B, nb0C, nb1A, nb1B, nb1C) :=
    match spatialBase? with
    | some base => base
    | none =>
      let (a0, b0, c0) := hbdNeighborsABC g sliceIds gridW gridH sliceId 0 mbGx mbGy 4
      let (a1, b1, c1) := hbdNeighborsABC g sliceIds gridW gridH sliceId 1 mbGx mbGy 4
      (a0, b0, c0, a1, b1, c1)
  for dy in [:2] do
    for dx in [:2] do
      let gx := mbGx + sx0 + dx
      let gy := mbGy + sy0 + dy
      let (colZero, mappedL0, mvCol, poc0, poc1) :=
        resolveHbdCollocatedMotion l0 l1 direct8x8 gx gy
      let dp :=
        if spatial then
          LeanAV.H264InterDeblockDpb.bDirectSpatial nb0A nb0B nb0C nb1A nb1B nb1C colZero
        else
          LeanAV.H264InterDeblockDpb.bDirectTemporal mvCol mappedL0 currPoc poc0 poc1
      let r0 := if dp.predFlagL0 then dp.refIdxL0 else -1
      let r1 := if dp.predFlagL1 then dp.refIdxL1 else -1
      let uid0? := if r0 ≥ 0 && r0.toNat < l0.size then some (l0[r0.toNat]!.uid) else none
      let uid1? := if r1 ≥ 0 && r1.toNat < l1.size then some (l1[r1.toNat]!.uid) else none
      let cur := g.getD (gy * gridW + gx) {}
      g := g.set! (gy * gridW + gx) {
        cur with
        refIdxL0 := r0
        mvL0 := if dp.predFlagL0 then dp.mvL0 else ⟨0, 0⟩
        refPicUidL0 := uid0?
        refIdxL1 := r1
        mvL1 := if dp.predFlagL1 then dp.mvL1 else ⟨0, 0⟩
        refPicUidL1 := uid1?
      }
  return g

private def deriveHbdInterMotion (mb : LeanAV.H264Entropy.MbSyntax)
    (kind : LeanAV.H264Syntax.H264SliceKind)
    (grid0 : Array HbdDecodedBlk4) (sliceIds : Array Int)
    (gridW gridH mbX mbY : Nat) (sliceId currPoc : Int)
    (spatial direct8x8 : Bool) (l0 l1 : Array HbdStoredPic) : Option (Array HbdDecodedBlk4) := Id.run do
  let mbGx := mbX * 4
  let mbGy := mbY * 4
  let mut g := grid0
  if mb.isSkip then
    if kind == .P then
      if l0.size == 0 then return none
      let (a, b, c) := hbdNeighborsABC g sliceIds gridW gridH sliceId 0 mbGx mbGy 4
      let mv := LeanAV.H264InterDeblockDpb.pSkipMv (!a.avail || !b.avail) a b c
      return some (setHbdRect g gridW mbGx mbGy 4 4 0 0 mv (some l0[0]!.uid))
    else if kind == .B then
      let (a0, b0, c0) := hbdNeighborsABC g sliceIds gridW gridH sliceId 0 mbGx mbGy 4
      let (a1, b1, c1) := hbdNeighborsABC g sliceIds gridW gridH sliceId 1 mbGx mbGy 4
      let spBase := some (a0, b0, c0, a1, b1, c1)
      for i8 in [:4] do
        g := deriveHbdDirectSubMb8x8 g sliceIds gridW gridH sliceId currPoc spatial direct8x8 l0 l1 mbGx mbGy i8 spBase
      return some g
    else return none
  let (info, numLists) :=
    if mb.kind == .pInter then (LeanAV.H264Entropy.pMbInfoTable.getD mb.interIdx {}, 1)
    else if mb.kind == .bInter then (LeanAV.H264Entropy.bMbInfoTable.getD mb.interIdx {}, 2)
    else ({}, 0)
  if numLists == 0 then return none
  if info.shape == .direct then
    let (a0, b0, c0) := hbdNeighborsABC g sliceIds gridW gridH sliceId 0 mbGx mbGy 4
    let (a1, b1, c1) := hbdNeighborsABC g sliceIds gridW gridH sliceId 1 mbGx mbGy 4
    let spBase := some (a0, b0, c0, a1, b1, c1)
    for i8 in [:4] do
      g := deriveHbdDirectSubMb8x8 g sliceIds gridW gridH sliceId currPoc spatial direct8x8 l0 l1 mbGx mbGy i8 spBase
    return some g
  let pics := #[l0, l1]
  let refs := #[mb.refL0, mb.refL1]
  let mvds := #[mb.mvdL0, mb.mvdL1]
  let uses := #[info.useL0, info.useL1]
  if info.shape == .p8x8 then
    let (a0, b0, c0) := hbdNeighborsABC g sliceIds gridW gridH sliceId 0 mbGx mbGy 4
    let (a1, b1, c1) := hbdNeighborsABC g sliceIds gridW gridH sliceId 1 mbGx mbGy 4
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
        g := deriveHbdDirectSubMb8x8 g sliceIds gridW gridH sliceId currPoc spatial direct8x8 l0 l1 mbGx mbGy i8 spBase
      else
        for lst in [:numLists] do
          let sUse := if lst == 0 then sub.useL0 else sub.useL1
          if sUse then
            let rc := if lst == 0 then rc0 else rc1
            let rvNat : Nat :=
              if mb.kind == .pInter && mb.interIdx == 4 then 0
              else (refs.getD lst #[]).getD rc 0
            if !(mb.kind == .pInter && mb.interIdx == 4) then
              if lst == 0 then rc0 := rc0 + 1 else rc1 := rc1 + 1
            let refPics := pics.getD lst #[]
            if rvNat ≥ refPics.size then return none
            let rv := Int.ofNat rvNat
            let uid? := some (refPics[rvNat]!.uid)
            for j in [:sub.subCnt] do
              let (off, bw, bh) := LeanAV.H264Entropy.subPartGeom sub.shape j
              let blkIdx := 4 * i8 + off
              let (xO, yO) := zScan4BlkCoord blkIdx
              let gx0 := mbGx + xO / 4
              let gy0 := mbGy + yO / 4
              let (nbA, nbB, nbC) := hbdNeighborsABC g sliceIds gridW gridH sliceId lst gx0 gy0 bw
              let mvp := LeanAV.H264InterDeblockDpb.mvpMedian rv nbA nbB nbC .p8x8 j
              let mc := if lst == 0 then mc0 else mc1
              let (dx, dy) := (mvds.getD lst #[]).getD mc (0, 0)
              if lst == 0 then mc0 := mc0 + 1 else mc1 := mc1 + 1
              g := setHbdRect g gridW gx0 gy0 bw bh lst rv ⟨mvp.x + dx, mvp.y + dy⟩ uid?
    return some g
  else
    let dpbShape : LeanAV.H264InterDeblockDpb.H264PartShape :=
      match info.shape with
      | .p16x8 => .p16x8
      | .p8x16 => .p8x16
      | _ => .p16x16
    for lst in [:numLists] do
      let mut rc := 0
      let mut mc := 0
      for pi in [:info.useL0.size] do
        if (uses.getD lst #[]).getD pi false then
          let (gx0, gy0, bw, bh) :=
            if info.shape == .p16x16 then (mbGx, mbGy, 4, 4)
            else if info.shape == .p16x8 then (mbGx, mbGy + 2 * pi, 4, 2)
            else (mbGx + 2 * pi, mbGy, 2, 4)
          let rvNat := (refs.getD lst #[]).getD rc 0
          let refPics := pics.getD lst #[]
          if rvNat ≥ refPics.size then return none
          let (a, b, c) := hbdNeighborsABC g sliceIds gridW gridH sliceId lst gx0 gy0 bw
          let mvp := LeanAV.H264InterDeblockDpb.mvpMedian (Int.ofNat rvNat) a b c dpbShape pi
          let (dx, dy) := (mvds.getD lst #[]).getD mc (0, 0)
          rc := rc + 1
          mc := mc + 1
          g := setHbdRect g gridW gx0 gy0 bw bh lst (Int.ofNat rvNat) ⟨mvp.x + dx, mvp.y + dy⟩ (some refPics[rvNat]!.uid)
    return some g

private def predictInterMbHbd (grid : Array HbdDecodedBlk4) (gridW mbX mbY : Nat)
    (l0 l1 : Array HbdStoredPic) (currPoc : Int) (wbipred : UInt8)
    (hasPwt : Bool) (pwt : LeanAV.H264Syntax.PredWeightTable)
    (chType bitDepth bitDepthC : Nat) : Option (Array Nat × Array Nat × Array Nat × Array Bool) := do
  let mbGx := mbX * 4
  let mbGy := mbY * 4
  let cw := if chType == 0 then 0 else if chType == 3 then 16 else 8
  let ch := if chType == 0 then 0 else if chType == 1 then 8 else 16
  let mut y := Array.replicate 256 0
  let mut u := Array.replicate (cw * ch) 0
  let mut v := Array.replicate (cw * ch) 0
  let mut nz := Array.replicate 16 false
  let mut ok := true
  let lLog := pwt.lumaLog2WeightDenom.toNat
  let cLog := pwt.chromaLog2WeightDenom.toNat
  for ry in [:4] do
    for rx in [:4] do
      let b := grid.getD ((mbGy + ry) * gridW + (mbGx + rx)) {}
      let use0 := b.refIdxL0 ≥ 0 && b.refIdxL0.toNat < l0.size
      let use1 := b.refIdxL1 ≥ 0 && b.refIdxL1.toNat < l1.size
      if !use0 && !use1 then ok := false
      else
        nz := nz.set! (ry * 4 + rx) b.hasCoeff
        for dy in [:4] do
          for dx in [:4] do
            let x0 := mbX * 16 + rx * 4 + dx
            let y0 := mbY * 16 + ry * 4 + dy
            let sample :=
              if use0 && use1 then
                let p0 := l0[b.refIdxL0.toNat]!
                let p1 := l1[b.refIdxL1.toNat]!
                let s0 := LeanAV.H264InterDeblockDpb.h264LumaQpelHbd p0.pic.y
                  (4 * Int.ofNat x0 + b.mvL0.x) (4 * Int.ofNat y0 + b.mvL0.y)
                let s1 := LeanAV.H264InterDeblockDpb.h264LumaQpelHbd p1.pic.y
                  (4 * Int.ofNat x0 + b.mvL1.x) (4 * Int.ofNat y0 + b.mvL1.y)
                if hasPwt then
                  let defW : Int := (1 : Int) <<< lLog
                  let e0 := pwt.l0Weights.getD b.refIdxL0.toNat {}
                  let e1 := pwt.l1Weights.getD b.refIdxL1.toNat {}
                  let w0 := if e0.lumaWeightFlag then e0.lumaWeight.toInt else defW
                  let o0 := if e0.lumaWeightFlag then e0.lumaOffset.toInt else 0
                  let w1 := if e1.lumaWeightFlag then e1.lumaWeight.toInt else defW
                  let o1 := if e1.lumaWeightFlag then e1.lumaOffset.toInt else 0
                  LeanAV.H264InterDeblockDpb.weightedBiPredPixelHbd bitDepth s0 s1 w0 w1 o0 o1 lLog
                else if wbipred == 2 && !p0.isLongTerm && !p1.isLongTerm then
                  LeanAV.H264InterDeblockDpb.implicitWeightedBiPredPixelHbd bitDepth s0 s1 currPoc p0.poc p1.poc
                else LeanAV.H264InterDeblockDpb.biPredSampleHbd bitDepth s0 s1
              else if use0 then
                let p0 := l0[b.refIdxL0.toNat]!
                let s0 := LeanAV.H264InterDeblockDpb.h264LumaQpelHbd p0.pic.y
                  (4 * Int.ofNat x0 + b.mvL0.x) (4 * Int.ofNat y0 + b.mvL0.y)
                if hasPwt then
                  let defW : Int := (1 : Int) <<< lLog
                  let e0 := pwt.l0Weights.getD b.refIdxL0.toNat {}
                  let w0 := if e0.lumaWeightFlag then e0.lumaWeight.toInt else defW
                  let o0 := if e0.lumaWeightFlag then e0.lumaOffset.toInt else 0
                  LeanAV.H264InterDeblockDpb.weightedUniPredPixelHbd bitDepth s0 w0 o0 lLog
                else s0
              else
                let p1 := l1[b.refIdxL1.toNat]!
                let s1 := LeanAV.H264InterDeblockDpb.h264LumaQpelHbd p1.pic.y
                  (4 * Int.ofNat x0 + b.mvL1.x) (4 * Int.ofNat y0 + b.mvL1.y)
                if hasPwt then
                  let defW : Int := (1 : Int) <<< lLog
                  let e1 := pwt.l1Weights.getD b.refIdxL1.toNat {}
                  let w1 := if e1.lumaWeightFlag then e1.lumaWeight.toInt else defW
                  let o1 := if e1.lumaWeightFlag then e1.lumaOffset.toInt else 0
                  LeanAV.H264InterDeblockDpb.weightedUniPredPixelHbd bitDepth s1 w1 o1 lLog
                else s1
            y := y.set! ((ry * 4 + dy) * 16 + (rx * 4 + dx)) sample
        if chType != 0 then
          let (bw, bh) := if chType == 1 then (2, 2) else if chType == 2 then (2, 4) else (4, 4)
          for dy in [:bh] do
            for dx in [:bw] do
              let cx := Int.ofNat (if chType == 3 then mbX * 16 + rx * 4 + dx else mbX * 8 + rx * 2 + dx)
              let cy := Int.ofNat (if chType == 1 then mbY * 8 + ry * 2 + dy else mbY * 16 + ry * 4 + dy)
              let sampleC (planeOf : HbdStoredPic → HbdPlane) (cb : Bool) : Nat :=
                if use0 && use1 then
                  let p0 := l0[b.refIdxL0.toNat]!
                  let p1 := l1[b.refIdxL1.toNat]!
                  let s0 := LeanAV.H264InterDeblockDpb.h264ChromaMcSampleHbd chType (planeOf p0) cx cy b.mvL0.x b.mvL0.y
                  let s1 := LeanAV.H264InterDeblockDpb.h264ChromaMcSampleHbd chType (planeOf p1) cx cy b.mvL1.x b.mvL1.y
                  if hasPwt then
                    let defW : Int := (1 : Int) <<< cLog
                    let e0 := pwt.l0Weights.getD b.refIdxL0.toNat {}
                    let e1 := pwt.l1Weights.getD b.refIdxL1.toNat {}
                    let pick (e : LeanAV.H264Syntax.PredWeightEntry) : Int × Int :=
                      if e.chromaWeightFlag then
                        if cb then (e.cbWeight.toInt, e.cbOffset.toInt) else (e.crWeight.toInt, e.crOffset.toInt)
                      else (defW, 0)
                    let (w0, o0) := pick e0
                    let (w1, o1) := pick e1
                    LeanAV.H264InterDeblockDpb.weightedBiPredPixelHbd bitDepthC s0 s1 w0 w1 o0 o1 cLog
                  else if wbipred == 2 && !p0.isLongTerm && !p1.isLongTerm then
                    LeanAV.H264InterDeblockDpb.implicitWeightedBiPredPixelHbd bitDepthC s0 s1 currPoc p0.poc p1.poc
                  else LeanAV.H264InterDeblockDpb.biPredSampleHbd bitDepthC s0 s1
                else if use0 then
                  let p0 := l0[b.refIdxL0.toNat]!
                  let s0 := LeanAV.H264InterDeblockDpb.h264ChromaMcSampleHbd chType (planeOf p0) cx cy b.mvL0.x b.mvL0.y
                  if hasPwt then
                    let defW : Int := (1 : Int) <<< cLog
                    let e0 := pwt.l0Weights.getD b.refIdxL0.toNat {}
                    let (w0, o0) :=
                      if e0.chromaWeightFlag then
                        if cb then (e0.cbWeight.toInt, e0.cbOffset.toInt) else (e0.crWeight.toInt, e0.crOffset.toInt)
                      else (defW, 0)
                    LeanAV.H264InterDeblockDpb.weightedUniPredPixelHbd bitDepthC s0 w0 o0 cLog
                  else s0
                else
                  let p1 := l1[b.refIdxL1.toNat]!
                  let s1 := LeanAV.H264InterDeblockDpb.h264ChromaMcSampleHbd chType (planeOf p1) cx cy b.mvL1.x b.mvL1.y
                  if hasPwt then
                    let defW : Int := (1 : Int) <<< cLog
                    let e1 := pwt.l1Weights.getD b.refIdxL1.toNat {}
                    let (w1, o1) :=
                      if e1.chromaWeightFlag then
                        if cb then (e1.cbWeight.toInt, e1.cbOffset.toInt) else (e1.crWeight.toInt, e1.crOffset.toInt)
                      else (defW, 0)
                    LeanAV.H264InterDeblockDpb.weightedUniPredPixelHbd bitDepthC s1 w1 o1 cLog
                  else s1
              let off :=
                if chType == 1 then (ry * 2 + dy) * 8 + (rx * 2 + dx)
                else if chType == 2 then (ry * 4 + dy) * 8 + (rx * 2 + dx)
                else (ry * 4 + dy) * 16 + (rx * 4 + dx)
              u := u.set! off (sampleC (fun p => p.pic.u) true)
              v := v.set! off (sampleC (fun p => p.pic.v) false)
  if ok then some (y, u, v, nz) else none

private def hbdBlkBs (isMbEdge : Bool) (p q : HbdDecodedBlk4) : Nat :=
  if p.isIntra || q.isIntra then if isMbEdge then 4 else 3
  else if p.hasCoeff || q.hasCoeff then 2
  else
    let mvDiff (a b : LeanAV.H264InterDeblockDpb.MotionVec) := (a.x - b.x).natAbs ≥ 4 || (a.y - b.y).natAbs ≥ 4
    let same := p.refPicUidL0 == q.refPicUidL0 && p.refPicUidL1 == q.refPicUidL1
    let swapped := p.refPicUidL0 == q.refPicUidL1 && p.refPicUidL1 == q.refPicUidL0
    if same then
      if (p.refPicUidL0.isSome && mvDiff p.mvL0 q.mvL0) || (p.refPicUidL1.isSome && mvDiff p.mvL1 q.mvL1) then 1 else 0
    else if swapped then
      if (p.refPicUidL0.isSome && mvDiff p.mvL0 q.mvL1) || (p.refPicUidL1.isSome && mvDiff p.mvL1 q.mvL0) then 1 else 0
    else 1

structure HbdMbMeta where
  sliceId      : Int := -1
  qpPrimeY     : Nat := 0
  is8x8        : Bool := false
  isIpcm       : Bool := false
  bypass       : Bool := false
  disableIdc   : Nat := 1
  alphaOffDiv2 : Int := 0
  betaOffDiv2  : Int := 0
  cqpOff       : Int := 0
  secCqpOff    : Int := 0
  deriving Inhabited

private def deblockHbdPicture (y0 u0 v0 : HbdPlane) (grid : Array HbdDecodedBlk4)
    (mbMetaArr : Array HbdMbMeta) (mbsW mbsH chType _bitDepthY bitDepthC qpBdOffY : Nat)
    (bypassFlag : Bool) : HbdPlane × HbdPlane × HbdPlane := Id.run do
  let gridW := mbsW * 4
  let qpBdOffC := 6 * (bitDepthC - 8)
  let mut y := y0
  let mut u := u0
  let mut v := v0
  for mbY in [:mbsH] do
    for mbX in [:mbsW] do
      let q := mbMetaArr.getD (mbY * mbsW + mbX) {}
      if q.sliceId ≥ 0 && q.disableIdc != 1 && q.disableIdc < 3 then
        for kx in ([0, 4, 8, 12] : List Nat) do
          let isMb := kx == 0
          let pMeta := if isMb && mbX > 0 then mbMetaArr.getD (mbY * mbsW + mbX - 1) q else q
          let isSlice := isMb && (mbX == 0 || pMeta.sliceId != q.sliceId)
          if mbX * 16 + kx > 0 && !(q.disableIdc == 2 && isSlice) &&
             !(LeanAV.H264InterDeblockDpb.skipInternalEdge8x8 q.is8x8 kx) then
            let qPY : Int := Int.ofNat ((pMeta.qpPrimeY + q.qpPrimeY + 1) / 2) - Int.ofNat qpBdOffY
            let qpcCbP := qpcFromQpyHbd pMeta.qpPrimeY pMeta.cqpOff bitDepthC
            let qpcCbQ := qpcFromQpyHbd q.qpPrimeY q.cqpOff bitDepthC
            let qpcCrP := qpcFromQpyHbd pMeta.qpPrimeY pMeta.secCqpOff bitDepthC
            let qpcCrQ := qpcFromQpyHbd q.qpPrimeY q.secCqpOff bitDepthC
            let qPCb : Int := Int.ofNat ((qpcCbP + qpcCbQ + 1) / 2) - Int.ofNat qpBdOffC
            let qPCr : Int := Int.ofNat ((qpcCrP + qpcCrQ + 1) / 2) - Int.ofNat qpBdOffC
            let gxQ := mbX * 4 + kx / 4
            for blkRow in [:4] do
              let gy := mbY * 4 + blkRow
              let pBlk := grid.getD (gy * gridW + gxQ - 1) {}
              let qBlk := grid.getD (gy * gridW + gxQ) {}
              let bS := hbdBlkBs isMb pBlk qBlk
              if bS > 0 then
                let bypP := bypassFlag && pMeta.bypass && !pMeta.isIpcm && pMeta.qpPrimeY == 0
                let bypQ := bypassFlag && q.bypass && !q.isIpcm && q.qpPrimeY == 0
                y := LeanAV.H264InterDeblockDpb.deblockVertEdge4Hbd y (mbX * 16 + kx)
                  (mbY * 16 + blkRow * 4) 4 bS qPY q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
                if chType != 0 then
                  u := LeanAV.H264InterDeblockDpb.deblockChromaVertStepHbd chType u mbX mbY kx blkRow bS q.is8x8
                    qPCb q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
                  v := LeanAV.H264InterDeblockDpb.deblockChromaVertStepHbd chType v mbX mbY kx blkRow bS q.is8x8
                    qPCr q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
        for ky in ([0, 4, 8, 12] : List Nat) do
          let isMb := ky == 0
          let pMeta := if isMb && mbY > 0 then mbMetaArr.getD ((mbY - 1) * mbsW + mbX) q else q
          let isSlice := isMb && (mbY == 0 || pMeta.sliceId != q.sliceId)
          if mbY * 16 + ky > 0 && !(q.disableIdc == 2 && isSlice) &&
             !(LeanAV.H264InterDeblockDpb.skipInternalEdge8x8 q.is8x8 ky) then
            let qPY : Int := Int.ofNat ((pMeta.qpPrimeY + q.qpPrimeY + 1) / 2) - Int.ofNat qpBdOffY
            let qpcCbP := qpcFromQpyHbd pMeta.qpPrimeY pMeta.cqpOff bitDepthC
            let qpcCbQ := qpcFromQpyHbd q.qpPrimeY q.cqpOff bitDepthC
            let qpcCrP := qpcFromQpyHbd pMeta.qpPrimeY pMeta.secCqpOff bitDepthC
            let qpcCrQ := qpcFromQpyHbd q.qpPrimeY q.secCqpOff bitDepthC
            let qPCb : Int := Int.ofNat ((qpcCbP + qpcCbQ + 1) / 2) - Int.ofNat qpBdOffC
            let qPCr : Int := Int.ofNat ((qpcCrP + qpcCrQ + 1) / 2) - Int.ofNat qpBdOffC
            let gyQ := mbY * 4 + ky / 4
            for blkCol in [:4] do
              let gx := mbX * 4 + blkCol
              let pBlk := grid.getD ((gyQ - 1) * gridW + gx) {}
              let qBlk := grid.getD (gyQ * gridW + gx) {}
              let bS := hbdBlkBs isMb pBlk qBlk
              if bS > 0 then
                let bypP := bypassFlag && pMeta.bypass && !pMeta.isIpcm && pMeta.qpPrimeY == 0
                let bypQ := bypassFlag && q.bypass && !q.isIpcm && q.qpPrimeY == 0
                y := LeanAV.H264InterDeblockDpb.deblockHorizEdge4Hbd y (mbX * 16 + blkCol * 4)
                  (mbY * 16 + ky) 4 bS qPY q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
                if chType != 0 then
                  u := LeanAV.H264InterDeblockDpb.deblockChromaHorizStepHbd chType u mbX mbY ky blkCol bS q.is8x8
                    qPCb q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
                  v := LeanAV.H264InterDeblockDpb.deblockChromaHorizStepHbd chType v mbX mbY ky blkCol bS q.is8x8
                    qPCr q.alphaOffDiv2 q.betaOffDiv2 bypP bypQ
  return (y, u, v)

private def collectHbdEmitted (before after : LeanAV.H264InterDeblockDpb.H264Dpb)
    (stored : Array HbdStoredPic) (emitted0 : Array Nat)
    : Option (Array HbdPic × Array HbdStoredPic × Array Nat) := do
  let newLog := after.outputPocLog.length - before.outputPocLog.length
  let cands := stored.filter fun sp =>
    !emitted0.contains sp.uid && !(after.entries.any fun e => e.uid == sp.uid && e.neededForOut)
  let sorted := cands.qsort fun a b => if a.poc != b.poc then a.poc < b.poc else a.uid < b.uid
  let mut pics : Array HbdPic := #[]
  let mut emitted := emitted0
  for sp in sorted.toList.take newLog do
    let cropped ←
      if sp.cropWidth == sp.pic.width && sp.cropHeight == sp.pic.height && sp.cropLeft == 0 && sp.cropTop == 0 then
        some sp.pic
      else do
        let y ← cropPlaneHbd sp.pic.y sp.cropLeft sp.cropTop sp.cropWidth sp.cropHeight
        if sp.pic.chromaFormatIdc == 0 then some { sp.pic with width := sp.cropWidth, height := sp.cropHeight, y := y }
        else
          let (cuX, cuY) := LeanAV.H264Syntax.h264CropUnits sp.pic.chromaFormatIdc.toUInt8 sp.pic.separateColourPlane true
          let cx := if cuX == 0 then sp.cropLeft else sp.cropLeft / cuX
          let cy := if cuY == 0 then sp.cropTop else sp.cropTop / cuY
          let cw := if sp.pic.chromaFormatIdc == 3 then sp.cropWidth else sp.cropWidth / 2
          let ch := if sp.pic.chromaFormatIdc == 1 then sp.cropHeight / 2 else sp.cropHeight
          let u ← cropPlaneHbd sp.pic.u cx cy cw ch
          let v ← cropPlaneHbd sp.pic.v cx cy cw ch
          some { sp.pic with width := sp.cropWidth, height := sp.cropHeight, y := y, u := u, v := v }
    pics := pics.push cropped
    emitted := emitted.push sp.uid
  let live := stored.filter fun sp =>
    after.entries.any fun e => e.uid == sp.uid && (LeanAV.H264InterDeblockDpb.isUsedForRef e || e.neededForOut)
  some (pics, live, emitted)

private def decodeHbdAccessUnitNalusCore (st0 : HbdDecoderState) (nalus : Array ByteArray)
    (spsCheck? : Option (LeanAV.H264Syntax.H264SpsFull → LeanAV.H264Syntax.H264PpsFull → Bool) := none)
    : Option (HbdDecoderState × Array HbdPic) := do
  let mut st := st0
  let mut vcl : Array ByteArray := #[]
  for nal in nalus do
    if nal.data.size == 0 then none
    else
      let hdr := nal.data.getD 0 0
      if (hdr &&& 0x80) != 0 then none
      else
        let nalType := (hdr &&& 0x1F).toNat
        if nalType == 7 then
          let st' ← registerHbdSps st nal
          st := st'
        else if nalType == 8 then
          let st' ← registerHbdPps st nal
          st := st'
        else if nalType == 1 || nalType == 5 then
          vcl := vcl.push nal
        else if nalType == 2 || nalType == 3 || nalType == 4 || nalType == 19 then
          none
  if vcl.isEmpty then some (st, #[])
  else
    let first := vcl[0]!
    let rbsp0 := LeanAV.H264Entropy.stripNalEmulationBytes first
    let entSps := st.spsTable.map (fun o => o.map (·.ent))
    let entPps := st.ppsTable.map (fun o => o.map (·.ent))
    let (shEnt0, _) ← LeanAV.H264Entropy.parseSliceHeaderFull rbsp0 entSps entPps
    let pps0 ← st.ppsTable.getD shEnt0.ppsId none
    let sps0 ← st.spsTable.getD pps0.syn.spsId.toNat none
    let sps := sps0.syn
    if match spsCheck? with | some chk => !chk sps pps0.syn | none => false then none
    else
      let shSyn0 ← LeanAV.H264Syntax.parseH264SliceHeaderFull (ByteSlice.ofByteArray first) sps pps0.syn
      if shSyn0.redundantPicCnt != 0 || !sps.frameMbsOnlyFlag then none
      else
        let mbsW := sps.picWidthInMbsMinus1.toNat + 1
        let mbsH := sps.picHeightInMapUnitsMinus1.toNat + 1
        let total := mbsW * mbsH
        let gridW := mbsW * 4
        let gridH := mbsH * 4
        let isSep444 := sps.chromaFormatIdc == 3 && sps.separateColourPlaneFlag
        let chType := if isSep444 then 0 else sps.chromaFormatIdc.toNat
        let bitY := sps.bitDepthLumaMinus8.toNat + 8
        let bitC := sps.bitDepthChromaMinus8.toNat + 8
        let qpBdY := 6 * sps.bitDepthLumaMinus8.toNat
        let qpBdC := 6 * sps.bitDepthChromaMinus8.toNat
        if !st.dpbInit then
          st := { st with
            dpb := { maxRefFrames := sps.maxNumRefFrames.toNat
                     maxDpbCapacity := Nat.max 16 (Nat.max 1 sps.maxNumRefFrames.toNat + 2)
                     maxFrameNum := 1 <<< (sps.log2MaxFrameNumMinus4.toNat + 4) }
            dpbInit := true }
        let (currPoc, nextPoc) := hbdPicturePoc sps shSyn0 st.pocState
        let midY := h264MidSample bitY
        let midC := h264MidSample bitC
        let (cw, chh) :=
          if isSep444 then (mbsW * 16, mbsH * 16)
          else if chType == 0 then (0, 0)
          else if chType == 1 then (mbsW * 8, mbsH * 8)
          else if chType == 2 then (mbsW * 8, mbsH * 16)
          else (mbsW * 16, mbsH * 16)
        let mut pY := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc (mbsW * 16) (mbsH * 16) bitY midY
        let mut pU := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc cw chh bitC midC
        let mut pV := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc cw chh bitC midC
        let mut sepPlanes : Array HbdPlane := #[pY, pU, pV]
        let mut sepGrids : Array (Array HbdDecodedBlk4) :=
          #[Array.replicate (gridW * gridH) {}, Array.replicate (gridW * gridH) {}, Array.replicate (gridW * gridH) {}]
        let mut sepMetas : Array (Array HbdMbMeta) :=
          #[Array.replicate total {}, Array.replicate total {}, Array.replicate total {}]
        let mut sepCovered : Array Nat := #[0, 0, 0]
        let mut grid : Array HbdDecodedBlk4 := Array.replicate (gridW * gridH) {}
        let mut modes : Array Nat := Array.replicate (gridW * gridH) 2
        let mut sliceIds : Array Int := Array.replicate (gridW * gridH) (-1)
        let mut intraF : Array Bool := Array.replicate (gridW * gridH) false
        let mut mbSlice : Array Int := Array.replicate total (-1)
        let mut mbIntra : Array Bool := Array.replicate total false
        let mut mbMeta : Array HbdMbMeta := Array.replicate total {}
        let mut covered : Nat := 0
        for sIdx in [:vcl.size] do
          let sNal := vcl[sIdx]!
          let sRbsp := LeanAV.H264Entropy.stripNalEmulationBytes sNal
          let (shEnt, bitStart) ← LeanAV.H264Entropy.parseSliceHeaderFull sRbsp entSps entPps
          let ppsPair ← st.ppsTable.getD shEnt.ppsId none
          if ppsPair.syn.spsId != sps.spsId then none
          else if match spsCheck? with | some chk => !chk sps ppsPair.syn | none => false then none
          else
            let pps := ppsPair.syn
            let shSyn ← LeanAV.H264Syntax.parseH264SliceHeaderFull (ByteSlice.ofByteArray sNal) sps pps
            if shSyn.redundantPicCnt != 0 then none
            else if (shSyn.nalUnitType == 5) != (shSyn0.nalUnitType == 5) || shSyn.frameNum != shSyn0.frameNum then none
            else
              let mbs ←
                if pps.entropyCodingModeFlag then
                  LeanAV.H264Entropy.decodeSliceCabac sRbsp shEnt bitStart sps0.ent ppsPair.ent
                else
                  LeanAV.H264Entropy.decodeSliceCavlc sRbsp shEnt bitStart sps0.ent ppsPair.ent
              if shEnt.firstMbInSlice + mbs.size > total then none
              else
                let cPlane := if isSep444 then shSyn.colourPlaneId.toNat else 0
                if cPlane > 2 then none
                else
                  let planeBit := if cPlane == 0 then bitY else bitC
                  let planeMid := if cPlane == 0 then midY else midC
                  let planeQpBd := if cPlane == 0 then qpBdY else qpBdC
                  if isSep444 && shEnt.firstMbInSlice == 0 then
                    pY := sepPlanes.getD cPlane pY
                    grid := sepGrids.getD cPlane grid
                    mbMeta := sepMetas.getD cPlane mbMeta
                    covered := sepCovered.getD cPlane 0
                    modes := Array.replicate (gridW * gridH) 2
                    sliceIds := Array.replicate (gridW * gridH) (-1)
                    intraF := Array.replicate (gridW * gridH) false
                    mbSlice := Array.replicate total (-1)
                    mbIntra := Array.replicate total false
                  let mut curQp : Int := shSyn.sliceQpY.toInt + Int.ofNat planeQpBd
                  let numL0 := shSyn.numRefIdxL0ActiveMinus1.toNat + 1
                  let numL1 := shSyn.numRefIdxL1ActiveMinus1.toNat + 1
                  let currFn := shSyn.frameNum.toNat
                  let (l0Dpb, l1Dpb) :=
                    if shSyn.sliceKind == .P then
                      let init0 := LeanAV.H264InterDeblockDpb.buildRefPicListP0 st.dpb currFn (Nat.max numL0 (st.dpb.entries.length + 1))
                      let mod0 := if shSyn.refPicListModFlagL0 then
                        LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb init0 currFn numL0 (hbdModOps shSyn.refPicListModL0)
                        else init0.take numL0
                      (mod0, [])
                    else if shSyn.sliceKind == .B then
                      let pool := Nat.max (Nat.max numL0 numL1) (st.dpb.entries.length + 1)
                      let (i0, i1) := LeanAV.H264InterDeblockDpb.buildRefPicListsB st.dpb currFn currPoc pool pool
                      let m0 := if shSyn.refPicListModFlagL0 then
                        LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb i0 currFn numL0 (hbdModOps shSyn.refPicListModL0)
                        else i0.take numL0
                      let m1 := if shSyn.refPicListModFlagL1 then
                        LeanAV.H264InterDeblockDpb.applyRefPicListMod st.dpb i1 currFn numL1 (hbdModOps shSyn.refPicListModL1)
                        else i1.take numL1
                      (m0, m1)
                    else ([], [])
                  let l0Raw ← resolveHbdRefs l0Dpb st.stored
                  let l1Raw ← resolveHbdRefs l1Dpb st.stored
                  let l0 := if isSep444 && cPlane != 0 then
                    l0Raw.map fun sp => { sp with pic := { sp.pic with y := if cPlane == 1 then sp.pic.u else sp.pic.v } }
                    else l0Raw
                  let l1 := if isSep444 && cPlane != 0 then
                    l1Raw.map fun sp => { sp with pic := { sp.pic with y := if cPlane == 1 then sp.pic.u else sp.pic.v } }
                    else l1Raw
                  let sid := Int.ofNat sIdx
                  for i in [:mbs.size] do
                    let mbIdx := shEnt.firstMbInSlice + i
                    if mbSlice.getD mbIdx (-1) != -1 then none
                    else
                      let mb := mbs[i]!
                      let mbX := mbIdx % mbsW
                      let mbY := mbIdx / mbsW
                      let isIntra := mb.kind.isIntra
                      let qpMod := 52 + planeQpBd
                      if mb.kind == .iPcm then curQp := Int.ofNat planeQpBd
                      else if !mb.isSkip && (mb.kind == .i16x16 || mb.cbp != 0) then
                        curQp := (curQp + mb.mbQpDelta + Int.ofNat qpMod).emod qpMod
                      let qpNat := curQp.toNat
                      let bypass := sps.qpprimeYZeroTransformBypass && mb.kind != .iPcm && qpNat == 0
                      mbSlice := mbSlice.set! mbIdx sid
                      mbIntra := mbIntra.set! mbIdx isIntra
                      for ry in [:4] do
                        for rx in [:4] do
                          let gIdx := (mbY * 4 + ry) * gridW + (mbX * 4 + rx)
                          sliceIds := sliceIds.set! gIdx sid
                          intraF := intraF.set! gIdx isIntra
                      let w4 := scalingWeights4 pps isIntra cPlane
                      let w8 := scalingWeights8 pps sps.chromaFormatIdc.toNat isIntra cPlane
                      let leftCol := extractMbRect pY (if mbX == 0 then 0 else mbX * 16 - 1) (mbY * 16) 1 16 planeMid
                      let topRowLen := if mbY > 0 && mbX + 1 < mbsW && mbSlice.getD (mbIdx - mbsW + 1) (-1) == sid then 24 else 16
                      let topRow := extractMbRect pY (mbX * 16) (if mbY == 0 then 0 else mbY * 16 - 1) topRowLen 1 planeMid
                      let topLeft := hbdGet pY (if mbX == 0 then 0 else mbX * 16 - 1) (if mbY == 0 then 0 else mbY * 16 - 1) planeMid
                      let leftAv := mbX > 0 && mbSlice.getD (mbIdx - 1) (-1) == sid &&
                        (!pps.constrainedIntraPredFlag || !isIntra || mbIntra.getD (mbIdx - 1) false)
                      let topAv := mbY > 0 && mbSlice.getD (mbIdx - mbsW) (-1) == sid &&
                        (!pps.constrainedIntraPredFlag || !isIntra || mbIntra.getD (mbIdx - mbsW) false)
                      let topLeftAv := mbX > 0 && mbY > 0 && mbSlice.getD (mbIdx - mbsW - 1) (-1) == sid &&
                        (!pps.constrainedIntraPredFlag || !isIntra || mbIntra.getD (mbIdx - mbsW - 1) false)
                      let topRightMbAv := mbY > 0 && mbX + 1 < mbsW && mbSlice.getD (mbIdx - mbsW + 1) (-1) == sid &&
                        (!pps.constrainedIntraPredFlag || !isIntra || mbIntra.getD (mbIdx - mbsW + 1) false)
                      let topRowEff := if topRightMbAv then topRow else topRow.extract 0 16
                      let canvas := extractMbRect pY (mbX * 16) (mbY * 16) 16 16 planeMid
                      if mb.kind == .iPcm then
                        let (yPcm, uPcm, vPcm) ← unpackIpcmSamplesHbd mb.pcmBytes chType planeBit bitC
                        pY := writeMbRect pY (mbX * 16) (mbY * 16) 16 yPcm
                        if chType != 0 then
                          let cW := if chType == 3 then 16 else 8
                          pU := writeMbRect pU (if chType == 3 then mbX * 16 else mbX * 8) (if chType == 1 then mbY * 8 else mbY * 16) cW uPcm
                          pV := writeMbRect pV (if chType == 3 then mbX * 16 else mbX * 8) (if chType == 1 then mbY * 8 else mbY * 16) cW vPcm
                        for ry in [:4] do
                          for rx in [:4] do
                            let gIdx := (mbY * 4 + ry) * gridW + (mbX * 4 + rx)
                            modes := modes.set! gIdx 2
                            grid := grid.set! gIdx { sliceId := sid, isIntra := true, hasCoeff := true, qpPrimeY := 0 }
                      else if isIntra then
                        let (recY, modes', nz) ← reconstructLumaMbHbd canvas mb
                          leftCol topRowEff topLeft leftAv topAv topLeftAv 16 qpNat planeBit bypass w4 w8 modes sliceIds intraF
                          gridW (mbX * 4) (mbY * 4) sid pps.constrainedIntraPredFlag
                        modes := modes'
                        pY := writeMbRect pY (mbX * 16) (mbY * 16) 16 recY
                        if chType == 3 then
                          let cX := mbX * 16
                          let cY := mbY * 16
                          let leftU := extractMbRect pU (if mbX == 0 then 0 else cX - 1) cY 1 16 midC
                          let topU := extractMbRect pU cX (if mbY == 0 then 0 else cY - 1) (if topRightMbAv then 24 else 16) 1 midC
                          let tlU := hbdGet pU (if mbX == 0 then 0 else cX - 1) (if mbY == 0 then 0 else cY - 1) midC
                          let canvasU := extractMbRect pU cX cY 16 16 midC
                          let recU := reconstructChroma444CausalMbHbd canvasU mb leftU topU tlU leftAv topAv topLeftAv
                            (qpcFromQpyHbd qpNat pps.chromaQpIndexOffset.toInt bitC) bitC bypass
                            (scalingWeights4 pps true 1) (scalingWeights8 pps sps.chromaFormatIdc.toNat true 1)
                            modes gridW (mbX * 4) (mbY * 4) 0
                          pU := writeMbRect pU cX cY 16 recU
                          let leftV := extractMbRect pV (if mbX == 0 then 0 else cX - 1) cY 1 16 midC
                          let topV := extractMbRect pV cX (if mbY == 0 then 0 else cY - 1) (if topRightMbAv then 24 else 16) 1 midC
                          let tlV := hbdGet pV (if mbX == 0 then 0 else cX - 1) (if mbY == 0 then 0 else cY - 1) midC
                          let canvasV := extractMbRect pV cX cY 16 16 midC
                          let recV := reconstructChroma444CausalMbHbd canvasV mb leftV topV tlV leftAv topAv topLeftAv
                            (qpcFromQpyHbd qpNat pps.secondChromaQpIndexOffset.toInt bitC) bitC bypass
                            (scalingWeights4 pps true 2) (scalingWeights8 pps sps.chromaFormatIdc.toNat true 2)
                            modes gridW (mbX * 4) (mbY * 4) 1
                          pV := writeMbRect pV cX cY 16 recV
                        else if chType != 0 then
                          let (cW, cH) := if chType == 1 then (8, 8) else (8, 16)
                          let cX := mbX * 8
                          let cY := if chType == 1 then mbY * 8 else mbY * 16
                          let predChromaPlane (src : HbdPlane) : Array Nat :=
                            let leftC := extractMbRect src (if mbX == 0 then 0 else cX - 1) cY 1 cH midC
                            let topC := extractMbRect src cX (if mbY == 0 then 0 else cY - 1) cW 1 midC
                            let tlC := hbdGet src (if mbX == 0 then 0 else cX - 1) (if mbY == 0 then 0 else cY - 1) midC
                            if chType == 1 then predChroma420Hbd mb.chromaPredMode leftC topC tlC leftAv topAv bitC
                            else predChroma422 mb.chromaPredMode leftC topC tlC leftAv topAv bitC
                          let recU := reconstructChromaMbHbd (predChromaPlane pU) mb chType
                            (qpcFromQpyHbd qpNat pps.chromaQpIndexOffset.toInt bitC) bitC bypass
                            (scalingWeights4 pps true 1) (scalingWeights8 pps sps.chromaFormatIdc.toNat true 1) cW 0 true
                          pU := writeMbRect pU cX cY cW recU
                          let recV := reconstructChromaMbHbd (predChromaPlane pV) mb chType
                            (qpcFromQpyHbd qpNat pps.secondChromaQpIndexOffset.toInt bitC) bitC bypass
                            (scalingWeights4 pps true 2) (scalingWeights8 pps sps.chromaFormatIdc.toNat true 2) cW 1 true
                          pV := writeMbRect pV cX cY cW recV
                        for ry in [:4] do
                          for rx in [:4] do
                            let gIdx := (mbY * 4 + ry) * gridW + (mbX * 4 + rx)
                            let prev : HbdDecodedBlk4 := grid.getD gIdx {}
                            let nextBlk : HbdDecodedBlk4 := { prev with
                              sliceId := sid, isIntra := true,
                              hasCoeff := nz.getD (ry * 4 + rx) false, qpPrimeY := qpNat,
                              refIdxL0 := -1, refIdxL1 := -1, refPicUidL0 := none, refPicUidL1 := none }
                            grid := grid.set! gIdx nextBlk
                      else
                        let g' ← deriveHbdInterMotion mb shSyn.sliceKind grid sliceIds gridW gridH mbX mbY sid currPoc
                          shSyn.directSpatialMvPredFlag sps.direct8x8InferenceFlag l0 l1
                        grid := g'
                        let (py, pu, pv, nz) ← predictInterMbHbd grid gridW mbX mbY l0 l1 currPoc pps.weightedBipredIdc
                          shSyn.hasPredWeightTable shSyn.predWeightTable chType planeBit bitC
                        let recY := reconstructLumaResidualHbd py mb qpNat planeBit bypass w4 w8
                        let recU := reconstructChromaMbHbd pu mb chType
                          (qpcFromQpyHbd qpNat pps.chromaQpIndexOffset.toInt bitC) bitC bypass
                          (scalingWeights4 pps false 1) (scalingWeights8 pps sps.chromaFormatIdc.toNat false 1)
                          (if chType == 3 then 16 else 8) 0 false
                        let recV := reconstructChromaMbHbd pv mb chType
                          (qpcFromQpyHbd qpNat pps.secondChromaQpIndexOffset.toInt bitC) bitC bypass
                          (scalingWeights4 pps false 2) (scalingWeights8 pps sps.chromaFormatIdc.toNat false 2)
                          (if chType == 3 then 16 else 8) 1 false
                        pY := writeMbRect pY (mbX * 16) (mbY * 16) 16 recY
                        if chType != 0 then
                          let cW := if chType == 3 then 16 else 8
                          pU := writeMbRect pU (if chType == 3 then mbX * 16 else mbX * 8) (if chType == 1 then mbY * 8 else mbY * 16) cW recU
                          pV := writeMbRect pV (if chType == 3 then mbX * 16 else mbX * 8) (if chType == 1 then mbY * 8 else mbY * 16) cW recV
                        for ry in [:4] do
                          for rx in [:4] do
                            let gIdx := (mbY * 4 + ry) * gridW + (mbX * 4 + rx)
                            let prev : HbdDecodedBlk4 := grid.getD gIdx {}
                            let nextBlk : HbdDecodedBlk4 := { prev with
                              sliceId := sid, isIntra := false,
                              hasCoeff := nz.getD (ry * 4 + rx) false || prev.hasCoeff, qpPrimeY := qpNat }
                            grid := grid.set! gIdx nextBlk
                      mbMeta := mbMeta.set! mbIdx {
                        sliceId := sid, qpPrimeY := if mb.kind == .iPcm then 0 else qpNat, is8x8 := mb.transform8x8 != 0, isIpcm := mb.kind == .iPcm,
                        bypass := bypass, disableIdc := shSyn.disableDeblockingFilterIdc.toNat,
                        alphaOffDiv2 := shSyn.sliceAlphaC0OffsetDiv2.toInt, betaOffDiv2 := shSyn.sliceBetaOffsetDiv2.toInt,
                        cqpOff := pps.chromaQpIndexOffset.toInt, secCqpOff := pps.secondChromaQpIndexOffset.toInt }
                      covered := covered + 1
                  if isSep444 then
                    sepPlanes := sepPlanes.set! cPlane pY
                    sepGrids := sepGrids.set! cPlane grid
                    sepMetas := sepMetas.set! cPlane mbMeta
                    sepCovered := sepCovered.set! cPlane covered
        if isSep444 then
          if sepCovered.getD 0 0 != total || sepCovered.getD 1 0 != total || sepCovered.getD 2 0 != total then none
          else
            let dummy := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc 0 0 bitC midC
            let (dY, _, _) := deblockHbdPicture (sepPlanes.getD 0 pY) dummy dummy (sepGrids.getD 0 grid) (sepMetas.getD 0 mbMeta) mbsW mbsH 0 bitY bitC qpBdY sps.qpprimeYZeroTransformBypass
            let (dU, _, _) := deblockHbdPicture (sepPlanes.getD 1 pU) dummy dummy (sepGrids.getD 1 grid) (sepMetas.getD 1 mbMeta) mbsW mbsH 0 bitC bitC qpBdC sps.qpprimeYZeroTransformBypass
            let (dV, _, _) := deblockHbdPicture (sepPlanes.getD 2 pV) dummy dummy (sepGrids.getD 2 grid) (sepMetas.getD 2 mbMeta) mbsW mbsH 0 bitC bitC qpBdC sps.qpprimeYZeroTransformBypass
            let (cuX, cuY) := LeanAV.H264Syntax.h264CropUnits sps.chromaFormatIdc sps.separateColourPlaneFlag true
            let cropL := if sps.frameCroppingFlag then sps.frameCropLeftOffset.toNat * cuX else 0
            let cropT := if sps.frameCroppingFlag then sps.frameCropTopOffset.toNat * cuY else 0
            let pic : HbdPic := {
              width := mbsW * 16, height := mbsH * 16, chromaFormatIdc := 3,
              separateColourPlane := true, bitDepthY := bitY, bitDepthC := bitC,
              y := dY, u := dU, v := dV }
            let uid := st.dpb.nextUid
            let hasMmco5 := shSyn0.nalRefIdc != 0 && shSyn0.nalUnitType != 5 &&
              shSyn0.adaptiveRefPicMarkingModeFlag && shSyn0.mmcoOps.any (fun op => op.opcode == 5)
            let mmco ← hbdMmcoOps shSyn0.mmcoOps
            let storedPic : HbdStoredPic := {
              uid := uid, poc := if hasMmco5 then 0 else currPoc,
              isLongTerm := shSyn0.nalUnitType == 5 && shSyn0.longTermReferenceFlag,
              pic := pic, cropLeft := cropL, cropTop := cropT,
              cropWidth := sps.widthPx.toNat, cropHeight := sps.heightPx.toNat,
              gridW4 := gridW, gridH4 := gridH, colGrid := sepGrids.getD 0 grid }
            let before := st.dpb
            let after := LeanAV.H264InterDeblockDpb.insertDecodedPicture before
              (shSyn0.nalUnitType == 5) shSyn0.noOutputOfPriorPicsFlag shSyn0.longTermReferenceFlag
              (shSyn0.nalRefIdc != 0) shSyn0.frameNum.toNat currPoc shSyn0.adaptiveRefPicMarkingModeFlag mmco 0
            let (emittedPics, live, emitted') ← collectHbdEmitted before after (st.stored.push storedPic) st.emitted
            some ({ st with dpb := after, stored := live, emitted := emitted', pocState := nextPoc }, emittedPics)
        else if covered != total then none
        else
          let (dY, dU, dV) := deblockHbdPicture pY pU pV grid mbMeta mbsW mbsH chType bitY bitC qpBdY sps.qpprimeYZeroTransformBypass
          let (cuX, cuY) := LeanAV.H264Syntax.h264CropUnits sps.chromaFormatIdc sps.separateColourPlaneFlag true
          let cropL := if sps.frameCroppingFlag then sps.frameCropLeftOffset.toNat * cuX else 0
          let cropT := if sps.frameCroppingFlag then sps.frameCropTopOffset.toNat * cuY else 0
          let pic : HbdPic := {
            width := mbsW * 16, height := mbsH * 16, chromaFormatIdc := chType,
            separateColourPlane := sps.separateColourPlaneFlag, bitDepthY := bitY, bitDepthC := bitC,
            y := dY, u := dU, v := dV }
          let uid := st.dpb.nextUid
          let hasMmco5 := shSyn0.nalRefIdc != 0 && shSyn0.nalUnitType != 5 &&
            shSyn0.adaptiveRefPicMarkingModeFlag && shSyn0.mmcoOps.any (fun op => op.opcode == 5)
          let mmco ← hbdMmcoOps shSyn0.mmcoOps
          let storedPic : HbdStoredPic := {
            uid := uid, poc := if hasMmco5 then 0 else currPoc,
            isLongTerm := shSyn0.nalUnitType == 5 && shSyn0.longTermReferenceFlag,
            pic := pic, cropLeft := cropL, cropTop := cropT,
            cropWidth := sps.widthPx.toNat, cropHeight := sps.heightPx.toNat,
            gridW4 := gridW, gridH4 := gridH, colGrid := grid }
          let before := st.dpb
          let after := LeanAV.H264InterDeblockDpb.insertDecodedPicture before
            (shSyn0.nalUnitType == 5) shSyn0.noOutputOfPriorPicsFlag shSyn0.longTermReferenceFlag
            (shSyn0.nalRefIdc != 0) shSyn0.frameNum.toNat currPoc shSyn0.adaptiveRefPicMarkingModeFlag mmco 0
          let (emittedPics, live, emitted') ← collectHbdEmitted before after (st.stored.push storedPic) st.emitted
          some ({ st with dpb := after, stored := live, emitted := emitted', pocState := nextPoc }, emittedPics)

def decodeHbdAccessUnitNalusChecked (st0 : HbdDecoderState) (nalus : Array ByteArray)
    (spsCheck? : Option (LeanAV.H264Syntax.H264SpsFull → LeanAV.H264Syntax.H264PpsFull → Bool) := none)
    : Option (HbdDecoderState × Array HbdPic) :=
  decodeHbdAccessUnitNalusCore st0 nalus spsCheck?

private def decodeHbdAccessUnitNalus (st0 : HbdDecoderState) (nalus : Array ByteArray)
    : Option (HbdDecoderState × Array HbdPic) :=
  decodeHbdAccessUnitNalusCore st0 nalus none

def flushHbdDecoderPictures (st : HbdDecoderState) : Option (HbdDecoderState × Array HbdPic) := do
  if !st.dpbInit then some (st, #[])
  else
    let before := st.dpb
    let after := LeanAV.H264InterDeblockDpb.flushDpb before
    let (pics, live, emitted') ← collectHbdEmitted before after st.stored st.emitted
    some ({ st with dpb := after, stored := live, emitted := emitted' }, pics)

def decodeAnnexBToPicturesHbd (annexB : ByteArray) : Option (Array HbdPic) := do
  let nals := LeanAV.H264Entropy.splitAnnexB annexB
  if nals.isEmpty then none
  else
    let mut st : HbdDecoderState := {}
    let mut pics : Array HbdPic := #[]
    let mut cur : Array ByteArray := #[]
    for nal in nals do
      if nal.size == 0 then none
      else
        let hdr := nal.data.getD 0 0
        if (hdr &&& 0x80) != 0 then none
        else
          let nalType := (hdr &&& 0x1F).toNat
          if nalType == 7 || nalType == 8 || nalType == 9 then
            if !cur.isEmpty then
              let (st', emitted) ← decodeHbdAccessUnitNalus st cur
              st := st'
              for p in emitted do pics := pics.push p
              cur := #[]
            if nalType == 7 then
              let st' ← registerHbdSps st nal
              st := st'
            else if nalType == 8 then
              let st' ← registerHbdPps st nal
              st := st'
          else if nalType == 1 || nalType == 5 then
            let rbsp := LeanAV.H264Entropy.stripNalEmulationBytes nal
            let (sh, _) ← LeanAV.H264Entropy.parseSliceHeaderFull rbsp
              (st.spsTable.map (fun o => o.map (·.ent))) (st.ppsTable.map (fun o => o.map (·.ent)))
            if sh.firstMbInSlice == 0 && !cur.isEmpty then
              let (st', emitted) ← decodeHbdAccessUnitNalus st cur
              st := st'
              for p in emitted do pics := pics.push p
              cur := #[nal]
            else cur := cur.push nal
          else if nalType == 2 || nalType == 3 || nalType == 4 || nalType == 19 then none
    if !cur.isEmpty then
      let (st', emitted) ← decodeHbdAccessUnitNalus st cur
      st := st'
      for p in emitted do pics := pics.push p
    let (_, flushed) ← flushHbdDecoderPictures st
    for p in flushed do pics := pics.push p
    if pics.isEmpty then none else some pics

def decodeAnnexBToCanonicalRaw (annexB : ByteArray) : Option ByteArray := do
  let pics ← decodeAnnexBToPicturesHbd annexB
  packPicturesHbdCanonicalRaw pics

def decodeMp4ToCanonicalRaw (mp4 : ByteArray) : Option ByteArray := do
  let tracks ← LeanAV.Format.demuxNativeMp4ContainerTracks (ByteSlice.ofByteArray mp4)
  let video := (tracks.filter fun t => t.kind == .video)[0]?
  let v ← video
  let avccBody ← LeanAV.Format.extractMp4StsdAvcCBody v.stsdBox
  let avcc ← LeanAV.H264Syntax.parseAvcDecoderConfigRecord avccBody
  let nalLen := avcc.lengthSizeMinusOne.toNat + 1
  let mut st : HbdDecoderState := {}
  for s in avcc.spsNalus do
    let st' ← registerHbdSps st s
    st := st'
  for p in avcc.ppsNalus do
    let st' ← registerHbdPps st p
    st := st'
  let mut pics : Array HbdPic := #[]
  for sample in v.samples do
    let pkt := mp4.extract sample.fileOff (sample.fileOff + sample.byteLen)
    let nalus ← LeanAV.H264Syntax.splitAvccPacket pkt nalLen
    let (st', emitted) ← decodeHbdAccessUnitNalus st nalus
    st := st'
    for pic in emitted do pics := pics.push pic
  let (_, flushed) ← flushHbdDecoderPictures st
  for pic in flushed do pics := pics.push pic
  packPicturesHbdCanonicalRaw pics

def highTierProfileFor (chroma bitDepth : Nat) (lossless : Bool) : Option UInt8 :=
  if lossless || chroma == 3 || bitDepth == 12 then
    if bitDepth ≤ 12 then some 244 else none
  else if chroma == 2 then
    if bitDepth ≤ 10 then some 122 else none
  else if chroma ≤ 1 then
    if bitDepth == 8 then some 100
    else if bitDepth == 10 then some 110
    else none
  else none

private def bitWriterToBitArrayEnc (w : BitWriter) : Array UInt8 := Id.run do
  let totalBits := w.bytes.size * 8 + w.bitsUsed
  let bytes := w.bytes.push (if w.bitsUsed > 0 then (w.curByte <<< (8 - w.bitsUsed).toUInt8) else 0)
  let mut out : Array UInt8 := Array.mkEmpty totalBits
  for i in [:totalBits] do
    let b := bytes.data.getD (i / 8) 0
    out := out.push ((b >>> (7 - (i % 8)).toUInt8) &&& 1)
  return out

private def pred4x4DcEnc (recP : HbdPlane) (x0 y0 : Nat) (bitDepth : Nat) : Int := Id.run do
  let mid := h264MidSample bitDepth
  let leftAv := x0 > 0
  let topAv := y0 > 0
  if leftAv && topAv then
    let mut s : Int := 0
    for i in [:4] do
      s := s + (hbdGet recP (x0 - 1) (y0 + i) mid : Int) + (hbdGet recP (x0 + i) (y0 - 1) mid : Int)
    return (s + 4) / 8
  else if leftAv then
    let mut s : Int := 0
    for i in [:4] do
      s := s + (hbdGet recP (x0 - 1) (y0 + i) mid : Int)
    return (s + 2) / 4
  else if topAv then
    let mut s : Int := 0
    for i in [:4] do
      s := s + (hbdGet recP (x0 + i) (y0 - 1) mid : Int)
    return (s + 2) / 4
  else
    return (mid : Int)

private def encodeChromaPlane420Or422
    (srcP recP : HbdPlane) (mbX mbY chType qpC bitC : Nat) (bypass : Bool := false)
    : Array Int × Array (Array Int) × HbdPlane := Id.run do
  let midC := h264MidSample bitC
  let cW := 8
  let cH := if chType == 1 then 8 else 16
  let cX := mbX * 8
  let cY := if chType == 1 then mbY * 8 else mbY * 16
  let leftAv := mbX > 0
  let topAv := mbY > 0
  let leftC := extractMbRect recP (if mbX == 0 then 0 else cX - 1) cY 1 cH midC
  let topC := extractMbRect recP cX (if mbY == 0 then 0 else cY - 1) cW 1 midC
  let tlC := hbdGet recP (if mbX == 0 then 0 else cX - 1) (if mbY == 0 then 0 else cY - 1) midC
  let pred :=
    if chType == 1 then predChroma420Hbd 0 leftC topC tlC leftAv topAv bitC
    else predChroma422 0 leftC topC tlC leftAv topAv bitC
  let src := extractMbRect srcP cX cY cW cH midC
  let nBlks := if chType == 1 then 4 else 8
  let mut rawDc := Array.replicate nBlks (0 : Int)
  let mut acRasters : Array (Array Int) := Array.replicate nBlks (Array.replicate 16 0)
  for blk in [:nBlks] do
    let bx := (blk % 2) * 4
    let by_ := (blk / 2) * 4
    let res16 := Array.ofFn fun k : Fin 16 =>
      let idx := (by_ + k.val / 4) * 8 + (bx + k.val % 4)
      (src.getD idx midC : Int) - (pred.getD idx midC : Int)
    if bypass then
      rawDc := rawDc.set! blk (res16.getD 0 0)
      acRasters := acRasters.set! blk (res16.set! 0 0)
    else
      let coeff16 := forwardDct4x4 res16
      rawDc := rawDc.set! blk (coeff16.getD 0 0)
      let q16 := Array.ofFn fun k : Fin 16 =>
        if k.val == 0 then 0 else quantCoeff4x4 (coeff16.getD k.val 0) qpC (k.val / 4) (k.val % 4) true 16
      acRasters := acRasters.set! blk q16
  let dcScan :=
    if bypass then
      if chType == 1 then rawDc else chromaDcRasterToScan2x4 rawDc
    else if chType == 1 then chromaDcQuant420Hbd rawDc qpC true 16
    else chromaDcRasterToScan2x4 (chromaDcQuant422 rawDc qpC true 16)
  let acScans := Array.ofFn fun b : Fin nBlks => raster16ToAc15Scan (acRasters.getD b.val #[])
  let recSamples :=
    if bypass then src
    else if chType == 1 then
      reconstructChroma420Hbd pred dcScan acRasters qpC bitC
    else
      reconstructChroma422Hbd pred (chromaDcScan2x4ToRaster dcScan) acRasters qpC bitC
  return (dcScan, acScans, writeMbRect recP cX cY cW recSamples)

def encodeCanonicalRawToAnnexB (raw : ByteArray) (pixFmt : String) (w h : Nat) (lossless : Bool := false) : Option ByteArray := do
  if w == 0 || h == 0 then none else
  let pics ← unpackCanonicalRawPicturesHbd raw pixFmt w h
  if pics.isEmpty then none
  else
    let pic0 := pics[0]!
    let profile ← highTierProfileFor pic0.chromaFormatIdc pic0.bitDepthY lossless
    let mbsW := (w + 15) / 16
    let mbsH := (h + 15) / 16
    let chType := pic0.chromaFormatIdc
    let bitY := pic0.bitDepthY
    let bitC := pic0.bitDepthC
    let sps : LeanAV.H264Syntax.H264SpsFull := {
      profileIdc := profile
      constraintSet3Flag := profile == 244 && bitY > 8 && false
      levelIdc := 40
      chromaFormatIdc := chType.toUInt8
      bitDepthLumaMinus8 := (bitY - 8).toUInt8
      bitDepthChromaMinus8 := (bitC - 8).toUInt8
      qpprimeYZeroTransformBypass := lossless
      picWidthInMbsMinus1 := (mbsW - 1).toUInt16
      picHeightInMapUnitsMinus1 := (mbsH - 1).toUInt16
      frameMbsOnlyFlag := true
      direct8x8InferenceFlag := true
      frameCroppingFlag := mbsW * 16 != w || mbsH * 16 != h
      frameCropRightOffset := ((mbsW * 16 - w) / (if chType == 0 || chType == 3 then 1 else 2)).toUInt16
      frameCropBottomOffset := ((mbsH * 16 - h) / (if chType == 1 then 2 else 1)).toUInt16
      widthPx := w.toUInt32
      heightPx := h.toUInt32
      maxNumRefFrames := 0
    }
    let pps : LeanAV.H264Syntax.H264PpsFull := {
      entropyCodingModeFlag := false
      deblockingFilterControlPresentFlag := true
      transform8x8ModeFlag := false
    }
    let spsNal ← LeanAV.H264Syntax.serializeH264SpsFull sps
    let ppsNal ← LeanAV.H264Syntax.serializeH264PpsFull pps chType.toUInt8 (bitY - 8).toUInt8
    let spsEnt ← LeanAV.H264Entropy.parseSpsFull spsNal
    let spsArr := (Array.replicate 32 none).set! 0 (some spsEnt)
    let ppsEnt ← LeanAV.H264Entropy.parsePpsFull ppsNal spsArr
    let sliceQpY : Int := if lossless then -(6 * (bitY - 8 : Int)) else 16
    let qpDelta : Int := sliceQpY - 26
    let qpPrimeY : Nat := if lossless then 0 else (sliceQpY + 6 * (bitY - 8 : Int)).toNat
    let qpC : Nat := if lossless then 0 else qpcFromQpyHbd qpPrimeY 0 bitC
    let midY := h264MidSample bitY
    let midC := h264MidSample bitC
    let (cw, chh) :=
      if chType == 0 then (0, 0)
      else if chType == 1 then (mbsW * 8, mbsH * 8)
      else if chType == 2 then (mbsW * 8, mbsH * 16)
      else (mbsW * 16, mbsH * 16)
    let mut aus : Array ByteArray := #[]
    for frameIdx in [:pics.size] do
      let pic := pics[frameIdx]!
      let gridW4 := mbsW * 4
      let gridH4 := mbsH * 4
      let mut mbs : Array LeanAV.H264Entropy.MbSyntax := Array.mkEmpty (mbsW * mbsH)
      let mut recY := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc (mbsW * 16) (mbsH * 16) bitY midY
      let mut recU := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc cw chh bitC midC
      let mut recV := LeanAV.H264InterDeblockDpb.PlaneHbd.alloc cw chh bitC midC
      let mut modeGrid : Array Nat := Array.replicate (gridW4 * gridH4) 2
      let mut blkSlices : Array Int := Array.replicate (gridW4 * gridH4) (-1)
      let mut blkIntra : Array Bool := Array.replicate (gridW4 * gridH4) false
      for mbY in [:mbsH] do
        for mbX in [:mbsW] do
          for ry in [:4] do
            for rx in [:4] do
              let gIdx := (mbY * 4 + ry) * gridW4 + (mbX * 4 + rx)
              blkSlices := blkSlices.set! gIdx 0
              blkIntra := blkIntra.set! gIdx true
          let mut predSyntax : Array (Nat × Nat) := Array.mkEmpty 16
          let mut lumaScans : Array (Array Int) := Array.replicate 16 (Array.replicate 16 0)
          let mut c444Scans : Array (Array Int) := Array.replicate 32 (Array.replicate 16 0)
          let mut cbpLuma : Nat := 0
          for zIdx in [:16] do
            let (bx, by_) := zScan4BlkCoord zIdx
            let gx := mbX * 4 + bx / 4
            let gy := mbY * 4 + by_ / 4
            let mpm := mpmOf modeGrid blkSlices blkIntra gridW4 gx gy 0 false
            predSyntax := predSyntax.push (modeToSyntax mpm 2)
            modeGrid := modeGrid.set! (gy * gridW4 + gx) 2
            let x0 := mbX * 16 + bx
            let y0 := mbY * 16 + by_
            let dcPredY := pred4x4DcEnc recY x0 y0 bitY
            let predY16 := Array.replicate 16 dcPredY.toNat
            let src4Y := extractMbRect pic.y x0 y0 4 4 midY
            let res4Y := Array.ofFn fun k : Fin 16 => (src4Y.getD k.val midY : Int) - dcPredY
            let levels4Y := if lossless then res4Y else quantBlock4x4Hbd res4Y qpPrimeY true
            let scan4Y := LeanAV.H264Entropy.rasterToZigzag4x4 levels4Y
            lumaScans := lumaScans.set! zIdx scan4Y
            let mut subNz := anyNz scan4Y 16
            let rec4Y := if lossless then src4Y else reconstructBlock4x4Hbd predY16 levels4Y qpPrimeY bitY
            recY := writeMbRect recY x0 y0 4 rec4Y
            if chType == 3 then
              let dcPredU := pred4x4DcEnc recU x0 y0 bitC
              let src4U := extractMbRect pic.u x0 y0 4 4 midC
              let res4U := Array.ofFn fun k : Fin 16 => (src4U.getD k.val midC : Int) - dcPredU
              let levels4U := if lossless then res4U else quantBlock4x4Hbd res4U qpC true
              let scan4U := LeanAV.H264Entropy.rasterToZigzag4x4 levels4U
              c444Scans := c444Scans.set! zIdx scan4U
              if anyNz scan4U 16 then subNz := true
              recU := writeMbRect recU x0 y0 4 (if lossless then src4U else reconstructBlock4x4Hbd (Array.replicate 16 dcPredU.toNat) levels4U qpC bitC)
              let dcPredV := pred4x4DcEnc recV x0 y0 bitC
              let src4V := extractMbRect pic.v x0 y0 4 4 midC
              let res4V := Array.ofFn fun k : Fin 16 => (src4V.getD k.val midC : Int) - dcPredV
              let levels4V := if lossless then res4V else quantBlock4x4Hbd res4V qpC true
              let scan4V := LeanAV.H264Entropy.rasterToZigzag4x4 levels4V
              c444Scans := c444Scans.set! (16 + zIdx) scan4V
              if anyNz scan4V 16 then subNz := true
              recV := writeMbRect recV x0 y0 4 (if lossless then src4V else reconstructBlock4x4Hbd (Array.replicate 16 dcPredV.toNat) levels4V qpC bitC)
            if subNz then
              cbpLuma := cbpLuma ||| (1 <<< (zIdx / 4))
          let mut cbpChroma : Nat := 0
          let mut finalChromaDc : Array (Array Int) := #[Array.replicate 8 0, Array.replicate 8 0]
          let mut finalChromaAc : Array (Array Int) := Array.replicate 16 (Array.replicate 15 0)
          if chType == 1 || chType == 2 then
            let nBlks := if chType == 1 then 4 else 8
            let (uDc, uAc, recU') := encodeChromaPlane420Or422 pic.u recU mbX mbY chType qpC bitC lossless
            let (vDc, vAc, recV') := encodeChromaPlane420Or422 pic.v recV mbX mbY chType qpC bitC lossless
            recU := recU'
            recV := recV'
            let mut hasAc := false
            let mut cAc : Array (Array Int) := Array.mkEmpty (2 * nBlks)
            for b in [:nBlks] do
              let s := uAc.getD b (Array.replicate 15 0)
              if anyNz s 15 then hasAc := true
              cAc := cAc.push s
            for b in [:nBlks] do
              let s := vAc.getD b (Array.replicate 15 0)
              if anyNz s 15 then hasAc := true
              cAc := cAc.push s
            let hasDc := anyNz uDc nBlks || anyNz vDc nBlks
            cbpChroma := if hasAc then 2 else if hasDc then 1 else 0
            finalChromaDc := if cbpChroma == 0 then #[Array.replicate nBlks 0, Array.replicate nBlks 0] else #[uDc, vDc]
            finalChromaAc := if cbpChroma < 2 then Array.replicate (2 * nBlks) (Array.replicate 15 0) else cAc
          let mbSyn : LeanAV.H264Entropy.MbSyntax := {
            kind := .iNxN, intraIdx := 0, intraPred := predSyntax,
            chromaPredMode := 0, cbp := cbpLuma ||| (cbpChroma <<< 4),
            lumaAcOr4x4 := lumaScans,
            chromaDc := finalChromaDc, chromaAc := finalChromaAc,
            chroma444AcOr4x4 := c444Scans }
          mbs := mbs.push mbSyn
      let idrPicId := frameIdx % 2
      let wPre :=
        let w0 := LeanAV.H264Entropy.writeUNat BitWriter.empty 0 4
        let w1 := LeanAV.H264Entropy.writeUENat w0 idrPicId
        let w2 := LeanAV.H264Entropy.writeUNat w1 ((frameIdx * 2) % 16) 4
        let w3 := LeanAV.H264Entropy.writeU1Nat w2 0
        LeanAV.H264Entropy.writeU1Nat w3 0
      let wSuf := LeanAV.H264Entropy.writeUENat BitWriter.empty 1
      let sh : LeanAV.H264Entropy.SliceHeaderFull := {
        nalHdr := 0x65
        firstMbInSlice := 0
        sliceType := 7
        sliceTypeNos := 2
        ppsId := 0
        prefixBits := bitWriterToBitArrayEnc wPre
        cabacInitIdc := 0
        sliceQpDelta := qpDelta
        suffixBits := bitWriterToBitArrayEnc wSuf
        numRefL0 := 1
        numRefL1 := 1
        sliceQpY := sliceQpY
      }
      let slice ← LeanAV.H264Entropy.encodeSliceCavlc sh mbs spsEnt ppsEnt
      let nals := if frameIdx == 0 then #[spsNal, ppsNal, slice] else #[slice]
      aus := aus.push (LeanAV.H264Entropy.joinAnnexB nals)
    some (Id.run do
      let mut out := ByteArray.empty
      for au in aus do out := out ++ au
      return out)

def encodeCanonicalRawToMp4 (raw : ByteArray) (pixFmt : String) (w h : Nat) : Option ByteArray := do
  let annex ← encodeCanonicalRawToAnnexB raw pixFmt w h
  let pics ← unpackCanonicalRawPicturesHbd raw pixFmt w h
  let pic0 := pics[0]!
  let profile ← highTierProfileFor pic0.chromaFormatIdc pic0.bitDepthY false
  let nals := LeanAV.H264Entropy.splitAnnexB annex
  let spsNal := nals[0]!
  let ppsNal := nals[1]!
  let sps ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray spsNal)
  let avcc := LeanAV.H264Syntax.buildAvcDecoderConfigRecordFromSps { sps with profileIdc := profile } spsNal ppsNal
  let avccBody ← LeanAV.H264Syntax.serializeAvcDecoderConfigRecord avcc
  let mut samples : Array LeanAV.Format.SynthMp4Sample := #[]
  let mut i := 2
  while i < nals.size do
    let pkt ← LeanAV.H264Syntax.packAvccPacket #[nals[i]!] 4
    samples := samples.push { data := pkt, dur := 1, cttsOff := 0, isSync := true }
    i := i + 1
  let trk : LeanAV.Format.SynthMp4Track := {
    kind := .video, timescale := 25, width := w, height := h,
    stsdBox := LeanAV.Format.buildAvc1StsdBox w h avccBody, samples := samples }
  LeanAV.Format.muxSynthMp4Container #[trk]

def transcodeMp4HighTier (mp4 : ByteArray) : Option ByteArray := do
  let raw ← decodeMp4ToCanonicalRaw mp4
  let tracks ← LeanAV.Format.demuxNativeMp4ContainerTracks (ByteSlice.ofByteArray mp4)
  let v ← (tracks.filter fun t => t.kind == .video)[0]?
  let avccBody ← LeanAV.Format.extractMp4StsdAvcCBody v.stsdBox
  let avcc ← LeanAV.H264Syntax.parseAvcDecoderConfigRecord avccBody
  let sps ← LeanAV.H264Syntax.parseH264SpsFull (ByteSlice.ofByteArray (avcc.spsNalus[0]!))
  let pix :=
    if sps.chromaFormatIdc == 0 && sps.bitDepthLumaMinus8 == 0 then "gray"
    else if sps.chromaFormatIdc == 0 && sps.bitDepthLumaMinus8 == 2 then "gray10le"
    else if sps.chromaFormatIdc == 0 && sps.bitDepthLumaMinus8 == 4 then "gray12le"
    else if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 0 then "yuv420p"
    else if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 2 then "yuv420p10le"
    else if sps.chromaFormatIdc == 1 && sps.bitDepthLumaMinus8 == 4 then "yuv420p12le"
    else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 0 then "yuv422p"
    else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 2 then "yuv422p10le"
    else if sps.chromaFormatIdc == 2 && sps.bitDepthLumaMinus8 == 4 then "yuv422p12le"
    else if sps.chromaFormatIdc == 3 && sps.bitDepthLumaMinus8 == 0 then "yuv444p"
    else if sps.chromaFormatIdc == 3 && sps.bitDepthLumaMinus8 == 2 then "yuv444p10le"
    else "yuv444p12le"
  encodeCanonicalRawToMp4 raw pix sps.widthPx.toNat sps.heightPx.toNat

private def parseSignedInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (String.ofList cs).toNat?.map fun n => -(n : Int)
  | _ => s.toNat?.map fun n => (n : Int)

def runH264IntraProbeCli (args : List String) : IO UInt32 := do
  match args with
  | "pred4x4" :: modeStr :: la :: ta :: tra :: tla :: tlStr :: rest =>
    let mode := modeStr.toNat?.getD 2
    let left := (rest.take 4).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let top := ((rest.drop 4).take 4).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let tr := ((rest.drop 8).take 4).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let n : IntraNeighbors := {
      leftAvail := la == "1", topAvail := ta == "1", topRightAvail := tra == "1",
      topLeftAvail := tla == "1", left := left, top := top, topRight := tr,
      topLeft := (tlStr.toNat?.getD 128).toUInt8 }
    let out := pred4x4 mode n
    IO.println (String.intercalate "," (out.toList.map fun b => toString b.toNat))
    return 0
  | "pred8x8" :: modeStr :: la :: ta :: tra :: tla :: tlStr :: rest =>
    let mode := modeStr.toNat?.getD 2
    let left := (rest.take 8).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let top := ((rest.drop 8).take 8).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let tr := ((rest.drop 16).take 8).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let n : IntraNeighbors := {
      leftAvail := la == "1", topAvail := ta == "1", topRightAvail := tra == "1",
      topLeftAvail := tla == "1", left := left, top := top, topRight := tr,
      topLeft := (tlStr.toNat?.getD 128).toUInt8 }
    let out := pred8x8 mode n
    IO.println (String.intercalate "," (out.toList.map fun b => toString b.toNat))
    return 0
  | "pred16x16" :: modeStr :: la :: ta :: tlStr :: rest =>
    let mode := modeStr.toNat?.getD 2
    let left := (rest.take 16).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let top := ((rest.drop 16).take 16).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let out := pred16x16 mode left top (tlStr.toNat?.getD 128).toUInt8 (la == "1") (ta == "1")
    IO.println (String.intercalate "," (out.toList.map fun b => toString b.toNat))
    return 0
  | "pred-chroma" :: modeStr :: la :: ta :: tlStr :: rest =>
    let mode := modeStr.toNat?.getD 0
    let left := (rest.take 8).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let top := ((rest.drop 8).take 8).map (fun x => (x.toNat?.getD 128).toUInt8) |>.toArray
    let out := predChroma mode left top (tlStr.toNat?.getD 128).toUInt8 (la == "1") (ta == "1")
    IO.println (String.intercalate "," (out.toList.map fun b => toString b.toNat))
    return 0
  | "idct4x4" :: qpStr :: dcOverrideStr :: rest =>
    let qp := qpStr.toNat?.getD 26
    let dcO := if dcOverrideStr == "none" then none else parseSignedInt? dcOverrideStr
    let lv := (rest.take 16).map (fun x => (parseSignedInt? x).getD 0) |>.toArray
    let out := inverseResidual4x4 lv qp dcO
    IO.println (String.intercalate "," (out.toList.map toString))
    return 0
  | "idct8x8" :: qpStr :: rest =>
    let qp := qpStr.toNat?.getD 26
    let lv := (rest.take 64).map (fun x => (parseSignedInt? x).getD 0) |>.toArray
    let out := inverseResidual8x8 lv qp
    IO.println (String.intercalate "," (out.toList.map toString))
    return 0
  | "luma-dc" :: qpStr :: rest =>
    let qp := qpStr.toNat?.getD 26
    let dc := (rest.take 16).map (fun x => (parseSignedInt? x).getD 0) |>.toArray
    let out := lumaDcDequant dc qp
    IO.println (String.intercalate "," (out.toList.map toString))
    return 0
  | "chroma-dc" :: qpcStr :: c0 :: c1 :: c2 :: c3 :: _ =>
    let qpc := qpcStr.toNat?.getD 26
    let (d0, d1, d2, d3) := chromaDcDequant
      ((parseSignedInt? c0).getD 0) ((parseSignedInt? c1).getD 0)
      ((parseSignedInt? c2).getD 0) ((parseSignedInt? c3).getD 0) qpc
    IO.println s!"{d0},{d1},{d2},{d3}"
    return 0
  | "lossless-mb-roundtrip" :: partStr :: chromaModeStr :: rest =>
    let part := partStr.toNat?.getD 0
    let cMode := chromaModeStr.toNat?.getD 0
    let yArr := (List.range 256).map (fun i => ((i * 29 + (i / 16) * 13 + 17) % 256).toUInt8) |>.toArray
    let uArr := (List.range 64).map (fun i => ((120 + i * 7 + (i / 8) * 19) % 256).toUInt8) |>.toArray
    let vArr := (List.range 64).map (fun i => ((200 + i * 11 + (i / 8) * 5) % 256).toUInt8) |>.toArray
    let mb : H264Yuv420pMb := { y := yArr, u := uArr, v := vArr }
    let nbrs : H264IntraMbNeighbors := {
      leftAvail := true, topAvail := true, topRightAvail := true, topLeftAvail := true,
      leftY := (List.range 16).map (fun i => (40 + i * 9).toUInt8) |>.toArray,
      topY := (List.range 16).map (fun i => (60 + i * 7).toUInt8) |>.toArray,
      topRightY := (List.range 16).map (fun i => (90 + i * 5).toUInt8) |>.toArray,
      topLeftY := 55,
      leftU := (List.range 8).map (fun i => (110 + i * 6).toUInt8) |>.toArray,
      topU := (List.range 8).map (fun i => (115 + i * 5).toUInt8) |>.toArray,
      topLeftU := 112,
      leftV := (List.range 8).map (fun i => (140 + i * 4).toUInt8) |>.toArray,
      topV := (List.range 8).map (fun i => (145 + i * 3).toUInt8) |>.toArray,
      topLeftV := 142 }
    let modes := if rest.isEmpty then [0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6]
                 else rest.map (fun s => s.toNat?.getD 2)
    let coded := encodeLosslessIntraMb mb nbrs part modes cMode
    let dec := decodeLosslessIntraMb coded nbrs
    let ok := dec == mb
    IO.println s!"\{\"ok\":{ok},\"partition\":{part},\"blocks\":{coded.yBlocks.length}}"
    return if ok then 0 else 1
  | "lossy-mb" :: partStr :: qpStr :: offStr :: _ =>
    let part := partStr.toNat?.getD 0
    let qp := qpStr.toNat?.getD 12
    let off := (parseSignedInt? offStr).getD 0
    let yArr := (List.range 256).map (fun i => ((80 + (i % 16) * 5 + (i / 16) * 4) % 256).toUInt8) |>.toArray
    let uArr := (List.range 64).map (fun i => ((120 + (i % 8) * 3 + (i / 8) * 2) % 256).toUInt8) |>.toArray
    let vArr := (List.range 64).map (fun i => ((135 + (i % 8) * 2 + (i / 8) * 3) % 256).toUInt8) |>.toArray
    let mb : H264Yuv420pMb := { y := yArr, u := uArr, v := vArr }
    let nbrs : H264IntraMbNeighbors := {
      leftAvail := true, topAvail := true, topRightAvail := true, topLeftAvail := true,
      leftY := Array.replicate 16 80, topY := Array.replicate 16 80,
      topRightY := Array.replicate 16 140, topLeftY := 80,
      leftU := Array.replicate 8 120, topU := Array.replicate 8 120, topLeftU := 120,
      leftV := Array.replicate 8 135, topV := Array.replicate 8 135, topLeftV := 135 }
    let coded := encodeLossyIntraMb mb nbrs part qp off
    let recMb := reconstructLossyIntraMb coded nbrs
    let maxDiff (a b : Array UInt8) : Nat := Id.run do
      let mut m := 0
      for i in [:a.size] do
        let da := (a.getD i 0).toNat
        let db := (b.getD i 0).toNat
        let d := if da ≥ db then da - db else db - da
        if d > m then m := d
      return m
    let errY := maxDiff mb.y recMb.y
    let errU := maxDiff mb.u recMb.u
    let errV := maxDiff mb.v recMb.v
    let valid := H264Yuv420pMb.valid recMb
    IO.println s!"\{\"ok\":{valid},\"err_y\":{errY},\"err_u\":{errU},\"err_v\":{errV},\"qpc\":{qpcFromQpy (clampQp qp) off}}"
    return if valid then 0 else 1
  | "ipcm-roundtrip" :: rest =>
    let padBits := match rest with
      | p :: _ => (p.toNat?.getD 3) % 8
      | [] => 3
    let yArr := (List.range 256).map (fun i =>
      if i == 10 || i == 11 || i == 12 then (0 : UInt8)
      else if i == 13 then 1
      else if i == 20 || i == 21 then 0
      else if i == 22 then 3
      else ((i * 29 + (i / 16) * 13 + 7) % 256).toUInt8) |>.toArray
    let uArr := (List.range 64).map (fun i => ((110 + i * 7 + (i / 8) * 19) % 256).toUInt8) |>.toArray
    let vArr := (List.range 64).map (fun i => ((140 + i * 11 + (i / 8) * 5) % 256).toUInt8) |>.toArray
    let mb : H264Yuv420pMb := { y := yArr, u := uArr, v := vArr }
    let raw := encodeIpcmMb420 mb
    let decRaw := decodeIpcmMb420 raw
    let wPre := BitWriter.empty.writeBitsMSB 0 padBits
    let wPost := writeIpcmMb420Bits wPre mb
    let bs := wPost.toByteArray
    let rPre : BitReader := { slice := ByteSlice.ofByteArray bs, bitOffset := padBits }
    let decBits := readIpcmMb420Bits rPre
    let dummyNbrs : H264IntraMbNeighbors := default
    let decCoded := decodeLosslessIntraMb (encodeLosslessIntraMb mb dummyNbrs 3 [] 0) dummyNbrs
    let annexB := encodeAnnexBIpcmIdr16x16 mb
    let decAnnexB := decodeAnnexBIpcmIdr16x16 annexB
    let nzOk := (List.range 24).all (fun k => ipcmBlockNonZeroCount k == 16) && ipcmBlockNonZeroCount 24 == 0
    let bitsOk := match decBits with
      | some (mbB, rAfter) => mbB == mb && rAfter.bitOffset % 8 == 0 && wPost.bitsUsed == 0
      | none => false
    let ok := raw.size == 384 && decRaw == some mb && bitsOk && decCoded == mb && decAnnexB == some mb && nzOk
    let msg :=
      s!"\{\"ok\":{ok},\"pcm_bytes\":{raw.size},\"mb_type\":{ipcmMbTypeI}," ++
      s!"\"nz\":{ipcmBlockNonZeroCount 0},\"annexb_bytes\":{annexB.size}}"
    IO.println msg
    return if ok then 0 else 1
  | "ipcm-encode-annexb" :: inRawPath :: outH264Path :: _ =>
    let raw ← IO.FS.readBinFile inRawPath
    match decodeIpcmMb420 raw.data with
    | none => return 1
    | some mb =>
      IO.FS.writeBinFile outH264Path (encodeAnnexBIpcmIdr16x16 mb)
      return 0
  | "ipcm-decode-annexb" :: inH264Path :: outRawPath :: _ =>
    let h264 ← IO.FS.readBinFile inH264Path
    match decodeAnnexBIpcmIdr16x16 h264 with
    | none => return 1
    | some mb =>
      IO.FS.writeBinFile outRawPath { data := encodeIpcmMb420 mb }
      return 0
  | "decode-annexb-raw" :: inH264Path :: outRawPath :: _ =>
    let h264 ← IO.FS.readBinFile inH264Path
    match decodeAnnexBToCanonicalRaw h264 with
    | none => return 1
    | some raw =>
      IO.FS.writeBinFile outRawPath raw
      return 0
  | "decode-mp4-raw" :: inMp4Path :: outRawPath :: _ =>
    let mp4 ← IO.FS.readBinFile inMp4Path
    match decodeMp4ToCanonicalRaw mp4 with
    | none => return 1
    | some raw =>
      IO.FS.writeBinFile outRawPath raw
      return 0
  | "encode-annexb-raw" :: pixFmt :: widthStr :: heightStr :: inRawPath :: outH264Path :: _ =>
    let raw ← IO.FS.readBinFile inRawPath
    match encodeCanonicalRawToAnnexB raw pixFmt (widthStr.toNat?.getD 0) (heightStr.toNat?.getD 0) with
    | none => return 1
    | some h264 =>
      IO.FS.writeBinFile outH264Path h264
      return 0
  | "encode-mp4-raw" :: pixFmt :: widthStr :: heightStr :: inRawPath :: outMp4Path :: _ =>
    let raw ← IO.FS.readBinFile inRawPath
    match encodeCanonicalRawToMp4 raw pixFmt (widthStr.toNat?.getD 0) (heightStr.toNat?.getD 0) with
    | none => return 1
    | some mp4 =>
      IO.FS.writeBinFile outMp4Path mp4
      return 0
  | "transcode-mp4-hbd" :: inMp4Path :: outMp4Path :: _ =>
    let mp4 ← IO.FS.readBinFile inMp4Path
    match transcodeMp4HighTier mp4 with
    | none => return 1
    | some out =>
      IO.FS.writeBinFile outMp4Path out
      return 0
  | _ => return 2

end LeanAV.H264IntraTransform
