import LeanAV.Spec
import LeanAV.Core

namespace LeanAV.H264IntraTransform

open LeanAV.Spec
open LeanAV.Core

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

def encodeLosslessIntraMb (mb : H264Yuv420pMb) (nbrs : H264IntraMbNeighbors)
    (partitionKind : Nat) (lumaModes : List Nat) (chromaMode : Nat) : LosslessIntraMbCoded :=
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
  | _ => return 2

end LeanAV.H264IntraTransform
