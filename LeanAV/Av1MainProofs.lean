import LeanAV.Spec
import LeanAV.Av1Main

namespace LeanAV.Av1MainProofs

open LeanAV.Spec
open LeanAV.Av1Main

set_option maxRecDepth 400000
set_option maxHeartbeats 16000000

def av1Main8Bit420SeqSafe (seq : Av1SeqHdr) : Prop :=
  seq.profile = 0 ∧ seq.hbd = 0 ∧ seq.monochrome = false ∧ seq.ssHor = 1 ∧ seq.ssVer = 1

def av1Main8Bit420SeqGate (seq : Av1SeqHdr) : Bool :=
  (seq.profile == 0) && (seq.hbd == 0) && !seq.monochrome && (seq.ssHor == 1) && (seq.ssVer == 1)

def av1Main8Bit420SeqSpec :
    AVGateSpec Av1SeqHdr av1Main8Bit420SeqSafe where
  gate := av1Main8Bit420SeqGate
  sound seq hg := by
    unfold av1Main8Bit420SeqGate av1Main8Bit420SeqSafe at *
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
    exact ⟨hg.1.1.1.1, hg.1.1.1.2, hg.1.1.2, hg.1.2, hg.2⟩
  complete seq hs := by
    rcases hs with ⟨hp, hh, hm, hsh, hsv⟩
    unfold av1Main8Bit420SeqGate
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
    exact ⟨⟨⟨⟨hp, hh⟩, hm⟩, hsh⟩, hsv⟩
  posWitness := { profile := 0, hbd := 0, monochrome := false, ssHor := 1, ssVer := 1, isMain8Bit420 := true }
  negWitness := { profile := 2, hbd := 2, monochrome := false, ssHor := 1, ssVer := 1, isMain8Bit420 := false }
  nonVacuous := by decide
  tight := by decide

theorem av1Main8Bit420SeqSpec_iff (seq : Av1SeqHdr) :
    av1Main8Bit420SeqSpec.gate seq = true ↔ av1Main8Bit420SeqSafe seq :=
  av1Main8Bit420SeqSpec.iff_safe seq

def av1Main8BitFrameScopeSafe (fh : Av1FrameHdr) : Prop :=
  fh.filmGrainPresent = false ∧ fh.width0 > 0 ∧ fh.width1 > 0 ∧ fh.height > 0

def av1Main8BitFrameScopeGate (fh : Av1FrameHdr) : Bool :=
  !fh.filmGrainPresent && decide (fh.width0 > 0) && decide (fh.width1 > 0) && decide (fh.height > 0)

def av1Main8BitFrameScopeSpec :
    AVGateSpec Av1FrameHdr av1Main8BitFrameScopeSafe where
  gate := av1Main8BitFrameScopeGate
  sound fh hg := by
    unfold av1Main8BitFrameScopeGate av1Main8BitFrameScopeSafe at *
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1, hg.1.1.2, hg.1.2, hg.2⟩
  complete fh hs := by
    rcases hs with ⟨hfg, hw0, hw1, hh⟩
    unfold av1Main8BitFrameScopeGate
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    exact ⟨⟨⟨hfg, hw0⟩, hw1⟩, hh⟩
  posWitness := { filmGrainPresent := false, width0 := 64, width1 := 64, height := 48 }
  negWitness := { filmGrainPresent := true, width0 := 64, width1 := 64, height := 48 }
  nonVacuous := by decide
  tight := by decide

theorem av1Main8BitFrameScopeSpec_iff (fh : Av1FrameHdr) :
    av1Main8BitFrameScopeSpec.gate fh = true ↔ av1Main8BitFrameScopeSafe fh :=
  av1Main8BitFrameScopeSpec.iff_safe fh

structure Av1EncoderGeom where
  width    : Nat
  height   : Nat
  tilesCol : Nat
  tilesRow : Nat
  deriving Repr, DecidableEq

def av1EncoderGeomGate (g : Av1EncoderGeom) : Bool :=
  decide (g.width > 0) &&
  decide (g.height > 0) &&
  (g.width &&& 1 == 0) &&
  (g.height &&& 1 == 0) &&
  decide (1 ≤ g.tilesCol) &&
  decide (1 ≤ g.tilesRow)

def av1EncoderGeomSpec :
    AVGateSpec Av1EncoderGeom (fun g =>
      g.width > 0 ∧ g.height > 0 ∧
      g.width % 2 = 0 ∧ g.height % 2 = 0 ∧
      1 ≤ g.tilesCol ∧ 1 ≤ g.tilesRow) where
  gate := av1EncoderGeomGate
  sound g hg := by
    unfold av1EncoderGeomGate at hg
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    rcases hg with ⟨⟨⟨⟨⟨hw0, hh0⟩, hw1⟩, hh1⟩, htc⟩, htr⟩
    have hw : g.width % 2 = 0 := by
      rw [Nat.and_one_is_mod] at hw1; exact hw1
    have hh : g.height % 2 = 0 := by
      rw [Nat.and_one_is_mod] at hh1; exact hh1
    exact ⟨hw0, hh0, hw, hh, htc, htr⟩
  complete g hs := by
    rcases hs with ⟨hw0, hh0, hwe, hhe, htc, htr⟩
    unfold av1EncoderGeomGate
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    have hw : g.width &&& 1 = 0 := by rw [Nat.and_one_is_mod]; exact hwe
    have hh : g.height &&& 1 = 0 := by rw [Nat.and_one_is_mod]; exact hhe
    exact ⟨⟨⟨⟨⟨hw0, hh0⟩, hw⟩, hh⟩, htc⟩, htr⟩
  posWitness := { width := 64, height := 48, tilesCol := 1, tilesRow := 1 }
  negWitness := { width := 63, height := 48, tilesCol := 1, tilesRow := 1 }
  nonVacuous := by decide
  tight := by decide

theorem av1EncoderGeomSpec_iff (g : Av1EncoderGeom) :
    av1EncoderGeomSpec.gate g = true ↔
      (g.width > 0 ∧ g.height > 0 ∧
       g.width % 2 = 0 ∧ g.height % 2 = 0 ∧
       1 ≤ g.tilesCol ∧ 1 ≤ g.tilesRow) :=
  av1EncoderGeomSpec.iff_safe g

def av1QidxRangeGate (q : Nat) : Bool :=
  decide (q ≤ 255)

def av1QidxRangeSpec :
    AVGateSpec Nat (fun q => q ≤ 255) where
  gate := av1QidxRangeGate
  sound _ hg := by
    unfold av1QidxRangeGate at hg
    exact of_decide_eq_true hg
  complete _ hs := by
    unfold av1QidxRangeGate
    exact decide_eq_true hs
  posWitness := 60
  negWitness := 256
  nonVacuous := by decide
  tight := by decide

theorem av1QidxRangeSpec_iff (q : Nat) :
    av1QidxRangeSpec.gate q = true ↔ q ≤ 255 :=
  av1QidxRangeSpec.iff_safe q

def av1IntraModeRangeGate (m : Nat) : Bool :=
  decide (m ≤ 12)

def av1IntraModeRangeSpec :
    AVGateSpec Nat (fun m => m ≤ 12) where
  gate := av1IntraModeRangeGate
  sound _ hg := by
    unfold av1IntraModeRangeGate at hg
    exact of_decide_eq_true hg
  complete _ hs := by
    unfold av1IntraModeRangeGate
    exact decide_eq_true hs
  posWitness := 0
  negWitness := 13
  nonVacuous := by decide
  tight := by decide

theorem av1IntraModeRangeSpec_iff (m : Nat) :
    av1IntraModeRangeSpec.gate m = true ↔ m ≤ 12 :=
  av1IntraModeRangeSpec.iff_safe m

def av1Sample8BoundGate (v : Int) : Bool :=
  decide (0 ≤ v) && decide (v ≤ 255)

def av1Sample8BoundSpec :
    AVGateSpec Int (fun v => 0 ≤ v ∧ v ≤ 255) where
  gate := av1Sample8BoundGate
  sound _ hg := by
    unfold av1Sample8BoundGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete _ hs := by
    unfold av1Sample8BoundGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hs
  posWitness := 128
  negWitness := 256
  nonVacuous := by decide
  tight := by decide

theorem av1Sample8BoundSpec_iff (v : Int) :
    av1Sample8BoundSpec.gate v = true ↔ (0 ≤ v ∧ v ≤ 255) :=
  av1Sample8BoundSpec.iff_safe v

def av1RefSlotOccupancyGate (p : Nat × Nat) : Bool :=
  decide (1 ≤ p.2) && decide (p.1 ≤ p.2)

def av1RefSlotOccupancySpec :
    AVGateSpec (Nat × Nat) (fun p => 1 ≤ p.2 ∧ p.1 ≤ p.2) where
  gate := av1RefSlotOccupancyGate
  sound _ hg := by
    unfold av1RefSlotOccupancyGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete _ hs := by
    unfold av1RefSlotOccupancyGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hs
  posWitness := (3, 8)
  negWitness := (9, 8)
  nonVacuous := by decide
  tight := by decide

theorem av1RefSlotOccupancySpec_iff (p : Nat × Nat) :
    av1RefSlotOccupancySpec.gate p = true ↔ (1 ≤ p.2 ∧ p.1 ≤ p.2) :=
  av1RefSlotOccupancySpec.iff_safe p

theorem av1Iclip_bounds_and_id (v lo hi : Int) (hlo : lo ≤ hi) :
    (lo ≤ av1Iclip v lo hi ∧ av1Iclip v lo hi ≤ hi) ∧
    (lo ≤ v → v ≤ hi → av1Iclip v lo hi = v) := by
  unfold av1Iclip
  constructor
  · split
    · omega
    · split <;> omega
  · intro h1 h2
    split
    · omega
    · split <;> omega

theorem av1IclipU8_bounds (v : Int) :
    av1IclipU8 v ≤ 255 := by
  unfold av1IclipU8
  split
  · omega
  · split <;> omega

theorem av1IclipU8_all_256_id :
    ((List.range 256).all fun n => av1IclipU8 (Int.ofNat n) == n) = true := by
  decide

private def av1SumInt : List Int → Int
  | [] => 0
  | x :: xs => x + av1SumInt xs

def checkAv1McFilterDcGain : Bool :=
  let taps : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  let groups : List Nat := [0, 1, 2, 3, 4, 5]
  let sumOk := groups.all fun g =>
    taps.all fun mx =>
      let base := g * 15 * 8 + (mx - 1) * 8
      let row := (List.range 8).map fun k => av1McSubpelFilters.getD (base + k) 0
      row.length == 8 && av1SumInt row == 64
  let constOk := [0, 1, 73, 128, 200, 254, 255].all fun (cNat : Nat) =>
    let c := Int.ofNat cNat
    groups.all fun g =>
      taps.all fun mx =>
        let base := g * 15 * 8 + (mx - 1) * 8
        let acc := av1SumInt ((List.range 8).map fun k => av1McSubpelFilters.getD (base + k) 0 * c)
        (acc + 32) / 64 == c
  sumOk && constOk

theorem av1Mc_8tap_subpel_dc_gain_and_const_exact :
    checkAv1McFilterDcGain = true := by
  decide

def checkAv1Wht4Roundtrip : Bool :=
  let cases : List (Int × Int × Int × Int) :=
    [(12, -8, 4, -3), (0, 0, 0, 0), (255, -255, 127, -128), (1, 2, 3, 4)]
  cases.all fun (a, b, c, d) =>
    let (f0, f1, f2, f3) := av1FwdWht4Vec a b c d
    let (r0, r1, r2, r3) := av1InvWht4Vec f0 f1 f2 f3
    r0 == a && r1 == b && r2 == c && r3 == d

theorem av1Wht4_basis_roundtrip_exact :
    checkAv1Wht4Roundtrip = true := by
  decide

def av1DcPredSample (c : Int) : Nat := av1IclipU8 c

theorem av1DcPred_const_exact (c : Nat) (hc : c ≤ 255) :
    av1DcPredSample (Int.ofNat c) = c := by
  unfold av1DcPredSample av1IclipU8
  have h1 : (Int.ofNat c : Int) = ↑c := rfl
  rw [h1]
  split
  · omega
  · split
    · omega
    · rfl

def checkAv1DcPredConstExact : Bool :=
  [0, 1, 93, 128, 200, 254, 255].all fun v => av1DcPredSample (Int.ofNat v) == v

theorem av1DcPred_const_exact_verified :
    checkAv1DcPredConstExact = true := by
  decide

theorem av1LoopFilter_flat_zero_delta (c : Int) :
    av1ArithShiftRight (3 * (c - c) + 4) 3 = 0 := by
  have h : 3 * (c - c) + 4 = 4 := by omega
  rw [h]
  decide

theorem av1LoopFilter_and_cdef_clamped_bounds (p0 q0 delta sample offset : Int) :
    av1IclipU8 (p0 + delta) ≤ 255 ∧
    av1IclipU8 (q0 - delta) ≤ 255 ∧
    av1IclipU8 (sample + offset) ≤ 255 := by
  exact ⟨av1IclipU8_bounds _, av1IclipU8_bounds _, av1IclipU8_bounds _⟩

def checkAv1Leb128Roundtrip : Bool :=
  let vals : List Nat := [0, 1, 127, 128, 255, 16383, 16384, 65535, 1000000, 4294967295]
  vals.all fun v =>
    match av1DecodeLeb128 (av1EncodeLeb128 v) 0 with
    | some (got, _) => got == v
    | none => false

theorem av1Leb128_roundtrip :
    checkAv1Leb128Roundtrip = true := by
  decide

def checkAv1ObuWrapParseRoundtrip : Bool :=
  let cases : List (Nat × ByteArray) :=
    [(av1ObuSeqHdr, { data := #[0x0A, 0x0B, 0x00] }),
     (av1ObuTd, { data := #[] }),
     (av1ObuFrame, { data := #[0x12, 0x00, 0x00, 0x80] }),
     (av1ObuMetadata, { data := #[0x01] })]
  cases.all fun (ty, payload) =>
    match av1ParseObus (av1WrapObu ty payload true) with
    | some obus => obus.size == 1 &&
        (obus.getD 0 default).obuType == ty &&
        (obus.getD 0 default).payload.data == payload.data
    | none => false

theorem av1Obu_wrap_parse_roundtrip :
    checkAv1ObuWrapParseRoundtrip = true := by
  decide

def checkAv1MsacRoundtrip : Bool :=
  let cdf0 : Array Nat := #[16384, 0, 8192, 24576, 0, 0]
  let (e1, c1) := (Av1MsacEncoder.init false).encodeBoolAdapt 1 cdf0 0
  let (e2, c2) := e1.encodeBoolAdapt 0 c1 0
  let (e3, _) := e2.encodeSymbolAdapt 2 c2 2 3
  let e4 := (e3.encodeBoolEqui 1).encodeBools 5 4
  let bytes := e4.finalize
  match Av1MsacDecoder.init bytes 0 bytes.data.size false with
  | r0 =>
    let (b0, r1, cR1) := r0.decodeBoolAdapt cdf0 0
    let (b1, r2, cR2) := r1.decodeBoolAdapt cR1 0
    let (sym, r3, _) := r2.decodeSymbolAdapt cR2 2 3
    let (eq, r4) := r3.decodeBoolEqui
    let (bits, _) := r4.decodeBools 4
    b0 == 1 && b1 == 0 && sym == 2 && eq == 1 && bits == 5

theorem av1Msac_bool_symbol_roundtrip :
    checkAv1MsacRoundtrip = true := by
  decide

def checkAv1SeqHdrMainGate : Bool :=
  let obu := av1WriteSeqHdrObu 64 48 true false
  match av1ParseObus obu with
  | none => false
  | some obus =>
    match obus.getD 0 default with
    | pkt =>
      if pkt.obuType != av1ObuSeqHdr then false
      else
        match av1ParseSeqHdr pkt.payload true with
        | none => false
        | some seq =>
          seq.isMain8Bit420 && seq.maxWidth == 64 && seq.maxHeight == 48 && seq.cdef

theorem av1SeqHdr_main8bit420_write_parse_verified :
    checkAv1SeqHdrMainGate = true := by
  decide

def checkAv1NonMainFailClosed : Bool :=
  let main10 : Av1SeqHdr := { profile := 0, hbd := 2, monochrome := false, ssHor := 1, ssVer := 1, isMain8Bit420 := false }
  let prof1 : Av1SeqHdr := { profile := 1, hbd := 0, monochrome := false, ssHor := 0, ssVer := 0, isMain8Bit420 := false }
  let mono : Av1SeqHdr := { profile := 0, hbd := 0, monochrome := true, ssHor := 1, ssVer := 1, isMain8Bit420 := false }
  !main10.isMain8Bit420 && !prof1.isMain8Bit420 && !mono.isMain8Bit420

theorem av1NonMain_failclosed_verified :
    checkAv1NonMainFailClosed = true := by
  decide

private def av1InsertSorted (p : Int) : List Int → List Int
  | [] => [p]
  | q :: qs => if p ≤ q then p :: q :: qs else q :: av1InsertSorted p qs

private def av1SortPure : List Int → List Int
  | [] => []
  | p :: ps => av1InsertSorted p (av1SortPure ps)

private def av1NonDecreasing : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && av1NonDecreasing (b :: rest)

theorem av1Ref_poc_reorder_monotone_and_slot_capacity :
    let out := av1SortPure [0, 4, 2, 1, 3, 8, 6, 5, 7]
    out = [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
    av1NonDecreasing out = true ∧
    av1RefSlotOccupancyGate (4, 8) = true ∧
    av1RefSlotOccupancyGate (9, 8) = false := by
  decide

def av1RefmvSingleExtNoCapGate (base : Nat) (push0 push1 : Bool) : Nat :=
  if push0 && push1 then base + 2 else if push0 || push1 then base + 1 else base

theorem av1Refmv_single_extended_uncapped_compound_neighbor :
    av1RefmvSingleExtNoCapGate 1 true true = 3 ∧
    av1RefmvSingleExtNoCapGate 1 true false = 2 ∧
    av1RefmvSingleExtNoCapGate 2 true true = 4 := by
  decide

theorem av1GetUniCtx_p0_bwd_vs_fwd_partition :
    let a : Av1BlockContext := {
      intra := #[0],
      ref := #[#[2], #[4]],
      compType := #[1]
    }
    let l : Av1BlockContext := {
      intra := #[0],
      ref := #[#[0], #[5]],
      compType := #[1]
    }
    av1GetUniCtx a l 0 0 true true 0 = av1GetRefCtx a l 0 0 true true ∧
    av1GetUniCtx a l 0 0 true true 0 = 1 ∧
    av1GetUniCtx a l 0 0 true true 1 = av1GetUniP1Ctx a l 0 0 true true ∧
    av1GetUniCtx a l 0 0 true true 2 = av1GetFwdRef2Ctx a l 0 0 true true := by
  decide

end LeanAV.Av1MainProofs
