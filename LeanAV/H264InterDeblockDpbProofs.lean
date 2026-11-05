import LeanAV.Spec
import LeanAV.Core
import LeanAV.Video
import LeanAV.Encoder
import LeanAV.H264InterDeblockDpb

namespace LeanAV.H264InterDeblockDpbProofs

open LeanAV.Spec
open LeanAV.Core
open LeanAV.Video
open LeanAV.Encoder
open LeanAV.H264InterDeblockDpb

theorem clip3_bounds (lo hi x : Int) (hlo : lo ≤ hi) :
    lo ≤ clip3 lo hi x ∧ clip3 lo hi x ≤ hi := by
  unfold clip3
  split
  · omega
  · split <;> omega

theorem clip3_id_in_range (lo hi x : Int) (h0 : lo ≤ x) (h1 : x ≤ hi) :
    clip3 lo hi x = x := by
  unfold clip3
  split
  · omega
  · split <;> omega

theorem h264Tap6_dc_gain_32 (v : Int) :
    h264Tap6 v v v v v v = 32 * v := by
  unfold h264Tap6
  omega

theorem h264Tap6_palindromic_symm (e f g h i j : Int) :
    h264Tap6 j i h g f e = h264Tap6 e f g h i j := by
  unfold h264Tap6
  omega

theorem h264Round5_monotone (b1 b2 : Int) (h : b1 ≤ b2) :
    h264Round5 b1 ≤ h264Round5 b2 := by
  unfold h264Round5 clip3
  have hd : (b1 + 16) / 32 ≤ (b2 + 16) / 32 := by omega
  omega

theorem h264Round6_monotone (j1 j2 : Int) (h : j1 ≤ j2) :
    h264Round6 j1 ≤ h264Round6 j2 := by
  unfold h264Round6 clip3
  have hd : (j1 + 512) / 1024 ≤ (j2 + 512) / 1024 := by omega
  omega

theorem h264Round5_dc_exact (v : Int) (hv0 : 0 ≤ v) (hv1 : v ≤ 255) :
    h264Round5 (h264Tap6 v v v v v v) = v := by
  rw [h264Tap6_dc_gain_32]
  unfold h264Round5 clip3
  have hf : (32 * v + 16) / 32 = v := by omega
  rw [hf]
  split
  · omega
  · split <;> omega

theorem h264Round6_dc_exact (v : Int) (hv0 : 0 ≤ v) (hv1 : v ≤ 255) :
    h264Round6 (h264Tap6 (32 * v) (32 * v) (32 * v) (32 * v) (32 * v) (32 * v)) = v := by
  rw [h264Tap6_dc_gain_32]
  unfold h264Round6 clip3
  have hf : (32 * (32 * v) + 512) / 1024 = v := by omega
  rw [hf]
  split
  · omega
  · split <;> omega

theorem avgRound_idempotent (v : Int) :
    avgRound v v = v := by
  unfold avgRound
  omega

theorem avgRound_symm (a b : Int) :
    avgRound a b = avgRound b a := by
  unfold avgRound
  have h : a + b + 1 = b + a + 1 := by omega
  rw [h]

theorem avgRound_between_endpoints (a b : Int) :
    min a b ≤ avgRound a b ∧ avgRound a b ≤ max a b := by
  unfold avgRound
  omega

theorem sampleExt_in_bounds_exact (p : Plane2D) (x y : Nat)
    (hx : x < p.width) (hy : y < p.height) :
    sampleExt p (Int.ofNat x) (Int.ofNat y) = Int.ofNat (planePixelD p y x).toNat ∧
    sampleExt p (Int.ofNat x) (Int.ofNat y) < 256 := by
  unfold sampleExt
  have hne : (p.width == 0 || p.height == 0) = false := by
    cases hw : p.width == 0 <;> cases hh : p.height == 0 <;> simp_all
    all_goals omega
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hcx : (clip3 0 (Int.ofNat p.width - 1) (Int.ofNat x)).toNat = x := by
    unfold clip3
    simp only [Int.ofNat_eq_natCast]
    omega
  have hcy : (clip3 0 (Int.ofNat p.height - 1) (Int.ofNat y)).toNat = y := by
    unfold clip3
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hcx, hcy]
  refine ⟨rfl, ?_⟩
  simp only [Int.ofNat_eq_natCast]
  have hlt : (planePixelD p y x).toNat < 256 := UInt8.toNat_lt _
  omega

theorem h264CenterJ1_eq_vert (p : Plane2D) (xInt yInt : Int) :
    h264CenterJ1 p xInt yInt = h264CenterJ1Vert p xInt yInt := by
  unfold h264CenterJ1 h264CenterJ1Vert h264HorizB1 h264VertH1 h264Tap6
  omega

theorem h264LumaFracInt_zero_zero (p : Plane2D) (xInt yInt : Int) :
    h264LumaFracInt p xInt yInt 0 0 = sampleExt p xInt yInt := by
  rfl

def h264LumaFracCoordsValidGate (coords : Nat × Nat) : Bool :=
  coords.1 < 4 && coords.2 < 4

def h264LumaFracCoordsValidSpec : AVGateSpec (Nat × Nat) (fun c => c.1 < 4 ∧ c.2 < 4) where
  gate := h264LumaFracCoordsValidGate
  sound := by
    intro c hg
    unfold h264LumaFracCoordsValidGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete := by
    intro c ⟨hx, hy⟩
    unfold h264LumaFracCoordsValidGate
    simp [hx, hy]
  posWitness := (2, 2)
  negWitness := (4, 1)
  nonVacuous := by decide
  tight := by decide

theorem h264LumaHalfPel_matches_video_helper_step :
    let p : Plane2D := {
      width := 8, height := 2, stride := 8,
      data := ⟨#[10, 10, 10, 220, 220, 220, 220, 220,
                 40, 40, 200, 200, 50, 50, 50, 50]⟩
    }
    h264LumaFrac p 2 0 2 0 = clip1Y (h264LumaFracInt p 2 0 2 0) ∧
    h264LumaFrac p 3 0 0 2 = clip1Y (h264LumaFracInt p 3 0 0 2) := by
  decide

theorem h264LumaFracInt_qpel_2_3_avg_j_s (p : Plane2D) (xInt yInt : Int) :
    h264LumaFracInt p xInt yInt 2 3 =
      avgRound (h264Round6 (h264CenterJ1 p xInt yInt))
               (h264Round5 (h264HorizB1 p xInt (yInt + 1))) := by
  rfl

theorem h264LumaFrac_non_dc_2_3_exact :
    let p : Plane2D := {
      width := 8, height := 8, stride := 8,
      data := ⟨((List.range 64).map fun idx =>
        let r := idx / 8
        let c := idx % 8
        UInt8.ofNat ((17 * r + 31 * c + 5 * r * c + 23) % 256)).toArray⟩
    }
    h264Round6 (h264CenterJ1 p 3 3) = 123 ∧
    h264Round5 (h264HorizB1 p 3 4) = 142 ∧
    h264LumaFrac p 3 3 2 3 = 133 := by
  decide

theorem h264LumaFrac_dc_all_16_exact :
    let p := Plane2D.alloc 8 8 8 137
    (List.range 4).all (fun yf =>
      (List.range 4).all (fun xf =>
        h264LumaFrac p 3 3 xf yf == 137)) = true := by
  decide

theorem h264LumaQpel_negative_mv_boundary_ext :
    let p := Plane2D.alloc 4 4 4 89
    h264LumaQpel p (-7) (-5) = 89 ∧ h264LumaQpel p 25 31 = 89 := by
  decide

theorem h264ChromaBilinear_weights_sum_64 (xf yf : Int) :
    (8 - xf) * (8 - yf) + xf * (8 - yf) + (8 - xf) * yf + xf * yf = 64 := by
  have h1 : (8 - xf) * (8 - yf) + xf * (8 - yf) = 8 * (8 - yf) := by
    rw [← Int.add_mul]
    have hs : 8 - xf + xf = 8 := by omega
    rw [hs]
  have h2 : (8 - xf) * yf + xf * yf = 8 * yf := by
    rw [← Int.add_mul]
    have hs : 8 - xf + xf = 8 := by omega
    rw [hs]
  calc
    (8 - xf) * (8 - yf) + xf * (8 - yf) + (8 - xf) * yf + xf * yf
        = ((8 - xf) * (8 - yf) + xf * (8 - yf)) + ((8 - xf) * yf + xf * yf) := by omega
    _ = 8 * (8 - yf) + 8 * yf := by rw [h1, h2]
    _ = 64 := by omega

theorem h264ChromaFracInt_zero_zero (p : Plane2D) (xIntC yIntC : Int) :
    h264ChromaFracInt p xIntC yIntC 0 0 = sampleExt p xIntC yIntC := by
  unfold h264ChromaFracInt
  simp
  omega

theorem h264ChromaFrac_dc_all_64_exact :
    let p := Plane2D.alloc 4 4 4 173
    (List.range 8).all (fun yf =>
      (List.range 8).all (fun xf =>
        h264ChromaFrac p 1 1 xf yf == 173)) = true := by
  decide

def h264ChromaFracCoordsValidGate (coords : Nat × Nat) : Bool :=
  coords.1 < 8 && coords.2 < 8

def h264ChromaFracCoordsValidSpec : AVGateSpec (Nat × Nat) (fun c => c.1 < 8 ∧ c.2 < 8) where
  gate := h264ChromaFracCoordsValidGate
  sound := by
    intro c hg
    unfold h264ChromaFracCoordsValidGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete := by
    intro c ⟨hx, hy⟩
    unfold h264ChromaFracCoordsValidGate
    simp [hx, hy]
  posWitness := (5, 3)
  negWitness := (8, 0)
  nonVacuous := by decide
  tight := by decide

theorem partSize_bounds_and_div4 (s : H264PartShape) :
    let (w, h) := partSize s
    4 ≤ w ∧ w ≤ 16 ∧ 4 ≤ h ∧ h ≤ 16 ∧ w % 4 = 0 ∧ h % 4 = 0 := by
  cases s <;> decide

theorem biPredSample_comm (a b : UInt8) :
    biPredSample a b = biPredSample b a := by
  unfold biPredSample mcBiPredPixel
  rw [UInt16.add_comm a.toUInt16 b.toUInt16]

theorem implicitBiWeightScaleFactor_rejects_zero_td (pocCur poc0 : Int) :
    implicitBiWeightScaleFactor pocCur poc0 poc0 = none := by
  unfold implicitBiWeightScaleFactor clip3
  simp

theorem implicitBiWeightScaleFactor_sum_64 (pocCur poc0 poc1 w0 w1 : Int)
    (h : implicitBiWeightScaleFactor pocCur poc0 poc1 = some (w0, w1)) :
    w0 + w1 = 64 ∧ -64 ≤ w1 ∧ w1 ≤ 128 := by
  unfold implicitBiWeightScaleFactor at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next hrange =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrange
      rcases h with ⟨hw0, hw1⟩
      omega

def implicitBiWeightValidGate (pocs : Int × Int × Int) : Bool :=
  (implicitBiWeightScaleFactor pocs.1 pocs.2.1 pocs.2.2).isSome

def implicitBiWeightValidSpec : AVGateSpec (Int × Int × Int)
    (fun p => ∃ w, implicitBiWeightScaleFactor p.1 p.2.1 p.2.2 = some w) where
  gate := implicitBiWeightValidGate
  sound := by
    intro p hg
    unfold implicitBiWeightValidGate at hg
    cases h : implicitBiWeightScaleFactor p.1 p.2.1 p.2.2 with
    | none => simp [h] at hg
    | some w => exact ⟨w, rfl⟩
  complete := by
    intro p ⟨w, hw⟩
    unfold implicitBiWeightValidGate
    simp [hw]
  posWitness := (2, 0, 4)
  negWitness := (2, 4, 4)
  nonVacuous := by decide
  tight := by decide

theorem median3_symm_ab (a b c : Int) :
    median3 a b c = median3 b a c := by
  unfold median3
  omega

theorem median3_idempotent (x c : Int) :
    median3 x x c = x := by
  unfold median3
  omega

theorem median3_bounds (a b c : Int) :
    min a (min b c) ≤ median3 a b c ∧ median3 a b c ≤ max a (max b c) := by
  unfold median3
  omega

theorem mvpMedian_left_only_fallback (targetRef rA : Int) (mvA mvB mvC : MotionVec) :
    mvpMedian targetRef ⟨true, rA, mvA⟩ ⟨false, 0, mvB⟩ ⟨false, 0, mvC⟩ .p16x16 0 = mvA := by
  unfold mvpMedian
  simp

theorem mvpMedian_directional_16x8_and_8x16 :
    let nA : NeighborMv := ⟨true, 0, ⟨12, -4⟩⟩
    let nB : NeighborMv := ⟨true, 0, ⟨-8, 20⟩⟩
    let nC : NeighborMv := ⟨true, 0, ⟨16, 4⟩⟩
    mvpMedian 0 nA nB nC .p16x8 0 = ⟨-8, 20⟩ ∧
    mvpMedian 0 nA nB nC .p16x8 1 = ⟨12, -4⟩ ∧
    mvpMedian 0 nA nB nC .p8x16 0 = ⟨12, -4⟩ ∧
    mvpMedian 0 nA nB nC .p8x16 1 = ⟨16, 4⟩ := by
  decide

theorem pSkipMv_zero_when_left_missing (nbB nbC : NeighborMv) (mvA : MotionVec) (rA : Int) :
    pSkipMv false ⟨false, rA, mvA⟩ nbB nbC = ⟨0, 0⟩ := by
  unfold pSkipMv
  simp

theorem pSkipMv_zero_when_top_zero_ref0 (edge : Bool) (nbA nbC : NeighborMv) :
    pSkipMv edge nbA ⟨true, 0, ⟨0, 0⟩⟩ nbC = ⟨0, 0⟩ := by
  unfold pSkipMv
  cases edge <;> cases nbA.avail <;> simp

theorem bDirectTemporal_mv_diff_conserves_collocated (mvCol : MotionVec) (r0 pocCur poc0 poc1 : Int) :
    let res := bDirectTemporal mvCol r0 pocCur poc0 poc1
    res.mvL0.x - res.mvL1.x = mvCol.x ∧ res.mvL0.y - res.mvL1.y = mvCol.y := by
  unfold bDirectTemporal
  dsimp only
  split
  · dsimp only
    omega
  · dsimp only
    omega

theorem bDirectSpatial_colZero_zeros_unit_mv :
    let zA : NeighborMv := ⟨true, 0, ⟨1, -1⟩⟩
    let zB : NeighborMv := ⟨true, 0, ⟨1, 0⟩⟩
    let zC : NeighborMv := ⟨true, 0, ⟨0, -1⟩⟩
    let res := bDirectSpatial zA zB zC zA zB zC true
    res.mvL0 = ⟨0, 0⟩ ∧ res.mvL1 = ⟨0, 0⟩ ∧ res.predFlagL0 = true ∧ res.predFlagL1 = true := by
  decide

theorem mvdRateBits_zero_mvd_is_two (mv : MotionVec) :
    mvdRateBits mv mv = 2 := by
  unfold mvdRateBits expGolombSignedBits
  simp [expGolombSignedBits.bitLen]

theorem refineMotionSubpel_recovers_qpel_shift :
    let refP : Plane2D := {
      width := 6, height := 6, stride := 6,
      data := ⟨((List.range 36).map fun idx =>
        let r := idx / 6
        let c := idx % 6
        UInt8.ofNat (10 + 19 * r + 31 * c + 7 * r * c)).toArray⟩
    }
    let p00 := h264LumaQpel refP (4 * 2 - 1) (4 * 2 + 2)
    let p01 := h264LumaQpel refP (4 * 3 - 1) (4 * 2 + 2)
    let p10 := h264LumaQpel refP (4 * 2 - 1) (4 * 3 + 2)
    let p11 := h264LumaQpel refP (4 * 3 - 1) (4 * 3 + 2)
    let srcP : Plane2D := {
      width := 6, height := 6, stride := 6,
      data := ⟨((List.range 36).map fun idx =>
        if idx == 14 then p00
        else if idx == 15 then p01
        else if idx == 20 then p10
        else if idx == 21 then p11
        else 10).toArray⟩
    }
    let est := refineMotionSubpel srcP refP 2 2 2 2 0 0 ⟨-1, 2⟩ 1
    est.mv = ⟨-1, 2⟩ ∧ est.sad = 0 ∧ est.rdCost = 2 := by
  decide

theorem h264DeblockTables_sizes_and_monotone :
    h264AlphaTable.size = 52 ∧
    h264BetaTable.size = 52 ∧
    h264Tc0Table1.size = 52 ∧
    h264Tc0Table2.size = 52 ∧
    h264Tc0Table3.size = 52 ∧
    (List.range 16).all (fun i => lookupAlpha i == 0 && lookupBeta i == 0) = true ∧
    (List.range 51).all (fun i =>
      lookupAlpha i ≤ lookupAlpha (i + 1) &&
      lookupBeta i ≤ lookupBeta (i + 1) &&
      lookupTc0 i 1 ≤ lookupTc0 i 2 &&
      lookupTc0 i 2 ≤ lookupTc0 i 3) = true := by
  decide

theorem deblockIndexA_le_51 (qp off : Int) :
    deblockIndexA qp off ≤ 51 := by
  unfold deblockIndexA
  have hb := clip3_bounds 0 51 (qp + 2 * off) (by decide)
  omega

theorem deblockIndexB_le_51 (qp off : Int) :
    deblockIndexB qp off ≤ 51 := by
  unfold deblockIndexB
  have hb := clip3_bounds 0 51 (qp + 2 * off) (by decide)
  omega

theorem bSFromFlags_le_4 (mb iP iQ cP cQ mv : Bool) :
    bSFromFlags mb iP iQ cP cQ mv ≤ 4 := by
  unfold bSFromFlags
  cases mb <;> cases iP
  all_goals cases iQ <;> cases cP
  all_goals cases cQ <;> cases mv
  all_goals decide

theorem shouldFilterEdge_8x8_skips_4_and_12 (idc : Nat) (isSlice : Bool) (bS : Nat) :
    shouldFilterEdge idc isSlice true 4 bS = false ∧
    shouldFilterEdge idc isSlice true 12 bS = false := by
  unfold shouldFilterEdge skipInternalEdge8x8
  constructor
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> simp
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> simp

theorem filterLumaSamples8_bS0_identity (s : DeblockSamples8) (qp a b : Int) :
    filterLumaSamples8 s 0 qp a b = s := by
  unfold filterLumaSamples8
  simp

theorem filterLumaSamples8_preserves_p3_q3 (s : DeblockSamples8) (bS : Nat) (qp a b : Int) :
    (filterLumaSamples8 s bS qp a b).p3 = s.p3 ∧
    (filterLumaSamples8 s bS qp a b).q3 = s.q3 := by
  unfold filterLumaSamples8
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem filterLumaSamples8_normal_preserves_p2_q2 (s : DeblockSamples8) (bS : Nat) (qp a b : Int)
    (hb4 : bS ≠ 4) :
    (filterLumaSamples8 s bS qp a b).p2 = s.p2 ∧
    (filterLumaSamples8 s bS qp a b).q2 = s.q2 := by
  unfold filterLumaSamples8
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · have hne : (bS == 4) = false := beq_false_of_ne hb4
      simp [hne]

theorem filterChromaSamples4_bS0_identity (p1 p0 q0 q1 : UInt8) (qp a b : Int) :
    filterChromaSamples4 p1 p0 q0 q1 0 qp a b = (p0, q0) := by
  unfold filterChromaSamples4
  simp

def disableDeblockIdcValidGate (idc : Nat) : Bool :=
  idc ≤ 2

def disableDeblockIdcValidSpec : AVGateSpec Nat (fun idc => idc ≤ 2) where
  gate := disableDeblockIdcValidGate
  sound := by
    intro idc hg
    unfold disableDeblockIdcValidGate at hg
    exact of_decide_eq_true hg
  complete := by
    intro idc h
    unfold disableDeblockIdcValidGate
    exact decide_eq_true h
  posWitness := 2
  negWitness := 3
  nonVacuous := by decide
  tight := by decide

structure DeblockEdgeQuery where
  disableIdc : Nat
  isSlice    : Bool
  trans8x8   : Bool
  coord      : Nat
  bS         : Nat
  deriving Repr, DecidableEq, Inhabited

def DeblockEdgeActiveProp (q : DeblockEdgeQuery) : Prop :=
  1 ≤ q.bS ∧ q.bS ≤ 4 ∧ q.disableIdc ≤ 2 ∧ q.disableIdc ≠ 1 ∧
  ¬(q.disableIdc = 2 ∧ q.isSlice = true) ∧
  ¬(q.trans8x8 = true ∧ q.coord % 8 = 4)

def deblockEdgeActiveGate (q : DeblockEdgeQuery) : Bool :=
  shouldFilterEdge q.disableIdc q.isSlice q.trans8x8 q.coord q.bS

theorem shouldFilterEdge_iff (q : DeblockEdgeQuery) :
    shouldFilterEdge q.disableIdc q.isSlice q.trans8x8 q.coord q.bS = true ↔
    DeblockEdgeActiveProp q := by
  unfold shouldFilterEdge skipInternalEdge8x8 DeblockEdgeActiveProp
  constructor
  · intro h
    split at h
    · cases h
    · next h1 =>
      split at h
      · cases h
      · next h2 =>
        split at h
        · cases h
        · next h3 =>
          split at h
          · cases h
          · next h4 =>
            split at h
            · cases h
            · next h5 =>
              simp only [beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
                not_and, not_or] at h1 h2 h3 h4 h5
              refine ⟨by omega, by omega, by omega, h1, ?_, ?_⟩
              · intro ⟨hd2, hs⟩
                exact h3 hd2 hs
              · intro ⟨ht8, hm8⟩
                have h5' := h5 ht8
                omega
  · rintro ⟨hbs1, hbs4, hle2, hne1, hns, hn8⟩
    have hc1 : (q.disableIdc == 1) = false := beq_false_of_ne hne1
    have hge3 : ¬(q.disableIdc ≥ 3) := by omega
    have hc3 : ((q.disableIdc == 2) && q.isSlice) = false := by
      cases hs : q.isSlice <;> simp_all
    have hb0 : (q.bS == 0) = false := beq_false_of_ne (by omega)
    have hbgt4 : ¬(q.bS > 4) := by omega
    have hc5 : (q.trans8x8 && (q.coord % 16 == 4 || q.coord % 16 == 12)) = false := by
      cases ht : q.trans8x8
      · simp
      · have hm : q.coord % 8 ≠ 4 := fun hm => hn8 ⟨ht, hm⟩
        have hm4 : (q.coord % 16 == 4) = false := beq_false_of_ne (by omega)
        have hm12 : (q.coord % 16 == 12) = false := beq_false_of_ne (by omega)
        simp [hm4, hm12]
    simp [hc1, hge3, hc3, hb0, hbgt4, hc5]

def deblockEdgeActiveSpec : AVGateSpec DeblockEdgeQuery DeblockEdgeActiveProp where
  gate := deblockEdgeActiveGate
  sound := fun q hg => (shouldFilterEdge_iff q).mp hg
  complete := fun q hp => (shouldFilterEdge_iff q).mpr hp
  posWitness := ⟨0, false, true, 8, 2⟩
  negWitness := ⟨0, false, true, 4, 2⟩
  nonVacuous := by decide
  tight := by decide

theorem filterLumaSamples8_reduces_step_discontinuity :
    let step : DeblockSamples8 := ⟨100, 100, 100, 100, 108, 108, 108, 108⟩
    let outStrong := filterLumaSamples8 step 4 30 0 0
    let outNormal := filterLumaSamples8 step 2 30 0 0
    (Int.ofNat outStrong.q0.toNat - Int.ofNat outStrong.p0.toNat).natAbs < 8 ∧
    (Int.ofNat outNormal.q0.toNat - Int.ofNat outNormal.p0.toNat).natAbs < 8 := by
  decide

def dpbCapacityValidSpec : AVGateSpec H264Dpb
    (fun dpb =>
      dpb.maxDpbCapacity ≥ 1 ∧ dpb.maxDpbCapacity ≤ 16 ∧
      dpb.maxRefFrames ≤ dpb.maxDpbCapacity ∧
      dpb.entries.length ≤ dpb.maxDpbCapacity ∧
      dpbRefCount dpb ≤ dpb.maxRefFrames) where
  gate := dpbCapacityValid
  sound := by
    intro dpb hg
    unfold dpbCapacityValid at hg
    exact of_decide_eq_true hg
  complete := by
    intro dpb h
    unfold dpbCapacityValid
    exact decide_eq_true h
  posWitness := { maxRefFrames := 4, maxDpbCapacity := 16, maxFrameNum := 16 }
  negWitness := { maxRefFrames := 4, maxDpbCapacity := 17, maxFrameNum := 16 }
  nonVacuous := by decide
  tight := by decide

theorem flushDpb_clears_entries_and_lt_idx (dpb : H264Dpb) :
    (flushDpb dpb).entries = [] ∧ (flushDpb dpb).maxLongTermIdx = -1 := by
  unfold flushDpb
  exact ⟨rfl, rfl⟩

theorem clearIdrDpb_resets_entries_bound (dpb : H264Dpb) (noOut ltFlag : Bool) (poc : Int) (dig : UInt64) :
    (clearIdrDpb dpb noOut ltFlag poc dig).entries.length ≤ 1 ∧
    (clearIdrDpb dpb noOut ltFlag poc dig).entries.length ≤ dpb.maxDpbCapacity := by
  unfold clearIdrDpb
  cases noOut <;> simp [flushDpb, List.length_take] <;> omega

theorem buildRefPicListP0_length_le_active (dpb : H264Dpb) (currFn numAct : Nat) :
    (buildRefPicListP0 dpb currFn numAct).length ≤ numAct := by
  unfold buildRefPicListP0
  simp [List.length_take]
  omega

theorem buildRefPicListsB_lengths_le_active (dpb : H264Dpb) (currFn : Nat) (currPoc : Int) (n0 n1 : Nat) :
    (buildRefPicListsB dpb currFn currPoc n0 n1).1.length ≤ n0 ∧
    (buildRefPicListsB dpb currFn currPoc n0 n1).2.length ≤ n1 := by
  unfold buildRefPicListsB
  simp [List.length_take]
  omega

theorem dpb_b_slice_swaps_identical_l1_when_all_past :
    let d0 : H264Dpb := { maxRefFrames := 4, maxDpbCapacity := 8, maxFrameNum := 16 }
    let d1 := insertDecodedPicture d0 true false false true 0 0 false []
    let d2 := insertDecodedPicture d1 false false false true 1 4 false []
    let (l0, l1) := buildRefPicListsB d2 2 6 2 2
    l0.map DpbPicture.poc = [4, 0] ∧ l1.map DpbPicture.poc = [0, 4] := by
  decide

theorem dpb_sliding_window_wraparound_evicts_oldest :
    let d0 : H264Dpb := { maxRefFrames := 2, maxDpbCapacity := 4, maxFrameNum := 16 }
    let d1 := insertDecodedPicture d0 false false false true 14 28 false []
    let d2 := insertDecodedPicture d1 false false false true 15 30 false []
    let d3 := insertDecodedPicture d2 false false false true 0 32 false []
    let l0 := buildRefPicListP0 d3 1 2
    dpbCapacityValid d3 = true ∧ l0.map DpbPicture.frameNum = [0, 15] := by
  decide

theorem dpb_rplm_and_mmco_all_ops_exact :
    let d0 : H264Dpb := { maxRefFrames := 3, maxDpbCapacity := 6, maxFrameNum := 16 }
    let d1 := insertDecodedPicture d0 true false false true 0 0 false []
    let d2 := insertDecodedPicture d1 false false false true 1 2 false []
    let d3 := insertDecodedPicture d2 false false false true 2 4 true
      [.setMaxLongTermIdxPlus1 2, .assignLongTermIdx 1 0, .markCurrLongTerm 1]
    let initL0 := buildRefPicListP0 d3 3 3
    let modL0 := applyRefPicListMod d3 initL0 3 2 [.longTermPic 1, .subPicNum 1, .endLoop]
    let d4 := insertDecodedPicture d3 false false false true 3 6 true
      [.markLongUnused 0, .setMaxLongTermIdxPlus1 1, .markShortUnused 1]
    let d5 := insertDecodedPicture d4 false false false true 4 8 true [.markAllUnused]
    let df := flushDpb d5
    modL0.map DpbPicture.poc = [4, 2] ∧
    dpbCapacityValid d3 = true ∧
    dpbCapacityValid d4 = true ∧
    dpbCapacityValid d5 = true ∧
    df.outputPocLog = [0, 2, 4, 6, 0] ∧
    df.priorCvsMonitor = true := by
  decide

theorem dpb_mmco_rejects_lt_idx_gt_max (dpb : H264Dpb) (currFn dpm1 ltIdx : Nat)
    (cm : DpbRefMark) (m5 : Bool) (hgt : (ltIdx : Int) > dpb.maxLongTermIdx) :
    let refreshed := refreshShortTermPicNums dpb.entries currFn dpb.maxFrameNum
    applySingleMmco dpb currFn cm m5 (.assignLongTermIdx dpm1 ltIdx) =
      ({ dpb with entries := refreshed }, cm, m5) ∧
    applySingleMmco dpb currFn cm m5 (.markCurrLongTerm ltIdx) =
      ({ dpb with entries := refreshed }, cm, m5) := by
  unfold applySingleMmco
  simp
  constructor <;> intro hle <;> omega

theorem dpb_marking_before_bump_reproducer_monotone :
    let d0 : H264Dpb := { maxRefFrames := 3, maxDpbCapacity := 3, maxFrameNum := 16 }
    let d1 := insertDecodedPicture d0 false false false true 0 0 false []
    let d2 := insertDecodedPicture d1 false false false true 1 2 false []
    let d3 := insertDecodedPicture d2 false false false true 2 8 false []
    let d4 := insertDecodedPicture d3 false false false true 3 4 false []
    let df := flushDpb d4
    dpbCapacityValid d4 = true ∧
    df.outputPocLog = [0, 2, 4, 8] ∧
    df.priorCvsMonitor = true := by
  decide

theorem derivePocType1_cycle_nonref_and_mmco5_exact :
    let offsets : Array Int := #[4, 6]
    let (p0, off0) := derivePocType1 true true false false false 0 4 0 0 (-2) 0 offsets 0 0
    let (p1, off1) := derivePocType1 false true false false false 1 4 off0 0 (-2) 0 offsets 0 0
    let (p2, off2) := derivePocType1 false false false false false 2 4 off1 1 (-2) 0 offsets (-1) 0
    let (p3, off3) := derivePocType1 false true false false false 2 4 off2 2 (-2) 0 offsets 2 0
    let (pPostM5, offPostM5) := derivePocType1 false true true false false 1 4 16 15 (-2) 0 offsets 0 0
    (p0, off0) = (0, 0) ∧
    (p1, off1) = (4, 0) ∧
    (p2, off2) = (1, 0) ∧
    (p3, off3) = (12, 0) ∧
    (pPostM5, offPostM5) = (4, 0) := by
  decide

theorem derivePocType2_mmco5_resets_prev_offset :
    let (pPost, offPost) := derivePocType2 false true true 1 4 16 15
    pPost = 2 ∧ offPost = 0 := by
  decide

theorem dpb_b_pyramid_bumping_monotone_poc :
    let d0 : H264Dpb := { maxRefFrames := 4, maxDpbCapacity := 4, maxFrameNum := 16 }
    let d1 := insertDecodedPicture d0 true false false true 0 0 false []
    let d2 := insertDecodedPicture d1 false false false true 1 8 false []
    let d3 := insertDecodedPicture d2 false false false true 2 4 false []
    let d4 := insertDecodedPicture d3 false false false false 3 2 false []
    let d5 := insertDecodedPicture d4 false false false false 3 6 false []
    let df := flushDpb d5
    dpbCapacityValid d5 = true ∧ df.outputPocLog = [0, 2, 4, 6, 8] ∧ df.priorCvsMonitor = true := by
  decide

theorem parseAnnexBSpsFull_scaling_matrix_zero_next_scale_exact :
    let spsBytes : Array UInt8 := #[0x67, 0x64, 0x00, 0x1E, 0xAD, 0x84, 0x40, 0x76, 0x23, 0xC8]
    parseAnnexBSpsFull { ba := ⟨spsBytes⟩, off := 0, len := spsBytes.size } =
      some {
        spsId := 0, log2MaxFrameNum := 4, picOrderCntType := 0,
        log2MaxPicOrderCntLsb := 4, deltaPicOrderAlwaysZero := false,
        offsetForNonRefPic := 0, offsetForTopToBottomField := 0, offsetForRefFrame := #[],
        maxNumRefFrames := 2, frameMbsOnly := true,
        separateColourPlane := false, chromaArrayType := 1
      } := by
  decide

def annexBSpsValidGate (bs : Array UInt8) : Bool :=
  (parseAnnexBSpsFull { ba := ⟨bs⟩, off := 0, len := bs.size }).isSome

def annexBSpsValidSpec : AVGateSpec (Array UInt8)
    (fun bs => ∃ sps, parseAnnexBSpsFull { ba := ⟨bs⟩, off := 0, len := bs.size } = some sps) where
  gate := annexBSpsValidGate
  sound := by
    intro bs hg
    unfold annexBSpsValidGate at hg
    cases h : parseAnnexBSpsFull { ba := ⟨bs⟩, off := 0, len := bs.size } with
    | none => simp [h] at hg
    | some sps => exact ⟨sps, rfl⟩
  complete := by
    intro bs ⟨sps, hsps⟩
    unfold annexBSpsValidGate
    simp [hsps]
  posWitness := #[0x67, 0x42, 0x00, 0x1E, 0x9A, 0x74, 0x05, 0x81, 0xEC, 0x80]
  negWitness := #[0x68, 0xCE, 0x3C, 0x80]
  nonVacuous := by decide
  tight := by decide

def annexBPpsValidGate (bs : Array UInt8) : Bool :=
  (parseAnnexBPpsFull { ba := ⟨bs⟩, off := 0, len := bs.size }).isSome

def annexBPpsValidSpec : AVGateSpec (Array UInt8)
    (fun bs => ∃ pps, parseAnnexBPpsFull { ba := ⟨bs⟩, off := 0, len := bs.size } = some pps) where
  gate := annexBPpsValidGate
  sound := by
    intro bs hg
    unfold annexBPpsValidGate at hg
    cases h : parseAnnexBPpsFull { ba := ⟨bs⟩, off := 0, len := bs.size } with
    | none => simp [h] at hg
    | some pps => exact ⟨pps, rfl⟩
  complete := by
    intro bs ⟨pps, hpps⟩
    unfold annexBPpsValidGate
    simp [hpps]
  posWitness := #[0x68, 0xCE, 0x3C, 0x80]
  negWitness := #[0x67, 0x42, 0x00, 0x1E]
  nonVacuous := by decide
  tight := by decide

end LeanAV.H264InterDeblockDpbProofs

