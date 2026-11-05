import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.H264IntraTransform

namespace LeanAV.H264IntraTransformProofs

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream
open LeanAV.H264IntraTransform

def h264QpGateSpec : AVGateSpec Int (fun qp => 0 ≤ qp ∧ qp ≤ 51) where
  gate := isValidQp
  sound := by
    intro qp h
    simpa [isValidQp] using h
  complete := by
    intro qp h
    simpa [isValidQp] using h
  posWitness := 26
  negWitness := 52
  nonVacuous := by decide
  tight := by decide

def h264ChromaQpOffsetGateSpec : AVGateSpec Int (fun off => -12 ≤ off ∧ off ≤ 12) where
  gate := isValidChromaQpOffset
  sound := by
    intro off h
    simpa [isValidChromaQpOffset] using h
  complete := by
    intro off h
    simpa [isValidChromaQpOffset] using h
  posWitness := 0
  negWitness := 13
  nonVacuous := by decide
  tight := by decide

def h264PixelRangeGateSpec : AVGateSpec Int (fun v => 0 ≤ v ∧ v ≤ 255) where
  gate := isValidPixelInt
  sound := by
    intro v h
    simpa [isValidPixelInt] using h
  complete := by
    intro v h
    simpa [isValidPixelInt] using h
  posWitness := 128
  negWitness := 256
  nonVacuous := by decide
  tight := by decide

def h264IntraNxNModeGateSpec : AVGateSpec Nat (fun m => m ≤ 8) where
  gate := isValidIntraNxNMode
  sound := by
    intro m h
    simpa [isValidIntraNxNMode] using h
  complete := by
    intro m h
    simpa [isValidIntraNxNMode] using h
  posWitness := 4
  negWitness := 9
  nonVacuous := by decide
  tight := by decide

def h264Intra16x16ModeGateSpec : AVGateSpec Nat (fun m => m ≤ 3) where
  gate := isValidIntra16x16Mode
  sound := by
    intro m h
    simpa [isValidIntra16x16Mode] using h
  complete := by
    intro m h
    simpa [isValidIntra16x16Mode] using h
  posWitness := 2
  negWitness := 4
  nonVacuous := by decide
  tight := by decide

def h264IntraChromaModeGateSpec : AVGateSpec Nat (fun m => m ≤ 3) where
  gate := isValidIntraChromaMode
  sound := by
    intro m h
    simpa [isValidIntraChromaMode] using h
  complete := by
    intro m h
    simpa [isValidIntraChromaMode] using h
  posWitness := 0
  negWitness := 5
  nonVacuous := by decide
  tight := by decide

def IntraNxNModeLegalSafe (mode : Nat) (n : IntraNeighbors) : Prop :=
  ((mode = 0 ∨ mode = 3 ∨ mode = 7) ∧ n.topAvail = true) ∨
  ((mode = 1 ∨ mode = 8) ∧ n.leftAvail = true) ∨
  mode = 2 ∨
  ((mode = 4 ∨ mode = 5 ∨ mode = 6) ∧
    n.topAvail = true ∧ n.leftAvail = true ∧ n.topLeftAvail = true)

def h264IntraNxNLegalityGate (p : Nat × IntraNeighbors) : Bool :=
  isLegalIntraNxNMode p.1 p.2

theorem isLegalIntraNxNMode_iff (mode : Nat) (n : IntraNeighbors) :
    isLegalIntraNxNMode mode n = true ↔ IntraNxNModeLegalSafe mode n := by
  unfold isLegalIntraNxNMode IntraNxNModeLegalSafe
  match mode with
  | 0 | 3 | 7 => simp
  | 1 | 8 => simp
  | 2 => simp
  | 4 | 5 | 6 => simp [Bool.and_eq_true, and_assoc]
  | _ + 9 => simp

def h264IntraNxNLegalityGateSpec : AVGateSpec (Nat × IntraNeighbors)
    (fun p => IntraNxNModeLegalSafe p.1 p.2) where
  gate := h264IntraNxNLegalityGate
  sound := by
    intro p h
    exact (isLegalIntraNxNMode_iff p.1 p.2).mp h
  complete := by
    intro p h
    exact (isLegalIntraNxNMode_iff p.1 p.2).mpr h
  posWitness := (2, { leftAvail := false, topAvail := false, topRightAvail := false,
                      topLeftAvail := false, left := #[], top := #[], topRight := #[], topLeft := 128 })
  negWitness := (4, { leftAvail := false, topAvail := true, topRightAvail := false,
                      topLeftAvail := false, left := #[], top := #[], topRight := #[], topLeft := 128 })
  nonVacuous := by decide
  tight := by decide

def Intra16x16ModeLegalSafe (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) : Prop :=
  (mode = 0 ∧ topAvail = true) ∨
  (mode = 1 ∧ leftAvail = true) ∨
  mode = 2 ∨
  (mode = 3 ∧ topAvail = true ∧ leftAvail = true ∧ topLeftAvail = true)

def h264Intra16x16LegalityGate (p : Nat × Bool × Bool × Bool) : Bool :=
  isLegalIntra16x16Mode p.1 p.2.1 p.2.2.1 p.2.2.2

theorem isLegalIntra16x16Mode_iff (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) :
    isLegalIntra16x16Mode mode leftAvail topAvail topLeftAvail = true ↔
      Intra16x16ModeLegalSafe mode leftAvail topAvail topLeftAvail := by
  unfold isLegalIntra16x16Mode Intra16x16ModeLegalSafe
  match mode with
  | 0 | 1 | 2 => simp
  | 3 => simp [Bool.and_eq_true, and_assoc]
  | _ + 4 => simp

def h264Intra16x16LegalityGateSpec : AVGateSpec (Nat × Bool × Bool × Bool)
    (fun p => Intra16x16ModeLegalSafe p.1 p.2.1 p.2.2.1 p.2.2.2) where
  gate := h264Intra16x16LegalityGate
  sound := by
    intro p h
    exact (isLegalIntra16x16Mode_iff p.1 p.2.1 p.2.2.1 p.2.2.2).mp h
  complete := by
    intro p h
    exact (isLegalIntra16x16Mode_iff p.1 p.2.1 p.2.2.1 p.2.2.2).mpr h
  posWitness := (2, (false, false, false))
  negWitness := (3, (true, true, false))
  nonVacuous := by decide
  tight := by decide

def IntraChromaModeLegalSafe (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) : Prop :=
  mode = 0 ∨
  (mode = 1 ∧ leftAvail = true) ∨
  (mode = 2 ∧ topAvail = true) ∨
  (mode = 3 ∧ topAvail = true ∧ leftAvail = true ∧ topLeftAvail = true)

def h264IntraChromaLegalityGate (p : Nat × Bool × Bool × Bool) : Bool :=
  isLegalIntraChromaMode p.1 p.2.1 p.2.2.1 p.2.2.2

theorem isLegalIntraChromaMode_iff (mode : Nat) (leftAvail topAvail topLeftAvail : Bool) :
    isLegalIntraChromaMode mode leftAvail topAvail topLeftAvail = true ↔
      IntraChromaModeLegalSafe mode leftAvail topAvail topLeftAvail := by
  unfold isLegalIntraChromaMode IntraChromaModeLegalSafe
  match mode with
  | 0 | 1 | 2 => simp
  | 3 => simp [Bool.and_eq_true, and_assoc]
  | _ + 4 => simp

def h264IntraChromaLegalityGateSpec : AVGateSpec (Nat × Bool × Bool × Bool)
    (fun p => IntraChromaModeLegalSafe p.1 p.2.1 p.2.2.1 p.2.2.2) where
  gate := h264IntraChromaLegalityGate
  sound := by
    intro p h
    exact (isLegalIntraChromaMode_iff p.1 p.2.1 p.2.2.1 p.2.2.2).mp h
  complete := by
    intro p h
    exact (isLegalIntraChromaMode_iff p.1 p.2.1 p.2.2.1 p.2.2.2).mpr h
  posWitness := (0, (false, false, false))
  negWitness := (3, (false, true, true))
  nonVacuous := by decide
  tight := by decide

theorem h264Clip1_valid_and_saturates (v : Int) :
    isValidPixelInt (clip1 v) = true ∧
    (v ≤ 0 → clip1 v = 0) ∧
    (255 ≤ v → clip1 v = 255) := by
  unfold isValidPixelInt clip1 clip3
  refine ⟨?_, ?_, ?_⟩
  · split
    · simp
    · split <;> simp <;> omega
  · intro hv
    split <;> omega
  · intro hv
    split
    · omega
    · split <;> omega

theorem h264Clip1_id_on_valid_pixel (v : Int) (h0 : 0 ≤ v) (h1 : v ≤ 255) :
    clip1 v = v := by
  unfold clip1 clip3
  split
  · omega
  · split <;> omega

theorem h264ClipU8_toNat_eq_clip1 (v : Int) :
    ((clipU8 v).toNat : Int) = clip1 v := by
  have hb : 0 ≤ clip1 v ∧ clip1 v ≤ 255 := by
    have hv := (h264Clip1_valid_and_saturates v).1
    simpa [isValidPixelInt] using hv
  unfold clipU8
  have hlt : (clip1 v).toNat < 256 := by omega
  have hu : ((clip1 v).toNat.toUInt8).toNat = (clip1 v).toNat := by
    simp [Nat.mod_eq_of_lt hlt]
  omega

theorem h264ClampQp_valid (qp : Nat) :
    isValidQp (clampQp qp : Int) = true ∧ clampQp qp ≤ 51 := by
  unfold clampQp isValidQp
  split <;> simp <;> omega

theorem h264ClampQp_id_on_valid (qp : Nat) (h : qp ≤ 51) :
    clampQp qp = qp := by
  unfold clampQp
  split <;> omega

theorem h264QpcFromQpy_bounded (qpy : Nat) (off : Int) :
    qpcFromQpy qpy off ≤ 39 ∧ isValidQp (qpcFromQpy qpy off : Int) = true := by
  have hall : ∀ k : Fin 52,
      let qpc := if k.val < 30 then k.val else qpcTable30.getD (k.val - 30) 39
      qpc ≤ 39 ∧ isValidQp (qpc : Int) = true := by decide
  unfold qpcFromQpy clip3
  have hclip : (if (qpy : Int) + off < 0 then (0 : Int) else if (qpy : Int) + off > 51 then 51 else (qpy : Int) + off).toNat < 52 := by
    split
    · omega
    · split <;> omega
  simpa using hall ⟨_, hclip⟩

theorem h264QpcTable_spec_witnesses :
    qpcFromQpy 0 0 = 0 ∧
    qpcFromQpy 29 0 = 29 ∧
    qpcFromQpy 30 0 = 29 ∧
    qpcFromQpy 36 0 = 34 ∧
    qpcFromQpy 51 0 = 39 ∧
    qpcFromQpy 51 12 = 39 ∧
    qpcFromQpy 2 (-12) = 0 := by
  decide

theorem h264AsrInt_zero (n : Nat) :
    asrInt 0 n = 0 := by
  simp [asrInt, Int.zero_fdiv]

theorem h264AsrInt_mul_pow2_exact (k : Int) (n : Nat) :
    asrInt (k * (2 : Int) ^ n) n = k := by
  unfold asrInt
  have hp : (2 : Int) ^ n ≠ 0 := by
    have hpos : (0 : Nat) < 2 ^ n := Nat.pow_pos (by decide)
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact Int.mul_fdiv_cancel k hp

theorem h264AsrInt_neg_odd_floors_toward_neg_inf :
    asrInt (-1) 1 = -1 ∧ asrInt (-3) 1 = -2 ∧ asrInt (-33) 6 = -1 ∧ asrInt 31 6 = 0 := by
  decide

theorem h264Hadamard2x2_involution_4x (a b c d : Int) :
    let (h0, h1, h2, h3) := hadamard2x2 a b c d
    hadamard2x2 h0 h1 h2 h3 = (4 * a, 4 * b, 4 * c, 4 * d) := by
  dsimp [hadamard2x2]
  simp only [Prod.mk.injEq]
  omega

theorem h264Hadamard4x4_1d_involution_4x (x0 x1 x2 x3 : Int) :
    let (y0, y1, y2, y3) := hadamard4Butterfly1D x0 x1 x2 x3
    hadamard4Butterfly1D y0 y1 y2 y3 = (4 * x0, 4 * x1, 4 * x2, 4 * x3) := by
  dsimp [hadamard4Butterfly1D]
  simp only [Prod.mk.injEq]
  omega

theorem h264Hadamard4x4_involution_16x (x : Array Int) (hx : x.size = 16) :
    hadamard4x4 (hadamard4x4 x) = x.map (fun v => 16 * v) := by
  apply Array.ext
  · simp [hadamard4x4, hx]
  · intro idx h1 h2
    have hlt : idx < 16 := by simpa [hadamard4x4] using h1
    rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨
        idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨ idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hadamard4x4, hadamard4Butterfly1D, Array.getD, hx] <;> omega

theorem h264Idct4Butterfly1D_dc_basis (d0 : Int) :
    idct4Butterfly1D (2 * d0) 0 0 0 = (2 * d0, 2 * d0, 2 * d0, 2 * d0) := by
  unfold idct4Butterfly1D asrInt
  simp [Int.zero_fdiv]

theorem h264Idct4Butterfly1D_even_basis (d2 : Int) :
    idct4Butterfly1D 0 0 (2 * d2) 0 = (2 * d2, -2 * d2, -2 * d2, 2 * d2) := by
  unfold idct4Butterfly1D asrInt
  simp only [Int.zero_fdiv, Prod.mk.injEq]
  omega

theorem h264Idct4Butterfly1D_odd_basis (k : Int) :
    idct4Butterfly1D 0 (2 * k) 0 0 = (2 * k, k, -k, -2 * k) ∧
    idct4Butterfly1D 0 0 0 (2 * k) = (k, -2 * k, 2 * k, -k) := by
  unfold idct4Butterfly1D asrInt
  have hdiv : Int.fdiv (2 * k) 2 = k := by
    have hc : 2 * k = k * 2 := by omega
    rw [hc]
    exact Int.mul_fdiv_cancel k (by decide)
  have hpow : (2 : Int) ^ 1 = 2 := rfl
  simp only [hpow, Int.zero_fdiv, hdiv, Prod.mk.injEq]
  omega

theorem h264Fdct4Butterfly1D_basis_orthogonality (c : Int) :
    fdct4Butterfly1D c c c c = (4 * c, 0, 0, 0) ∧
    fdct4Butterfly1D c (-c) (-c) c = (0, 0, 4 * c, 0) ∧
    fdct4Butterfly1D (2 * c) c (-c) (-2 * c) = (0, 10 * c, 0, 0) ∧
    fdct4Butterfly1D c (-2 * c) (2 * c) (-c) = (0, 0, 0, 10 * c) := by
  dsimp [fdct4Butterfly1D]
  simp only [Prod.mk.injEq]
  omega

theorem h264Idct8Butterfly1D_dc_and_even_basis (k : Int) :
    idct8Butterfly1D (2 * k) 0 0 0 0 0 0 0 =
      (2 * k, 2 * k, 2 * k, 2 * k, 2 * k, 2 * k, 2 * k, 2 * k) ∧
    idct8Butterfly1D 0 0 0 0 (2 * k) 0 0 0 =
      (2 * k, -2 * k, -2 * k, 2 * k, 2 * k, -2 * k, -2 * k, 2 * k) := by
  dsimp [idct8Butterfly1D, asrInt]
  simp only [Prod.mk.injEq]
  omega

theorem h264Fdct8Butterfly1D_dc_and_nyquist (c : Int) :
    fdct8Butterfly1D c c c c c c c c = (8 * c, 0, 0, 0, 0, 0, 0, 0) ∧
    fdct8Butterfly1D c (-c) (-c) c c (-c) (-c) c = (0, 0, 0, 0, 8 * c, 0, 0, 0) := by
  dsimp [fdct8Butterfly1D, asrInt]
  have h3 : c - c = 0 := by omega
  have h4 : -c - -c = 0 := by omega
  have h5 : c + c - (c + c) = 0 := by omega
  have h6 : -c + -c - (-c + -c) = 0 := by omega
  have hz2 : Int.fdiv 0 2 = 0 := by decide
  have hz4 : Int.fdiv 0 4 = 0 := by decide
  simp [h3, h4, h5, h6, hz2, hz4]
  omega

theorem h264LosslessSample_roundtrip (s p : UInt8) :
    losslessSampleReconstruct p (losslessSampleResidual s p) = s := by
  unfold losslessSampleReconstruct losslessSampleResidual
  have hsum : (p.toNat : Int) + ((s.toNat : Int) - (p.toNat : Int)) = (s.toNat : Int) := by omega
  rw [hsum]
  have hs0 : (0 : Int) ≤ (s.toNat : Int) := Int.natCast_nonneg _
  have hs1 : (s.toNat : Int) ≤ 255 := by
    have hlt := s.toNat_lt
    omega
  unfold clipU8
  rw [h264Clip1_id_on_valid_pixel (s.toNat : Int) hs0 hs1]
  simp [UInt8.ofNat_toNat]

theorem h264SamplesLosslessList_roundtrip :
    ∀ (samples preds : List UInt8),
      samples.length = preds.length →
      decodeSamplesLosslessList preds (encodeSamplesLosslessList samples preds) = samples
  | [], [], _ => rfl
  | _ :: _, [], hlen => by simp at hlen
  | [], _ :: _, hlen => by simp at hlen
  | s :: ss, p :: ps, hlen => by
    simp only [encodeSamplesLosslessList, decodeSamplesLosslessList,
      h264LosslessSample_roundtrip s p]
    rw [h264SamplesLosslessList_roundtrip ss ps (Nat.succ.inj hlen)]

theorem h264SamplesLossless_roundtrip (samples preds : Array UInt8)
    (hsz : samples.size = preds.size) :
    decodeSamplesLossless preds (encodeSamplesLossless samples preds) = samples := by
  unfold encodeSamplesLossless decodeSamplesLossless
  have hlen : samples.toList.length = preds.toList.length := by simpa using hsz
  simp [h264SamplesLosslessList_roundtrip samples.toList preds.toList hlen]

theorem h264SamplesLosslessList_length :
    ∀ (samples preds : List UInt8),
      samples.length = preds.length →
      (encodeSamplesLosslessList samples preds).length = samples.length
  | [], [], _ => rfl
  | _ :: _, [], hlen => by simp at hlen
  | [], _ :: _, hlen => by simp at hlen
  | _ :: ss, _ :: ps, hlen => by
    simp [encodeSamplesLosslessList, h264SamplesLosslessList_length ss ps (Nat.succ.inj hlen)]

theorem h264SamplesLossless_size (samples preds : Array UInt8)
    (hsz : samples.size = preds.size) :
    (encodeSamplesLossless samples preds).size = samples.size := by
  unfold encodeSamplesLossless
  have hlen : samples.toList.length = preds.toList.length := by simpa using hsz
  simpa using h264SamplesLosslessList_length samples.toList preds.toList hlen

theorem h264DpcmLine4_roundtrip (r0 r1 r2 r3 : Int) :
    let (c0, c1, c2, c3) := dpcmLine4 r0 r1 r2 r3
    undpcmLine4 c0 c1 c2 c3 = (r0, r1, r2, r3) := by
  dsimp [dpcmLine4, undpcmLine4]
  refine Prod.ext rfl ?_
  refine Prod.ext (by dsimp; omega) ?_
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem h264DpcmLine8_roundtrip (r0 r1 r2 r3 r4 r5 r6 r7 : Int) :
    let (c0, c1, c2, c3, c4, c5, c6, c7) := dpcmLine8 r0 r1 r2 r3 r4 r5 r6 r7
    undpcmLine8 c0 c1 c2 c3 c4 c5 c6 c7 = (r0, r1, r2, r3, r4, r5, r6, r7) := by
  dsimp [dpcmLine8, undpcmLine8]
  refine Prod.ext rfl ?_
  refine Prod.ext (by dsimp; omega) ?_
  refine Prod.ext (by dsimp; omega) ?_
  refine Prod.ext (by dsimp; omega) ?_
  refine Prod.ext (by dsimp; omega) ?_
  refine Prod.ext (by dsimp; omega) ?_
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem h264ResidualDpcm4x4_roundtrip (mode : Nat) (res : Array Int) (hsz : res.size = 16) :
    decodeResidualDpcm4x4 mode (encodeResidualDpcm4x4 mode res) = res := by
  apply Array.ext
  · unfold decodeResidualDpcm4x4
    by_cases h0 : (mode == 0) = true
    · simp [h0, hsz]
    · by_cases h1 : (mode == 1) = true <;> simp [h0, h1, hsz]
  · intro idx hi1 hi2
    have hlt : idx < 16 := by simpa [hsz] using hi2
    by_cases h0 : (mode == 0) = true
    · rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨
          idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨ idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [encodeResidualDpcm4x4, decodeResidualDpcm4x4, dpcmLine4, undpcmLine4, h0, Array.getD, hsz] <;> omega
    · by_cases h1 : (mode == 1) = true
      · rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨
            idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨ idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [encodeResidualDpcm4x4, decodeResidualDpcm4x4, dpcmLine4, undpcmLine4, h0, h1, Array.getD, hsz] <;> omega
      · rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨
            idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨ idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [encodeResidualDpcm4x4, decodeResidualDpcm4x4, h0, h1, Array.getD, hsz]

theorem h264DpcmPrefixSum_telescope (n : Nat) (f g : Nat → Int)
    (h0 : g 0 = f 0) (hstep : ∀ k, k < n → g (k + 1) = f (k + 1) - f k) :
    dpcmPrefixSum n g = f n := by
  induction n with
  | zero => simp [dpcmPrefixSum, h0]
  | succ m ih =>
    have hm := ih (fun k hk => hstep k (by omega))
    have hs := hstep m (by omega)
    simp only [dpcmPrefixSum, hm, hs]
    omega

theorem h264ResidualDpcm8x8_roundtrip (mode : Nat) (res : Array Int) (hsz : res.size = 64) :
    decodeResidualDpcm8x8 mode (encodeResidualDpcm8x8 mode res) = res := by
  have henc_get : ∀ (k : Nat) (hk : k < 64),
      (encodeResidualDpcm8x8 mode res).getD k 0 =
        let r := k / 8; let c := k % 8
        if mode == 0 then
          if r == 0 then res.getD c 0 else res.getD (r * 8 + c) 0 - res.getD ((r - 1) * 8 + c) 0
        else if mode == 1 then
          if c == 0 then res.getD (r * 8) 0 else res.getD (r * 8 + c) 0 - res.getD (r * 8 + c - 1) 0
        else res.getD k 0 := by
    intro k hk
    unfold encodeResidualDpcm8x8
    simp [Array.getD, hk]
  apply Array.ext
  · simp [decodeResidualDpcm8x8, hsz]
  · intro idx hi1 hi2
    have hlt : idx < 64 := by simpa [hsz] using hi2
    have hres_idx : res.getD idx 0 = res[idx]'hi2 := by simp [Array.getD, hi2]
    let r := idx / 8
    let c := idx % 8
    have hr8 : r < 8 := by omega
    have hc8 : c < 8 := by omega
    have hrc_eq : r * 8 + c = idx := by omega
    by_cases h0 : (mode == 0) = true
    · simp only [decodeResidualDpcm8x8, Array.getElem_ofFn, h0, ↓reduceIte]
      have htel := h264DpcmPrefixSum_telescope r
        (fun k => res.getD (k * 8 + c) 0)
        (fun k => (encodeResidualDpcm8x8 mode res).getD (k * 8 + c) 0)
        (by
          have hd : c / 8 = 0 := by omega
          have hm : c % 8 = c := by omega
          have := henc_get c (by omega)
          simpa [h0, hd, hm] using this)
        (by
          intro k hk
          have hkc : (k + 1) * 8 + c < 64 := by omega
          have hd : ((k + 1) * 8 + c) / 8 = k + 1 := by omega
          have hm : ((k + 1) * 8 + c) % 8 = c := by omega
          have := henc_get ((k + 1) * 8 + c) hkc
          simpa [h0, hd, hm] using this)
      calc dpcmPrefixSum (idx / 8) (fun k => (encodeResidualDpcm8x8 mode res).getD (k * 8 + idx % 8) 0)
          = res.getD (r * 8 + c) 0 := htel
        _ = res.getD idx 0 := by rw [hrc_eq]
        _ = res[idx]'hi2 := hres_idx
    · by_cases h1 : (mode == 1) = true
      · simp only [decodeResidualDpcm8x8, Array.getElem_ofFn, h0, h1, Bool.false_eq_true, ↓reduceIte]
        have htel := h264DpcmPrefixSum_telescope c
          (fun k => res.getD (r * 8 + k) 0)
          (fun k => (encodeResidualDpcm8x8 mode res).getD (r * 8 + k) 0)
          (by
            have hrk : r * 8 < 64 := by omega
            have hd : (r * 8) / 8 = r := by omega
            have hm : (r * 8) % 8 = 0 := by omega
            have := henc_get (r * 8) hrk
            simpa [h0, h1, hd, hm] using this)
          (by
            intro k hk
            have hrk : r * 8 + (k + 1) < 64 := by omega
            have hd : (r * 8 + (k + 1)) / 8 = r := by omega
            have hm : (r * 8 + (k + 1)) % 8 = k + 1 := by omega
            have hsub : r * 8 + (k + 1) - 1 = r * 8 + k := by omega
            have := henc_get (r * 8 + (k + 1)) hrk
            simpa [h0, h1, hd, hm, hsub] using this)
        calc dpcmPrefixSum (idx % 8) (fun k => (encodeResidualDpcm8x8 mode res).getD ((idx / 8) * 8 + k) 0)
            = res.getD (r * 8 + c) 0 := htel
          _ = res.getD idx 0 := by rw [hrc_eq]
          _ = res[idx]'hi2 := hres_idx
      · simp only [decodeResidualDpcm8x8, Array.getElem_ofFn, h0, h1, Bool.false_eq_true, ↓reduceIte]
        rw [henc_get idx hlt]
        simp [h0, h1, hres_idx]

theorem h264Pred_sizes_exact (m : Nat) (n : IntraNeighbors)
    (l16 t16 l8 t8 : Array UInt8) (tl : UInt8) (la ta : Bool) :
    (pred4x4 m n).size = 16 ∧
    (pred8x8 m n).size = 64 ∧
    (pred16x16 m l16 t16 tl la ta).size = 256 ∧
    (predChroma m l8 t8 tl la ta).size = 64 := by
  exact ⟨by unfold pred4x4; exact Array.size_ofFn,
         by unfold pred8x8; exact Array.size_ofFn,
         by unfold pred16x16; exact Array.size_ofFn,
         by unfold predChroma; exact Array.size_ofFn⟩

theorem h264ZScan4_grid_bijection :
    ∀ bx byy : Fin 4,
      let b := zScan4BlkIdx bx.val byy.val
      b < 16 ∧
      zScan4BlkCoord b = (bx.val * 4, byy.val * 4) := by
  decide

theorem h264ZScan4_coord_roundtrip (idx : Nat) (hlt : idx < 256) :
    let y := idx / 16
    let x := idx % 16
    let b := zScan4BlkIdx (x / 4) (y / 4)
    b < 16 ∧
    (zScan4BlkCoord b).1 + x % 4 = x ∧
    (zScan4BlkCoord b).2 + y % 4 = y := by
  have hbx : (idx % 16) / 4 < 4 := by omega
  have hby : (idx / 16) / 4 < 4 := by omega
  have hgrid := h264ZScan4_grid_bijection ⟨(idx % 16) / 4, hbx⟩ ⟨(idx / 16) / 4, hby⟩
  rcases hgrid with ⟨hb, hcoord⟩
  refine ⟨hb, ?_, ?_⟩
  · have h1 := congrArg Prod.fst hcoord
    dsimp at h1
    omega
  · have h2 := congrArg Prod.snd hcoord
    dsimp at h2
    omega

theorem h264ExtractMbBlock4_size (y256 : Array UInt8) (xO yO : Nat) :
    (extractMbBlock4 y256 xO yO).size = 16 := by
  unfold extractMbBlock4; exact Array.size_ofFn

theorem h264ExtractMbBlock8_size (y256 : Array UInt8) (xO yO : Nat) :
    (extractMbBlock8 y256 xO yO).size = 64 := by
  unfold extractMbBlock8; exact Array.size_ofFn

theorem h264Subblocks4x4_roundtrip (srcY256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    ∀ (sched : List (Nat × Nat × Bool)) (canvas : Array UInt8) (modes : List Nat),
      decodeSubblocks4x4List canvas nbrs sched modes
        (encodeSubblocks4x4List srcY256 canvas nbrs sched modes) =
      sched.map (fun (xO, yO, _) => extractMbBlock4 srcY256 xO yO)
  | [], _, _ => rfl
  | (xO, yO, trAv) :: rest, canvas, modes => by
    simp only [encodeSubblocks4x4List, decodeSubblocks4x4List, List.headD_cons, List.drop_succ_cons,
      List.drop_zero, List.map_cons]
    have hp : (pred4x4 (modes.headD 2) (mbSubblockNeighbors 4 canvas nbrs xO yO trAv)).size = 16 := by
      unfold pred4x4; exact Array.size_ofFn
    have hb : (extractMbBlock4 srcY256 xO yO).size = 16 := h264ExtractMbBlock4_size srcY256 xO yO
    have henc_sz : (encodeSamplesLossless (extractMbBlock4 srcY256 xO yO)
        (pred4x4 (modes.headD 2) (mbSubblockNeighbors 4 canvas nbrs xO yO trAv))).size = 16 := by
      rw [h264SamplesLossless_size _ _ (by omega), hb]
    have hblk : decodeSamplesLossless
        (pred4x4 (modes.headD 2) (mbSubblockNeighbors 4 canvas nbrs xO yO trAv))
        (decodeResidualDpcm4x4 (modes.headD 2)
          (encodeResidualDpcm4x4 (modes.headD 2)
            (encodeSamplesLossless (extractMbBlock4 srcY256 xO yO)
              (pred4x4 (modes.headD 2) (mbSubblockNeighbors 4 canvas nbrs xO yO trAv))))) =
        extractMbBlock4 srcY256 xO yO := by
      rw [h264ResidualDpcm4x4_roundtrip _ _ henc_sz,
          h264SamplesLossless_roundtrip _ _ (by omega)]
    rw [hblk, h264Subblocks4x4_roundtrip srcY256 nbrs rest _ (modes.drop 1)]

theorem h264Subblocks8x8_roundtrip (srcY256 : Array UInt8) (nbrs : H264IntraMbNeighbors) :
    ∀ (sched : List (Nat × Nat × Bool)) (canvas : Array UInt8) (modes : List Nat),
      decodeSubblocks8x8List canvas nbrs sched modes
        (encodeSubblocks8x8List srcY256 canvas nbrs sched modes) =
      sched.map (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)
  | [], _, _ => rfl
  | (xO, yO, trAv) :: rest, canvas, modes => by
    simp only [encodeSubblocks8x8List, decodeSubblocks8x8List, List.headD_cons, List.drop_succ_cons,
      List.drop_zero, List.map_cons]
    have hp : (pred8x8 (modes.headD 2) (mbSubblockNeighbors 8 canvas nbrs xO yO trAv)).size = 64 := by
      unfold pred8x8; exact Array.size_ofFn
    have hb : (extractMbBlock8 srcY256 xO yO).size = 64 := h264ExtractMbBlock8_size srcY256 xO yO
    have henc_sz : (encodeSamplesLossless (extractMbBlock8 srcY256 xO yO)
        (pred8x8 (modes.headD 2) (mbSubblockNeighbors 8 canvas nbrs xO yO trAv))).size = 64 := by
      rw [h264SamplesLossless_size _ _ (by omega), hb]
    have hblk : decodeSamplesLossless
        (pred8x8 (modes.headD 2) (mbSubblockNeighbors 8 canvas nbrs xO yO trAv))
        (decodeResidualDpcm8x8 (modes.headD 2)
          (encodeResidualDpcm8x8 (modes.headD 2)
            (encodeSamplesLossless (extractMbBlock8 srcY256 xO yO)
              (pred8x8 (modes.headD 2) (mbSubblockNeighbors 8 canvas nbrs xO yO trAv))))) =
        extractMbBlock8 srcY256 xO yO := by
      rw [h264ResidualDpcm8x8_roundtrip _ _ henc_sz,
          h264SamplesLossless_roundtrip _ _ (by omega)]
    rw [hblk, h264Subblocks8x8_roundtrip srcY256 nbrs rest _ (modes.drop 1)]

theorem h264ExtractMbBlock4_getD (y256 : Array UInt8) (xO yO sub : Nat) (hsub : sub < 16) :
    (extractMbBlock4 y256 xO yO).getD sub 0 =
      y256.getD ((yO + sub / 4) * 16 + (xO + sub % 4)) 0 := by
  unfold extractMbBlock4
  simp [Array.getD, hsub]

theorem h264ExtractMbBlock8_getD (y256 : Array UInt8) (xO yO sub : Nat) (hsub : sub < 64) :
    (extractMbBlock8 y256 xO yO).getD sub 0 =
      y256.getD ((yO + sub / 8) * 16 + (xO + sub % 8)) 0 := by
  unfold extractMbBlock8
  simp [Array.getD, hsub]

theorem h264AssembleMbBlocks4_extract (srcY256 : Array UInt8) (hsz : srcY256.size = 256)
    (topAv topRightAv : Bool) :
    assembleMbBlocks4 ((zScan4Schedule topAv topRightAv).map (fun (xO, yO, _) => extractMbBlock4 srcY256 xO yO)) =
    srcY256 := by
  apply Array.ext
  · simp [assembleMbBlocks4, hsz]
  · intro idx hi1 hi2
    have hlt : idx < 256 := by simpa [hsz] using hi2
    rcases h264ZScan4_coord_roundtrip idx hlt with ⟨hb, hx, hy⟩
    have hget_blk : (((zScan4Schedule topAv topRightAv).map
        (fun (xO, yO, _) => extractMbBlock4 srcY256 xO yO)).toArray).getD
        (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4)) #[] =
        extractMbBlock4 srcY256
          (zScan4BlkCoord (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4))).1
          (zScan4BlkCoord (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4))).2 := by
      rcases (by omega :
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 0 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 1 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 2 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 3 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 4 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 5 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 6 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 7 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 8 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 9 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 10 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 11 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 12 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 13 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 14 ∨
          zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4) = 15) with
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        (rw [h]; simp [zScan4Schedule, List.range, List.range.loop, Array.getD])
    have hsub : (idx / 16 % 4) * 4 + (idx % 16 % 4) < 16 := by omega
    have hpix : ((zScan4BlkCoord (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4))).2 +
        ((idx / 16 % 4) * 4 + (idx % 16 % 4)) / 4) * 16 +
        ((zScan4BlkCoord (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4))).1 +
        ((idx / 16 % 4) * 4 + (idx % 16 % 4)) % 4) = idx := by omega
    simp only [assembleMbBlocks4, Array.getElem_ofFn]
    change ((((zScan4Schedule topAv topRightAv).map
      (fun (xO, yO, _) => extractMbBlock4 srcY256 xO yO)).toArray).getD
      (zScan4BlkIdx (idx % 16 / 4) (idx / 16 / 4)) #[]).getD
      ((idx / 16 % 4) * 4 + (idx % 16 % 4)) 0 = srcY256[idx]'hi2
    rw [hget_blk, h264ExtractMbBlock4_getD _ _ _ _ hsub, hpix]
    simp [Array.getD, hi2]

theorem h264AssembleMbBlocks8_extract (srcY256 : Array UInt8) (hsz : srcY256.size = 256)
    (topAv topRightAv : Bool) :
    assembleMbBlocks8 ((zScan8Schedule topAv topRightAv).map (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)) =
    srcY256 := by
  apply Array.ext
  · simp [assembleMbBlocks8, hsz]
  · intro idx hi1 hi2
    have hlt : idx < 256 := by simpa [hsz] using hi2
    let y := idx / 16
    let x := idx % 16
    let b := (y / 8) * 2 + (x / 8)
    have hsub : (y % 8) * 8 + (x % 8) < 64 := by omega
    simp only [assembleMbBlocks8, Array.getElem_ofFn]
    change ((((zScan8Schedule topAv topRightAv).map
      (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)).toArray).getD b #[]).getD
      ((y % 8) * 8 + (x % 8)) 0 = srcY256[idx]'hi2
    rcases (by omega : x / 8 = 0 ∨ x / 8 = 1) with hx8 | hx8 <;>
    rcases (by omega : y / 8 = 0 ∨ y / 8 = 1) with hy8 | hy8
    · have hb0 : b = 0 := by dsimp [b]; omega
      have hblk : (((zScan8Schedule topAv topRightAv).map
          (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)).toArray).getD 0 #[] =
          extractMbBlock8 srcY256 0 0 := by simp [zScan8Schedule, Array.getD]
      have hpix : (0 + ((y % 8) * 8 + (x % 8)) / 8) * 16 + (0 + ((y % 8) * 8 + (x % 8)) % 8) = idx := by omega
      rw [hb0, hblk, h264ExtractMbBlock8_getD _ _ _ _ hsub, hpix]
      simp [Array.getD, hi2]
    · have hb2 : b = 2 := by dsimp [b]; omega
      have hblk : (((zScan8Schedule topAv topRightAv).map
          (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)).toArray).getD 2 #[] =
          extractMbBlock8 srcY256 0 8 := by simp [zScan8Schedule, Array.getD]
      have hpix : (8 + ((y % 8) * 8 + (x % 8)) / 8) * 16 + (0 + ((y % 8) * 8 + (x % 8)) % 8) = idx := by omega
      rw [hb2, hblk, h264ExtractMbBlock8_getD _ _ _ _ hsub, hpix]
      simp [Array.getD, hi2]
    · have hb1 : b = 1 := by dsimp [b]; omega
      have hblk : (((zScan8Schedule topAv topRightAv).map
          (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)).toArray).getD 1 #[] =
          extractMbBlock8 srcY256 8 0 := by simp [zScan8Schedule, Array.getD]
      have hpix : (0 + ((y % 8) * 8 + (x % 8)) / 8) * 16 + (8 + ((y % 8) * 8 + (x % 8)) % 8) = idx := by omega
      rw [hb1, hblk, h264ExtractMbBlock8_getD _ _ _ _ hsub, hpix]
      simp [Array.getD, hi2]
    · have hb3 : b = 3 := by dsimp [b]; omega
      have hblk : (((zScan8Schedule topAv topRightAv).map
          (fun (xO, yO, _) => extractMbBlock8 srcY256 xO yO)).toArray).getD 3 #[] =
          extractMbBlock8 srcY256 8 8 := by simp [zScan8Schedule, Array.getD]
      have hpix : (8 + ((y % 8) * 8 + (x % 8)) / 8) * 16 + (8 + ((y % 8) * 8 + (x % 8)) % 8) = idx := by omega
      rw [hb3, hblk, h264ExtractMbBlock8_getD _ _ _ _ hsub, hpix]
      simp [Array.getD, hi2]

theorem h264ClipU8_of_u8 (s : UInt8) :
    clipU8 (s.toNat : Int) = s := by
  have hs : s.toNat < 256 := s.toBitVec.isLt
  have hclip : clip1 (s.toNat : Int) = (s.toNat : Int) :=
    h264Clip1_id_on_valid_pixel (s.toNat : Int) (by omega) (by omega)
  unfold clipU8
  rw [hclip]
  simp

theorem h264MapClipU8_of_toNat (arr : Array UInt8) :
    (arr.map fun s => (s.toNat : Int)).map clipU8 = arr := by
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp [h264ClipU8_of_u8]

theorem h264LosslessIntraMb_encode_decode_roundtrip
    (mb : H264Yuv420pMb) (nbrs : H264IntraMbNeighbors)
    (partitionKind : Nat) (lumaModes : List Nat) (chromaMode : Nat)
    (hvalid : mb.valid = true) :
    decodeLosslessIntraMb (encodeLosslessIntraMb mb nbrs partitionKind lumaModes chromaMode) nbrs = mb := by
  unfold H264Yuv420pMb.valid at hvalid
  simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨hy, hu⟩, hv⟩
  by_cases hp3 : (partitionKind == 3) = true
  · unfold encodeLosslessIntraMb decodeLosslessIntraMb
    simp only [hp3, ↓reduceIte, beq_self_eq_true, List.headD_cons, h264MapClipU8_of_toNat]
  · have hpu : (predChroma chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail).size = 64 := by
      unfold predChroma; exact Array.size_ofFn
    have hpv : (predChroma chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail).size = 64 := by
      unfold predChroma; exact Array.size_ofFn
    have hrecU : decodeSamplesLossless
        (predChroma chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail)
        (encodeSamplesLossless mb.u
          (predChroma chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail)) = mb.u :=
      h264SamplesLossless_roundtrip mb.u _ (by omega)
    have hrecV : decodeSamplesLossless
        (predChroma chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail)
        (encodeSamplesLossless mb.v
          (predChroma chromaMode nbrs.leftV nbrs.topV nbrs.topLeftV nbrs.leftAvail nbrs.topAvail)) = mb.v :=
      h264SamplesLossless_roundtrip mb.v _ (by omega)
    unfold encodeLosslessIntraMb decodeLosslessIntraMb
    simp only [hp3, Bool.false_eq_true, ↓reduceIte]
    rw [hrecU, hrecV]
    by_cases hp0 : (partitionKind == 0) = true
    · simp only [hp0, ↓reduceIte]
      rw [h264Subblocks4x4_roundtrip, h264AssembleMbBlocks4_extract mb.y hy]
    · by_cases hp1 : (partitionKind == 1) = true
      · simp only [hp0, hp1, Bool.false_eq_true, ↓reduceIte]
        rw [h264Subblocks8x8_roundtrip, h264AssembleMbBlocks8_extract mb.y hy]
      · simp only [hp0, hp1, Bool.false_eq_true, ↓reduceIte, List.headD_cons]
        have hpy : (pred16x16 (lumaModes.headD 2) nbrs.leftY nbrs.topY nbrs.topLeftY
            nbrs.leftAvail nbrs.topAvail).size = 256 := by
          unfold pred16x16; exact Array.size_ofFn
        rw [h264SamplesLossless_roundtrip mb.y _ (by omega)]

def h264ValidYuv420pMbGateSpec : AVGateSpec H264Yuv420pMb
    (fun mb => mb.y.size = 256 ∧ mb.u.size = 64 ∧ mb.v.size = 64) where
  gate := H264Yuv420pMb.valid
  sound := by
    intro mb h
    unfold H264Yuv420pMb.valid at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  complete := by
    intro mb h
    unfold H264Yuv420pMb.valid
    simp [h.1, h.2.1, h.2.2]
  posWitness := { y := Array.replicate 256 128, u := Array.replicate 64 128, v := Array.replicate 64 128 }
  negWitness := { y := Array.replicate 16 128, u := Array.replicate 64 128, v := Array.replicate 64 128 }
  nonVacuous := by simp [H264Yuv420pMb.valid]
  tight := by simp [H264Yuv420pMb.valid]

theorem h264ChromaDcDequant_threshold30_no_rounding :
    chromaDcDequant 1 0 0 0 18 = (40, 40, 40, 40) ∧
    chromaDcDequant 1 0 0 0 26 = (104, 104, 104, 104) ∧
    chromaDcDequant 1 0 0 0 30 = (160, 160, 160, 160) ∧
    chromaDcDequant 1 0 0 0 39 = (448, 448, 448, 448) ∧
    chromaDcDequant 1 0 0 0 0 = (5, 5, 5, 5) := by
  decide

theorem h264LumaDcDequant_threshold36_witnesses :
    let dc1 : Array Int := #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    (lumaDcDequant dc1 10).getD 0 0 = 8 ∧
    (lumaDcDequant dc1 36).getD 0 0 = 160 ∧
    (lumaDcDequant dc1 40).getD 0 0 = 256 := by
  simp [lumaDcDequant, hadamard4x4, hadamard4Butterfly1D, qpDiv6, levelScale4x4,
        qpMod6, posClass4x4, v4x4Table, shlInt, asrInt, Array.getD]

theorem h264PosClass8x8_six_classes_bounded (i j : Fin 8) :
    posClass8x8 i.val j.val < 6 := by
  revert i j
  decide

theorem h264PosClass4x4_three_classes_bounded (i j : Fin 4) :
    posClass4x4 i.val j.val < 3 := by
  revert i j
  decide

theorem h264Idct4x4_zero_is_zero :
    idct4x4FromScaled (Array.replicate 16 0) = Array.replicate 16 0 := by
  decide

theorem h264Idct8x8_zero_is_zero :
    idct8x8FromScaled (Array.replicate 64 0) = Array.replicate 64 0 := by
  decide

theorem h264ZScan4AllowTopRight_bottom_right_corners_unavailable (topAv trAv : Bool) :
    zScan4AllowTopRight 3 topAv trAv = false ∧
    zScan4AllowTopRight 7 topAv trAv = false ∧
    zScan4AllowTopRight 11 topAv trAv = false ∧
    zScan4AllowTopRight 13 topAv trAv = false ∧
    zScan4AllowTopRight 15 topAv trAv = false ∧
    zScan4AllowTopRight 5 topAv trAv = trAv ∧
    zScan4AllowTopRight 0 topAv trAv = topAv := by
  cases topAv <;> cases trAv <;> decide

theorem h264Ipcm_raw_size (mb : H264Yuv420pMb) (hvalid : mb.valid = true) :
    (encodeIpcmMb420 mb).size = 384 := by
  unfold H264Yuv420pMb.valid at hvalid
  simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨hy, hu⟩, hv⟩
  unfold encodeIpcmMb420
  simp [Array.size_append, hy, hu, hv]

theorem h264Ipcm_raw_roundtrip (mb : H264Yuv420pMb) (hvalid : mb.valid = true) :
    decodeIpcmMb420 (encodeIpcmMb420 mb) = some mb := by
  unfold H264Yuv420pMb.valid at hvalid
  simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨hy, hu⟩, hv⟩
  unfold decodeIpcmMb420 encodeIpcmMb420
  have hsize : ((mb.y ++ mb.u ++ mb.v).size == 384) = true := by
    simp [Array.size_append, hy, hu, hv]
  simp only [hsize, ↓reduceIte, Option.some.injEq]
  have hyEq : (Array.ofFn fun i : Fin 256 => (mb.y ++ mb.u ++ mb.v).getD i.val 0) = mb.y := by
    apply Array.ext
    · simp [hy]
    · intro i hi1 hi2
      have hb : i < mb.y.size + (mb.u.size + mb.v.size) := by omega
      simp [Array.getElem_ofFn, Array.getD, Array.getElem_append, hb, hi2]
  have huEq : (Array.ofFn fun i : Fin 64 => (mb.y ++ mb.u ++ mb.v).getD (256 + i.val) 0) = mb.u := by
    apply Array.ext
    · simp [hu]
    · intro i hi1 hi2
      have hb : 256 + i < mb.y.size + (mb.u.size + mb.v.size) := by omega
      have hnlt : ¬ (256 + i < mb.y.size) := by omega
      have hsub : 256 + i - mb.y.size = i := by omega
      simp [Array.getElem_ofFn, Array.getD, Array.getElem_append, hb, hnlt, hsub, hi2]
  have hvEq : (Array.ofFn fun i : Fin 64 => (mb.y ++ mb.u ++ mb.v).getD (320 + i.val) 0) = mb.v := by
    apply Array.ext
    · simp [hv]
    · intro i hi1 hi2
      have hb : 320 + i < mb.y.size + (mb.u.size + mb.v.size) := by omega
      have hnlt1 : ¬ (320 + i < mb.y.size) := by omega
      have hnlt2 : ¬ (320 + i - mb.y.size < mb.u.size) := by omega
      have hsub : 320 + i - mb.y.size - mb.u.size = i := by omega
      simp [Array.getElem_ofFn, Array.getD, Array.getElem_append, hb, hnlt1, hnlt2, hsub]
  cases mb
  dsimp only at hyEq huEq hvEq
  rw [hyEq, huEq, hvEq]

private def ipcmPrefixBytes (padBits : Nat) : Array UInt8 :=
  (((BitWriter.empty.writeBitsMSB 0 padBits).writeUE ipcmMbTypeI).alignToByte).bytes.data

private theorem h264Ipcm_prefix_size (padBits : Fin 8) :
    (ipcmPrefixBytes padBits.val).size = 2 := by
  revert padBits
  decide

private theorem h264Ipcm_prefix_cz_bool (padBits : Fin 8) :
    (match BitReader.readUE.countZeros 6
        { slice := ByteSlice.ofByteArray { data := ipcmPrefixBytes padBits.val },
          bitOffset := padBits.val } 0 with
     | some (z, r1) => z == 4 && r1.bitOffset == padBits.val + 5
     | none => false) = true := by
  revert padBits
  decide

private theorem h264Ipcm_prefix_msb_bool (padBits : Fin 8) :
    (match BitReader.readBitsMSB
        { slice := ByteSlice.ofByteArray { data := ipcmPrefixBytes padBits.val },
          bitOffset := padBits.val + 5 } 4 with
     | some (suf, r2) => suf == 10 && r2.bitOffset == padBits.val + 9
     | none => false) = true := by
  revert padBits
  decide

private theorem h264Ipcm_pad9_align (padBits : Fin 8) :
    (if (padBits.val + 9) % 8 == 0 then padBits.val + 9 else (padBits.val + 9) + (8 - (padBits.val + 9) % 8)) = 16 := by
  revert padBits
  decide

private theorem ipcmCursorOk (off req tot : Nat)
    (h1 : off + req ≤ tot) (h2 : req ≤ 64) (h3 : tot < UInt64.size) :
    verifyBitstreamCursor off.toUInt64 req.toUInt64 tot.toUInt64 = 1 := by
  unfold verifyBitstreamCursor
  have ho : off.toUInt64.toNat = off := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by omega) h3)
  have hr : req.toUInt64.toNat = req := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by omega) h3)
  have ht : tot.toUInt64.toNat = tot := UInt64.toNat_ofNat_of_lt h3
  have c1 : off.toUInt64 ≤ tot.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, ho, ht]; omega
  have c2 : req.toUInt64 ≤ tot.toUInt64 - off.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ c1, hr, ht, ho]; omega
  have c3 : req.toUInt64 ≤ 64 := by
    rw [UInt64.le_iff_toNat_le, hr]; change req ≤ 64; omega
  simp [c1, c2, c3]

private theorem readBit_pre_eq (pre : Array UInt8) (off : Nat)
    (hoff : off + 1 ≤ pre.size * 8) (hsmall : pre.size * 8 < UInt64.size) :
    let sPre := ByteSlice.ofByteArray { data := pre }
    let bit := ((pre.getD (0 + off / 8) 0) >>> (7 - off % 8).toUInt8) &&& 1
    BitReader.readBit { slice := sPre, bitOffset := off } =
      some (bit, { slice := sPre, bitOffset := off + 1 }) := by
  dsimp only
  unfold BitReader.readBit BitReader.totalBits ByteSlice.ofByteArray ByteArray.size
  have hok : verifyBitstreamCursor off.toUInt64 1 (pre.size * 8).toUInt64 = 1 :=
    ipcmCursorOk off 1 (pre.size * 8) hoff (by omega) hsmall
  have hlt : off / 8 < pre.size := by omega
  simp only [hok, beq_self_eq_true, ↓reduceIte, hlt]

private theorem readBit_append_prefix (pre post : Array UInt8) (off : Nat)
    (hoff : off + 1 ≤ pre.size * 8)
    (hsmall : (pre.size + post.size) * 8 < UInt64.size) :
    let sPre := ByteSlice.ofByteArray { data := pre }
    let sFull := ByteSlice.ofByteArray { data := pre ++ post }
    let bit := ((pre.getD (0 + off / 8) 0) >>> (7 - off % 8).toUInt8) &&& 1
    BitReader.readBit { slice := sPre, bitOffset := off } =
      some (bit, { slice := sPre, bitOffset := off + 1 }) ∧
    BitReader.readBit { slice := sFull, bitOffset := off } =
      some (bit, { slice := sFull, bitOffset := off + 1 }) := by
  have hsz : (pre ++ post).size = pre.size + post.size := Array.size_append
  have hpre := readBit_pre_eq pre off hoff (by omega)
  have hfull := readBit_pre_eq (pre ++ post) off (by rw [hsz]; omega) (by rw [hsz]; exact hsmall)
  dsimp only at hpre hfull ⊢
  have hlt1 : off / 8 < pre.size := by omega
  have hlt2' : off / 8 < pre.size + post.size := by omega
  have hget : (pre ++ post).getD (0 + off / 8) 0 = pre.getD (0 + off / 8) 0 := by
    have hz : 0 + off / 8 = off / 8 := by omega
    rw [hz]
    simp [Array.getD, hlt1, hlt2']
  rw [hget] at hfull
  exact ⟨hpre, hfull⟩

private theorem readBitsMSBLoop_append_prefix (pre post : Array UInt8) (off0 : Nat) :
    ∀ (k cur : Nat) (acc : UInt64),
      cur + k ≤ pre.size * 8 →
      let sPre := ByteSlice.ofByteArray { data := pre }
      let sFull := ByteSlice.ofByteArray { data := pre ++ post }
      BitReader.readBitsMSB.loop { slice := sFull, bitOffset := off0 } k cur acc =
        let (v, _) := BitReader.readBitsMSB.loop { slice := sPre, bitOffset := off0 } k cur acc
        (v, { slice := sFull, bitOffset := cur + k })
  | 0, cur, acc, _ => by simp [BitReader.readBitsMSB.loop]
  | k + 1, cur, acc, hbound => by
    intro sPre sFull
    have hsz : (pre ++ post).size = pre.size + post.size := Array.size_append
    have hlt1 : cur / 8 < pre.size := by omega
    have hlt2 : cur / 8 < (pre ++ post).size := by rw [hsz]; omega
    have hlt2' : cur / 8 < pre.size + post.size := by omega
    have hget : (pre ++ post).getD (0 + cur / 8) 0 = pre.getD (0 + cur / 8) 0 := by
      have hz : 0 + cur / 8 = cur / 8 := by omega
      rw [hz]
      simp [Array.getD, hlt1, hlt2']
    unfold BitReader.readBitsMSB.loop
    dsimp only [sPre, sFull, ByteSlice.ofByteArray, ByteArray.size]
    simp only [hlt1, hlt2, ↓reduceIte, hget]
    have ih := readBitsMSBLoop_append_prefix pre post off0 k (cur + 1)
      ((acc <<< 1) ||| (((pre.getD (0 + cur / 8) 0) >>> (7 - cur % 8).toUInt8) &&& 1).toUInt64) (by omega)
    dsimp only [ByteSlice.ofByteArray, ByteArray.size] at ih
    rw [ih]
    have heq : cur + 1 + k = cur + (k + 1) := by omega
    simp [heq]

private theorem readBitsMSB_append_prefix (pre post : Array UInt8) (off n : Nat)
    (hoff : off + n ≤ pre.size * 8) (hn : n ≤ 64)
    (hsmall : (pre.size + post.size) * 8 < UInt64.size) :
    let sPre := ByteSlice.ofByteArray { data := pre }
    let sFull := ByteSlice.ofByteArray { data := pre ++ post }
    BitReader.readBitsMSB { slice := sFull, bitOffset := off } n =
      match BitReader.readBitsMSB { slice := sPre, bitOffset := off } n with
      | some (v, r1) => some (v, { slice := sFull, bitOffset := r1.bitOffset })
      | none => none := by
  dsimp only [BitReader.readBitsMSB, BitReader.totalBits, ByteSlice.ofByteArray, ByteArray.size]
  have hsz : (pre ++ post).size = pre.size + post.size := Array.size_append
  have hok1 : verifyBitstreamCursor off.toUInt64 n.toUInt64 (pre.size * 8).toUInt64 = 1 :=
    ipcmCursorOk off n (pre.size * 8) hoff hn (by omega)
  have hok2 : verifyBitstreamCursor off.toUInt64 n.toUInt64 ((pre ++ post).size * 8).toUInt64 = 1 := by
    rw [hsz]; exact ipcmCursorOk off n ((pre.size + post.size) * 8) (by omega) hn hsmall
  simp only [hok1, hok2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hloop := readBitsMSBLoop_append_prefix pre post off n off 0 hoff
  dsimp only [ByteSlice.ofByteArray, ByteArray.size] at hloop
  have hoff_pre :
      (BitReader.readBitsMSB.loop
        { slice := { ba := { data := pre }, off := 0, len := pre.size },
          bitOffset := off } n off 0).2.bitOffset = off + n := by
    let rec loop_off (k cur : Nat) (acc : UInt64) :
        (BitReader.readBitsMSB.loop
          { slice := { ba := { data := pre }, off := 0, len := pre.size },
            bitOffset := off } k cur acc).2.bitOffset = cur + k := by
      cases k with
      | zero => simp [BitReader.readBitsMSB.loop]
      | succ k' =>
        unfold BitReader.readBitsMSB.loop
        rw [loop_off k' (cur + 1)]
        omega
    exact loop_off n off 0
  rw [hloop, ← hoff_pre]

private theorem countZeros_append_prefix (pre post : Array UInt8) :
    ∀ (fuel off lz : Nat),
      off + fuel ≤ pre.size * 8 →
      (pre.size + post.size) * 8 < UInt64.size →
      let sPre := ByteSlice.ofByteArray { data := pre }
      let sFull := ByteSlice.ofByteArray { data := pre ++ post }
      BitReader.readUE.countZeros fuel { slice := sFull, bitOffset := off } lz =
        match BitReader.readUE.countZeros fuel { slice := sPre, bitOffset := off } lz with
        | some (z, r1) => some (z, { slice := sFull, bitOffset := r1.bitOffset })
        | none => none
  | 0, off, lz, _, _ => by simp [BitReader.readUE.countZeros]
  | fuel + 1, off, lz, hbound, hsmall => by
    intro sPre sFull
    have ⟨hpre, hfull⟩ := readBit_append_prefix pre post off (by omega) hsmall
    unfold BitReader.readUE.countZeros
    dsimp only [sPre, sFull]
    rw [hpre, hfull]
    by_cases hb1 : (((pre.getD (0 + off / 8) 0) >>> (7 - off % 8).toUInt8) &&& 1 == 1) = true
    · simp only [hb1, ↓reduceIte]
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      have ih := countZeros_append_prefix pre post fuel (off + 1) (lz + 1) (by omega) hsmall
      dsimp only at ih
      exact ih

private theorem readIpcmBytesList_exact (pre raw : Array UInt8) :
    ∀ (i k : Nat),
      i + k ≤ raw.size →
      readIpcmBytesList (ByteSlice.ofByteArray { data := pre ++ raw }) (pre.size + i) k =
        (raw.toList.drop i).take k
  | i, 0, _ => by simp [readIpcmBytesList]
  | i, k + 1, hbound => by
    unfold readIpcmBytesList
    have hi : i < raw.size := by omega
    have hget : (ByteSlice.ofByteArray { data := pre ++ raw }).getByteD (pre.size + i) 0 = raw[i]'hi := by
      unfold ByteSlice.getByteD ByteSlice.ofByteArray ByteArray.size
      have hsub : pre.size + i - pre.size = i := by omega
      simp [ByteArray.get!, hsub, hi]
    have hstep : pre.size + i + 1 = pre.size + (i + 1) := by omega
    rw [hget, hstep, readIpcmBytesList_exact pre raw (i + 1) k (by omega)]
    have hdrop : raw.toList.drop i = raw.toList[i] :: raw.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (l := raw.toList) (i := i) (by simpa using hi)
    rw [hdrop]
    simp [Array.getElem_toList]

theorem h264Ipcm_bits_roundtrip (padBits : Fin 8) (mb : H264Yuv420pMb) (hvalid : mb.valid = true) :
    let wPre := BitWriter.empty.writeBitsMSB 0 padBits.val
    let wPost := writeIpcmMb420Bits wPre mb
    let bs := wPost.toByteArray
    let rPre : BitReader := { slice := ByteSlice.ofByteArray bs, bitOffset := padBits.val }
    readIpcmMb420Bits rPre = some (mb, { slice := ByteSlice.ofByteArray bs, bitOffset := (2 + 384) * 8 }) := by
  have hrawSz : (encodeIpcmMb420 mb).size = 384 := h264Ipcm_raw_size mb hvalid
  have hrawRt : decodeIpcmMb420 (encodeIpcmMb420 mb) = some mb := h264Ipcm_raw_roundtrip mb hvalid
  have hpreSz := h264Ipcm_prefix_size padBits
  have hczBool := h264Ipcm_prefix_cz_bool padBits
  have hmsbBool := h264Ipcm_prefix_msb_bool padBits
  have hal9 := h264Ipcm_pad9_align padBits
  have hpBound : padBits.val < 8 := padBits.isLt
  have hsmall : ((ipcmPrefixBytes padBits.val).size + (encodeIpcmMb420 mb).size) * 8 < UInt64.size := by
    rw [hpreSz, hrawSz]; decide
  have hczApp :=
    countZeros_append_prefix (ipcmPrefixBytes padBits.val) (encodeIpcmMb420 mb)
      6 padBits.val 0 (by omega) hsmall
  have hmsbApp :=
    readBitsMSB_append_prefix (ipcmPrefixBytes padBits.val) (encodeIpcmMb420 mb)
      (padBits.val + 5) 4 (by omega) (by omega) hsmall
  dsimp only at hczApp hmsbApp
  cases hczM :
      BitReader.readUE.countZeros 6
        { slice := ByteSlice.ofByteArray { data := ipcmPrefixBytes padBits.val },
          bitOffset := padBits.val } 0 with
  | none =>
    rw [hczM] at hczBool
    exact False.elim (Bool.false_ne_true hczBool)
  | some zr =>
    rcases zr with ⟨z, r1⟩
    rw [hczM] at hczBool hczApp
    dsimp only at hczApp
    simp only [Bool.and_eq_true, beq_iff_eq] at hczBool
    rcases hczBool with ⟨rfl, hr1o⟩
    rw [hr1o] at hczApp
    cases hmsbM :
        BitReader.readBitsMSB
          { slice := ByteSlice.ofByteArray { data := ipcmPrefixBytes padBits.val },
            bitOffset := padBits.val + 5 } 4 with
    | none =>
      rw [hmsbM] at hmsbBool
      exact False.elim (Bool.false_ne_true hmsbBool)
    | some sr =>
      rcases sr with ⟨suf, r2⟩
      rw [hmsbM] at hmsbBool hmsbApp
      dsimp only at hmsbApp
      simp only [Bool.and_eq_true, beq_iff_eq] at hmsbBool
      rcases hmsbBool with ⟨rfl, hr2o⟩
      rw [hr2o] at hmsbApp
      have hbsEq : ((writeIpcmMb420Bits (BitWriter.empty.writeBitsMSB 0 padBits.val) mb).toByteArray) =
          { data := ipcmPrefixBytes padBits.val ++ encodeIpcmMb420 mb } := by
        unfold writeIpcmMb420Bits BitWriter.toByteArray ipcmPrefixBytes
        change (BitWriter.alignToByte
          { bytes := { data :=
              (((BitWriter.empty.writeBitsMSB 0 padBits.val).writeUE ipcmMbTypeI).alignToByte).bytes.data ++
                encodeIpcmMb420 mb },
            curByte := 0, bitsUsed := 0 }).bytes = _
        unfold BitWriter.alignToByte
        rfl
      dsimp only
      rw [hbsEq]
      unfold readIpcmMb420Bits
      let fullSlice := ByteSlice.ofByteArray { data := ipcmPrefixBytes padBits.val ++ encodeIpcmMb420 mb }
      have hrue :
          ({ slice := fullSlice, bitOffset := padBits.val } : BitReader).readUE 5 =
            some (ipcmMbTypeI, { slice := fullSlice, bitOffset := padBits.val + 9 }) := by
        unfold BitReader.readUE
        dsimp only
        rw [hczApp]
        change (match ({ slice := fullSlice, bitOffset := padBits.val + 5 } : BitReader).readBitsMSB 4 with
                | none => none
                | some (suffix, finalR) =>
                  some (((1 : UInt64) <<< (4 : Nat).toUInt64) - 1 + suffix, finalR)) = _
        rw [hmsbApp]
        dsimp only
        have hmEq : (((1 : UInt64) <<< (4 : Nat).toUInt64) - 1 + 10) = ipcmMbTypeI := by decide
        rw [hmEq]
      dsimp only
      rw [hrue]
      dsimp only
      have htypeEq : (ipcmMbTypeI != ipcmMbTypeI) = false := by decide
      simp only [htypeEq, Bool.false_eq_true, ↓reduceIte]
      have halOff :
          ({ slice := fullSlice, bitOffset := padBits.val + 9 } : BitReader).alignToByte =
            { slice := fullSlice, bitOffset := 16 } := by
        unfold BitReader.alignToByte
        dsimp only
        cases hrem : (padBits.val + 9) % 8 == 0
        · rw [hrem] at hal9
          simp only [Bool.false_eq_true, ↓reduceIte] at hal9 ⊢
          rw [hal9]
        · rw [hrem] at hal9
          simp only [↓reduceIte] at hal9 ⊢
          rw [hal9]
      rw [halOff]
      have hslen : fullSlice.len = 386 := by
        dsimp only [fullSlice]
        unfold ByteSlice.ofByteArray ByteArray.size
        dsimp only
        rw [Array.size_append, hpreSz, hrawSz]
      have hcond : ((16 : Nat) % 8 != 0 || 16 / 8 + 384 > fullSlice.len) = false := by
        rw [hslen]; decide
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have hbytes :=
        readIpcmBytesList_exact (ipcmPrefixBytes padBits.val) (encodeIpcmMb420 mb) 0 384 (by omega)
      have hzero : (ipcmPrefixBytes padBits.val).size + 0 = 16 / 8 := by omega
      rw [hzero] at hbytes
      have htake : ((encodeIpcmMb420 mb).toList.drop 0).take 384 = (encodeIpcmMb420 mb).toList := by
        have hlen : (encodeIpcmMb420 mb).toList.length = 384 := by simpa using hrawSz
        simp [List.take_of_length_le (Nat.le_of_eq hlen)]
      have htoArr : (encodeIpcmMb420 mb).toList.toArray = encodeIpcmMb420 mb := Array.toArray_toList
      rw [hbytes, htake, htoArr]
      change (match decodeIpcmMb420 (encodeIpcmMb420 mb) with
              | none => none
              | some mb' =>
                some (mb', ({ slice := fullSlice, bitOffset := (16 / 8 + 384) * 8 } : BitReader))) =
             some (mb, ({ slice := fullSlice, bitOffset := (2 + 384) * 8 } : BitReader))
      rw [hrawRt]

theorem h264Ipcm_byte_aligned (w : BitWriter) (mb : H264Yuv420pMb) :
    (writeIpcmMb420Bits w mb).bitsUsed = 0 := by
  unfold writeIpcmMb420Bits
  simp

theorem h264Ipcm_nz_16 (blkIdx : Nat) (h : blkIdx < 24) :
    ipcmBlockNonZeroCount blkIdx = 16 := by
  unfold ipcmBlockNonZeroCount
  simp [h]

theorem h264Ipcm_nz_beyond_chroma (blkIdx : Nat) (h : 24 ≤ blkIdx) :
    ipcmBlockNonZeroCount blkIdx = 0 := by
  unfold ipcmBlockNonZeroCount
  simp [h]

end LeanAV.H264IntraTransformProofs
