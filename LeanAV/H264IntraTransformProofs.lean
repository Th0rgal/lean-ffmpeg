import LeanAV.Spec
import LeanAV.Core
import LeanAV.H264IntraTransform

namespace LeanAV.H264IntraTransformProofs

open LeanAV.Spec
open LeanAV.Core
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

def h264IntraNxNLegalityGate (p : Nat × IntraNeighbors) : Bool :=
  isLegalIntraNxNMode p.1 p.2

def h264IntraNxNLegalityGateSpec : AVGateSpec (Nat × IntraNeighbors)
    (fun p => isLegalIntraNxNMode p.1 p.2 = true) where
  gate := h264IntraNxNLegalityGate
  sound := by intro p h; exact h
  complete := by intro p h; exact h
  posWitness := (2, { leftAvail := false, topAvail := false, topRightAvail := false,
                      topLeftAvail := false, left := #[], top := #[], topRight := #[], topLeft := 128 })
  negWitness := (4, { leftAvail := false, topAvail := true, topRightAvail := false,
                      topLeftAvail := false, left := #[], top := #[], topRight := #[], topLeft := 128 })
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

theorem h264LosslessIntraMb_encode_decode_roundtrip
    (mb : H264Yuv420pMb) (nbrs : H264IntraMbNeighbors)
    (partitionKind : Nat) (lumaModes : List Nat) (chromaMode : Nat)
    (hvalid : mb.valid = true) :
    decodeLosslessIntraMb (encodeLosslessIntraMb mb nbrs partitionKind lumaModes chromaMode) nbrs = mb := by
  unfold H264Yuv420pMb.valid at hvalid
  simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨hy, hu⟩, hv⟩
  have hpu : (predChroma chromaMode nbrs.leftU nbrs.topU nbrs.topLeftU nbrs.leftAvail nbrs.topAvail).size = 64 := by
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
  dsimp only
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

end LeanAV.H264IntraTransformProofs
