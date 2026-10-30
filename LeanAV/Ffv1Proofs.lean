import LeanAV.Spec
import LeanAV.Ffv1
import LeanAV.Ffv1Container
import LeanAV.Ffv1Pipeline
import LeanAV.Md5

namespace LeanAV.Ffv1Proofs

open LeanAV.Spec
open LeanAV.Ffv1
open LeanAV.Ffv1Container
open LeanAV.Ffv1Pipeline
open LeanAV.Md5

theorem ffv1PixelFormat_parse_toString_roundtrip (fmt : Ffv1PixelFormat) :
    Ffv1PixelFormat.parse fmt.toString = some fmt := by
  cases fmt <;> decide

theorem ffv1PixelFormat_rejects_zero_dims (fmt : Ffv1PixelFormat) (w h : Nat) :
    (w = 0 ∨ h = 0) → fmt.frameByteSize w h = none := by
  intro hzero
  cases hzero with
  | inl hw => subst hw; simp [Ffv1PixelFormat.frameByteSize]
  | inr hh => subst hh; simp [Ffv1PixelFormat.frameByteSize]

theorem ffv1PixelFormat_yuv420p_rejects_odd_width (w h : Nat)
    (hw : w % 2 = 1) :
    Ffv1PixelFormat.frameByteSize .yuv420p w h = none := by
  unfold Ffv1PixelFormat.frameByteSize
  by_cases hz : (w == 0 || h == 0) = true
  · simp [hz]
  · simp [hz]
    omega

theorem ffv1PixelFormat_gray_exact_bytes (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Ffv1PixelFormat.frameByteSize .gray w h = some (w * h) := by
  cases w with
  | zero => omega
  | succ w' =>
    cases h with
    | zero => omega
    | succ h' => simp [Ffv1PixelFormat.frameByteSize]

theorem ffv1PixelFormat_rgb24_exact_bytes (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Ffv1PixelFormat.frameByteSize .rgb24 w h = some (w * h * 3) := by
  cases w with
  | zero => omega
  | succ w' =>
    cases h with
    | zero => omega
    | succ h' => simp [Ffv1PixelFormat.frameByteSize]

theorem ffv1PixelFormat_bgr0_exact_bytes (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Ffv1PixelFormat.frameByteSize .bgr0 w h = some (w * h * 4) := by
  cases w with
  | zero => omega
  | succ w' =>
    cases h with
    | zero => omega
    | succ h' => simp [Ffv1PixelFormat.frameByteSize]

theorem ffv1PixelFormat_yuv420p_exact_bytes (w h : Nat)
    (hw : 0 < w) (hh : 0 < h) (hwe : w % 2 = 0) (hhe : h % 2 = 0) :
    Ffv1PixelFormat.frameByteSize .yuv420p w h = some (w * h + 2 * ((w / 2) * (h / 2))) := by
  unfold Ffv1PixelFormat.frameByteSize
  have hz : (w == 0 || h == 0) = false := by
    cases w <;> cases h <;> simp_all
  simp [hz, hwe, hhe]

theorem ffv1MedianPred_symm_left_top (l t lt : Int) :
    medianPredInt l t lt = medianPredInt t l lt := by
  unfold medianPredInt
  have hmin : min l t = min t l := Int.min_comm l t
  have hmax : max l t = max t l := Int.max_comm l t
  have hadd : l + t = t + l := Int.add_comm l t
  rw [hmin, hmax, hadd]

theorem ffv1MedianPred_idempotent_equal_neighbors (x lt : Int) :
    medianPredInt x x lt = x := by
  unfold medianPredInt
  omega

theorem ffv1MedianPred_bounds (l t lt : Int) :
    min l t ≤ medianPredInt l t lt ∧ medianPredInt l t lt ≤ max l t := by
  unfold medianPredInt
  omega

theorem ffv1Rct_inverse_forward_exact (r g b : Int) :
    let (y, cb, cr) := rctForward r g b
    rctInverse y cb cr = (r, g, b) := by
  dsimp [rctForward, rctInverse]
  have hcb : b - g + 256 - 256 = b - g := by omega
  have hcr : r - g + 256 - 256 = r - g := by omega
  rw [hcb, hcr]
  have hg : g + (b - g + (r - g)).fdiv 4 - (b - g + (r - g)).fdiv 4 = g := by omega
  rw [hg]
  have hr : r - g + g = r := by omega
  have hb : b - g + g = b := by omega
  rw [hr, hb]

theorem ffv1Rct_chroma_offset_9bit_range (r g b : Int)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 255)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 255)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 255) :
    let (_, cb, cr) := rctForward r g b
    1 ≤ cb ∧ cb ≤ 511 ∧ 1 ≤ cr ∧ cr ≤ 511 := by
  dsimp [rctForward]
  omega

theorem ffv1FoldSigned_8bit_bounds (diff : Int) :
    -128 ≤ foldSigned diff 8 ∧ foldSigned diff 8 < 128 := by
  unfold foldSigned
  change -128 ≤ (if diff % 256 ≥ 128 then diff % 256 - 256 else diff % 256) ∧
    (if diff % 256 ≥ 128 then diff % 256 - 256 else diff % 256) < 128
  omega

theorem ffv1FoldSigned_8bit_residual_reconstruct (sample pred : Int)
    (hs0 : 0 ≤ sample) (hs1 : sample < 256) :
    (pred + foldSigned (sample - pred) 8) % 256 = sample := by
  unfold foldSigned
  change (pred + (if (sample - pred) % 256 ≥ 128 then (sample - pred) % 256 - 256 else (sample - pred) % 256)) % 256 = sample
  omega

theorem ffv1FoldSigned_9bit_bounds (diff : Int) :
    -256 ≤ foldSigned diff 9 ∧ foldSigned diff 9 < 256 := by
  unfold foldSigned
  change -256 ≤ (if diff % 512 ≥ 256 then diff % 512 - 512 else diff % 512) ∧
    (if diff % 512 ≥ 256 then diff % 512 - 512 else diff % 512) < 256
  omega

theorem ffv1FoldSigned_9bit_residual_reconstruct (sample pred : Int)
    (hs0 : 0 ≤ sample) (hs1 : sample < 512) :
    (pred + foldSigned (sample - pred) 9) % 512 = sample := by
  unfold foldSigned
  change (pred + (if (sample - pred) % 512 ≥ 256 then (sample - pred) % 512 - 512 else (sample - pred) % 512)) % 512 = sample
  omega

theorem ffv1FoldSigned_neg_residual_reconstruct (sample pred : Int)
    (hs0 : 0 ≤ sample) (hs1 : sample < 256) :
    (pred - foldSigned (-(sample - pred)) 8) % 256 = sample := by
  unfold foldSigned
  change (pred - (if (-(sample - pred)) % 256 ≥ 128 then (-(sample - pred)) % 256 - 256 else (-(sample - pred)) % 256)) % 256 = sample
  omega

theorem ffv1SliceGrid_rejected_invalid_counts :
    sliceGridForCount 0 = none ∧
    sliceGridForCount 2 = none ∧
    sliceGridForCount 3 = none ∧
    sliceGridForCount 65 = none := by
  decide

theorem ffv1SliceGrid_supported_product_exact :
    sliceGridForCount 1 = some (1, 1) ∧
    sliceGridForCount 4 = some (2, 2) ∧
    sliceGridForCount 9 = some (3, 3) ∧
    sliceGridForCount 16 = some (4, 4) ∧
    sliceGridForCount 64 = some (8, 8) := by
  decide

def ffv1SliceCountValidGate (n : Nat) : Bool :=
  (sliceGridForCount n).isSome

def ffv1SliceCountValidSpec : AVGateSpec Nat (fun n => ∃ g, sliceGridForCount n = some g) where
  gate := ffv1SliceCountValidGate
  sound := by
    intro x hg
    unfold ffv1SliceCountValidGate at hg
    cases h : sliceGridForCount x with
    | none => simp [h] at hg
    | some g => exact ⟨g, rfl⟩
  complete := by
    intro x ⟨g, hg⟩
    unfold ffv1SliceCountValidGate
    simp [hg]
  posWitness := 4
  negWitness := 3
  nonVacuous := by decide
  tight := by decide

def ffv1PixelFormatValidGate (s : String) : Bool :=
  (Ffv1PixelFormat.parse s).isSome

def ffv1PixelFormatValidSpec : AVGateSpec String (fun s => ∃ fmt, Ffv1PixelFormat.parse s = some fmt) where
  gate := ffv1PixelFormatValidGate
  sound := by
    intro s hg
    unfold ffv1PixelFormatValidGate at hg
    cases h : Ffv1PixelFormat.parse s with
    | none => simp [h] at hg
    | some fmt => exact ⟨fmt, rfl⟩
  complete := by
    intro s ⟨fmt, hfmt⟩
    unfold ffv1PixelFormatValidGate
    simp [hfmt]
  posWitness := "yuv420p"
  negWitness := "nv12"
  nonVacuous := by decide
  tight := by decide

theorem ffv1EncoderConfig_rejects_bad_coder (fmt : Ffv1PixelFormat) (c slices ec gop : Nat)
    (hc : 2 < c) :
    makeEncoderConfiguration fmt c slices ec gop = .error "Invalid FFV1 coder code" := by
  unfold makeEncoderConfiguration
  simp [hc, Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1EncoderConfig_rejects_bad_slicecrc (fmt : Ffv1PixelFormat) (c slices ec gop : Nat)
    (hc : c ≤ 2) (hec : 1 < ec) :
    makeEncoderConfiguration fmt c slices ec gop = .error "Invalid FFV1 slicecrc mode" := by
  unfold makeEncoderConfiguration
  have hnc : ¬ (2 < c) := by omega
  simp [hnc, hec, Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1EncoderConfig_gop1_sets_intra (fmt : Ffv1PixelFormat) :
    (match makeEncoderConfiguration fmt 0 1 0 1 with
     | .ok cfg => cfg.intra == 1 && cfg.microVersion == 4 && cfg.bits == 8
     | .error _ => false) = true := by
  cases fmt <;> rfl

theorem ffv1EncoderConfig_gop12_clears_intra (fmt : Ffv1PixelFormat) :
    (match makeEncoderConfiguration fmt 2 4 1 12 with
     | .ok cfg => cfg.intra == 0 && cfg.horizontalSlices == 2 && cfg.verticalSlices == 2
     | .error _ => false) = true := by
  cases fmt <;> rfl

theorem ffv1EncodeFrameV3_rejects_zero_width (cfg : Configuration) (h : Nat)
    (fmt : Ffv1PixelFormat) (raw : ByteArray) (ctx : Nat) (kf : Bool) (gop : GopState) :
    encodeFrameV3 cfg 0 h fmt raw ctx kf gop = .error "Invalid FFV1 frame dimensions" := by
  unfold encodeFrameV3
  simp [Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1EncodeFrameV3_rejects_zero_height (cfg : Configuration) (w : Nat)
    (fmt : Ffv1PixelFormat) (raw : ByteArray) (ctx : Nat) (kf : Bool) (gop : GopState) :
    encodeFrameV3 cfg w 0 fmt raw ctx kf gop = .error "Invalid FFV1 frame dimensions" := by
  unfold encodeFrameV3
  simp [Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1EncodeFrameV3_rejects_oversized_width (cfg : Configuration) (w h : Nat)
    (fmt : Ffv1PixelFormat) (raw : ByteArray) (ctx : Nat) (kf : Bool) (gop : GopState)
    (hw : 16384 < w) :
    encodeFrameV3 cfg w h fmt raw ctx kf gop = .error "Invalid FFV1 frame dimensions" := by
  unfold encodeFrameV3
  simp [hw, Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1ContainerMux_rejects_unknown_format (s : LeanAV.Ffv1Container.Stream) :
    LeanAV.Ffv1Container.mux "mp4" s = .error "Unsupported FFV1 container format" := by
  rfl

theorem ffv1ContainerDemux_rejects_empty :
    LeanAV.Ffv1Container.demux ByteArray.empty = .error "Unrecognized FFV1 container" := by
  rfl

theorem ffv1WriteY4M_rejects_rgb24 (frames : Array ByteArray) (w h tn td sn sd : Nat) :
    writeY4M { width := w, height := h, timeNum := tn, timeDen := td, sarNum := sn, sarDen := sd,
               pixelFormat := .rgb24, frames := frames } =
      .error "Unsupported Y4M pixel format" := by
  unfold writeY4M
  simp [Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1WriteY4M_rejects_bgr0 (frames : Array ByteArray) (w h tn td sn sd : Nat) :
    writeY4M { width := w, height := h, timeNum := tn, timeDen := td, sarNum := sn, sarDen := sd,
               pixelFormat := .bgr0, frames := frames } =
      .error "Unsupported Y4M pixel format" := by
  unfold writeY4M
  simp [Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem ffv1WriteY4M_rejects_zero_timeNum (frames : Array ByteArray) (w h td sn sd : Nat) :
    writeY4M { width := w, height := h, timeNum := 0, timeDen := td, sarNum := sn, sarDen := sd,
               pixelFormat := .yuv420p, frames := frames } =
      .error "Invalid Y4M dimensions or rational" := by
  unfold writeY4M
  simp [Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

def ffv1CoderOptionGate (s : String) : Bool :=
  (parseCoderOption s).isSome

def ffv1CoderOptionGateSpec : AVGateSpec String (fun s => ∃ c, parseCoderOption s = some c) where
  gate := ffv1CoderOptionGate
  sound := by
    intro s hg
    unfold ffv1CoderOptionGate at hg
    cases h : parseCoderOption s with
    | none => simp [h] at hg
    | some c => exact ⟨c, rfl⟩
  complete := by
    intro s ⟨c, hc⟩
    unfold ffv1CoderOptionGate
    simp [hc]
  posWitness := "range_tab"
  negWitness := "arithmetic_unknown"
  nonVacuous := by decide
  tight := by decide

def ffv1NativePlanGate (args : List String) : Bool :=
  let plan := LeanAV.PlanIR.parseArgsToPlanIR args
  plan.errors.isEmpty &&
  plan.backend.tier == .independentVerified &&
  plan.backend.delegatedContainer == false

theorem ffv1NativePlanGate_accepts_encode_and_rejects_libx264 :
    ffv1NativePlanGate ["-i", "in.y4m", "-c:v", "ffv1", "-level", "3", "out.mkv"] = true ∧
    ffv1NativePlanGate ["-i", "in.y4m", "-c:v", "libx264", "out.mp4"] = false := by
  decide

def ffv1NativePlanGateSpec : AVGateSpec (List String)
    (fun args =>
      let plan := LeanAV.PlanIR.parseArgsToPlanIR args
      plan.errors.isEmpty = true ∧
      plan.backend.tier = LeanAV.PlanIR.BackendTier.independentVerified ∧
      plan.backend.delegatedContainer = false) where
  gate := ffv1NativePlanGate
  sound := by
    intro args hg
    unfold ffv1NativePlanGate at hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact ⟨hg.1.1, hg.1.2, hg.2⟩
  complete := by
    intro args ⟨hv, ht, hd⟩
    unfold ffv1NativePlanGate
    simp [hv, ht, hd]
  posWitness := ["-i", "in.y4m", "-c:v", "ffv1", "-level", "3", "out.mkv"]
  negWitness := ["-i", "in.y4m", "-c:v", "libx264", "out.mp4"]
  nonVacuous := by decide
  tight := by decide

theorem ffv1NativePlan_explicit_ffv1_disables_fallback :
    let plan := LeanAV.PlanIR.parseArgsToPlanIR ["-i", "in.y4m", "-c:v", "ffv1", "out.mkv"]
    plan.errors.isEmpty = true ∧
    plan.backend.tier = LeanAV.PlanIR.BackendTier.independentVerified ∧
    plan.backend.fallbackAllowed = false := by
  decide

theorem ffv1CliParser_parses_encode_and_rejects_multistream :
    (match parseFfv1CliArgs ["-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "16x16", "-r", "25",
                             "-i", "in.yuv", "-c:v", "ffv1", "-level", "3", "-coder", "1",
                             "-context", "1", "-slices", "4", "-slicecrc", "1", "-g", "3", "out.mkv"] with
     | some job => job.mode == .encode && job.coder == 2 && job.ctxModel == 1 &&
                   job.slices == 4 && job.sliceCrc == 1 && job.gopSize == 3
     | none => false) = true ∧
    parseFfv1CliArgs ["-i", "a.mkv", "-i", "b.mkv", "-c:v", "ffv1", "out.mkv"] = none ∧
    parseFfv1CliArgs ["-i", "a.mkv", "-vf", "scale=8:8", "-c:v", "ffv1", "out.mkv"] = none := by
  decide

theorem ffv1SrGolomb_decode_encode_roundtrip (i : Int) :
    srGolombMapFromNat (srGolombMapToNat i) = i := by
  unfold srGolombMapToNat srGolombMapFromNat
  by_cases hi : i < 0
  · simp [hi]
    omega
  · simp [hi]
    omega

theorem ffv1SrGolomb_encode_decode_roundtrip (v : Nat) :
    srGolombMapToNat (srGolombMapFromNat v) = v := by
  unfold srGolombMapFromNat srGolombMapToNat
  change (let half : Int := ↑(v / 2);
    let x := if (v % 2 == 1) = true then -(half + 1) else half;
    if x < 0 then (-x).toNat * 2 - 1 else x.toNat * 2) = v
  dsimp only
  split
  · next hb =>
    have hv : v % 2 = 1 := by simpa using hb
    split
    · omega
    · next hnlt => omega
  · next hb =>
    have hv : v % 2 ≠ 1 := by simpa using hb
    split
    · next hlt => omega
    · omega

theorem ffv1SrGolomb_encode_injective (a b : Int)
    (h : srGolombMapToNat a = srGolombMapToNat b) : a = b := by
  have ha := ffv1SrGolomb_decode_encode_roundtrip a
  have hb := ffv1SrGolomb_decode_encode_roundtrip b
  rw [← ha, ← hb, h]

theorem ffv1NativePlan_rawvideo_input_mkv_output :
    let plan := LeanAV.PlanIR.parseArgsToPlanIR
      ["-f", "rawvideo", "-pix_fmt", "rgb24", "-s", "64x48", "-r", "30",
       "-i", "in.rgb", "-c:v", "ffv1", "-level", "3", "out.mkv"]
    plan.errors.isEmpty = true ∧
    plan.backend.tier = LeanAV.PlanIR.BackendTier.independentVerified ∧
    (plan.outputs.map (·.format)) = ["matroska"] ∧
    plan.backend.fallbackAllowed = false := by
  decide

def ffv1ResidualEncodePixel8 (sample pred : Int) : Int :=
  foldSigned (sample - pred) 8

def ffv1ResidualDecodePixel8 (pred coded : Int) : Int :=
  (pred + coded) % 256

def ffv1ResidualEncodePlaneList : List (Int × Int) → List Int
  | [] => []
  | (s, p) :: rest => ffv1ResidualEncodePixel8 s p :: ffv1ResidualEncodePlaneList rest

def ffv1ResidualDecodePlaneList : List Int → List Int → List Int
  | [], _ => []
  | _, [] => []
  | p :: ps, c :: cs => ffv1ResidualDecodePixel8 p c :: ffv1ResidualDecodePlaneList ps cs

theorem ffv1ResidualPlaneList_decode_encode_roundtrip :
    ∀ (samples preds : List Int),
      samples.length = preds.length →
      (∀ s ∈ samples, 0 ≤ s ∧ s < 256) →
      ffv1ResidualDecodePlaneList preds (ffv1ResidualEncodePlaneList (samples.zip preds)) = samples
  | [], [], _, _ => rfl
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen
  | s :: ss, p :: ps, hlen, hbounds => by
    have hs : 0 ≤ s ∧ s < 256 := hbounds s List.mem_cons_self
    have hss : ∀ x ∈ ss, 0 ≤ x ∧ x < 256 := fun x hx => hbounds x (List.mem_cons_of_mem s hx)
    have hlen' : ss.length = ps.length := Nat.succ.inj hlen
    simp only [List.zip_cons_cons, ffv1ResidualEncodePlaneList, ffv1ResidualDecodePlaneList,
      ffv1ResidualEncodePixel8, ffv1ResidualDecodePixel8]
    rw [ffv1FoldSigned_8bit_residual_reconstruct s p hs.1 hs.2]
    rw [ffv1ResidualPlaneList_decode_encode_roundtrip ss ps hlen' hss]

structure Ffv1Yuv420pFrameSpec where
  width : Nat
  height : Nat
  ySamples : List Int
  uSamples : List Int
  vSamples : List Int
  hEven : width % 2 = 0 ∧ height % 2 = 0 ∧ 0 < width ∧ 0 < height
  hLenY : ySamples.length = width * height
  hLenU : uSamples.length = (width / 2) * (height / 2)
  hLenV : vSamples.length = (width / 2) * (height / 2)
  hBoundsY : ∀ x ∈ ySamples, 0 ≤ x ∧ x < 256
  hBoundsU : ∀ x ∈ uSamples, 0 ≤ x ∧ x < 256
  hBoundsV : ∀ x ∈ vSamples, 0 ≤ x ∧ x < 256

theorem ffv1Yuv420pFrameSpec_lossless_roundtrip (f : Ffv1Yuv420pFrameSpec)
    (yPreds uPreds vPreds : List Int)
    (hy : f.ySamples.length = yPreds.length)
    (hu : f.uSamples.length = uPreds.length)
    (hv : f.vSamples.length = vPreds.length) :
    ffv1ResidualDecodePlaneList yPreds (ffv1ResidualEncodePlaneList (f.ySamples.zip yPreds)) = f.ySamples ∧
    ffv1ResidualDecodePlaneList uPreds (ffv1ResidualEncodePlaneList (f.uSamples.zip uPreds)) = f.uSamples ∧
    ffv1ResidualDecodePlaneList vPreds (ffv1ResidualEncodePlaneList (f.vSamples.zip vPreds)) = f.vSamples := by
  exact ⟨ffv1ResidualPlaneList_decode_encode_roundtrip f.ySamples yPreds hy f.hBoundsY,
         ffv1ResidualPlaneList_decode_encode_roundtrip f.uSamples uPreds hu f.hBoundsU,
         ffv1ResidualPlaneList_decode_encode_roundtrip f.vSamples vPreds hv f.hBoundsV⟩

theorem ffv1RangeSplit_partition_and_bounds (rng state : Nat)
    (hr : 256 ≤ rng) (hs1 : 1 ≤ state) (hs2 : state ≤ 255) :
    let part := rng * state / 256
    let rem := rng - part
    1 ≤ part ∧ part < rng ∧ 1 ≤ rem ∧ rem < rng ∧ part + rem = rng := by
  dsimp only
  have hlo : 256 ≤ rng * state := by
    calc 256 = 256 * 1 := by omega
         _ ≤ rng * 1 := Nat.mul_le_mul_right 1 hr
         _ ≤ rng * state := Nat.mul_le_mul_left rng hs1
  have hhi : rng * state ≤ rng * 255 := Nat.mul_le_mul_left rng hs2
  omega

theorem ffv1RangeDecoder_refill_terminates_one_step (rng : Nat) (hr : 1 ≤ rng) :
    256 ≤ (if rng < 256 then rng * 256 else rng) := by
  split <;> omega

structure Ffv1RawYuv420pFrame where
  width : Nat
  height : Nat
  yPlane : List UInt8
  uPlane : List UInt8
  vPlane : List UInt8
  deriving DecidableEq, Repr

def Ffv1RawYuv420pFrame.valid (f : Ffv1RawYuv420pFrame) : Bool :=
  0 < f.width && 0 < f.height && f.width % 2 == 0 && f.height % 2 == 0 &&
  f.yPlane.length == f.width * f.height &&
  f.uPlane.length == (f.width / 2) * (f.height / 2) &&
  f.vPlane.length == (f.width / 2) * (f.height / 2)

def encodePlaneMedianResiduals8 : List UInt8 → UInt8 → List Int
  | [], _ => []
  | b :: bs, prev =>
    let s := Int.ofNat b.toNat
    let p := medianPredInt (Int.ofNat prev.toNat) 0 0
    foldSigned (s - p) 8 :: encodePlaneMedianResiduals8 bs b

def decodePlaneMedianResiduals8 : List Int → UInt8 → List UInt8
  | [], _ => []
  | c :: cs, prev =>
    let p := medianPredInt (Int.ofNat prev.toNat) 0 0
    let s := ((p + c) % 256).toNat.toUInt8
    s :: decodePlaneMedianResiduals8 cs s

theorem decodePlaneMedianResiduals8_roundtrip :
    ∀ (bs : List UInt8) (prev : UInt8),
      decodePlaneMedianResiduals8 (encodePlaneMedianResiduals8 bs prev) prev = bs
  | [], _ => rfl
  | b :: bs, prev => by
    have hb0 : (0 : Int) ≤ Int.ofNat b.toNat := Int.natCast_nonneg _
    have hb1 : Int.ofNat b.toNat < 256 := by
      exact Int.ofNat_lt.mpr b.toNat_lt
    simp only [encodePlaneMedianResiduals8, decodePlaneMedianResiduals8]
    rw [ffv1FoldSigned_8bit_residual_reconstruct (Int.ofNat b.toNat)
      (medianPredInt (Int.ofNat prev.toNat) 0 0) hb0 hb1]
    have hcast : (Int.ofNat b.toNat).toNat.toUInt8 = b := UInt8.ofNat_toNat
    rw [hcast, decodePlaneMedianResiduals8_roundtrip bs b]

structure Ffv1CodedYuv420pPacket where
  width : Nat
  height : Nat
  yCodes : List Nat
  uCodes : List Nat
  vCodes : List Nat
  deriving DecidableEq, Repr

def ffv1EncodeYuv420pPure (f : Ffv1RawYuv420pFrame) : Option Ffv1CodedYuv420pPacket :=
  if !f.valid then none
  else
    some {
      width := f.width
      height := f.height
      yCodes := (encodePlaneMedianResiduals8 f.yPlane 0).map srGolombMapToNat
      uCodes := (encodePlaneMedianResiduals8 f.uPlane 0).map srGolombMapToNat
      vCodes := (encodePlaneMedianResiduals8 f.vPlane 0).map srGolombMapToNat
    }

def ffv1DecodeYuv420pPure (pkt : Ffv1CodedYuv420pPacket) : Option Ffv1RawYuv420pFrame :=
  let out : Ffv1RawYuv420pFrame := {
    width := pkt.width
    height := pkt.height
    yPlane := decodePlaneMedianResiduals8 (pkt.yCodes.map srGolombMapFromNat) 0
    uPlane := decodePlaneMedianResiduals8 (pkt.uCodes.map srGolombMapFromNat) 0
    vPlane := decodePlaneMedianResiduals8 (pkt.vCodes.map srGolombMapFromNat) 0
  }
  if out.valid then some out else none

theorem srGolombMap_list_roundtrip :
    ∀ (xs : List Int), (xs.map srGolombMapToNat).map srGolombMapFromNat = xs
  | [] => rfl
  | x :: xs => by
    simp [ffv1SrGolomb_decode_encode_roundtrip, srGolombMap_list_roundtrip xs]

theorem ffv1DecodeYuv420pPure_encode_roundtrip (f : Ffv1RawYuv420pFrame)
    (hv : f.valid = true) :
    (ffv1EncodeYuv420pPure f).bind ffv1DecodeYuv420pPure = some f := by
  unfold ffv1EncodeYuv420pPure
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
  unfold ffv1DecodeYuv420pPure
  simp only [srGolombMap_list_roundtrip, decodePlaneMedianResiduals8_roundtrip]
  cases f
  simp only [hv, ↓reduceIte]

theorem ffv1RangeDecoder_refill_inv (r : RangeDecoder) (hr : 1 ≤ r.range) :
    256 ≤ r.refill.range ∧ r.refill.position ≤ r.position + 1 := by
  unfold RangeDecoder.refill
  split
  · dsimp only
    omega
  · omega

theorem ffv1RangeDecoder_getBit_range_inv (r : RangeDecoder) (state : Nat)
    (hr : 256 ≤ r.range) (hs1 : 1 ≤ state) (hs2 : state ≤ 255) :
    let (_, _, next) := r.getBit state
    256 ≤ next.range ∧ next.position ≤ r.position + 1 := by
  have hsplit := ffv1RangeSplit_partition_and_bounds r.range state hr hs1 hs2
  dsimp only at hsplit
  unfold RangeDecoder.getBit
  dsimp only
  split
  · exact ffv1RangeDecoder_refill_inv { r with range := r.range - r.range * state / 256 } hsplit.2.2.1
  · exact ffv1RangeDecoder_refill_inv
      { r with low := r.low - (r.range - r.range * state / 256), range := r.range * state / 256 } hsplit.1

end LeanAV.Ffv1Proofs
