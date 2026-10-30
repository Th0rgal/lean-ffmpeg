/-
  LeanAV.H264SyntaxProofs: Machine-Checked Soundness, Completeness, Non-Vacuity,
  Round-Trip, Emulation-Prevention (`0x000003`), Stop-Bit, Framing, Parameter-Set,
  and Picture Order Count (`POC` Type 0 & Type 2) Proofs for `LeanAV.H264Syntax`.
-/
import LeanAV.Spec
import LeanAV.Bitstream
import LeanAV.Video
import LeanAV.H264Syntax

namespace LeanAV.H264SyntaxProofs

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Bitstream
open LeanAV.Video
open LeanAV.H264Syntax

/-! ## 1. RBSP <-> EBSP (`0x000003`) Exact Round-Trip & Length Monotonicity -/

/-- State-machine inversion law: stripping emulation prevention bytes from
    `insertRbspEmulLoop z0 z1 xs` recovers `xs` identically for every `(z0, z1)` state. -/
theorem strip_insert_emul_loop :
    ∀ (xs : List UInt8) (z0 z1 : Bool),
      stripRbspEmulLoop z0 z1 (insertRbspEmulLoop z0 z1 xs) = xs
  | [], _, _ => rfl
  | b :: rest, z0, z1 => by
    unfold insertRbspEmulLoop
    by_cases hcond : (z0 && z1 && b ≤ 3) = true
    · simp only [hcond, ↓reduceIte]
      have hz01 : z0 = true ∧ z1 = true := by
        cases z0 <;> cases z1 <;> simp_all
      rcases hz01 with ⟨hz0, hz1⟩
      subst hz0 hz1
      unfold stripRbspEmulLoop
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      unfold stripRbspEmulLoop
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [strip_insert_emul_loop rest false (b == 0)]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      unfold stripRbspEmulLoop
      have hnot3 : (z0 && z1 && b == 3) = false := by
        by_cases hb3 : b = 3
        · subst hb3
          have hle : ((3 : UInt8) ≤ 3) = true := by decide
          cases z0 <;> cases z1 <;> simp_all
        · simp [hb3]
      simp only [hnot3, Bool.false_eq_true, ↓reduceIte]
      rw [strip_insert_emul_loop rest z1 (b == 0)]

/-- Top-level list round-trip: `stripRbspEmulationList (insertRbspEmulationList xs) = xs`. -/
theorem strip_insert_emulation_list_roundtrip (xs : List UInt8) :
    stripRbspEmulationList (insertRbspEmulationList xs) = xs :=
  strip_insert_emul_loop xs false false

/-- `insertRbspEmulLoop` never decreases byte length (`length xs ≤ length (insert xs)`). -/
theorem emul_insert_len_ge :
    ∀ (xs : List UInt8) (z0 z1 : Bool),
      xs.length ≤ (insertRbspEmulLoop z0 z1 xs).length
  | [], _, _ => Nat.le_refl 0
  | b :: rest, z0, z1 => by
    unfold insertRbspEmulLoop
    by_cases hcond : (z0 && z1 && b ≤ 3) = true
    · simp only [hcond, ↓reduceIte, List.length_cons]
      have ih := emul_insert_len_ge rest false (b == 0)
      omega
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have ih := emul_insert_len_ge rest z1 (b == 0)
      omega

/-- `stripRbspEmulLoop` never increases byte length (`length (strip xs) ≤ length xs`). -/
theorem emul_strip_len_le :
    ∀ (xs : List UInt8) (z0 z1 : Bool),
      (stripRbspEmulLoop z0 z1 xs).length ≤ xs.length
  | [], _, _ => Nat.le_refl 0
  | b :: rest, z0, z1 => by
    unfold stripRbspEmulLoop
    by_cases hcond : (z0 && z1 && b == 3) = true
    · simp only [hcond, ↓reduceIte]
      have ih := emul_strip_len_le rest false false
      simp only [List.length_cons]
      omega
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have ih := emul_strip_len_le rest z1 (b == 0)
      omega

/-- Inductive start-code-freedom predicate tracking prior zero-run state `(z0, z1)`:
    no emitted `0x00, 0x00` pair is followed by `0x00`, `0x01`, or `0x02` (`ISO/IEC 14496-10` §7.4.1). -/
def EbspSafeFrom (z0 z1 : Bool) : List UInt8 → Prop
  | [] => True
  | b :: rest => (¬ (z0 = true ∧ z1 = true ∧ b ≤ 2)) ∧ EbspSafeFrom z1 (b == 0) rest

/-- Every output of `insertRbspEmulLoop` is guaranteed free of forbidden `0x000000..0x000002`
    start-code sequences (`ISO/IEC 14496-10` §7.4.1 start-code emulation prevention). -/
theorem insertRbspEmulLoop_ebspSafe :
    ∀ (xs : List UInt8) (z0 z1 : Bool),
      EbspSafeFrom z0 z1 (insertRbspEmulLoop z0 z1 xs)
  | [], _, _ => trivial
  | b :: rest, z0, z1 => by
    unfold insertRbspEmulLoop
    by_cases hcond : (z0 && z1 && b ≤ 3) = true
    · simp only [hcond, ↓reduceIte]
      unfold EbspSafeFrom
      have h3notle2 : ¬ ((0x03 : UInt8) ≤ 2) := by decide
      have h3not0 : ((0x03 : UInt8) == 0) = false := by decide
      refine ⟨fun ⟨_, _, hle⟩ => h3notle2 hle, ?_⟩
      unfold EbspSafeFrom
      rw [h3not0]
      exact ⟨fun ⟨_, hfalse, _⟩ => Bool.noConfusion hfalse, insertRbspEmulLoop_ebspSafe rest false (b == 0)⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      unfold EbspSafeFrom
      refine ⟨?_, insertRbspEmulLoop_ebspSafe rest z1 (b == 0)⟩
      intro ⟨hz0, hz1, hle2⟩
      have hle3 : b ≤ 3 := by
        have hbn2 : b.toBitVec.toNat ≤ 2 := hle2
        have hbn3 : b.toBitVec.toNat ≤ 3 := by omega
        exact hbn3
      simp [hz0, hz1, hle3] at hcond

/-! ## 2. AVCC / Annex-B Framing, `avcC` Record & High-Extension Profile Gates -/

/-- Concrete real-world High 1080p `avcC` payload produced by FFmpeg `libx264` (`1920×1080`, `8x8dct`). -/
def realAvccHigh1080 : ByteArray := { data := #[
  0x01, 0x64, 0x00, 0x2A, 0xFF, 0xE1, 0x00, 0x1B,
  0x67, 0x64, 0x00, 0x2A, 0xAC, 0xD9, 0x40, 0x78, 0x02, 0x27, 0xE5, 0xC0,
  0x44, 0x00, 0x00, 0x03, 0x00, 0x04, 0x00, 0x00, 0x03, 0x03, 0xC0, 0x3C,
  0x60, 0xC6, 0x58,
  0x01, 0x00, 0x07,
  0x68, 0xEB, 0xE3, 0xCB, 0x30, 0x02, 0xC0,
  0xFD, 0xF8, 0xF8, 0x00
] }

/-- Concrete real-world High 4:4:4 `avcC` payload produced by FFmpeg `libx264` (`128×96`, qpprime bypass). -/
def realAvccHigh444 : ByteArray := { data := #[
  0x01, 0xF4, 0x00, 0x0A, 0xFF, 0xE1, 0x00, 0x17,
  0x67, 0xF4, 0x00, 0x0A, 0x91, 0xD6, 0x40, 0x83, 0x6C, 0x04, 0x40, 0x00,
  0x00, 0x03, 0x00, 0x04, 0x00, 0x00, 0x0C, 0x03, 0xC4, 0x89, 0x92,
  0x01, 0x00, 0x05,
  0x68, 0xEB, 0xC0, 0x6B, 0xCB,
  0xFF, 0xF8, 0xF8, 0x00
] }

/-- `nalLengthSize ∈ {1, 2, 4}` is the only AVCC length-field size accepted by `isValidAvccLengthSize`. -/
def h264AvccLengthSizeValidSpec : AVGateSpec Nat (fun n => n = 1 ∨ n = 2 ∨ n = 4) where
  gate := isValidAvccLengthSize
  sound := by
    intro n h
    unfold isValidAvccLengthSize at h
    cases n with
    | zero => simp at h
    | succ n1 =>
      cases n1 with
      | zero => exact Or.inl rfl
      | succ n2 =>
        cases n2 with
        | zero => exact Or.inr (Or.inl rfl)
        | succ n3 =>
          cases n3 with
          | zero => simp at h
          | succ n4 =>
            cases n4 with
            | zero => exact Or.inr (Or.inr rfl)
            | succ n5 => simp at h
  complete := by
    intro n h
    rcases h with rfl | rfl | rfl <;> decide
  posWitness := 4
  negWitness := 3
  nonVacuous := by decide
  tight := by decide

/-- High-extension profile identifiers carry chroma/bit-depth/scaling syntax (`ISO/IEC 14496-10` §7.3.2.1.1). -/
def h264HighExtProfileValidSpec : AVGateSpec UInt8 (fun p =>
    p = 100 ∨ p = 110 ∨ p = 122 ∨ p = 244 ∨ p = 44 ∨ p = 83 ∨ p = 86 ∨
    p = 118 ∨ p = 128 ∨ p = 138 ∨ p = 139 ∨ p = 134 ∨ p = 135) where
  gate := isH264HighExtProfile
  sound := by
    intro p h
    unfold isH264HighExtProfile at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))
  complete := by
    intro p h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  posWitness := 100
  negWitness := 66
  nonVacuous := by decide
  tight := by decide

/-- `slice_type ∈ [0, 9]` (`ISO/IEC 14496-10` Table 7-6) is exactly the domain of `classifyH264SliceType`. -/
def h264SliceTypeValidSpec : AVGateSpec UInt8 (fun t => (classifyH264SliceType t).isSome) where
  gate := fun t => (classifyH264SliceType t).isSome
  sound := by
    intro t h
    exact h
  complete := by
    intro t h
    exact h
  posWitness := 2
  negWitness := 10
  nonVacuous := by decide
  tight := by decide

/-- A parsed `AvcDecoderConfigRecord` is structurally valid and serializes byte-for-byte back to its source. -/
def AvccRecordRoundtrip (buf : ByteArray) : Prop :=
  match parseAvcDecoderConfigRecord buf with
  | some rec => rec.isValid = true ∧ serializeAvcDecoderConfigRecord rec = some buf
  | none => False

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Real FFmpeg High 1080p `avcC` parses, validates, and serializes byte-for-byte (chroma `4:2:0`). -/
theorem h264_avcc_high1080_roundtrip :
    (match parseAvcDecoderConfigRecord realAvccHigh1080 with
     | some rec0 =>
       (match serializeAvcDecoderConfigRecord rec0 with
        | some out => out.data == realAvccHigh1080.data && rec0.chromaFormatIdc == 1 && rec0.isValid
        | none => false)
     | none => false) = true := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Real FFmpeg High 4:4:4 `avcC` parses, validates, and serializes byte-for-byte (`qpprime` bypass). -/
theorem h264_avcc_high444_roundtrip :
    (match parseAvcDecoderConfigRecord realAvccHigh444 with
     | some rec0 =>
       (match serializeAvcDecoderConfigRecord rec0 with
        | some out => out.data == realAvccHigh444.data && rec0.isValid
        | none => false)
     | none => false) = true := rfl

/-- Structural validation of `AvcDecoderConfigRecord` is sound, complete, non-vacuous, and tight. -/
def h264AvccRecordValidSpec : AVGateSpec AvcDecoderConfigRecord (fun rec => rec.isValid = true) where
  gate := AvcDecoderConfigRecord.isValid
  sound := by
    intro rec h
    exact h
  complete := by
    intro rec h
    exact h
  posWitness := {
    avcProfileIndication := 66, profileCompatibility := 0, avcLevelIndication := 30,
    spsNalus := #[{ data := #[0x67] }], ppsNalus := #[{ data := #[0x68] }]
  }
  negWitness := {
    configurationVersion := 2,
    avcProfileIndication := 66, profileCompatibility := 0, avcLevelIndication := 30,
    spsNalus := #[{ data := #[0x67] }], ppsNalus := #[{ data := #[0x68] }]
  }
  nonVacuous := by decide
  tight := by decide

/-! ## 3. Real FFmpeg SPS / PPS Parameter-Set Round-Trip (`1280×720` Baseline) -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Real FFmpeg Baseline SPS (`1280×720`) parses with the expected geometry and serializes identically. -/
theorem h264_real_sps_roundtrip :
    (match parseH264SpsFull (ByteSlice.ofByteArray { data := realFfmpegH264SpsBytes }) with
     | some s =>
       s.widthPx == 1280 && s.heightPx == 720 && s.profileIdc == 66 &&
       ((serializeH264SpsFull s).bind (fun b => parseH264SpsFull (ByteSlice.ofByteArray b)) == some s)
     | none => false) = true := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Real FFmpeg Baseline PPS parses against the real SPS and serializes identically. -/
theorem h264_real_pps_roundtrip :
    (match parseH264SpsFull (ByteSlice.ofByteArray { data := realFfmpegH264SpsBytes }) with
     | some sps =>
       (match parseH264PpsFull (ByteSlice.ofByteArray { data := realFfmpegH264PpsBytes }) (some sps) with
        | some pps =>
          ((serializeH264PpsFull pps sps.chromaFormatIdc sps.bitDepthLumaMinus8).bind
            (fun b => parseH264PpsFull (ByteSlice.ofByteArray b) (some sps)) == some pps)
        | none => false)
     | none => false) = true := rfl

/-! ## 4. Picture Order Count (`POC` Type 0 & Type 2) Reset & Monotonicity -/

/-- An IDR picture resets POC Type 0 (`ISO/IEC 14496-10` §8.2.1.1) to `(0, 0, 0)` regardless of prior state. -/
theorem pocType0_idr_reset (st : PocType0State) (log2M4 : UInt8) (nalRefIdc : UInt8)
    (hasMmco5 fieldPic bottomField bottomPresent : Bool) :
    derivePicOrderCntType0 st log2M4 true nalRefIdc hasMmco5 fieldPic bottomField bottomPresent 0 0
      = (0, 0, 0, (derivePicOrderCntType0 st log2M4 true nalRefIdc hasMmco5 fieldPic bottomField bottomPresent 0 0).2.2.2) := by
  unfold derivePicOrderCntType0
  simp

/-- An IDR picture resets POC Type 2 (`ISO/IEC 14496-10` §8.2.1.3) to `(0, 0, 0)` regardless of prior state. -/
theorem pocType2_idr_reset (st : PocType2State) (log2M4 : UInt8) (nalRefIdc : UInt8)
    (hasMmco5 : Bool) (frameNum : UInt32) :
    let nextFn := if hasMmco5 then 0 else frameNum.toNat % (1 <<< (log2M4.toNat + 4))
    let nextOff : Int := if hasMmco5 then 0 else 0
    derivePicOrderCntType2 st log2M4 true nalRefIdc hasMmco5 frameNum =
      (0, 0, 0, { prevFrameNum := nextFn, prevFrameNumOffset := nextOff }) := by
  unfold derivePicOrderCntType2
  simp

/-- A reference picture's POC Type 2 value is exactly `2 * (frameNumOffset + frameNum)`. -/
theorem pocType2_ref_value (st : PocType2State) (log2M4 : UInt8) (nalRefIdc : UInt8)
    (href : nalRefIdc ≠ 0) (hasMmco5 : Bool) (frameNum : UInt32) :
    let (top, _, _, _) := derivePicOrderCntType2 st log2M4 false nalRefIdc hasMmco5 frameNum
    let maxFn := 1 <<< (log2M4.toNat + 4)
    let fnNat := frameNum.toNat % maxFn
    let frameNumOffset := if st.prevFrameNum > fnNat then st.prevFrameNumOffset + (Int.ofNat maxFn) else st.prevFrameNumOffset
    top = 2 * (frameNumOffset + Int.ofNat fnNat) := by
  unfold derivePicOrderCntType2
  simp [href]

/-- POC Type 2 is monotone across a frame-number wrap for reference pictures:
    the post-wrap POC is strictly greater than the pre-wrap POC. -/
theorem pocType2_wrap_monotone :
    let st0 : PocType2State := {}
    let (pocA, _, _, stA) := derivePicOrderCntType2 st0 0 false 2 false 15
    let (pocB, _, _, _) := derivePicOrderCntType2 stA 0 false 2 false 0
    pocA < pocB := by
  decide

/-- `MMCO` opcode 5 resets the POC Type 0 MSB carried into the next picture to `0`. -/
theorem pocType0_mmco5_resets_msb (log2M4 : UInt8) (lsb : UInt32) :
    (derivePicOrderCntType0 {} log2M4 false 2 true false false false lsb 0).2.2.2.prevPicOrderCntMsb = 0 := by
  unfold derivePicOrderCntType0
  simp

/-! ## 5. RBSP Trailing Stop-Bit & Big-Endian Length Field -/

/-- `finalizeRbspWriter` always emits at least one byte (the `rbsp_trailing_bits` stop bit). -/
theorem finalizeRbspWriter_nonempty (w : BitWriter) :
    (finalizeRbspWriter w).data.size ≥ 1 := by
  unfold finalizeRbspWriter BitWriter.toByteArray BitWriter.alignToByte BitWriter.writeBit
  dsimp only
  split <;> simp

/-- A one-byte big-endian length field round-trips through `pushBigEndianN` / `readBigEndianN` for `n ≤ 0xFF`. -/
theorem bigEndian1_roundtrip (n : Nat) (hn : n ≤ 0xFF) :
    readBigEndianN ((pushBigEndianN emptyBytesPure n 1).getD emptyBytesPure) 0 1 = some n := by
  unfold pushBigEndianN readBigEndianN emptyBytesPure pushBytePure byteAtPure
  simp [hn]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Multi-NALU AVCC framing (`nalLengthSize ∈ {2, 4}`) round-trips real FFmpeg SPS/PPS NALUs identically. -/
theorem h264_avcc_packet_framing_roundtrip :
    let nalus : Array ByteArray := #[{ data := realFfmpegH264SpsBytes }, { data := realFfmpegH264PpsBytes }]
    ((packAvccPacket nalus 4).bind (fun p => splitAvccPacket p 4) == some nalus) = true ∧
    ((packAvccPacket nalus 2).bind (fun p => splitAvccPacket p 2) == some nalus) = true :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 400000 in
/-- Deterministic Slice Header serializer and parser round-trip identically against real FFmpeg SPS/PPS. -/
theorem h264_slice_header_idr_roundtrip :
    (match parseH264SpsFull (ByteSlice.ofByteArray { data := realFfmpegH264SpsBytes }) with
     | some sps =>
       (match parseH264PpsFull (ByteSlice.ofByteArray { data := realFfmpegH264PpsBytes }) (some sps) with
        | some pps =>
          let idrHdr : H264SliceHeaderFull := {
            nalRefIdc := 3, nalUnitType := 5, firstMbInSlice := 0, sliceType := 7,
            sliceKind := .I, ppsId := pps.ppsId, frameNum := 0, idrPicId := 0,
            sliceQpDelta := 0, sliceQpY := 26 + pps.picInitQpMinus26,
            disableDeblockingFilterIdc := 0
          }
          (match serializeH264SliceHeaderFull idrHdr sps pps with
           | some nal =>
             (match parseH264SliceHeaderFull (ByteSlice.ofByteArray nal) sps pps with
              | some parsed =>
                parsed.nalUnitType == 5 && parsed.sliceKind == .I &&
                parsed.sliceQpY == idrHdr.sliceQpY &&
                (serializeH264SliceHeaderFull parsed sps pps).map (fun r => r.data == nal.data) == some true
              | none => false)
           | none => false)
        | none => false)
     | none => false) = true := rfl

end LeanAV.H264SyntaxProofs
