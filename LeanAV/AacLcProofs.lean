import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Bitstream
import LeanAV.AacLc
import LeanAV.PlanIR

namespace LeanAV.AacLcProofs

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Bitstream
open LeanAV.AacLc

set_option maxRecDepth 400000
set_option maxHeartbeats 12800000

theorem aacSampleRate_all_indices_roundtrip :
    ((List.range 13).all fun i =>
      match aacSampleRateFromIndex i.toUInt8 with
      | some sr => aacSampleRateToIndex sr == some i.toUInt8
      | none => false) = true ∧
    aacSampleRateFromIndex 13 = none ∧
    aacSampleRateToIndex 0 = none ∧
    aacSampleRateToIndex 47999 = none := by
  decide

theorem aacLcAsc_all_rates_mono_stereo_roundtrip :
    ((List.range 13).all fun i =>
      let sfi := i.toUInt8
      let m : AacLcAsc := { samplingFrequencyIndex := sfi, channelConfiguration := 1 }
      let st : AacLcAsc := { samplingFrequencyIndex := sfi, channelConfiguration := 2 }
      decodeAacLcAscBytes (encodeAacLcAscBytes m) == some m &&
      decodeAacLcAscBytes (encodeAacLcAscBytes st) == some st) = true := by
  decide

theorem aacLcAsc_rejects_main_profile :
    decodeAacLcAscBytes (encodeAacLcAscBytes { audioObjectType := 1, samplingFrequencyIndex := 3, channelConfiguration := 2 }) = none := by
  decide

theorem aacLcAsc_rejects_short_list :
    decodeAacLcAscBytes [0x12] = none := by
  decide

theorem aacAdtsCrc16_init_xorout_empty :
    aacAdtsCrc16Bytes [] = 0 := by
  decide

theorem aacAdtsCrc16_standard_vector_123456789 :
    let vec : List UInt8 := [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]
    aacAdtsCrc16Bytes vec = 0x5118 ∧
    aacAdtsCrc16Slice (ByteSlice.ofByteArray (ByteArray.mk vec.toArray)) = 0x5118 := by
  decide

theorem aacAdtsCrc16_mux_demux_roundtrip_and_tamper :
    let raw := ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]
    (match muxAdtsFrame 3 2 raw true with
     | none => false
     | some frm =>
       let ok :=
         match demuxAdtsStream (ByteSlice.ofByteArray frm) true with
         | some (hdr, payloads) =>
           !hdr.protectionAbsent && hdr.crc16 == 0x5118 && payloads.size == 1 &&
           (let p := payloads.getD 0 (ByteSlice.ofByteArray ByteArray.empty)
            p.ba.extract p.off (p.off + p.len) == raw)
         | none => false
       let tampered := frm.set! 9 (frm.data.getD 9 0 ^^^ 0x01)
       let rejected := (demuxAdtsStream (ByteSlice.ofByteArray tampered) true).isNone
       ok && rejected) = true := by
  decide

theorem aacAdtsCrc16_detects_bitflip :
    aacAdtsCrc16Bytes [0x12, 0x10, 0x56, 0xE5, 0x00] ≠
      aacAdtsCrc16Bytes [0x13, 0x10, 0x56, 0xE5, 0x00] := by
  decide

theorem aacAdtsHeader_all_rates_crc_and_nocrc_roundtrip :
    ((List.range 13).all fun i =>
      let sfi := i.toUInt8
      let h7 : AacLcAdtsHeader := {
        mpegVersion := 0, protectionAbsent := true, profileObjectType := 2,
        samplingFrequencyIdx := sfi, channelConfiguration := 2, frameLength := 256,
        bufferFullness := 0x7FF, numRawBlocksMinus1 := 0, crc16 := 0
      }
      let h9 : AacLcAdtsHeader := {
        mpegVersion := 1, protectionAbsent := false, profileObjectType := 2,
        samplingFrequencyIdx := sfi, channelConfiguration := 1, frameLength := 384,
        bufferFullness := 0x7FF, numRawBlocksMinus1 := 0, crc16 := 0xA55A
      }
      let dec (h : AacLcAdtsHeader) :=
        decodeAacLcAdtsHeader (ByteSlice.ofByteArray (ByteArray.mk (encodeAacLcAdtsHeaderBytes h).toArray))
      dec h7 == some h7 && dec h9 == some h9) = true := by
  decide

theorem aacAdtsHeader_rejects_bad_sync :
    decodeAacLcAdtsHeader (ByteSlice.ofByteArray (ByteArray.mk #[0xFE, 0xF1, 0x4C, 0x80, 0x02, 0x1F, 0xFC])) = none := by
  decide

theorem aacAdtsHeader_rejects_layer :
    decodeAacLcAdtsHeader (ByteSlice.ofByteArray (ByteArray.mk #[0xFF, 0xF3, 0x4C, 0x80, 0x02, 0x1F, 0xFC])) = none := by
  decide

def aacLcAscValidGate (asc : AacLcAsc) : Bool :=
  isValidAacLcAsc asc

def aacLcAscValidSpec :
    AVGateSpec AacLcAsc (fun asc =>
      asc.audioObjectType = 2 ∧
      asc.samplingFrequencyIndex ≤ 12 ∧
      (asc.channelConfiguration = 1 ∨ asc.channelConfiguration = 2) ∧
      asc.frameLengthFlag = false ∧
      asc.dependsOnCoreCoder = false ∧
      asc.extensionFlag = false) where
  gate := aacLcAscValidGate
  sound _ hg := by
    unfold aacLcAscValidGate isValidAacLcAsc at hg
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1.1.1, hg.1.1.1.1.2, hg.1.1.1.2, hg.1.1.2, hg.1.2, hg.2⟩
  complete _ hs := by
    rcases hs with ⟨h1, h2, h3, h4, h5, h6⟩
    unfold aacLcAscValidGate isValidAacLcAsc
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  posWitness := { samplingFrequencyIndex := 3, channelConfiguration := 2 }
  negWitness := { audioObjectType := 1, samplingFrequencyIndex := 3, channelConfiguration := 2 }
  nonVacuous := by decide
  tight := by decide

theorem aacLcAscValidSpec_iff (asc : AacLcAsc) :
    aacLcAscValidSpec.gate asc = true ↔
      (asc.audioObjectType = 2 ∧
       asc.samplingFrequencyIndex ≤ 12 ∧
       (asc.channelConfiguration = 1 ∨ asc.channelConfiguration = 2) ∧
       asc.frameLengthFlag = false ∧
       asc.dependsOnCoreCoder = false ∧
       asc.extensionFlag = false) :=
  aacLcAscValidSpec.iff_safe asc

def aacLcAdtsHeaderValidGate (h : AacLcAdtsHeader) : Bool :=
  isValidAacLcAdtsHeader h

def aacLcAdtsHeaderValidSpec :
    AVGateSpec AacLcAdtsHeader (fun h =>
      (h.mpegVersion = 0 ∨ h.mpegVersion = 1) ∧
      h.profileObjectType = 2 ∧
      h.samplingFrequencyIdx ≤ 12 ∧
      (h.channelConfiguration = 1 ∨ h.channelConfiguration = 2) ∧
      h.headerBytes ≤ h.frameLength.toNat ∧
      h.frameLength.toNat ≤ 8191 ∧
      h.bufferFullness ≤ 0x07FF ∧
      h.numRawBlocksMinus1 = 0) where
  gate := aacLcAdtsHeaderValidGate
  sound _ hg := by
    unfold aacLcAdtsHeaderValidGate isValidAacLcAdtsHeader at hg
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1.1.1.1.1, hg.1.1.1.1.1.1.2, hg.1.1.1.1.1.2, hg.1.1.1.1.2,
           hg.1.1.1.2, hg.1.1.2, hg.1.2, hg.2⟩
  complete _ hs := by
    rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    unfold aacLcAdtsHeaderValidGate isValidAacLcAdtsHeader
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  posWitness := { samplingFrequencyIdx := 3, channelConfiguration := 2, frameLength := 7 }
  negWitness := { samplingFrequencyIdx := 15, channelConfiguration := 2, frameLength := 7 }
  nonVacuous := by decide
  tight := by decide

theorem aacLcAdtsHeaderValidSpec_iff (h : AacLcAdtsHeader) :
    aacLcAdtsHeaderValidSpec.gate h = true ↔
      ((h.mpegVersion = 0 ∨ h.mpegVersion = 1) ∧
       h.profileObjectType = 2 ∧
       h.samplingFrequencyIdx ≤ 12 ∧
       (h.channelConfiguration = 1 ∨ h.channelConfiguration = 2) ∧
       h.headerBytes ≤ h.frameLength.toNat ∧
       h.frameLength.toNat ≤ 8191 ∧
       h.bufferFullness ≤ 0x07FF ∧
       h.numRawBlocksMinus1 = 0) :=
  aacLcAdtsHeaderValidSpec.iff_safe h

def aacSwbMonotone (tbl : List Nat) (expectedEnd : Nat) : Bool :=
  match tbl with
  | [] => false
  | a :: rest =>
    a == 0 &&
    (rest.foldl (fun acc b =>
      match acc with
      | none => none
      | some prev => if prev < b && prev % 4 == 0 && b % 4 == 0 then some b else none)
      (some a)) == some expectedEnd

def aacSwbTableValidGate (sfi : UInt8) : Bool :=
  match aacSwbOffsetsLong sfi, aacSwbOffsetsShort sfi with
  | some long, some short => aacSwbMonotone long.toList 1024 && aacSwbMonotone short.toList 128
  | _, _ => false

def aacSwbTableValidSpec :
    AVGateSpec UInt8 (fun sfi =>
      ∃ long short, aacSwbOffsetsLong sfi = some long ∧ aacSwbOffsetsShort sfi = some short ∧
        aacSwbMonotone long.toList 1024 = true ∧ aacSwbMonotone short.toList 128 = true) where
  gate := aacSwbTableValidGate
  sound sfi hg := by
    unfold aacSwbTableValidGate at hg
    cases hl : aacSwbOffsetsLong sfi with
    | none => simp [hl] at hg
    | some long =>
      cases hs : aacSwbOffsetsShort sfi with
      | none => simp [hl, hs] at hg
      | some short =>
        simp only [hl, hs, Bool.and_eq_true] at hg
        exact ⟨long, short, rfl, rfl, hg.1, hg.2⟩
  complete sfi h := by
    rcases h with ⟨long, short, hl, hs, hlong, hshort⟩
    unfold aacSwbTableValidGate
    simp [hl, hs, hlong, hshort]
  posWitness := 3
  negWitness := 13
  nonVacuous := by decide
  tight := by decide

theorem aacSwbTableValidSpec_iff (sfi : UInt8) :
    aacSwbTableValidSpec.gate sfi = true ↔
      ∃ long short, aacSwbOffsetsLong sfi = some long ∧ aacSwbOffsetsShort sfi = some short ∧
        aacSwbMonotone long.toList 1024 = true ∧ aacSwbMonotone short.toList 128 = true :=
  aacSwbTableValidSpec.iff_safe sfi

theorem aacSwbOffsets_all_rates_valid :
    ((List.range 13).all fun i => aacSwbTableValidGate i.toUInt8) = true := by
  decide

theorem aacDequantCoeff_zero (sf : Nat) :
    aacDequantizeCoeff 0 sf = 0.0 := by
  unfold aacDequantizeCoeff
  rfl

theorem aacValidQuantCoeff_bounds (q : Int) :
    isValidAacQuantCoeff q = true ↔ -8191 ≤ q ∧ q ≤ 8191 := by
  unfold isValidAacQuantCoeff
  simp

theorem aacValidScaleFactor_bounds (sf : Nat) :
    isValidAacScaleFactor sf = true ↔ sf ≤ 255 := by
  unfold isValidAacScaleFactor
  simp

theorem aacWindowSequence_roundtrip (s : AacWindowSequence) :
    AacWindowSequence.ofUInt8? s.toUInt8 = some s := by
  cases s <;> decide

theorem aacWindowSequence_rejects_four :
    AacWindowSequence.ofUInt8? 4 = none := by
  decide

theorem aacWindowTransition_legal_eight :
    isValidAacWindowTransition .onlyLong .onlyLong = true ∧
    isValidAacWindowTransition .onlyLong .longStart = true ∧
    isValidAacWindowTransition .longStart .eightShort = true ∧
    isValidAacWindowTransition .longStart .longStop = true ∧
    isValidAacWindowTransition .eightShort .eightShort = true ∧
    isValidAacWindowTransition .eightShort .longStop = true ∧
    isValidAacWindowTransition .longStop .onlyLong = true ∧
    isValidAacWindowTransition .longStop .longStart = true := by
  decide

theorem aacWindowTransition_rejects_illegal :
    isValidAacWindowTransition .onlyLong .eightShort = false ∧
    isValidAacWindowTransition .onlyLong .longStop = false ∧
    isValidAacWindowTransition .longStart .onlyLong = false ∧
    isValidAacWindowTransition .eightShort .onlyLong = false ∧
    isValidAacWindowTransition .longStop .eightShort = false := by
  decide

def aacWindowTransitionValidGate (p : AacWindowSequence × AacWindowSequence) : Bool :=
  isValidAacWindowTransition p.1 p.2

def aacWindowTransitionValidSpec :
    AVGateSpec (AacWindowSequence × AacWindowSequence) (fun p =>
      (p.1 = .onlyLong ∧ (p.2 = .onlyLong ∨ p.2 = .longStart)) ∨
      (p.1 = .longStart ∧ (p.2 = .eightShort ∨ p.2 = .longStop)) ∨
      (p.1 = .eightShort ∧ (p.2 = .eightShort ∨ p.2 = .longStop)) ∨
      (p.1 = .longStop ∧ (p.2 = .onlyLong ∨ p.2 = .longStart))) where
  gate := aacWindowTransitionValidGate
  sound p hg := by
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> simp_all [aacWindowTransitionValidGate, isValidAacWindowTransition]
  complete p hs := by
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> simp_all [aacWindowTransitionValidGate, isValidAacWindowTransition]
  posWitness := (.onlyLong, .longStart)
  negWitness := (.onlyLong, .eightShort)
  nonVacuous := by decide
  tight := by decide

theorem aacWindowTransitionValidSpec_iff (p : AacWindowSequence × AacWindowSequence) :
    aacWindowTransitionValidSpec.gate p = true ↔
      ((p.1 = .onlyLong ∧ (p.2 = .onlyLong ∨ p.2 = .longStart)) ∨
       (p.1 = .longStart ∧ (p.2 = .eightShort ∨ p.2 = .longStop)) ∨
       (p.1 = .eightShort ∧ (p.2 = .eightShort ∨ p.2 = .longStop)) ∨
       (p.1 = .longStop ∧ (p.2 = .onlyLong ∨ p.2 = .longStart))) :=
  aacWindowTransitionValidSpec.iff_safe p

theorem aacMdctFold_long_and_short_sizes (bLong bShort bBad : Array Float)
    (hl : bLong.size = 2048) (hs : bShort.size = 256) (hb : bBad.size = 512) :
    (aacMdctFold bLong).size = 1024 ∧
    (aacMdctFold bShort).size = 128 ∧
    aacMdctFold bBad = #[] := by
  unfold aacMdctFold
  simp [hl, hs, hb]

theorem aacImdct_long_and_short_sizes (cLong cShort cBad : Array Float)
    (hl : cLong.size = 1024) (hs : cShort.size = 128) (hb : cBad.size = 64) :
    (aacImdct cLong).size = 2048 ∧
    (aacImdct cShort).size = 256 ∧
    aacImdct cBad = #[] := by
  unfold aacImdct
  simp [hl, hs, hb]

theorem aacTdacOverlapAdd_exact (prev cur : Array Float) (n : Nat)
    (hp : prev.size = 2 * n) (hc : cur.size = 2 * n) (hn : 0 < n) (i : Nat) (hi : i < n) :
    (aacTdacOverlapAdd prev cur).size = n ∧
    (aacTdacOverlapAdd prev cur).getD i 0.0 = prev.getD (n + i) 0.0 + cur.getD i 0.0 := by
  unfold aacTdacOverlapAdd
  dsimp only
  have hdiv : prev.size / 2 = n := by omega
  have hcond : (cur.size != prev.size || prev.size / 2 == 0) = false := by
    simp [hp, hc]; omega
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, hdiv, Array.size_ofFn, true_and]
  simp [Array.getD, hdiv, hi]

theorem aacCompositeLongWindow_start_and_stop_zones (useKbdCur useKbdPrev : Bool) :
    (aacBuildCompositeLongWindow .longStart useKbdCur useKbdPrev).size = 2048 ∧
    (aacBuildCompositeLongWindow .longStart useKbdCur useKbdPrev).getD 1200 (-1.0) = 1.0 ∧
    (aacBuildCompositeLongWindow .longStart useKbdCur useKbdPrev).getD 1800 (-1.0) = 0.0 ∧
    (aacBuildCompositeLongWindow .longStop useKbdCur useKbdPrev).size = 2048 ∧
    (aacBuildCompositeLongWindow .longStop useKbdCur useKbdPrev).getD 200 (-1.0) = 0.0 ∧
    (aacBuildCompositeLongWindow .longStop useKbdCur useKbdPrev).getD 800 (-1.0) = 1.0 := by
  unfold aacBuildCompositeLongWindow
  simp [Array.getD]

theorem aacSynthesizeFrame_all_four_sequences_size (spec saved : Array Float)
    (seq : AacWindowSequence) (kCur kPrev : Bool)
    (hspec : spec.size = 1024) (hsaved : saved.size = 1024) :
    (aacSynthesizeFrame spec saved seq kCur kPrev).1.size = 1024 ∧
    (aacSynthesizeFrame spec saved seq kCur kPrev).2.size = 1024 := by
  unfold aacSynthesizeFrame
  have hc : (spec.size != 1024 || saved.size != 1024) = false := by simp [hspec, hsaved]
  simp [hc]

theorem aacTnsMaxOrder_lc :
    aacTnsMaxOrder false = 12 ∧ aacTnsMaxOrder true = 7 := by
  decide

theorem aacTnsMaxBands_short_48k :
    aacTnsMaxBandsShort.getD 3 0 = 14 ∧ aacTnsMaxBandsShort.getD 4 0 = 14 ∧
      aacTnsMaxBandsShort.getD 5 0 = 14 := by
  decide

theorem aacClipTnsFilterLength_bounds (filtLen sfiMaxBands maxSfb : Nat) :
    aacClipTnsFilterLength filtLen sfiMaxBands maxSfb ≤ sfiMaxBands ∧
    aacClipTnsFilterLength filtLen sfiMaxBands maxSfb ≤ maxSfb ∧
    aacClipTnsFilterLength filtLen sfiMaxBands maxSfb ≤ filtLen := by
  unfold aacClipTnsFilterLength
  simp only [Nat.min_def]
  split <;> split <;> omega

theorem aacTns_24k_short_bottom_starts_at_num_swb :
    swbOffsetShort24k.size - 1 = 15 ∧
    aacTnsMaxBandsShort.getD 6 0 = 14 ∧
    aacClipTnsFilterLength 15 (aacTnsMaxBandsShort.getD 6 0) 15 = 14 ∧
    (let sp := (Array.replicate 1024 (0.0 : Float)).set! 4 8.0
     let k := aacTnsTmp2Map0_4.getD 2 0.0
     let f : AacTnsFilter := { length := 14, order := 1, direction := false, coefIndices := #[2], parcor := #[k] }
     let tns : AacTnsInfo := { present := true, coefRes := Array.replicate 8 true, filters := #[#[f], #[], #[], #[], #[], #[], #[], #[]] }
     let out := aacApplyTns sp tns 6 true 15 true
     out.getD 0 0.0 == 0.0 && out.getD 4 0.0 == 8.0 && out.getD 5 0.0 == 0.0 - 8.0 * (-k)) = true := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

theorem aacEscape_16 : aacEscapeFindN 9 0 16 = 0 := by decide
theorem aacEscape_31 : aacEscapeFindN 9 0 31 = 0 := by decide
theorem aacEscape_32 : aacEscapeFindN 9 0 32 = 1 := by decide
theorem aacEscape_8191 : aacEscapeFindN 9 0 8191 = 8 := by decide
theorem aacEscape_rejects_15 : aacWriteEscape BitWriter.empty 15 = none := by decide
theorem aacEscape_rejects_8192 : aacWriteEscape BitWriter.empty 8192 = none := by decide

theorem aacSfDeltaIndex_in_range (diff : Int)
    (h : diff + 60 < 0 ∨ diff + 60 > 120) :
    aacWriteSfDelta BitWriter.empty diff = none := by
  unfold aacWriteSfDelta
  dsimp only
  rcases h with hlt | hgt
  · have hb : (decide (diff + 60 < 0) || decide (diff + 60 > 120)) = true := by
      simp [hlt]
    simp [hb]
  · have hb : (decide (diff + 60 < 0) || decide (diff + 60 > 120)) = true := by
      simp [hgt]
    simp [hb]

theorem aacSfDelta_all_121_roundtrip :
    ((List.range 121).all fun k =>
      let diff : Int := (k : Int) - 60
      match aacWriteSfDelta BitWriter.empty diff with
      | none => false
      | some w =>
        let r0 := BitReader.ofSlice (ByteSlice.ofByteArray w.toByteArray)
        match aacReadSfDelta r0 with
        | none => false
        | some (d, r1) => d == diff && r1.bitOffset == w.totalBitsWritten) = true := by
  decide

theorem aacCbIndex_zero_book1 :
    aacCbIndex 1 #[0, 0, 0, 0] = some 40 := by
  decide

theorem aacCbIndex_signed_book1 :
    aacCbIndex 1 #[-1, 0, 1, -1] = some 15 := by
  decide

theorem aacCbIndex_escape_book11 :
    aacCbIndex 11 #[-512, 8191] = some (16 * 17 + 16) := by
  decide

theorem aacCbUnpack_book1_zero :
    aacCbUnpack 1 40 = #[0, 0, 0, 0] := by
  decide

theorem aacCbUnpack_book11_escape :
    aacCbUnpack 11 (16 * 17 + 16) = #[16, 16] := by
  decide

def aacTupleRoundtripOk (book : Nat) (tup : Array Int) : Bool :=
  match aacEncodeTuple BitWriter.empty book tup with
  | none => false
  | some w =>
    let bitsWritten := w.totalBitsWritten
    let r0 := BitReader.ofSlice (ByteSlice.ofByteArray w.toByteArray)
    match aacDecodeTuple r0 book with
    | none => false
    | some (dec, r1) => dec == tup && r1.bitOffset == bitsWritten

theorem aacHuffman_all_11_books_escape_and_book12 :
    aacTupleRoundtripOk 1 #[0, 0, 0, 0] = true ∧
    aacTupleRoundtripOk 1 #[-1, 0, 1, -1] = true ∧
    aacTupleRoundtripOk 2 #[1, -1, 0, 1] = true ∧
    aacTupleRoundtripOk 3 #[0, 2, -2, 1] = true ∧
    aacTupleRoundtripOk 4 #[-2, 1, 0, 2] = true ∧
    aacTupleRoundtripOk 5 #[-4, 4] = true ∧
    aacTupleRoundtripOk 6 #[3, -2] = true ∧
    aacTupleRoundtripOk 7 #[0, -7] = true ∧
    aacTupleRoundtripOk 8 #[7, -5] = true ∧
    aacTupleRoundtripOk 9 #[-12, 11] = true ∧
    aacTupleRoundtripOk 10 #[12, -9] = true ∧
    aacTupleRoundtripOk 11 #[-15, 15] = true ∧
    aacTupleRoundtripOk 11 #[16, -31] = true ∧
    aacTupleRoundtripOk 11 #[-32, 512] = true ∧
    aacTupleRoundtripOk 11 #[-8191, 8191] = true ∧
    aacEncodeTuple BitWriter.empty 11 #[8192, 0] = none ∧
    aacEncodeTuple BitWriter.empty 12 #[0, 0] = none ∧
    aacDecodeTuple (BitReader.ofSlice (ByteSlice.ofByteArray (ByteArray.mk #[0x00, 0x00]))) 12 = none := by
  decide

theorem aacHuffCodebook_sizes :
    aacSfCodes.size = 121 ∧ aacSfBits.size = 121 ∧
    (aacCbCodes 1).size = 81 ∧ (aacCbBits 11).size = 289 ∧
    aacCbDim 1 = 4 ∧ aacCbDim 11 = 2 ∧ aacCbSigned 1 = true ∧ aacCbSigned 11 = false := by
  decide

theorem aacBandBook_zero_rejects_nonzero :
    aacBandBookBits 0 #[1] = none ∧ aacBandBookBits 0 #[0, 0, 0, 0] = some 0 := by
  decide

def aacQuantCoeffValidGate (q : Int) : Bool :=
  isValidAacQuantCoeff q

def aacQuantCoeffValidSpec :
    AVGateSpec Int (fun q => -8191 ≤ q ∧ q ≤ 8191) where
  gate := aacQuantCoeffValidGate
  sound q hg := by
    unfold aacQuantCoeffValidGate isValidAacQuantCoeff at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨hg.1, hg.2⟩
  complete q hs := by
    unfold aacQuantCoeffValidGate isValidAacQuantCoeff
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hs.1, hs.2⟩
  posWitness := 4096
  negWitness := 8192
  nonVacuous := by decide
  tight := by decide

def aacScaleFactorValidGate (sf : Nat) : Bool :=
  isValidAacScaleFactor sf

def aacScaleFactorValidSpec :
    AVGateSpec Nat (fun sf => sf ≤ 255) where
  gate := aacScaleFactorValidGate
  sound sf hg := by
    unfold aacScaleFactorValidGate isValidAacScaleFactor at hg
    simpa using hg
  complete sf hs := by
    unfold aacScaleFactorValidGate isValidAacScaleFactor
    simpa using hs
  posWitness := 100
  negWitness := 256
  nonVacuous := by decide
  tight := by decide

theorem aacQuantCoeffValidSpec_iff (q : Int) :
    aacQuantCoeffValidSpec.gate q = true ↔ -8191 ≤ q ∧ q ≤ 8191 :=
  aacQuantCoeffValidSpec.iff_safe q

theorem aacScaleFactorValidSpec_iff (sf : Nat) :
    aacScaleFactorValidSpec.gate sf = true ↔ sf ≤ 255 :=
  aacScaleFactorValidSpec.iff_safe sf

def aacSectionBookValidGate (book : UInt8) : Bool :=
  isValidAacSectionBook book

def aacSectionBookValidSpec :
    AVGateSpec UInt8 (fun book => book ≠ 12 ∧ book ≤ 15) where
  gate := aacSectionBookValidGate
  sound book hg := by
    unfold aacSectionBookValidGate isValidAacSectionBook at hg
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hg
    exact hg
  complete book hs := by
    unfold aacSectionBookValidGate isValidAacSectionBook
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact hs
  posWitness := 11
  negWitness := 12
  nonVacuous := by decide
  tight := by decide

theorem aacSectionBookValidSpec_iff (book : UInt8) :
    aacSectionBookValidSpec.gate book = true ↔ (book ≠ 12 ∧ book ≤ 15) :=
  aacSectionBookValidSpec.iff_safe book

theorem aacSections_real_roundtrip :
    let books : Array UInt8 := #[1, 1, 0, 0, 0, 7, 13, 15, 11, 11]
    aacExpandSections (aacBuildSections books) = books := by
  decide

theorem aacPulseData_roundtrip_apply_and_bounds :
    let p : AacPulseData := { present := true, startSfb := 1, offsets := #[0, 2, 1], amps := #[5, 3, 7] }
    let rtOk :=
      match aacWritePulseData BitWriter.empty p false 49 with
      | none => false
      | some w =>
        let r0 := BitReader.ofSlice (ByteSlice.ofByteArray w.toByteArray)
        match aacReadPulseData r0 false swbOffsetLong48k with
        | none => false
        | some (p', r1) => p' == p && r1.bitOffset == w.totalBitsWritten
    let qBase := (((Array.replicate 1024 (0 : Int)).set! 4 (-2)).set! 6 3)
    let books : Array UInt8 := #[0, 1, 13, 15]
    let pMulti : AacPulseData := { present := true, startSfb := 1, offsets := #[0, 2, 1, 1], amps := #[5, 4, 3, 9] }
    let appOk :=
      match aacApplyPulses qBase pMulti swbOffsetLong48k books 4 with
      | none => false
      | some qOut =>
        qOut.getD 4 0 == -7 && qOut.getD 6 0 == 7 && qOut.getD 7 0 == -3 && qOut.getD 8 0 == 0
    let pPnsIs : AacPulseData := { present := true, startSfb := 2, offsets := #[1, 4], amps := #[6, 6] }
    let skipOk :=
      match aacApplyPulses (Array.replicate 1024 (0 : Int)) pPnsIs swbOffsetLong48k books 4 with
      | none => false
      | some qOut => qOut.getD 9 0 == 0 && qOut.getD 13 0 == 0
    let pOob : AacPulseData := { present := true, startSfb := 48, offsets := #[31, 31, 31, 4], amps := #[1, 1, 1, 1] }
    rtOk = true ∧
    appOk = true ∧
    skipOk = true ∧
    aacWritePulseData BitWriter.empty p true 14 = none ∧
    aacApplyPulses qBase pOob swbOffsetLong48k (Array.replicate 49 1) 49 = none := by
  decide

theorem aacMuxDemuxAdts_payload_present :
    let payload := ByteArray.mk #[0x21, 0x10]
    (match muxAdtsFrame 3 2 payload false with
     | some frm => frm.size == 9 && (decodeAacLcAdtsHeader (ByteSlice.ofByteArray frm)).isSome
     | none => false) = true := by
  decide

private theorem getD_set_eq {α : Type} (a : Array α) (i : Nat) (v d : α) (hi : i < a.size) :
    (a.set! i v).getD i d = v := by
  simp [Array.getD, Array.set!, Array.setIfInBounds, hi]

private theorem getD_set_ne {α : Type} (a : Array α) (i j : Nat) (v d : α) (h : i ≠ j) :
    (a.set! j v).getD i d = a.getD i d := by
  by_cases hi : i < a.size <;> by_cases hj : j < a.size
  · simp [Array.getD, Array.set!, Array.setIfInBounds, hj, hi, Array.getElem_set_ne hj hi h.symm]
  · simp [Array.getD, Array.set!, Array.setIfInBounds, hj, hi]
  · simp [Array.getD, Array.set!, Array.setIfInBounds, hj, hi]
  · simp [Array.getD, Array.set!, Array.setIfInBounds, hj, hi]

private theorem set_size_eq {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  by_cases hi : i < a.size <;> simp [Array.set!, Array.setIfInBounds, hi]

private theorem pnsScaleBins_preserve_ge (spec nv : Array Float) (sc : Float) (off s0 idx rem : Nat)
    (hge : off + s0 + rem ≤ idx) :
    (aacPnsScaleBins spec nv sc off s0 rem).getD idx 0.0 = spec.getD idx 0.0 := by
  induction rem generalizing spec with
  | zero => rfl
  | succ j ih =>
    unfold aacPnsScaleBins
    dsimp only
    rw [ih _ (by omega), getD_set_ne _ _ _ _ _ (by omega)]

theorem aacPns_deterministic_seed_and_dequant (gain : Float) :
    let p : AacChannelPayload := {
      globalGain := 100, maxSfb := 1,
      sections := #[{ book := 13, length := 1 }],
      sf := #[0], isScale := #[0.0], pnsGain := #[gain],
      q := Array.replicate 1024 0, tns := {} }
    let r1 := aacPnsNextRng aacPnsFrameInitSeed
    let r2 := aacPnsNextRng r1
    let r3 := aacPnsNextRng r2
    let r4 := aacPnsNextRng r3
    r4 ≠ aacPnsFrameInitSeed ∧
    (aacDequantizeChannel p swbOffsetLong48k #[1]).2 = r4 ∧
    (aacDequantizeChannel p swbOffsetLong48k #[1]).1.getD 4 0.0 = 0.0 ∧
    (aacPnsGenNoiseBins aacPnsFrameInitSeed 0.0 [] 4).2.2.getD 0 0.0 = Float.ofInt r1.toInt32.toInt := by
  dsimp only
  refine ⟨by decide, rfl, ?_, rfl⟩
  have hdeq : (aacDequantizeChannel {
      globalGain := 100, maxSfb := 1,
      sections := #[{ book := 13, length := 1 }],
      sf := #[0], isScale := #[0.0], pnsGain := #[gain],
      q := Array.replicate 1024 0, tns := {} } swbOffsetLong48k #[1]).1 =
      (aacPnsDequantWins (Array.replicate 1024 0.0) aacPnsFrameInitSeed gain 0 0 4 0 1).1 := rfl
  rw [hdeq]
  unfold aacPnsDequantWins
  dsimp only
  unfold aacPnsDequantWins
  dsimp only
  rw [pnsScaleBins_preserve_ge _ _ _ 0 0 4 4 (by omega)]
  simp [Array.getD]

theorem aacShortGroup_two_two_two_two :
    (#[2, 2, 2, 2] : Array Nat).size = 4 ∧
    ((#[2, 2, 2, 2] : Array Nat).foldl (· + ·) 0) = 8 := by
  decide

theorem aacStandalonePlan_wav_to_aac_and_aac_to_wav :
    let pEnc := LeanAV.PlanIR.parseArgsToPlanIR ["-y", "-i", "in.wav", "-c:a", "aac", "-b:a", "128k", "out.aac"]
    let pDec := LeanAV.PlanIR.parseArgsToPlanIR ["-y", "-i", "in.aac", "out.wav"]
    let pFixed := LeanAV.PlanIR.parseArgsToPlanIR ["-y", "-i", "in.wav", "-c:a", "aac_fixed", "out.aac"]
    LeanAV.PlanIR.standaloneAacAdtsPlanGateSpec.gate pEnc = true ∧
    LeanAV.PlanIR.standaloneAacAdtsPlanGateSpec.gate pDec = true ∧
    LeanAV.PlanIR.standaloneAacAdtsPlanGateSpec.gate pFixed = false := by
  decide

theorem aacMidSide_int_butterfly (l r : Int) :
    let m2 := l + r
    let s2 := l - r
    m2 + s2 = 2 * l ∧ m2 - s2 = 2 * r := by
  dsimp only
  omega

theorem aacEncodeMidSide_active_and_inactive :
    let ch0 := ((Array.replicate 1024 (0.0 : Float)).set! 0 5.0).set! 4 8.0
    let ch1 := ((Array.replicate 1024 (0.0 : Float)).set! 0 6.0).set! 4 0.0
    let (modeA, maskA, out0A, out1A) := aacEncodeMidSide ch0 ch1 #[0, 4, 8] #[1] 2
    let (modeZ, maskZ, out0Z, out1Z) := aacEncodeMidSide ch0 ch0 #[0, 4, 8] #[1] 2
    (modeA == 1 && maskA == #[true, false] &&
     out0A.getD 0 0.0 == 5.5 && out1A.getD 0 0.0 == -0.5 &&
     out0A.getD 4 0.0 == 8.0 && out1A.getD 4 0.0 == 0.0 &&
     modeZ == 2 && maskZ == #[true, true] &&
     out0Z.getD 0 0.0 == 5.0 && out1Z.getD 0 0.0 == 0.0 &&
     out0Z.getD 4 0.0 == 8.0 && out1Z.getD 4 0.0 == 0.0) = true := by
  decide

theorem aacDecodeMidSide_butterfly_and_pns_suppression :
    let ch0 := ((Array.replicate 1024 (0.0 : Float)).set! 0 5.0).set! 4 7.0
    let ch1 := ((Array.replicate 1024 (0.0 : Float)).set! 0 3.0).set! 4 2.0
    let (lOut, rOut) := aacDecodeMidSide ch0 ch1 #[0, 4, 8] #[1] 2 1 #[true, true] #[1, 13] #[1, 1]
    lOut.getD 0 0.0 == 8.0 && rOut.getD 0 0.0 == 2.0 &&
    lOut.getD 4 0.0 == 7.0 && rOut.getD 4 0.0 == 2.0 := by
  decide

theorem aacDecodeIntensityStereo_books_14_15_and_ms_flip :
    let ch0 := ((Array.replicate 1024 (0.0 : Float)).set! 0 4.0).set! 4 6.0
    let ch1 := Array.replicate 1024 (0.0 : Float)
    let outNoMs := aacDecodeIntensityStereo ch0 ch1 #[0, 4, 8] #[1] 2 0 #[] #[15, 14] #[2.0, 3.0]
    let outFlip := aacDecodeIntensityStereo ch0 ch1 #[0, 4, 8] #[1] 2 1 #[true, true] #[15, 14] #[2.0, 3.0]
    outNoMs.getD 0 0.0 == 8.0 && outNoMs.getD 4 0.0 == -18.0 &&
    outFlip.getD 0 0.0 == -8.0 && outFlip.getD 4 0.0 == 18.0 := by
  decide

private theorem getD_replicate_eq {α : Type} (n : Nat) (v : α) (i : Nat) (d : α) (h : i < n) :
    (Array.replicate n v).getD i d = v := by
  simp [Array.getD, h]

private theorem testDequant2Bands (p : AacChannelPayload) (rng : UInt32)
    (hmax : p.maxSfb = 2)
    (hsec : p.sections = #[{ book := 1, length := 2 }])
    (hsf : p.sf = #[100, 100])
    (hq0 : p.q.getD 0 0 = 1) (hq1 : p.q.getD 1 0 = 0) (hq2 : p.q.getD 2 0 = 0) (hq3 : p.q.getD 3 0 = 0)
    (hq4 : p.q.getD 4 0 = 1) (hq5 : p.q.getD 5 0 = 0) (hq6 : p.q.getD 6 0 = 0) (hq7 : p.q.getD 7 0 = 0) :
    let (spec, rng') := aacDequantizeChannel p #[0, 4, 8] #[1] rng
    rng' = rng ∧ spec.size = 1024 ∧
    spec.getD 0 0.0 = 1.0 ∧ spec.getD 4 0.0 = 1.0 ∧ spec.getD 5 0.0 = 0.0 := by
  dsimp only
  have hexp : aacExpandSections p.sections = #[1, 1] := by rw [hsec]; decide
  have hd1 : aacDequantizeCoeff 1 100 = 1.0 := by decide
  have hd0 : aacDequantizeCoeff 0 100 = 0.0 := by decide
  unfold aacDequantizeChannel
  simp only [hexp]
  unfold aacDequantizeGroups
  simp only [hmax]
  unfold aacDequantizeBands
  simp only [hsf, show (#[1, 1] : Array UInt8).getD 0 0 = 1 from rfl,
    show (#[0, 4, 8] : Array Nat).getD 0 0 = 0 from rfl,
    show (#[0, 4, 8] : Array Nat).getD 1 0 = 4 from rfl,
    show (#[100, 100] : Array Nat).getD 0 0 = 100 from rfl,
    show ((1 : UInt8) != 0 && (1 : UInt8) <= 11) = true from rfl, ↓reduceIte,
    show 4 - 0 = 4 from rfl]
  unfold aacDequantizeSpectralWins aacDequantizeSpectralBins
  unfold aacDequantizeSpectralBins; unfold aacDequantizeSpectralBins
  unfold aacDequantizeSpectralBins; unfold aacDequantizeSpectralBins
  unfold aacDequantizeSpectralWins; unfold aacDequantizeBands
  simp only [hsf, show (#[1, 1] : Array UInt8).getD 1 0 = 1 from rfl,
    show (#[0, 4, 8] : Array Nat).getD 1 0 = 4 from rfl,
    show (#[0, 4, 8] : Array Nat).getD 2 4 = 8 from rfl,
    show (#[100, 100] : Array Nat).getD 1 0 = 100 from rfl,
    show ((1 : UInt8) != 0 && (1 : UInt8) <= 11) = true from rfl, ↓reduceIte,
    show 8 - 4 = 4 from rfl]
  unfold aacDequantizeSpectralWins aacDequantizeSpectralBins
  unfold aacDequantizeSpectralBins; unfold aacDequantizeSpectralBins
  unfold aacDequantizeSpectralBins; unfold aacDequantizeSpectralBins
  unfold aacDequantizeSpectralWins; unfold aacDequantizeBands aacDequantizeGroups
  dsimp only
  simp only [Nat.zero_mul, Nat.zero_add,
    show 4 + 3 = 7 from rfl, show 4 + 2 = 6 from rfl, show 4 + 1 = 5 from rfl, show 4 + 0 = 4 from rfl,
    hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hd1, hd0]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]
    rfl
  · rw [getD_set_ne _ 0 4 _ _ (by omega), getD_set_ne _ 0 5 _ _ (by omega),
        getD_set_ne _ 0 6 _ _ (by omega), getD_set_ne _ 0 7 _ _ (by omega)]
    exact getD_set_eq _ 0 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq]; show 0 < 1024; omega)
  · exact getD_set_eq _ 4 _ _ (by
      iterate 7 (rw [set_size_eq])
      show 4 < 1024
      omega)
  · rw [getD_set_ne _ 5 4 _ _ (by omega)]
    exact getD_set_eq _ 5 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 5 < 1024; omega)

private theorem testMsDecode2Bands (d0 d1 : Array Float)
    (hsz0 : d0.size = 1024) (hsz1 : d1.size = 1024)
    (hd0_0 : d0.getD 0 0.0 = 1.0) (hd0_4 : d0.getD 4 0.0 = 1.0) (hd0_5 : d0.getD 5 0.0 = 0.0)
    (hd1_0 : d1.getD 0 0.0 = 1.0) (hd1_4 : d1.getD 4 0.0 = 1.0) (hd1_5 : d1.getD 5 0.0 = 0.0) :
    let (ms0, ms1) := aacDecodeMidSide d0 d1 #[0, 4, 8] #[1] 2 1 #[false, true] #[1, 1] #[1, 1]
    ms0.size = 1024 ∧ ms1.size = 1024 ∧
    ms0.getD 0 0.0 = 1.0 ∧ ms0.getD 4 0.0 = 2.0 ∧ ms0.getD 5 0.0 = 0.0 ∧
    ms1.getD 0 0.0 = 1.0 ∧ ms1.getD 4 0.0 = 0.0 ∧ ms1.getD 5 0.0 = 0.0 := by
  dsimp only
  unfold aacDecodeMidSide
  simp only [hsz0, hsz1, bne_self_eq_false, Bool.or_false,
    show ((1 : UInt8) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  unfold aacDecodeMsGroups aacDecodeMsBands
  simp only [show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (#[false, true] : Array Bool).getD 0 false = false from rfl, Bool.false_and]
  unfold aacDecodeMsBands
  simp only [show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (#[false, true] : Array Bool).getD 1 false = true from rfl,
    show (#[1, 1] : Array UInt8).getD 1 0 = 1 from rfl,
    show (true && decide ((1 : UInt8) < 13) && decide ((1 : UInt8) < 13)) = true from rfl,
    show (#[0, 4, 8] : Array Nat).getD 1 0 = 4 from rfl,
    show (#[0, 4, 8] : Array Nat).getD 2 4 = 8 from rfl]
  unfold aacMsTransformWins aacMsTransformBins
  simp only [show 8 - 4 = 4 from rfl, Nat.zero_add, Nat.zero_mul, Bool.false_eq_true, ↓reduceIte]
  unfold aacMsTransformBins; simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte]
  unfold aacMsTransformBins; simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte]
  unfold aacMsTransformBins; simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte]
  unfold aacMsTransformBins aacMsTransformWins aacDecodeMsBands aacDecodeMsGroups
  dsimp only
  have h1p1 : (1.0 : Float) + 1.0 = 2.0 := by decide
  have h1m1 : (1.0 : Float) - 1.0 = 0.0 := by decide
  have h0p0 : (0.0 : Float) + 0.0 = 0.0 := by decide
  have h0m0 : (0.0 : Float) - 0.0 = 0.0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq]; exact hsz0
  · rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq]; exact hsz1
  · rw [getD_set_ne _ 0 7 _ _ (by omega), getD_set_ne _ 0 6 _ _ (by omega),
        getD_set_ne _ 0 5 _ _ (by omega), getD_set_ne _ 0 4 _ _ (by omega), hd0_0]
  · rw [getD_set_ne _ 4 7 _ _ (by omega), getD_set_ne _ 4 6 _ _ (by omega),
        getD_set_ne _ 4 5 _ _ (by omega), getD_set_eq _ 4 _ _ (by omega), hd0_4, hd1_4, h1p1]
  · rw [getD_set_ne _ 5 7 _ _ (by omega), getD_set_ne _ 5 6 _ _ (by omega),
        getD_set_eq _ 5 _ _ (by rw [set_size_eq]; omega),
        getD_set_ne _ 5 4 _ _ (by omega), getD_set_ne _ 5 4 _ _ (by omega), hd0_5, hd1_5, h0p0]
  · rw [getD_set_ne _ 0 7 _ _ (by omega), getD_set_ne _ 0 6 _ _ (by omega),
        getD_set_ne _ 0 5 _ _ (by omega), getD_set_ne _ 0 4 _ _ (by omega), hd1_0]
  · rw [getD_set_ne _ 4 7 _ _ (by omega), getD_set_ne _ 4 6 _ _ (by omega),
        getD_set_ne _ 4 5 _ _ (by omega), getD_set_eq _ 4 _ _ (by omega), hd0_4, hd1_4, h1m1]
  · rw [getD_set_ne _ 5 7 _ _ (by omega), getD_set_ne _ 5 6 _ _ (by omega),
        getD_set_eq _ 5 _ _ (by rw [set_size_eq]; omega),
        getD_set_ne _ 5 4 _ _ (by omega), getD_set_ne _ 5 4 _ _ (by omega), hd0_5, hd1_5, h0m0]

private theorem testIsNoop2Bands (ms0 ms1 : Array Float) (isScale : Array Float)
    (hsz0 : ms0.size = 1024) (hsz1 : ms1.size = 1024) :
    aacDecodeIntensityStereo ms0 ms1 #[0, 4, 8] #[1] 2 1 #[false, true] #[1, 1] isScale = ms1 := by
  unfold aacDecodeIntensityStereo
  simp only [hsz0, hsz1, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  unfold aacDecodeIsGroups aacDecodeIsBands
  simp only [show (#[1, 1] : Array UInt8).getD 0 0 = 1 from rfl,
    show (((1 : UInt8) == 14) || ((1 : UInt8) == 15)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  unfold aacDecodeIsBands
  simp only [show (#[1, 1] : Array UInt8).getD 1 0 = 1 from rfl,
    show (((1 : UInt8) == 14) || ((1 : UInt8) == 15)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  unfold aacDecodeIsBands aacDecodeIsGroups
  rfl

private theorem testParcor1 (v : Float) :
    aacTnsParcorToLpc (#[v].extract 0 1) = #[-v] := rfl

private theorem testTnsOrder1Symbolic (ms0 : Array Float) (v : Float)
    (hsz : ms0.size = 1024)
    (hm0 : ms0.getD 0 0.0 = 1.0)
    (hm4 : ms0.getD 4 0.0 = 2.0)
    (hm5 : ms0.getD 5 0.0 = 0.0) :
    let tns : AacTnsInfo := { present := true, coefRes := #[true], filters := #[#[{
        length := 48, order := 1, direction := false, coefCompress := false,
        coefIndices := #[2], parcor := #[v] }]] }
    let ch0 := aacApplyTns ms0 tns 3 false 2 true
    ch0.getD 0 0.0 = 1.0 ∧
    ch0.getD 4 0.0 = 2.0 ∧
    ch0.getD 5 0.0 = 0.0 - 2.0 * (-v) := by
  dsimp only
  have hred : aacApplyTns ms0 { present := true, coefRes := #[true], filters := #[#[{
        length := 48, order := 1, direction := false, coefCompress := false,
        coefIndices := #[2], parcor := #[v] }]] } 3 false 2 true =
      aacTnsFilterBins ms0 ms0 #[-v] true false 0 4 8 4 1 4 := by
    unfold aacApplyTns
    simp only [hsz, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      show (!true) = false from rfl,
      show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl]
    simp only [show swbOffsetLong48k.size - 1 = 49 from by decide,
      show aacTnsMaxBandsLong.getD (UInt8.toNat 3) 0 = 40 from by decide]
    simp only [show Nat.min 40 2 = 2 from rfl,
      show (2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    unfold aacApplyTnsWindows
    dsimp only
    have hfl : ((#[#[{ length := 48, order := 1, direction := false, coefCompress := false, coefIndices := #[2], parcor := #[v] }]] :
        Array (Array AacTnsFilter)).getD 0 #[]).toList =
        [{ length := 48, order := 1, direction := false, coefCompress := false, coefIndices := #[2], parcor := #[v] }] := rfl
    rw [hfl]
    unfold aacApplyTnsWindow
    simp only [show Nat.min (49 - Nat.min 49 48) 2 = 1 from rfl,
      show Nat.min 49 2 = 2 from rfl,
      show Nat.min (aacTnsMaxOrder false) 1 = 1 from rfl,
      show (decide (1 > 0) && decide ((#[v] : Array Float).size >= 1)) = true from rfl,
      show swbOffsetLong48k.getD 1 0 = 4 from by decide,
      show swbOffsetLong48k.getD 2 0 = 8 from by decide,
      show (8 > 4) = True from eq_true (by decide), ↓reduceIte,
      testParcor1 v]
    rfl
  rw [hred]
  unfold aacTnsFilterBins; dsimp only
  unfold aacTnsFilterBins; dsimp only
  unfold aacTnsFilterBins; dsimp only
  unfold aacTnsFilterBins; dsimp only
  unfold aacTnsFilterBins
  simp only [Bool.false_eq_true, ↓reduceIte,
    show 4 - 1 - 3 = 0 from rfl, show 4 - 1 - 2 = 1 from rfl,
    show 4 - 1 - 1 = 2 from rfl, show 4 - 1 - 0 = 3 from rfl,
    Nat.zero_add,
    show Nat.min 0 1 = 0 from rfl, show Nat.min 1 1 = 1 from rfl,
    show Nat.min 2 1 = 1 from rfl, show Nat.min 3 1 = 1 from rfl,
    show 4 + 1 = 5 from rfl, show 4 + 2 = 6 from rfl, show 4 + 3 = 7 from rfl]
  refine ⟨?_, ?_, ?_⟩
  · rw [getD_set_ne _ 0 7 _ _ (by omega), getD_set_ne _ 0 6 _ _ (by omega),
        getD_set_ne _ 0 5 _ _ (by omega), getD_set_ne _ 0 4 _ _ (by omega), hm0]
  · rw [getD_set_ne _ 4 7 _ _ (by omega), getD_set_ne _ 4 6 _ _ (by omega),
        getD_set_ne _ 4 5 _ _ (by omega), getD_set_eq _ 4 _ _ (by omega), hm4]
    rfl
  · rw [getD_set_ne _ 5 7 _ _ (by omega), getD_set_ne _ 5 6 _ _ (by omega),
        getD_set_eq _ 5 _ _ (by rw [set_size_eq]; omega)]
    unfold aacTnsTapSum; dsimp only
    unfold aacTnsTapSum
    simp only [Bool.false_eq_true, ↓reduceIte, show 5 - 1 = 4 from rfl,
      show (#[-v] : Array Float).getD 0 0.0 = -v from rfl]
    rw [getD_set_ne _ 5 4 _ _ (by omega), getD_set_eq _ 4 _ _ (by omega), hm5, hm4]
    rfl

private def cpeTestRaw : ByteArray :=
  ByteArray.mk #[33, 0, 138, 200, 34, 23, 128, 66, 66, 12, 130, 32, 66, 28]

private abbrev cpeAt (off : Nat) : BitReader :=
  { slice := ByteSlice.ofByteArray cpeTestRaw, bitOffset := off }

private theorem cpeGroups0_rfl (qInit : Array Int) :
    aacReadIcsGroups (cpeAt 65) qInit #[0, 4, 8] #[1, 1] 2 0 0 [1] =
      some ((((((((qInit.set! 0 1).set! 1 0).set! 2 0).set! 3 0).set! 4 1).set! 5 0).set! 6 0).set! 7 0,
            cpeAt 75) := rfl

private theorem cpeGroups1_rfl (qInit : Array Int) :
    aacReadIcsGroups (cpeAt 97) qInit #[0, 4, 8] #[1, 1] 2 0 0 [1] =
      some ((((((((qInit.set! 0 1).set! 1 0).set! 2 0).set! 3 0).set! 4 1).set! 5 0).set! 6 0).set! 7 0,
            cpeAt 107) := rfl

private theorem cpeIcs0_step :
    ∃ p0,
      aacReadIcs (cpeAt 23) 3 true .onlyLong false #[1] 2 =
        some (p0, .onlyLong, false, #[1], cpeAt 75) ∧
      p0.maxSfb = 2 ∧
      p0.sections = #[{ book := 1, length := 2 }] ∧
      p0.sf = #[100, 100] ∧
      p0.q.getD 0 0 = 1 ∧ p0.q.getD 1 0 = 0 ∧ p0.q.getD 2 0 = 0 ∧ p0.q.getD 3 0 = 0 ∧
      p0.q.getD 4 0 = 1 ∧ p0.q.getD 5 0 = 0 ∧ p0.q.getD 6 0 = 0 ∧ p0.q.getD 7 0 = 0 ∧
      p0.tns = { present := true, coefRes := #[true], filters := #[#[{
        length := 48, order := 1, direction := false, coefCompress := false,
        coefIndices := #[2], parcor := #[aacTnsTmp2Map0_4.getD 2 0.0] }]] } := by
  have h1 : (cpeAt 23).readBitsMSB 8 = some (100, cpeAt 31) := rfl
  have h2 : aacReadSections (cpeAt 31) false 1 2 =
      some (#[{ book := 1, length := 2 }], cpeAt 40) := rfl
  have h3 : aacReadScaleFactors (cpeAt 40) #[{ book := 1, length := 2 }] 100 =
      some (#[100, 100], #[0.0, 0.0], #[0.0, 0.0], cpeAt 42) := rfl
  have h4 : aacReadPulseData (cpeAt 42) false swbOffsetLong48k =
      some ({}, cpeAt 43) := rfl
  have h5 : aacReadTns (cpeAt 43) false =
      some ({ present := true, coefRes := #[true], filters := #[#[{
        length := 48, order := 1, direction := false, coefCompress := false,
        coefIndices := #[2], parcor := #[aacTnsTmp2Map0_4.getD 2 0.0] }]] }, cpeAt 64) := rfl
  have h6 : (cpeAt 64).readBit = some (0, cpeAt 65) := rfl
  have hswb : swbOffsetLong48k.extract 0 3 = #[0, 4, 8] := by decide
  have hexp : aacExpandSections #[{ book := 1, length := 2 }] = #[1, 1] := by decide
  unfold aacReadIcs
  rw [h1]
  simp only [show (!true) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (.onlyLong == AacWindowSequence.eightShort) = false from rfl,
    show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl,
    show (2 > swbOffsetLong48k.size - 1) = False from eq_false (by decide),
    show (#[1] : Array Nat).size = 1 from rfl,
    show (100 : UInt64).toNat = 100 from rfl, hswb]
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  rw [h4]; dsimp only
  rw [h5]; dsimp only
  rw [h6]; dsimp only
  simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hexp]
  rw [cpeGroups0_rfl]
  dsimp only
  unfold aacApplyPulses
  simp only [show (!false) = true from rfl, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · iterate 7 (rw [getD_set_ne _ 0 _ _ _ (by omega)])
    exact getD_set_eq _ 0 _ _ (by show 0 < 1024; omega)
  · iterate 6 (rw [getD_set_ne _ 1 _ _ _ (by omega)])
    exact getD_set_eq _ 1 _ _ (by rw [set_size_eq]; show 1 < 1024; omega)
  · iterate 5 (rw [getD_set_ne _ 2 _ _ _ (by omega)])
    exact getD_set_eq _ 2 _ _ (by rw [set_size_eq, set_size_eq]; show 2 < 1024; omega)
  · iterate 4 (rw [getD_set_ne _ 3 _ _ _ (by omega)])
    exact getD_set_eq _ 3 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq]; show 3 < 1024; omega)
  · iterate 3 (rw [getD_set_ne _ 4 _ _ _ (by omega)])
    exact getD_set_eq _ 4 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 4 < 1024; omega)
  · iterate 2 (rw [getD_set_ne _ 5 _ _ _ (by omega)])
    exact getD_set_eq _ 5 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 5 < 1024; omega)
  · rw [getD_set_ne _ 6 7 _ _ (by omega)]
    exact getD_set_eq _ 6 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 6 < 1024; omega)
  · exact getD_set_eq _ 7 _ _ (by
      iterate 7 (rw [set_size_eq])
      show 7 < 1024
      omega)

private theorem cpeIcs1_step :
    ∃ p1,
      aacReadIcs (cpeAt 75) 3 true .onlyLong false #[1] 2 =
        some (p1, .onlyLong, false, #[1], cpeAt 107) ∧
      p1.maxSfb = 2 ∧
      p1.sections = #[{ book := 1, length := 2 }] ∧
      p1.sf = #[100, 100] ∧
      p1.q.getD 0 0 = 1 ∧ p1.q.getD 1 0 = 0 ∧ p1.q.getD 2 0 = 0 ∧ p1.q.getD 3 0 = 0 ∧
      p1.q.getD 4 0 = 1 ∧ p1.q.getD 5 0 = 0 ∧ p1.q.getD 6 0 = 0 ∧ p1.q.getD 7 0 = 0 ∧
      p1.tns = {} := by
  have h1 : (cpeAt 75).readBitsMSB 8 = some (100, cpeAt 83) := rfl
  have h2 : aacReadSections (cpeAt 83) false 1 2 =
      some (#[{ book := 1, length := 2 }], cpeAt 92) := rfl
  have h3 : aacReadScaleFactors (cpeAt 92) #[{ book := 1, length := 2 }] 100 =
      some (#[100, 100], #[0.0, 0.0], #[0.0, 0.0], cpeAt 94) := rfl
  have h4 : aacReadPulseData (cpeAt 94) false swbOffsetLong48k =
      some ({}, cpeAt 95) := rfl
  have h5 : aacReadTns (cpeAt 95) false = some ({}, cpeAt 96) := rfl
  have h6 : (cpeAt 96).readBit = some (0, cpeAt 97) := rfl
  have hswb : swbOffsetLong48k.extract 0 3 = #[0, 4, 8] := by decide
  have hexp : aacExpandSections #[{ book := 1, length := 2 }] = #[1, 1] := by decide
  unfold aacReadIcs
  rw [h1]
  simp only [show (!true) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (.onlyLong == AacWindowSequence.eightShort) = false from rfl,
    show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl,
    show (2 > swbOffsetLong48k.size - 1) = False from eq_false (by decide),
    show (#[1] : Array Nat).size = 1 from rfl,
    show (100 : UInt64).toNat = 100 from rfl, hswb]
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  rw [h4]; dsimp only
  rw [h5]; dsimp only
  rw [h6]; dsimp only
  simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hexp]
  rw [cpeGroups1_rfl]
  dsimp only
  unfold aacApplyPulses
  simp only [show (!false) = true from rfl, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · iterate 7 (rw [getD_set_ne _ 0 _ _ _ (by omega)])
    exact getD_set_eq _ 0 _ _ (by show 0 < 1024; omega)
  · iterate 6 (rw [getD_set_ne _ 1 _ _ _ (by omega)])
    exact getD_set_eq _ 1 _ _ (by rw [set_size_eq]; show 1 < 1024; omega)
  · iterate 5 (rw [getD_set_ne _ 2 _ _ _ (by omega)])
    exact getD_set_eq _ 2 _ _ (by rw [set_size_eq, set_size_eq]; show 2 < 1024; omega)
  · iterate 4 (rw [getD_set_ne _ 3 _ _ _ (by omega)])
    exact getD_set_eq _ 3 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq]; show 3 < 1024; omega)
  · iterate 3 (rw [getD_set_ne _ 4 _ _ _ (by omega)])
    exact getD_set_eq _ 4 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 4 < 1024; omega)
  · iterate 2 (rw [getD_set_ne _ 5 _ _ _ (by omega)])
    exact getD_set_eq _ 5 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 5 < 1024; omega)
  · rw [getD_set_ne _ 6 7 _ _ (by omega)]
    exact getD_set_eq _ 6 _ _ (by rw [set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq, set_size_eq]; show 6 < 1024; omega)
  · exact getD_set_eq _ 7 _ _ (by
      iterate 7 (rw [set_size_eq])
      show 7 < 1024
      omega)

theorem aacCpe_tns_and_ms_raw_roundtrip :
    let k0 := aacTnsTmp2Map0_4.getD 2 0.0
    let cpeCh0 : AacChannelPayload := {
      globalGain := 100, maxSfb := 2,
      sections := #[{ book := 1, length := 2 }],
      sf := #[100, 100],
      q := ((Array.replicate 1024 (0 : Int)).set! 0 1).set! 4 1,
      tns := { present := true, coefRes := #[true], filters := #[#[{
        length := 48, order := 1, direction := false, coefCompress := false,
        coefIndices := #[2], parcor := #[k0] }]] } }
    let cpeCh1 : AacChannelPayload := {
      globalGain := 100, maxSfb := 2,
      sections := #[{ book := 1, length := 2 }],
      sf := #[100, 100],
      q := ((Array.replicate 1024 (0 : Int)).set! 0 1).set! 4 1,
      tns := {} }
    match aacWriteRawDataBlock .onlyLong false #[1] #[0, 4, 8] 1 #[false, true] #[cpeCh0, cpeCh1] with
    | none => False
    | some raw =>
      ∃ frm rngOut,
        aacReadRawDataBlock raw 3 aacPnsFrameInitSeed = some (frm, rngOut) ∧
        rngOut = aacPnsFrameInitSeed ∧
        frm.ch.size = 2 ∧
        frm.msMode = 1 ∧
        frm.msMask = #[false, true] ∧
        (frm.ch.getD 0 #[]).getD 0 0.0 = 1.0 ∧
        (frm.ch.getD 0 #[]).getD 4 0.0 = 2.0 ∧
        (frm.ch.getD 0 #[]).getD 5 0.0 = 0.0 - 2.0 * (-k0) ∧
        (frm.ch.getD 1 #[]).getD 0 0.0 = 1.0 ∧
        (frm.ch.getD 1 #[]).getD 4 0.0 = 0.0 ∧
        (frm.ch.getD 1 #[]).getD 5 0.0 = 0.0 := by
  dsimp only
  have hwrite : aacWriteRawDataBlock .onlyLong false #[1] #[0, 4, 8] 1 #[false, true]
      #[{ globalGain := 100, maxSfb := 2, sections := #[{ book := 1, length := 2 }], sf := #[100, 100],
          q := ((Array.replicate 1024 (0 : Int)).set! 0 1).set! 4 1,
          tns := { present := true, coefRes := #[true], filters := #[#[{
            length := 48, order := 1, direction := false, coefCompress := false,
            coefIndices := #[2], parcor := #[aacTnsTmp2Map0_4.getD 2 0.0] }]] } },
        { globalGain := 100, maxSfb := 2, sections := #[{ book := 1, length := 2 }], sf := #[100, 100],
          q := ((Array.replicate 1024 (0 : Int)).set! 0 1).set! 4 1, tns := {} }] =
      some cpeTestRaw := by decide
  rw [hwrite]
  dsimp only
  have hbr : BitReader.ofSlice (ByteSlice.ofByteArray cpeTestRaw) = cpeAt 0 := rfl
  have ht0 : (cpeAt 0).readBitsMSB 3 = some (1, cpeAt 3) := rfl
  have ht1 : (cpeAt 3).readBitsMSB 4 = some (0, cpeAt 7) := rfl
  have hcw : (cpeAt 7).readBit = some (1, cpeAt 8) := rfl
  have hinfo : aacReadIcsInfo (cpeAt 8) =
      some (.onlyLong, false, #[1], 2, cpeAt 19) := rfl
  have hms : (cpeAt 19).readBitsMSB 2 = some (1, cpeAt 21) := rfl
  have hmask : aacReadMsBits (cpeAt 21) [] 2 =
      some (#[false, true], cpeAt 23) := rfl
  have hend : (cpeAt 107).readBitsMSB 3 = some (7, cpeAt 110) := rfl
  have hswb : swbOffsetLong48k.extract 0 3 = #[0, 4, 8] := by decide
  obtain ⟨p0, hp0, hp0max, hp0sec, hp0sf, h0q0, h0q1, h0q2, h0q3, h0q4, h0q5, h0q6, h0q7, hp0tns⟩ := cpeIcs0_step
  obtain ⟨p1, hp1, hp1max, hp1sec, hp1sf, h1q0, h1q1, h1q2, h1q3, h1q4, h1q5, h1q6, h1q7, hp1tns⟩ := cpeIcs1_step
  unfold aacReadRawDataBlock aacReadRawElems
  rw [hbr, ht0]; dsimp only
  simp only [show ((1 : UInt64).toNat == 7) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [ht1]; dsimp only
  simp only [show ((1 : UInt64).toNat == 4) = false from rfl,
    show ((1 : UInt64).toNat == 6) = false from rfl,
    show ((1 : UInt64).toNat == 0) = false from rfl,
    show ((1 : UInt64).toNat == 1) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  unfold aacReadCpeElem
  rw [hcw]; dsimp only
  simp only [show ((1 : UInt8) == 1) = true from rfl, ↓reduceIte]
  rw [hinfo]; dsimp only
  rw [hms]; dsimp only
  simp only [show ((1 : UInt64).toNat == 3) = false from rfl,
    show ((1 : UInt64).toNat == 1) = true from rfl,
    show (#[1] : Array Nat).size * 2 = 2 from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [hmask]; dsimp only
  simp only [show (.onlyLong == AacWindowSequence.eightShort) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl,
    show (2 > swbOffsetLong48k.size - 1) = False from eq_false (by decide), hswb]
  rw [hp0]; dsimp only
  rw [hp1]; dsimp only
  unfold aacReadRawElems
  rw [hend]; dsimp only
  simp only [show ((7 : UInt64).toNat == 7) = true from rfl, ↓reduceIte, Option.map]
  have hd0 := testDequant2Bands p0 aacPnsFrameInitSeed hp0max hp0sec hp0sf h0q0 h0q1 h0q2 h0q3 h0q4 h0q5 h0q6 h0q7
  dsimp only at hd0
  rcases hd0 with ⟨hrng1, hsz0, hd0_0, hd0_4, hd0_5⟩
  have hd1 := testDequant2Bands p1 (aacDequantizeChannel p0 #[0, 4, 8] #[1] aacPnsFrameInitSeed).2
    hp1max hp1sec hp1sf h1q0 h1q1 h1q2 h1q3 h1q4 h1q5 h1q6 h1q7
  dsimp only at hd1
  rcases hd1 with ⟨hrng2, hsz1, hd1_0, hd1_4, hd1_5⟩
  have hbt0 : aacExpandSections p0.sections = #[1, 1] := by rw [hp0sec]; decide
  have hbt1 : aacExpandSections p1.sections = #[1, 1] := by rw [hp1sec]; decide
  have hmsOut := testMsDecode2Bands _ _ hsz0 hsz1 hd0_0 hd0_4 hd0_5 hd1_0 hd1_4 hd1_5
  dsimp only at hmsOut
  rcases hmsOut with ⟨hmsSz0, hmsSz1, hms0_0, hms0_4, hms0_5, hms1_0, hms1_4, hms1_5⟩
  refine ⟨_, _, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · exact hrng2.trans hrng1
  · simp only [show (1 : UInt64).toUInt8 = 1 from rfl, hbt0, hbt1]
    have his1 := testIsNoop2Bands
      (aacDecodeMidSide (aacDequantizeChannel p0 #[0, 4, 8] #[1] aacPnsFrameInitSeed).1
        (aacDequantizeChannel p1 #[0, 4, 8] #[1] (aacDequantizeChannel p0 #[0, 4, 8] #[1] aacPnsFrameInitSeed).2).1
        #[0, 4, 8] #[1] 2 1 #[false, true] #[1, 1] #[1, 1]).1
      (aacDecodeMidSide (aacDequantizeChannel p0 #[0, 4, 8] #[1] aacPnsFrameInitSeed).1
        (aacDequantizeChannel p1 #[0, 4, 8] #[1] (aacDequantizeChannel p0 #[0, 4, 8] #[1] aacPnsFrameInitSeed).2).1
        #[0, 4, 8] #[1] 2 1 #[false, true] #[1, 1] #[1, 1]).2
      p1.isScale hmsSz0 hmsSz1
    have htns0 := testTnsOrder1Symbolic _ (aacTnsTmp2Map0_4.getD 2 0.0) hmsSz0 hms0_0 hms0_4 hms0_5
    dsimp only at htns0
    rcases htns0 with ⟨ht0_0, ht0_4, ht0_5⟩
    have htnsOff : ∀ (x : Array Float) (m : Nat), aacApplyTns x {} 3 false m true = x :=
      fun _ _ => rfl
    have hget0 : ∀ (a b : Array Float), (#[a, b].getD 0 #[]) = a := fun _ _ => rfl
    have hget1 : ∀ (a b : Array Float), (#[a, b].getD 1 #[]) = b := fun _ _ => rfl
    rw [hget0, hget1, hp0tns, hp0max, his1, hp1tns, htnsOff]
    exact ⟨ht0_0, ht0_4, ht0_5, hms1_0, hms1_4, hms1_5⟩

theorem aacStream_payload_step_matches_frame_decode
    (adtsBytes : ByteArray) (pSlice : ByteSlice) (hdr : AacLcAdtsHeader) (frm : AacLcFrame)
    (firstFrame : Bool) (saved : Array (Array Float)) (prevKbd : Array Bool)
    (prevSeq : Array AacWindowSequence) (outChans : Array (Array Int32)) (rest : List ByteSlice)
    (hhdr : decodeAacLcAdtsHeader (ByteSlice.ofByteArray adtsBytes) = some hdr)
    (hpay : pSlice.ba.extract pSlice.off (pSlice.off + pSlice.len) =
            adtsBytes.extract hdr.headerBytes adtsBytes.size)
    (hdec : aacDecodeAdtsFrame adtsBytes = some (hdr, frm)) :
    aacDecodeAdtsPayloads hdr.samplingFrequencyIdx hdr.channelConfiguration.toNat
      firstFrame saved prevKbd prevSeq outChans (pSlice :: rest) =
    match aacSynthesizeDecodedFrame frm hdr.channelConfiguration.toNat firstFrame saved prevKbd prevSeq with
    | none => none
    | some (framePcm, saved', prevKbd', prevSeq') =>
      aacDecodeAdtsPayloads hdr.samplingFrequencyIdx hdr.channelConfiguration.toNat
        false saved' prevKbd' prevSeq'
        (aacAppendFramePcm hdr.channelConfiguration.toNat outChans framePcm) rest := by
  have hrawEq : ∃ rngOut,
      aacReadRawDataBlock (adtsBytes.extract hdr.headerBytes adtsBytes.size)
        hdr.samplingFrequencyIdx aacPnsFrameInitSeed = some (frm, rngOut) := by
    unfold aacDecodeAdtsFrame at hdec
    rw [hhdr] at hdec
    dsimp only [Bind.bind, Option.bind] at hdec
    cases hraw : aacReadRawDataBlock (adtsBytes.extract hdr.headerBytes adtsBytes.size)
        hdr.samplingFrequencyIdx aacPnsFrameInitSeed with
    | none =>
      rw [hraw] at hdec
      dsimp only at hdec
      cases hdec
    | some pr =>
      rcases pr with ⟨decoded, rngOut⟩
      rw [hraw] at hdec
      dsimp only at hdec
      cases hch : (decoded.ch.size != hdr.channelConfiguration.toNat)
      · rw [hch] at hdec
        simp only [Bool.false_eq_true, ↓reduceIte] at hdec
        injection hdec with hpair
        injection hpair with _ hfrm
        subst hfrm
        exact ⟨rngOut, rfl⟩
      · rw [hch] at hdec
        simp only [↓reduceIte] at hdec
        cases hdec
  rcases hrawEq with ⟨rngOut, hraw⟩
  conv => lhs; unfold aacDecodeAdtsPayloads
  dsimp only
  rw [hpay, hraw]
  rfl

private def pnsTestRaw : ByteArray :=
  ByteArray.mk #[0, 180, 0, 180, 48, 1, 192]

private def pnsTestAdts : ByteArray :=
  ByteArray.mk #[255, 241, 76, 64, 1, 223, 252, 0, 180, 0, 180, 48, 1, 192]

private def pnsTwoAdts : ByteArray :=
  pnsTestAdts ++ pnsTestAdts

private def pnsHdr0 : AacLcAdtsHeader :=
  { samplingFrequencyIdx := 3, channelConfiguration := 1, frameLength := 14 }

private abbrev pnsAt (off : Nat) : BitReader :=
  { slice := ByteSlice.ofByteArray pnsTestRaw, bitOffset := off }

private theorem pnsGroups_rfl (qInit : Array Int) :
    aacReadIcsGroups (pnsAt 47) qInit #[0, 4] #[13] 1 0 0 [1] =
      some (qInit, pnsAt 47) := rfl

private theorem pnsIcs_step :
    ∃ p,
      aacReadIcs (pnsAt 7) 3 false .onlyLong false #[1] 0 =
        some (p, .onlyLong, false, #[1], pnsAt 47) ∧
      p.maxSfb = 1 ∧
      p.sections = #[{ book := 13, length := 1 }] ∧
      p.pnsGain = #[1.0] ∧
      p.tns = {} := by
  have h1 : (pnsAt 7).readBitsMSB 8 = some (90, pnsAt 15) := rfl
  have h2 : aacReadIcsInfo (pnsAt 15) = some (.onlyLong, false, #[1], 1, pnsAt 26) := rfl
  have h3 : aacReadSections (pnsAt 26) false 1 1 =
      some (#[{ book := 13, length := 1 }], pnsAt 35) := rfl
  have h4 : aacReadScaleFactors (pnsAt 35) #[{ book := 13, length := 1 }] 90 =
      some (#[0], #[0.0], #[1.0], pnsAt 44) := rfl
  have h5 : aacReadPulseData (pnsAt 44) false swbOffsetLong48k = some ({}, pnsAt 45) := rfl
  have h6 : aacReadTns (pnsAt 45) false = some ({}, pnsAt 46) := rfl
  have h7 : (pnsAt 46).readBit = some (0, pnsAt 47) := rfl
  have hswb : swbOffsetLong48k.extract 0 2 = #[0, 4] := by decide
  have hexp : aacExpandSections #[{ book := 13, length := 1 }] = #[13] := by decide
  unfold aacReadIcs
  generalize Array.replicate 1024 (0 : Int) = qInit0
  rw [h1]
  simp only [show (!false) = true from rfl, ↓reduceIte,
    show (90 : UInt64).toNat = 90 from rfl]
  rw [h2]; dsimp only
  simp only [show (.onlyLong == AacWindowSequence.eightShort) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl,
    show (1 > swbOffsetLong48k.size - 1) = False from eq_false (by decide),
    show (#[1] : Array Nat).size = 1 from rfl, hswb]
  rw [h3]; dsimp only
  rw [h4]; dsimp only
  rw [h5]; dsimp only
  rw [h6]; dsimp only
  rw [h7]; dsimp only
  simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hexp]
  rw [pnsGroups_rfl]; dsimp only
  have hpulseOff : aacApplyPulses qInit0 {} swbOffsetLong48k #[13] 1 = some qInit0 := rfl
  rw [hpulseOff]; dsimp only
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

private def pnsR1 : UInt32 := aacPnsNextRng aacPnsFrameInitSeed
private def pnsR4 : UInt32 := aacPnsNextRng (aacPnsNextRng (aacPnsNextRng pnsR1))

private theorem pnsRaw_step :
    ∃ frm,
      aacReadRawDataBlock pnsTestRaw 3 aacPnsFrameInitSeed = some (frm, pnsR4) ∧
      frm.ch.size = 1 ∧
      (frm.ch.getD 0 #[]).getD 4 0.0 = 0.0 := by
  have hbr : BitReader.ofSlice (ByteSlice.ofByteArray pnsTestRaw) = pnsAt 0 := rfl
  have ht0 : (pnsAt 0).readBitsMSB 3 = some (0, pnsAt 3) := rfl
  have ht1 : (pnsAt 3).readBitsMSB 4 = some (0, pnsAt 7) := rfl
  have hend : (pnsAt 47).readBitsMSB 3 = some (7, pnsAt 50) := rfl
  have hswb : swbOffsetLong48k.extract 0 2 = #[0, 4] := by decide
  obtain ⟨p, hp, hpmax, hpsec, hpgain, hptns⟩ := pnsIcs_step
  unfold aacReadRawDataBlock aacReadRawElems
  rw [hbr, ht0]; dsimp only
  simp only [show ((0 : UInt64).toNat == 7) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [ht1]; dsimp only
  simp only [show ((0 : UInt64).toNat == 4) = false from rfl,
    show ((0 : UInt64).toNat == 6) = false from rfl,
    show ((0 : UInt64).toNat == 0) = true from rfl,
    show (Option.isSome none || (0 : UInt64).toNat != 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  rw [hp]; dsimp only
  simp only [show (.onlyLong == AacWindowSequence.eightShort) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show aacSwbOffsetsLong 3 = some swbOffsetLong48k from rfl, hpmax, hswb]
  unfold aacReadRawElems
  rw [hend]; dsimp only
  simp only [show ((7 : UInt64).toNat == 7) = true from rfl, ↓reduceIte, Option.map]
  unfold aacDequantizeChannel
  generalize hz : Array.replicate 1024 (0.0 : Float) = z0
  unfold aacDequantizeGroups aacDequantizeBands
  have hexp : aacExpandSections p.sections = #[13] := by rw [hpsec]; decide
  simp only [hpmax, hexp, hpgain,
    show (#[13] : Array UInt8).getD 0 0 = 13 from rfl,
    show (((13 : UInt8) != 0) && ((13 : UInt8) <= 11)) = false from rfl,
    show ((#[0, 4] : Array Nat).getD 0 0) = 0 from rfl,
    show ((#[0, 4] : Array Nat).getD 1 0) = 4 from rfl,
    show (((13 : UInt8) == 13) && decide (4 > 0)) = true from rfl,
    show (#[1.0] : Array Float).getD 0 0.0 = 1.0 from rfl,
    show 4 - 0 = 4 from rfl,
    Bool.false_eq_true, ↓reduceIte]
  unfold aacPnsDequantWins
  dsimp only
  unfold aacPnsDequantWins aacDequantizeBands aacDequantizeGroups
  dsimp only
  rw [hptns]
  have htnsOff : ∀ (x : Array Float), aacApplyTns x {} 3 false 1 true = x := fun _ => rfl
  rw [htnsOff]
  have hget0 : ∀ (a : Array Float), (#[a].getD 0 #[]) = a := fun _ => rfl
  refine ⟨_, rfl, rfl, ?_⟩
  rw [hget0, pnsScaleBins_preserve_ge _ _ _ 0 0 4 4 (by omega), ← hz,
    getD_replicate_eq 1024 0.0 4 0.0 (by omega)]

private theorem pnsHdr_ok :
    decodeAacLcAdtsHeader (ByteSlice.ofByteArray pnsTestAdts) = some pnsHdr0 := rfl

private theorem pnsDemux_ok :
    demuxAdtsStream (ByteSlice.ofByteArray pnsTwoAdts) false =
      some (pnsHdr0, #[{ ba := pnsTwoAdts, off := 7, len := 7 },
                       { ba := pnsTwoAdts, off := 21, len := 7 }]) := rfl

theorem aacDecodeAdtsStream_two_identical_frames
    (twoAdts singleAdts : ByteArray) (hdr : AacLcAdtsHeader) (ps0 ps1 : ByteSlice)
    (frm : AacLcFrame) (sr : UInt32) (verifyCrc : Bool)
    (hdemux : demuxAdtsStream (ByteSlice.ofByteArray twoAdts) verifyCrc = some (hdr, #[ps0, ps1]))
    (hhdr : decodeAacLcAdtsHeader (ByteSlice.ofByteArray singleAdts) = some hdr)
    (hp0 : ps0.ba.extract ps0.off (ps0.off + ps0.len) =
           singleAdts.extract hdr.headerBytes singleAdts.size)
    (hp1 : ps1.ba.extract ps1.off (ps1.off + ps1.len) =
           singleAdts.extract hdr.headerBytes singleAdts.size)
    (hsr : aacSampleRateFromIndex hdr.samplingFrequencyIdx = some sr)
    (hnch : (hdr.channelConfiguration.toNat != 1 && hdr.channelConfiguration.toNat != 2) = false)
    (hdec : aacDecodeAdtsFrame singleAdts = some (hdr, frm)) :
    aacDecodeAdtsStream (ByteSlice.ofByteArray twoAdts) verifyCrc =
      match aacSynthesizeDecodedFrame frm hdr.channelConfiguration.toNat true
          (Array.replicate hdr.channelConfiguration.toNat (Array.replicate 1024 0.0))
          (Array.replicate hdr.channelConfiguration.toNat false)
          (Array.replicate hdr.channelConfiguration.toNat .onlyLong) with
      | none => none
      | some (pcm0, s1, k1, q1) =>
        match aacSynthesizeDecodedFrame frm hdr.channelConfiguration.toNat false s1 k1 q1 with
        | none => none
        | some (pcm1, _, _, _) =>
          some (aacAppendFramePcm hdr.channelConfiguration.toNat
                  (aacAppendFramePcm hdr.channelConfiguration.toNat
                    (Array.replicate hdr.channelConfiguration.toNat #[]) pcm0) pcm1,
                sr, 16) := by
  have hstep0 := aacStream_payload_step_matches_frame_decode singleAdts ps0 hdr frm true
    (Array.replicate hdr.channelConfiguration.toNat (Array.replicate 1024 0.0))
    (Array.replicate hdr.channelConfiguration.toNat false)
    (Array.replicate hdr.channelConfiguration.toNat .onlyLong)
    (Array.replicate hdr.channelConfiguration.toNat #[]) [ps1] hhdr hp0 hdec
  have hstep1 : ∀ s1 k1 q1 out1,
      aacDecodeAdtsPayloads hdr.samplingFrequencyIdx hdr.channelConfiguration.toNat false s1 k1 q1 out1 [ps1] =
        match aacSynthesizeDecodedFrame frm hdr.channelConfiguration.toNat false s1 k1 q1 with
        | none => none
        | some (pcm1, _, _, _) => some (aacAppendFramePcm hdr.channelConfiguration.toNat out1 pcm1) := by
    intro s1 k1 q1 out1
    have h := aacStream_payload_step_matches_frame_decode singleAdts ps1 hdr frm false
      s1 k1 q1 out1 [] hhdr hp1 hdec
    rw [h]
    generalize aacSynthesizeDecodedFrame = synth1
    cases synth1 frm hdr.channelConfiguration.toNat false s1 k1 q1 with
    | none => rfl
    | some syn1 =>
      rcases syn1 with ⟨pcm1, s2, k2, q2⟩
      rfl
  have hstream :
      aacDecodeAdtsStream (ByteSlice.ofByteArray twoAdts) verifyCrc =
      (match aacDecodeAdtsPayloads hdr.samplingFrequencyIdx hdr.channelConfiguration.toNat true
           (Array.replicate hdr.channelConfiguration.toNat (Array.replicate 1024 0.0))
           (Array.replicate hdr.channelConfiguration.toNat false)
           (Array.replicate hdr.channelConfiguration.toNat .onlyLong)
           (Array.replicate hdr.channelConfiguration.toNat #[]) [ps0, ps1] with
       | none => none
       | some pcm => some (pcm, sr, 16)) := by
    unfold aacDecodeAdtsStream
    generalize Array.replicate 1024 (0.0 : Float) = z0
    rw [hdemux]; dsimp only
    rw [hsr]; dsimp only
    simp only [hnch, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hstream, hstep0]
  simp only [hstep1]
  generalize aacSynthesizeDecodedFrame = synth
  generalize Array.replicate 1024 (0.0 : Float) = z0
  cases synth frm hdr.channelConfiguration.toNat true
      (Array.replicate hdr.channelConfiguration.toNat z0)
      (Array.replicate hdr.channelConfiguration.toNat false)
      (Array.replicate hdr.channelConfiguration.toNat .onlyLong) with
  | none => rfl
  | some syn0 =>
    rcases syn0 with ⟨pcm0, s1, k1, q1⟩
    dsimp only
    cases synth frm hdr.channelConfiguration.toNat false s1 k1 q1 with
    | none => rfl
    | some syn1 =>
      rcases syn1 with ⟨pcm1, s2, k2, q2⟩
      rfl

theorem aacPnsAdts_frame_and_two_frame_stream_deterministic :
    ∃ hdr frm,
      aacReadRawDataBlock pnsTestRaw 3 aacPnsFrameInitSeed = some (frm, pnsR4) ∧
      pnsR4 ≠ aacPnsFrameInitSeed ∧
      (aacPnsGenNoiseBins aacPnsFrameInitSeed 0.0 [] 4).2.2.getD 0 0.0 =
        Float.ofInt pnsR1.toInt32.toInt ∧
      (frm.ch.getD 0 #[]).getD 4 0.0 = 0.0 ∧
      aacDecodeAdtsFrame pnsTestAdts = some (hdr, frm) ∧
      aacDecodeAdtsStream (ByteSlice.ofByteArray pnsTwoAdts) false =
        let nch := hdr.channelConfiguration.toNat
        match aacSynthesizeDecodedFrame frm nch true
            (Array.replicate nch (Array.replicate 1024 0.0))
            (Array.replicate nch false)
            (Array.replicate nch .onlyLong) with
        | none => none
        | some (pcm0, s1, k1, q1) =>
          match aacSynthesizeDecodedFrame frm nch false s1 k1 q1 with
          | none => none
          | some (pcm1, _, _, _) =>
            some (aacAppendFramePcm nch (aacAppendFramePcm nch (Array.replicate nch #[]) pcm0) pcm1,
                  48000, 16) := by
  rcases pnsRaw_step with ⟨frm, hrawEq, hfrmCh, hbin4Eq⟩
  have hhdr := pnsHdr_ok
  have hextr : pnsTestAdts.extract pnsHdr0.headerBytes pnsTestAdts.size = pnsTestRaw := by decide
  have hframeDec : aacDecodeAdtsFrame pnsTestAdts = some (pnsHdr0, frm) := by
    unfold aacDecodeAdtsFrame
    rw [hhdr]; dsimp only [Bind.bind, Option.bind]
    rw [hextr, show pnsHdr0.samplingFrequencyIdx = 3 from rfl, hrawEq]; dsimp only
    have hchOk : (frm.ch.size != pnsHdr0.channelConfiguration.toNat) = false := by
      rw [hfrmCh]; rfl
    simp only [hchOk, Bool.false_eq_true, ↓reduceIte]
  let ps0 : ByteSlice := { ba := pnsTwoAdts, off := 7, len := 7 }
  let ps1 : ByteSlice := { ba := pnsTwoAdts, off := 21, len := 7 }
  have hp0' : ps0.ba.extract ps0.off (ps0.off + ps0.len) =
      pnsTestAdts.extract pnsHdr0.headerBytes pnsTestAdts.size := by decide
  have hp1' : ps1.ba.extract ps1.off (ps1.off + ps1.len) =
      pnsTestAdts.extract pnsHdr0.headerBytes pnsTestAdts.size := by decide
  refine ⟨pnsHdr0, frm, hrawEq, by decide, rfl, hbin4Eq, hframeDec, ?_⟩
  exact aacDecodeAdtsStream_two_identical_frames pnsTwoAdts pnsTestAdts pnsHdr0 ps0 ps1
    frm 48000 false pnsDemux_ok hhdr hp0' hp1' rfl rfl hframeDec

end LeanAV.AacLcProofs
