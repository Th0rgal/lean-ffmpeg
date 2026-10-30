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
    AVGateSpec AacLcAsc (fun asc => isValidAacLcAsc asc = true) where
  gate := aacLcAscValidGate
  sound _ hg := by
    simpa [aacLcAscValidGate] using hg
  complete _ hs := by
    simpa [aacLcAscValidGate] using hs
  posWitness := { samplingFrequencyIndex := 3, channelConfiguration := 2 }
  negWitness := { audioObjectType := 1, samplingFrequencyIndex := 3, channelConfiguration := 2 }
  nonVacuous := by decide
  tight := by decide

theorem aacLcAscValidSpec_iff (asc : AacLcAsc) :
    aacLcAscValidSpec.gate asc = true ↔ isValidAacLcAsc asc = true :=
  aacLcAscValidSpec.iff_safe asc

def aacLcAdtsHeaderValidGate (h : AacLcAdtsHeader) : Bool :=
  isValidAacLcAdtsHeader h

def aacLcAdtsHeaderValidSpec :
    AVGateSpec AacLcAdtsHeader (fun h => isValidAacLcAdtsHeader h = true) where
  gate := aacLcAdtsHeaderValidGate
  sound _ hg := by
    simpa [aacLcAdtsHeaderValidGate] using hg
  complete _ hs := by
    simpa [aacLcAdtsHeaderValidGate] using hs
  posWitness := {
    samplingFrequencyIdx := 3
    channelConfiguration := 2
    frameLength := 7
  }
  negWitness := {
    samplingFrequencyIdx := 15
    channelConfiguration := 2
    frameLength := 7
  }
  nonVacuous := by decide
  tight := by decide

theorem aacLcAdtsHeaderValidSpec_iff (h : AacLcAdtsHeader) :
    aacLcAdtsHeaderValidSpec.gate h = true ↔ isValidAacLcAdtsHeader h = true :=
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
    AVGateSpec (AacWindowSequence × AacWindowSequence)
      (fun p => isValidAacWindowTransition p.1 p.2 = true) where
  gate := aacWindowTransitionValidGate
  sound _ hg := by
    simpa [aacWindowTransitionValidGate] using hg
  complete _ hs := by
    simpa [aacWindowTransitionValidGate] using hs
  posWitness := (.onlyLong, .longStart)
  negWitness := (.onlyLong, .eightShort)
  nonVacuous := by decide
  tight := by decide

theorem aacWindowTransitionValidSpec_iff (p : AacWindowSequence × AacWindowSequence) :
    aacWindowTransitionValidSpec.gate p = true ↔ isValidAacWindowTransition p.1 p.2 = true :=
  aacWindowTransitionValidSpec.iff_safe p

theorem aacTnsMaxOrder_lc :
    aacTnsMaxOrder false = 12 ∧ aacTnsMaxOrder true = 7 := by
  decide

theorem aacTnsMaxBands_short_48k :
    aacTnsMaxBandsShort.getD 3 0 = 14 ∧ aacTnsMaxBandsShort.getD 4 0 = 14 ∧
      aacTnsMaxBandsShort.getD 5 0 = 14 := by
  decide

theorem aacMidSide_int_butterfly (l r : Int) :
    let m2 := l + r
    let s2 := l - r
    m2 + s2 = 2 * l ∧ m2 - s2 = 2 * r := by
  dsimp only
  omega

def aacEscapeN (mag : Nat) : Option Nat :=
  if mag < 16 || mag > 8191 then none
  else
    let rec loop (fuel mag' : Nat) : Nat :=
      match fuel with
      | 0 => 0
      | fuel' + 1 =>
        if (1 <<< (fuel' + 4)) <= mag' then fuel'
        else loop fuel' mag'
    some (loop 9 mag)

theorem aacEscapeN_16 : aacEscapeN 16 = some 0 := by decide
theorem aacEscapeN_31 : aacEscapeN 31 = some 0 := by decide
theorem aacEscapeN_32 : aacEscapeN 32 = some 1 := by decide
theorem aacEscapeN_8191 : aacEscapeN 8191 = some 8 := by decide
theorem aacEscapeN_rejects_15 : aacEscapeN 15 = none := by decide
theorem aacEscapeN_rejects_8192 : aacEscapeN 8192 = none := by decide

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

def aacCbIndexList (book : Nat) (vals : List Int) : Option Nat :=
  let dim := aacCbDim book
  if dim == 0 || vals.length != dim then none
  else
    let signed := aacCbSigned book
    let maxA := aacCbMaxAbs book
    let off := aacCbOff book
    let base := if signed then 2 * maxA + 1 else maxA + 1
    vals.foldlM (fun idx v =>
      if signed then
        if v < -(maxA : Int) || v > (maxA : Int) then none
        else some (idx * base + (v + (off : Int)).toNat)
      else
        let a := if book == 11 then Nat.min 16 v.natAbs else v.natAbs
        if a > maxA then none else some (idx * base + a)) 0

theorem aacCbIndexList_zero_book1 :
    aacCbIndexList 1 [0, 0, 0, 0] = some 40 := by
  decide

theorem aacCbIndexList_signed_book1 :
    aacCbIndexList 1 [-1, 0, 1, -1] = some 15 := by
  decide

theorem aacCbIndexList_escape_book11 :
    aacCbIndexList 11 [-512, 8191] = some (16 * 17 + 16) := by
  decide

def aacCbUnpackList (book idx : Nat) : List Int :=
  let dim := aacCbDim book
  let signed := aacCbSigned book
  let maxA := aacCbMaxAbs book
  let off := aacCbOff book
  let base := if signed then 2 * maxA + 1 else maxA + 1
  if dim == 0 || base == 0 then []
  else
    let rec go (k rem : Nat) (acc : List Int) : List Int :=
      match k with
      | 0 => acc
      | k' + 1 =>
        let d := rem % base
        let v : Int := if signed then (d : Int) - (off : Int) else (d : Int)
        go k' (rem / base) (v :: acc)
    go dim idx []

theorem aacCbIndex_unpack_book1_zero :
    aacCbUnpackList 1 40 = [0, 0, 0, 0] := by
  decide

theorem aacCbIndex_unpack_book11_escape :
    aacCbUnpackList 11 (16 * 17 + 16) = [16, 16] := by
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

def aacBuildSectionsList (books : List UInt8) : List (UInt8 × Nat) :=
  let rec go (rest : List UInt8) (cur : UInt8) (len : Nat) (acc : List (UInt8 × Nat)) : List (UInt8 × Nat) :=
    match rest with
    | [] => (cur, len) :: acc
    | b :: bs =>
      if b == cur then go bs cur (len + 1) acc
      else go bs b 1 ((cur, len) :: acc)
  match books with
  | [] => []
  | b :: bs => (go bs b 1 []).reverse

def aacExpandSectionsList (secs : List (UInt8 × Nat)) : List UInt8 :=
  secs.flatMap fun (b, n) => List.replicate n b

theorem aacSections_list_roundtrip :
    let books : List UInt8 := [1, 1, 0, 0, 0, 7, 11, 11]
    aacExpandSectionsList (aacBuildSectionsList books) = books := by
  decide

theorem aacMuxDemuxAdts_payload_present :
    let payload := ByteArray.mk #[0x21, 0x10]
    (match muxAdtsFrame 3 2 payload false with
     | some frm => frm.size == 9 && (decodeAacLcAdtsHeader (ByteSlice.ofByteArray frm)).isSome
     | none => false) = true := by
  decide

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

end LeanAV.AacLcProofs
