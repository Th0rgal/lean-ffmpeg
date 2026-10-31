import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Bitstream
import LeanAV.H264Entropy

namespace LeanAV.H264EntropyProofs

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Bitstream
open LeanAV.H264Entropy

theorem entropyMode_parse_toString_roundtrip (m : EntropyMode) :
    EntropyMode.parse m.toString = some m := by
  cases m <;> decide

theorem entropyMode_parse_same_alias_and_rejects_unknown :
    EntropyMode.parse "same" = some .preserve ∧
    EntropyMode.parse "preserve" = some .preserve ∧
    EntropyMode.parse "cavlc" = some .cavlc ∧
    EntropyMode.parse "cabac" = some .cabac ∧
    EntropyMode.parse "invalid" = none := by
  decide

def entropyModeValidGate (s : String) : Bool :=
  (EntropyMode.parse s).isSome

def entropyModeValidSpec : AVGateSpec String (fun s => ∃ m, EntropyMode.parse s = some m) where
  gate := entropyModeValidGate
  sound := by
    intro s hg
    unfold entropyModeValidGate at hg
    cases h : EntropyMode.parse s with
    | none => simp [h] at hg
    | some m => exact ⟨m, rfl⟩
  complete := by
    intro s ⟨m, hm⟩
    unfold entropyModeValidGate
    simp [hm]
  posWitness := "cabac"
  negWitness := "vp9"
  nonVacuous := by decide
  tight := by decide

theorem blk4XY_xyToBlk4_bijection :
    blk4XY.size = 16 ∧
    ((List.range 16).all fun idx =>
      let (x, y) := blk4XY.getD idx (99, 99)
      x < 4 && y < 4 && xyToBlk4 x y == idx) = true ∧
    ((List.range 4).all fun y =>
      (List.range 4).all fun x =>
        let idx := xyToBlk4 x y
        idx < 16 && blk4XY.getD idx (99, 99) == (x, y)) = true := by
  decide

theorem rbspEmulation_insert_and_strip_roundtrip :
    let raw : ByteArray := { data := #[0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x02, 0x00, 0x00, 0x03, 0x5A] }
    let escaped := addRbspEmulationBytes raw
    escaped.data.size > raw.data.size ∧
    (stripNalEmulationBytes ({ data := #[0x65] ++ escaped.data })).data = #[0x65] ++ raw.data := by
  decide

theorem annexB_split_short_rejected_and_startcodes_parsed :
    let s3 : ByteArray := { data := #[0x00, 0x00, 0x01, 0x67, 0x42, 0x00, 0x0A, 0x00, 0x00, 0x00, 0x01, 0x68, 0xCE] }
    let nals := splitAnnexB s3
    (nals.size == 2 &&
     (nals.getD 0 { data := #[] }).data == #[0x67, 0x42, 0x00, 0x0A] &&
     (nals.getD 1 { data := #[] }).data == #[0x68, 0xCE] &&
     (splitAnnexB ({ data := #[0x00, 0x01] })).size == 0) = true := by
  decide

def supportedChromaAndBitDepthGate (p : Nat × Nat × Nat × Nat) : Bool :=
  let (chromaIdc, sepFlag, bdY, bdC) := p
  (chromaIdc == 0 || chromaIdc == 1) && sepFlag == 0 && bdY ≤ 6 && bdC ≤ 6

def supportedChromaAndBitDepthSpec :
    AVGateSpec (Nat × Nat × Nat × Nat)
      (fun p => (p.1 = 0 ∨ p.1 = 1) ∧ p.2.1 = 0 ∧ p.2.2.1 ≤ 6 ∧ p.2.2.2 ≤ 6) where
  gate := supportedChromaAndBitDepthGate
  sound := by
    intro ⟨c, s, by0, bc0⟩ hg
    unfold supportedChromaAndBitDepthGate at hg
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1, hg.1.1.2, hg.1.2, hg.2⟩
  complete := by
    intro ⟨c, s, by0, bc0⟩ ⟨hc, hs, hby, hbc⟩
    unfold supportedChromaAndBitDepthGate
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨hc, hs⟩, hby⟩, hbc⟩
  posWitness := (1, 0, 2, 2)
  negWitness := (2, 0, 0, 0)
  nonVacuous := by decide
  tight := by decide

def cavlcZeroBudgetGate (p : Nat × Nat × Nat) : Bool :=
  let (tc, zerosLeft, maxCoeff) := p
  0 < maxCoeff && maxCoeff ≤ 16 && tc ≤ maxCoeff && tc + zerosLeft ≤ maxCoeff

def cavlcZeroBudgetSpec :
    AVGateSpec (Nat × Nat × Nat)
      (fun p => 0 < p.2.2 ∧ p.2.2 ≤ 16 ∧ p.1 ≤ p.2.2 ∧ p.1 + p.2.1 ≤ p.2.2) where
  gate := cavlcZeroBudgetGate
  sound := by
    intro ⟨tc, zl, mc⟩ hg
    unfold cavlcZeroBudgetGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1, hg.1.1.2, hg.1.2, hg.2⟩
  complete := by
    intro ⟨tc, zl, mc⟩ ⟨h0, h1, h2, h3⟩
    unfold cavlcZeroBudgetGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  posWitness := (5, 7, 16)
  negWitness := (10, 8, 16)
  nonVacuous := by decide
  tight := by decide

def h264SliceNalTypeGate (nalHdr : UInt8) : Bool :=
  let nt := (nalHdr &&& 0x1F).toNat
  nt == 1 || nt == 5

def h264SliceNalTypeSpec :
    AVGateSpec UInt8 (fun b => (b &&& 0x1F).toNat = 1 ∨ (b &&& 0x1F).toNat = 5) where
  gate := h264SliceNalTypeGate
  sound := by
    intro b hg
    unfold h264SliceNalTypeGate at hg
    simp only [Bool.or_eq_true, beq_iff_eq] at hg
    exact hg
  complete := by
    intro b h
    unfold h264SliceNalTypeGate
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact h
  posWitness := 0x65
  negWitness := 0x62
  nonVacuous := by decide
  tight := by decide

def cabacStateByteGate (b : UInt8) : Bool :=
  b.toNat < 128

def cabacStateByteSpec : AVGateSpec UInt8 (fun b => b.toNat < 128) where
  gate := cabacStateByteGate
  sound := by
    intro b hg
    unfold cabacStateByteGate at hg
    simpa using hg
  complete := by
    intro b h
    unfold cabacStateByteGate
    simpa using h
  posWitness := 127
  negWitness := 128
  nonVacuous := by decide
  tight := by decide

def cavlcSignedLevelToCode (v : Int) : Nat :=
  let a := v.natAbs
  if v > 0 then 2 * a - 2 else 2 * a - 1

def cavlcCodeToSignedLevel (lc : Nat) : Int :=
  let mag : Int := ↑((lc + 2) / 2)
  if lc % 2 == 1 then -mag else mag

theorem cavlcSignedLevel_decode_encode_nonzero (v : Int) (hv : v ≠ 0) :
    cavlcCodeToSignedLevel (cavlcSignedLevelToCode v) = v := by
  unfold cavlcSignedLevelToCode cavlcCodeToSignedLevel
  by_cases hpos : v > 0
  · simp only [hpos, ↓reduceIte]
    have ha : 1 ≤ v.natAbs := by omega
    have hmod : ((2 * v.natAbs - 2) % 2 == 1) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [hmod]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [hpos, ↓reduceIte]
    have ha : 1 ≤ v.natAbs := by omega
    have hmod : ((2 * v.natAbs - 1) % 2 == 1) = true := by
      rw [beq_iff_eq]
      omega
    rw [hmod]
    simp only [↓reduceIte]
    omega

theorem cavlcSignedLevel_encode_decode_roundtrip (lc : Nat) :
    cavlcSignedLevelToCode (cavlcCodeToSignedLevel lc) = lc := by
  unfold cavlcCodeToSignedLevel cavlcSignedLevelToCode
  by_cases hodd : lc % 2 = 1
  · have hb : (lc % 2 == 1) = true := beq_iff_eq.mpr hodd
    rw [hb]
    simp only [↓reduceIte]
    have hnotpos : ¬ (-(↑((lc + 2) / 2) : Int) > 0) := by omega
    simp only [hnotpos, ↓reduceIte]
    omega
  · have hb : (lc % 2 == 1) = false := beq_eq_false_iff_ne.mpr hodd
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hpos : (↑((lc + 2) / 2) : Int) > 0 := by omega
    simp only [hpos, ↓reduceIte]
    omega

theorem cavlcSignedLevel_encode_injective (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : cavlcSignedLevelToCode a = cavlcSignedLevelToCode b) : a = b := by
  have h1 := cavlcSignedLevel_decode_encode_nonzero a ha
  have h2 := cavlcSignedLevel_decode_encode_nonzero b hb
  rw [← h1, ← h2, heq]

def cavlcLargeEscapeEncode (lc sl : Nat) : Nat × Nat × Nat :=
  let rem := if sl == 0 then lc - 30 else lc - (15 <<< sl)
  if rem < 4096 then
    (15, 12, rem)
  else
    let rec findP (p fuel : Nat) : Nat :=
      match fuel with
      | 0 => p
      | f + 1 => if rem ≥ ((1 <<< (p - 2)) - 4096) then findP (p + 1) f else p
    let p := findP 16 20
    let base := (1 <<< (p - 3)) - 4096
    (p, p - 3, rem - base)

def cavlcLargeEscapeDecode (pref sl lsuf0 : Nat) : Nat :=
  let lsuf := if pref ≥ 16 then lsuf0 + ((1 <<< (pref - 3)) - 4096) else lsuf0
  let baseLc := (15 <<< sl) + lsuf
  if sl == 0 then baseLc + 15 else baseLc

set_option maxRecDepth 400000 in
theorem cavlcLargeEscape_itu_roundtrip_across_suffixLengths :
    cavlcLargeEscapeDecode 15 0 0 = 30 ∧
    cavlcLargeEscapeDecode 15 1 0 = 30 ∧
    cavlcLargeEscapeDecode 16 1 0 = 4126 ∧
    ((List.range 7).all fun sl =>
      let minLc := if sl == 0 then 30 else 15 <<< sl
      [minLc, minLc + 1, minLc + 4095, minLc + 4096, minLc + 4851, minLc + 12345].all fun lc =>
        let (pref, lsz, lsuf0) := cavlcLargeEscapeEncode lc sl
        lsuf0 < (1 <<< lsz) && cavlcLargeEscapeDecode pref sl lsuf0 == lc) = true ∧
    (let lcHigh10 := cavlcSignedLevelToCode (-2426)
     let (pref, lsz, lsuf0) := cavlcLargeEscapeEncode lcHigh10 2
     pref == 16 && lsz == 13 &&
     cavlcCodeToSignedLevel (cavlcLargeEscapeDecode pref 2 lsuf0) == -2426) = true := by
  decide

def lookupNatIdxPure : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, target, idx => if x == target then some idx else lookupNatIdxPure xs target (idx + 1)

set_option maxRecDepth 400000 in
theorem cavlcCbpTables_bijection_420_and_monochrome :
    cavlcCbpIntraDec.size = 48 ∧
    cavlcCbpInterDec.size = 48 ∧
    cavlcCbpIntraGrayDec.size = 16 ∧
    cavlcCbpInterGrayDec.size = 16 ∧
    ((List.range 48).all fun cbp =>
      match lookupNatIdxPure cavlcCbpIntraDec.toList cbp 0,
            lookupNatIdxPure cavlcCbpInterDec.toList cbp 0 with
      | some ci, some ce =>
        ci < 48 && ce < 48 && cavlcCbpIntraDec.getD ci 999 == cbp && cavlcCbpInterDec.getD ce 999 == cbp
      | _, _ => false) = true ∧
    ((List.range 16).all fun cbp =>
      match lookupNatIdxPure cavlcCbpIntraGrayDec.toList cbp 0,
            lookupNatIdxPure cavlcCbpInterGrayDec.toList cbp 0 with
      | some ci, some ce =>
        ci < 16 && ce < 16 && cavlcCbpIntraGrayDec.getD ci 999 == cbp && cavlcCbpInterGrayDec.getD ce 999 == cbp
      | _, _ => false) = true := by
  decide

set_option maxRecDepth 200000 in
theorem cavlcPackedVlcTables_prefix_decode_exact :
    let testEntry (tab : Array UInt32) (base count sym : Nat) : Bool :=
      let packed := tab.getD (base + sym) 0
      let len := (packed >>> 16).toNat
      if len == 0 then true
      else
        let code := (packed &&& 0xFFFF).toUInt64
        let w := (BitWriter.empty.writeBitsMSB code len).writeBitsMSB 0 16
        let outBa := w.toByteArray
        let r0 : BitReader := { slice := { ba := outBa, off := 0, len := outBa.data.size }, bitOffset := 0 }
        match readPackedVlc r0 tab base count with
        | some (decSym, rEnd) => decSym == sym && rEnd.bitOffset == len
        | none => false
    cavlcCtEnc0.size = 68 ∧
    cavlcCtEnc1.size = 68 ∧
    cavlcCtEnc2.size = 68 ∧
    cavlcCtEnc3.size = 68 ∧
    cavlcCtChromaDcEnc.size = 20 ∧
    cavlcTz16Enc.size = 240 ∧
    cavlcTz4Enc.size = 12 ∧
    cavlcRunBeforeEnc.size = 105 ∧
    ([0, 4, 5, 15, 67].all fun s =>
      testEntry cavlcCtEnc0 0 68 s &&
      testEntry cavlcCtEnc1 0 68 s &&
      testEntry cavlcCtEnc2 0 68 s &&
      testEntry cavlcCtEnc3 0 68 s) = true ∧
    ([0, 5, 19].all fun s => testEntry cavlcCtChromaDcEnc 0 20 s) = true ∧
    ([0, 7, 14].all fun r => testEntry cavlcRunBeforeEnc (6 * 15) 15 r) = true := by
  decide

set_option maxRecDepth 400000 in
theorem cabacTables_bounds_and_state_transition_closure :
    cabacRangeTabLPS.size = 256 ∧
    cabacTransIdxLPS.size = 64 ∧
    cabacTransIdxMPS.size = 64 ∧
    cabacLast8x8.size = 63 ∧
    cabacSig8x8Frame.size = 63 ∧
    ((List.range 256).all fun k =>
      let r := cabacRangeTabLPS.getD k 0
      2 ≤ r && r ≤ 240) = true ∧
    ((List.range 64).all fun s =>
      cabacTransIdxLPS.getD s 99 < 64 && cabacTransIdxMPS.getD s 99 < 64) = true ∧
    ((List.range 63).all fun k =>
      cabacLast8x8.getD k 99 ≤ 8 && cabacSig8x8Frame.getD k 99 ≤ 14) = true ∧
    cabacTransIdxMPS.getD 62 0 = 62 ∧
    cabacTransIdxMPS.getD 63 0 = 63 ∧
    cabacTransIdxLPS.getD 63 0 = 63 := by
  decide

def cabacPackStateFromPre (pre : Nat) : UInt8 :=
  if pre ≤ 63 then ((63 - pre) * 2).toUInt8
  else ((pre - 64) * 2 + 1).toUInt8

def unpackCabacInitPure (packed : Nat) (qp : Int) : UInt8 :=
  let m : Int := Int.ofNat (packed >>> 8) - 128
  let n : Int := Int.ofNat (packed &&& 0xFF) - 128
  let raw : Int := Int.ediv (m * qp) 16 + n
  let pre : Nat := if raw ≤ 1 then 1 else if raw ≥ 126 then 126 else raw.toNat
  cabacPackStateFromPre pre

theorem cabacPackStateFromPre_7bit (pre : Nat) (h1 : 1 ≤ pre) (h126 : pre ≤ 126) :
    cabacStateByteGate (cabacPackStateFromPre pre) = true := by
  unfold cabacStateByteGate cabacPackStateFromPre
  split
  · next hle =>
    have hlt : (63 - pre) * 2 < 128 := by omega
    have h256 : (63 - pre) * 2 < 256 := by omega
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h256, hlt]
  · next hgt =>
    have hlt : (pre - 64) * 2 + 1 < 128 := by omega
    have h256 : (pre - 64) * 2 + 1 < 256 := by omega
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h256, hlt]

theorem unpackCabacInitPure_7bit_universal (packed : Nat) (qp : Int) :
    cabacStateByteGate (unpackCabacInitPure packed qp) = true := by
  unfold unpackCabacInitPure
  dsimp only
  apply cabacPackStateFromPre_7bit
  · split
    · omega
    · split <;> omega
  · split
    · omega
    · split <;> omega

set_option maxRecDepth 200000 in
theorem cabacInitTables_spot_exact :
    cabacInitI460.getD 0 0 = 38001 ∧
    cabacInitI1012.getD 0 0 = 32198 ∧
    cabacInitPB460_0.getD 11 0 = 38817 ∧
    cabacInitPB460_2.getD 11 0 = 40336 ∧
    cabacInitPB1012_2.getD 0 0 = 31695 ∧
    unpackCabacInitPure (cabacInitI460.getD 0 0) 26 = 92 := by
  decide

set_option maxRecDepth 400000 in
theorem cabacArithmeticCore_decision_bypass_terminate_roundtrip :
    let st0 : Array UInt8 := #[42, 81, 12, 119]
    let e0 := CabacEnc.init BitWriter.empty
    let (e1, s1) := e0.encodeDecision st0 0 1
    let (e2, s2) := e1.encodeDecision s1 1 0
    let (e3, s3) := e2.encodeDecision s2 0 1
    let (e4, s4) := e3.encodeDecision s3 2 0
    let (e5, _)  := e4.encodeDecision s4 3 1
    let e6 := ((e5.encodeBypass 1).encodeBypass 0).encodeBypass 1
    let e7 := (e6.encodeTerminate 0).encodeTerminate 1
    let d0 := CabacDec.init e7.w.toByteArray 0
    let (b0, d1, ds1) := d0.decodeDecision st0 0
    let (b1, d2, ds2) := d1.decodeDecision ds1 1
    let (b2, d3, ds3) := d2.decodeDecision ds2 0
    let (b3, d4, ds4) := d3.decodeDecision ds3 2
    let (b4, d5, _)   := d4.decodeDecision ds4 3
    let (bp0, d6) := d5.decodeBypass
    let (bp1, d7) := d6.decodeBypass
    let (bp2, d8) := d7.decodeBypass
    let (t0, d9)  := d8.decodeTerminate
    let (t1, _)   := d9.decodeTerminate
    (b0 == 1 && b1 == 0 && b2 == 1 && b3 == 0 && b4 == 1 &&
     bp0 == 1 && bp1 == 0 && bp2 == 1 && t0 == 0 && t1 == 1) = true := by
  decide

set_option maxRecDepth 200000 in
theorem cabacPcmReinit_byteAligned_roundtrip :
    let pcm : ByteArray := { data := #[0x11, 0x22, 0x33, 0x44] }
    let e0 := CabacEnc.init { bytes := pcm, curByte := 0, bitsUsed := 0 }
    let (e1, _) := e0.encodeDecision #[20] 0 0
    let e2 := e1.encodeTerminate 1
    let rbsp := e2.w.toByteArray
    let dInit : CabacDec := { rbsp := rbsp, pos := 0, total := rbsp.data.size * 8, irange := 510, ioffset := 0 }
    (match dInit.readPcmAndReinit 4 with
     | none => false
     | some (pcmOut, d2) =>
       let (bAfter, d3, _) := d2.decodeDecision #[20] 0
       let (tEnd, _) := d3.decodeTerminate
       pcmOut.data == pcm.data && bAfter == 0 && tEnd == 1) = true := by
  decide

theorem cabacPcmReinit_rejects_truncated_buffer :
    let d0 := CabacDec.init ({ data := #[0x00, 0x00] }) 0
    (d0.readPcmAndReinit 16).isNone = true := by
  decide

theorem mbKind_intra_inter_disjoint (k : MbKind) :
    ¬ (k.isIntra = true ∧ k.isInter = true) := by
  cases k <;> decide

theorem mbPartitionTables_itu_cardinalities :
    pMbInfoTable.size = 5 ∧
    pSubInfoTable.size = 4 ∧
    bMbInfoTable.size = 23 ∧
    bSubInfoTable.size = 13 ∧
    (pMbInfoTable.getD 4 {}).isRef0 = true ∧
    (pMbInfoTable.getD 3 {}).isRef0 = false := by
  decide

theorem pcmByteCount_420_and_monochrome_exact (sps : SpsFull) :
    (sps.chromaFormatIdc = 0 → sps.bitDepthLumaMinus8 = 0 → pcmByteCount sps = 256) ∧
    (sps.chromaFormatIdc = 1 → sps.bitDepthLumaMinus8 = 0 → sps.bitDepthChromaMinus8 = 0 → pcmByteCount sps = 384) ∧
    (sps.chromaFormatIdc = 1 → sps.bitDepthLumaMinus8 = 2 → sps.bitDepthChromaMinus8 = 2 → pcmByteCount sps = 480) := by
  unfold pcmByteCount
  refine ⟨?_, ?_, ?_⟩
  · intro hc hy; simp [hc, hy]
  · intro hc hy hcb; simp [hc, hy, hcb]
  · intro hc hy hcb; simp [hc, hy, hcb]

theorem cabacCbfCtx_unavailable_defaults_intra_one_inter_zero :
    let g := MbGrid.init 2 2
    let z16 := Array.replicate 16 0
    let zc := #[Array.replicate 4 0, Array.replicate 4 0]
    cabacCbfCtx g 0 0 true 0 z16 zc 0 = 88 ∧
    cabacCbfCtx g 0 0 false 0 z16 zc 0 = 85 ∧
    cabacCbfCtx g 0 0 true 2 z16 zc 0 = 96 ∧
    cabacCbfCtx g 0 0 false 2 z16 zc 0 = 93 ∧
    cabacCbfCtx g 0 0 true 3 z16 zc 0 = 100 ∧
    cabacCbfCtx g 0 0 false 3 z16 zc 0 = 97 := by
  decide

set_option maxRecDepth 200000 in
theorem pps_serialize_parse_noMoreRbsp_override_roundtrip :
    let sps : SpsFull := {
      profileIdc := 77, constraintFlags := 0, levelIdc := 10, spsId := 0,
      chromaFormatIdc := 1, separateColourPlaneFlag := 0, bitDepthLumaMinus8 := 0,
      bitDepthChromaMinus8 := 0, qpprimeYZeroTransformBypassFlag := 0,
      log2MaxFrameNum := 4, picOrderCntType := 0, log2MaxPocLsb := 4,
      deltaPicOrderAlwaysZeroFlag := 0, maxNumRefFrames := 2,
      picWidthInMbs := 2, picHeightInMapUnits := 2, frameMbsOnlyFlag := 1,
      direct8x8InferenceFlag := 1, rawNal := { data := #[] }
    }
    let spsList : Array (Option SpsFull) := #[some sps]
    let pps0 : PpsFull := {
      nalHdr := 0x68, ppsId := 0, spsId := 0, entropyCodingModeFlag := 0,
      bottomFieldPicOrderInFramePresentFlag := 0, numSliceGroupsMinus1 := 0,
      numRefIdxL0DefaultActiveMinus1 := 1, numRefIdxL1DefaultActiveMinus1 := 0,
      weightedPredFlag := 1, weightedBipredIdc := 2, picInitQpMinus26 := -4,
      picInitQsMinus26 := 0, chromaQpIndexOffset := -2,
      deblockingFilterControlPresentFlag := 1, constrainedIntraPredFlag := 0,
      redundantPicCntPresentFlag := 0, hasMoreRbsp := false, transform8x8ModeFlag := 0,
      picScalingBits := #[], secondChromaQpIndexOffset := -2
    }
    let nalCabac := serializePps pps0 (some 1)
    let nalCavlc := serializePps pps0 (some 0)
    (match parsePpsFull nalCabac spsList, parsePpsFull nalCavlc spsList with
     | some pCab, some pCav =>
       pCab.entropyCodingModeFlag == 1 && pCav.entropyCodingModeFlag == 0 &&
       pCab.picInitQpMinus26 == -4 &&
       pCab.weightedBipredIdc == 2 && pCav.chromaQpIndexOffset == -2
     | _, _ => false) = true := by
  decide

set_option maxRecDepth 200000 in
theorem sps_baseline_upgradeForCabac_promotes_to_main :
    let baseSpsNal : ByteArray := { data := #[0x67, 0x42, 0xC0, 0x0A, 0x8C, 0x8D, 0x40, 0x50, 0x17, 0xFC, 0xB8, 0x08, 0x80] }
    let sps0 : SpsFull := {
      profileIdc := 66, constraintFlags := 0xC0, levelIdc := 10, spsId := 0,
      chromaFormatIdc := 1, separateColourPlaneFlag := 0, bitDepthLumaMinus8 := 0,
      bitDepthChromaMinus8 := 0, qpprimeYZeroTransformBypassFlag := 0,
      log2MaxFrameNum := 4, picOrderCntType := 0, log2MaxPocLsb := 4,
      deltaPicOrderAlwaysZeroFlag := 0, maxNumRefFrames := 1,
      picWidthInMbs := 2, picHeightInMapUnits := 2, frameMbsOnlyFlag := 1,
      direct8x8InferenceFlag := 1, rawNal := baseSpsNal
    }
    let upg := upgradeSpsForCabac sps0
    let nonBase := upgradeSpsForCabac { sps0 with rawNal := { data := #[0x67, 0x64, 0x00, 0x0A] } }
    (upg.data.getD 0 0 == 0x67 &&
     upg.data.getD 1 0 == 77 &&
     (upg.data.getD 2 0 &&& 0x80) == 0 &&
     nonBase.data.getD 1 0 == 0x64) = true := by
  decide

set_option maxRecDepth 200000 in
theorem transcodeAnnexB_rejects_empty_and_data_partitioned_nal :
    let isErr (r : Except String ByteArray) (msg : String) : Bool :=
      match r with
      | .error e => e == msg
      | .ok _ => false
    isErr (transcodeAnnexB ({ data := #[] }) .preserve) "No H.264 Annex-B NAL units found" = true ∧
    isErr (transcodeAnnexB ({ data := #[0x00, 0x00, 0x00, 0x01, 0x62, 0xAA] }) .preserve)
      "Unsupported H.264 data-partitioned slice NAL" = true ∧
    isErr (transcodeAnnexB ({ data := #[0x00, 0x00, 0x00, 0x01, 0x67, 0x42] }) .preserve)
      "Unsupported or malformed H.264 SPS NAL" = true := by
  decide

end LeanAV.H264EntropyProofs
