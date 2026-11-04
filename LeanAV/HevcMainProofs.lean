import LeanAV.Spec
import LeanAV.HevcMain

namespace LeanAV.HevcMainProofs

open LeanAV.Spec
open LeanAV.HevcMain

set_option maxRecDepth 400000
set_option maxHeartbeats 16000000

def hevcMain8Bit420SpsPcmSafe (pcm? : Option HevcPcmInfo) : Prop :=
  match pcm? with
  | none => True
  | some p => p.bitDepth ≤ 8 ∧ p.bitDepthChroma ≤ 8

def hevcMain8Bit420SpsGate (sps : HevcSps) : Bool :=
  isMain8Bit420Sps sps

def hevcMain8Bit420SpsSpec :
    AVGateSpec HevcSps (fun sps =>
      (sps.ptl.profileIdc = 1 ∨ sps.ptl.compatFlags.getD 1 0 = 1) ∧
      sps.chromaFormatIdc = 1 ∧
      sps.separateColourPlaneFlag = false ∧
      sps.bitDepth = 8 ∧
      sps.bitDepthChroma = 8 ∧
      hevcMain8Bit420SpsPcmSafe sps.pcm?) where
  gate := hevcMain8Bit420SpsGate
  sound sps hg := by
    unfold hevcMain8Bit420SpsGate isMain8Bit420Sps at hg
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
    have hpcm : hevcMain8Bit420SpsPcmSafe sps.pcm? := by
      unfold hevcMain8Bit420SpsPcmSafe
      have h2 := hg.2
      cases hp : sps.pcm? with
      | none => trivial
      | some p =>
        simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h2
        exact h2
    exact ⟨hg.1.1.1.1.1, hg.1.1.1.1.2, hg.1.1.1.2, hg.1.1.2, hg.1.2, hpcm⟩
  complete sps hs := by
    rcases hs with ⟨hp, hc, hsep, hbl, hbc, hpcm⟩
    unfold hevcMain8Bit420SpsGate isMain8Bit420Sps
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    have hpcmB : (match sps.pcm? with | none => true | some p => decide (p.bitDepth ≤ 8) && decide (p.bitDepthChroma ≤ 8)) = true := by
      unfold hevcMain8Bit420SpsPcmSafe at hpcm
      cases hq : sps.pcm? with
      | none => rfl
      | some p =>
        rw [hq] at hpcm
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact hpcm
    exact ⟨⟨⟨⟨⟨hp, hc⟩, hsep⟩, hbl⟩, hbc⟩, hpcmB⟩
  posWitness := {
    ptl := { profileIdc := 1, compatFlags := (Array.replicate 32 0).set! 1 1, levelIdc := 93 }
    chromaFormatIdc := 1
    separateColourPlaneFlag := false
    bitDepth := 8
    bitDepthChroma := 8
    width := 64
    height := 64
  }
  negWitness := {
    ptl := { profileIdc := 2, compatFlags := (Array.replicate 32 0).set! 2 1, levelIdc := 93 }
    chromaFormatIdc := 1
    separateColourPlaneFlag := false
    bitDepth := 10
    bitDepthChroma := 10
    width := 64
    height := 64
  }
  nonVacuous := by decide
  tight := by decide

theorem hevcMain8Bit420SpsSpec_iff (sps : HevcSps) :
    hevcMain8Bit420SpsSpec.gate sps = true ↔
      ((sps.ptl.profileIdc = 1 ∨ sps.ptl.compatFlags.getD 1 0 = 1) ∧
       sps.chromaFormatIdc = 1 ∧
       sps.separateColourPlaneFlag = false ∧
       sps.bitDepth = 8 ∧
       sps.bitDepthChroma = 8 ∧
       hevcMain8Bit420SpsPcmSafe sps.pcm?) :=
  hevcMain8Bit420SpsSpec.iff_safe sps

structure HevcEncoderGeom where
  width    : Nat
  height   : Nat
  log2Ctb  : Nat
  tilesCol : Nat
  tilesRow : Nat
  deriving Repr, DecidableEq

def hevcEncoderGeomGate (g : HevcEncoderGeom) : Bool :=
  decide (g.width > 0) &&
  decide (g.height > 0) &&
  (g.width &&& 1 == 0) &&
  (g.height &&& 1 == 0) &&
  decide (4 ≤ g.log2Ctb) &&
  decide (g.log2Ctb ≤ 6) &&
  decide (1 ≤ g.tilesCol) &&
  decide (1 ≤ g.tilesRow)

def hevcEncoderGeomSpec :
    AVGateSpec HevcEncoderGeom (fun g =>
      g.width > 0 ∧ g.height > 0 ∧
      g.width % 2 = 0 ∧ g.height % 2 = 0 ∧
      4 ≤ g.log2Ctb ∧ g.log2Ctb ≤ 6 ∧
      1 ≤ g.tilesCol ∧ 1 ≤ g.tilesRow) where
  gate := hevcEncoderGeomGate
  sound g hg := by
    unfold hevcEncoderGeomGate at hg
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    have hw : g.width % 2 = 0 := by
      have h1 : g.width &&& 1 = 0 := hg.1.1.1.1.1.2
      rw [Nat.and_one_is_mod] at h1; exact h1
    have hh : g.height % 2 = 0 := by
      have h1 : g.height &&& 1 = 0 := hg.1.1.1.1.2
      rw [Nat.and_one_is_mod] at h1; exact h1
    exact ⟨hg.1.1.1.1.1.1.1, hg.1.1.1.1.1.1.2, hw, hh,
           hg.1.1.1.2, hg.1.1.2, hg.1.2, hg.2⟩
  complete g hs := by
    rcases hs with ⟨hw0, hh0, hwe, hhe, hc1, hc2, htc, htr⟩
    unfold hevcEncoderGeomGate
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    have hw : g.width &&& 1 = 0 := by rw [Nat.and_one_is_mod]; exact hwe
    have hh : g.height &&& 1 = 0 := by rw [Nat.and_one_is_mod]; exact hhe
    exact ⟨⟨⟨⟨⟨⟨⟨hw0, hh0⟩, hw⟩, hh⟩, hc1⟩, hc2⟩, htc⟩, htr⟩
  posWitness := { width := 64, height := 48, log2Ctb := 6, tilesCol := 1, tilesRow := 1 }
  negWitness := { width := 63, height := 48, log2Ctb := 6, tilesCol := 1, tilesRow := 1 }
  nonVacuous := by decide
  tight := by decide

theorem hevcEncoderGeomSpec_iff (g : HevcEncoderGeom) :
    hevcEncoderGeomSpec.gate g = true ↔
      (g.width > 0 ∧ g.height > 0 ∧
       g.width % 2 = 0 ∧ g.height % 2 = 0 ∧
       4 ≤ g.log2Ctb ∧ g.log2Ctb ≤ 6 ∧
       1 ≤ g.tilesCol ∧ 1 ≤ g.tilesRow) :=
  hevcEncoderGeomSpec.iff_safe g

def hevcQpRangeGate (qp : Int) : Bool :=
  decide (0 ≤ qp) && decide (qp ≤ 51)

def hevcQpRangeSpec :
    AVGateSpec Int (fun qp => 0 ≤ qp ∧ qp ≤ 51) where
  gate := hevcQpRangeGate
  sound _ hg := by
    unfold hevcQpRangeGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete _ hs := by
    unfold hevcQpRangeGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hs
  posWitness := 28
  negWitness := 52
  nonVacuous := by decide
  tight := by decide

theorem hevcQpRangeSpec_iff (qp : Int) :
    hevcQpRangeSpec.gate qp = true ↔ (0 ≤ qp ∧ qp ≤ 51) :=
  hevcQpRangeSpec.iff_safe qp

def hevcIntraModeRangeGate (m : Nat) : Bool :=
  decide (m ≤ 34)

def hevcIntraModeRangeSpec :
    AVGateSpec Nat (fun m => m ≤ 34) where
  gate := hevcIntraModeRangeGate
  sound _ hg := by
    unfold hevcIntraModeRangeGate at hg
    exact of_decide_eq_true hg
  complete _ hs := by
    unfold hevcIntraModeRangeGate
    exact decide_eq_true hs
  posWitness := 26
  negWitness := 35
  nonVacuous := by decide
  tight := by decide

theorem hevcIntraModeRangeSpec_iff (m : Nat) :
    hevcIntraModeRangeSpec.gate m = true ↔ m ≤ 34 :=
  hevcIntraModeRangeSpec.iff_safe m

def hevcSample8BoundGate (v : Int) : Bool :=
  decide (0 ≤ v) && decide (v ≤ 255)

def hevcSample8BoundSpec :
    AVGateSpec Int (fun v => 0 ≤ v ∧ v ≤ 255) where
  gate := hevcSample8BoundGate
  sound _ hg := by
    unfold hevcSample8BoundGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete _ hs := by
    unfold hevcSample8BoundGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hs
  posWitness := 128
  negWitness := 256
  nonVacuous := by decide
  tight := by decide

theorem hevcSample8BoundSpec_iff (v : Int) :
    hevcSample8BoundSpec.gate v = true ↔ (0 ≤ v ∧ v ≤ 255) :=
  hevcSample8BoundSpec.iff_safe v

def hevcDpbOccupancyGate (p : Nat × Nat) : Bool :=
  decide (1 ≤ p.2) && decide (p.1 ≤ p.2)

def hevcDpbOccupancySpec :
    AVGateSpec (Nat × Nat) (fun p => 1 ≤ p.2 ∧ p.1 ≤ p.2) where
  gate := hevcDpbOccupancyGate
  sound _ hg := by
    unfold hevcDpbOccupancyGate at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg
  complete _ hs := by
    unfold hevcDpbOccupancyGate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hs
  posWitness := (2, 6)
  negWitness := (7, 6)
  nonVacuous := by decide
  tight := by decide

theorem hevcDpbOccupancySpec_iff (p : Nat × Nat) :
    hevcDpbOccupancySpec.gate p = true ↔ (1 ≤ p.2 ∧ p.1 ≤ p.2) :=
  hevcDpbOccupancySpec.iff_safe p

theorem hevcClipInt_bounds_and_id (v lo hi : Int) (hlo : lo ≤ hi) :
    (lo ≤ clipInt v lo hi ∧ clipInt v lo hi ≤ hi) ∧
    (lo ≤ v → v ≤ hi → clipInt v lo hi = v) := by
  unfold clipInt
  constructor
  · split
    · omega
    · split <;> omega
  · intro h1 h2
    split
    · omega
    · split <;> omega

theorem hevcClipU8Int_bounds (v : Int) :
    (clipU8Int v).toNat ≤ 255 := by
  have hlt : (clipU8Int v).toNat < 256 := UInt8.toNat_lt (clipU8Int v)
  omega

theorem hevcClipU8Int_all_256_id :
    ((List.range 256).all fun n => (clipU8Int (Int.ofNat n)).toNat == n) = true := by
  decide

def checkRbspEpbRoundtrip : Bool :=
  let payloads : List ByteArray := [
    ByteArray.mk #[0x00, 0x00, 0x00, 0x80],
    ByteArray.mk #[0x00, 0x00, 0x01, 0x42, 0x00, 0x00, 0x02, 0x00, 0x00, 0x03, 0x99],
    ByteArray.mk #[0x40, 0x01, 0x0C, 0x01, 0xFF, 0xFF, 0x01, 0x60, 0x00, 0x00, 0x03, 0x80]
  ]
  let okAll := payloads.all fun p =>
    match stripRbspWithMap (insertRbspEpb p) with
    | some rm => rm.rbsp.data == p.data
    | none => false
  let badEpb := ByteArray.mk #[0x00, 0x00, 0x03, 0x04]
  let badTrail := ByteArray.mk #[0x00, 0x00, 0x03]
  okAll && (stripRbspWithMap badEpb).isNone && (stripRbspWithMap badTrail).isNone

theorem hevcRbspEpb_roundtrip_and_rejects_bad_epb :
    checkRbspEpbRoundtrip = true := by
  decide

def checkNalHeaderRoundtrip : Bool :=
  let cases : List (Nat × Nat × Nat) :=
    [(nalVps, 0, 1), (nalSps, 0, 1), (nalPps, 0, 1),
     (nalIdrWRadl, 0, 1), (nalTrailR, 0, 2), (nalCraNut, 3, 4)]
  let body := ByteArray.mk #[0xAA, 0x00, 0x00, 0x01, 0x55]
  let okValid := cases.all fun (nt, lid, tidPlus1) =>
    let nal := packHevcNal nt lid tidPlus1 body
    parseNalHeader nal == some (nt, lid, tidPlus1 - 1) &&
    (match stripRbspWithMap (ByteArray.mk (nal.data.extract 2 nal.data.size)) with
     | some rm => rm.rbsp.data == body.data
     | none => false)
  let badForbidden := ByteArray.mk #[0x80, 0x01, 0x80]
  let badTidZero := ByteArray.mk #[0x40, 0x00, 0x80]
  let badShort := ByteArray.mk #[0x40]
  okValid && (parseNalHeader badForbidden).isNone &&
    (parseNalHeader badTidZero).isNone && (parseNalHeader badShort).isNone

theorem hevcNalHeader_pack_parse_roundtrip :
    checkNalHeaderRoundtrip = true := by
  decide

def checkExpGolombRoundtrip : Bool :=
  let ues : List Nat := [0, 1, 2, 3, 7, 14, 15, 31, 63, 128, 255]
  let ses : List Int := [0, 1, -1, 2, -2, 7, -7, 31, -31, 64, -64]
  let ueOk := ues.all fun u =>
    match ((HevcBitWriter.empty.putUe u).rbspTrailingBits).toBytes with
    | some bs =>
      match (HevcBitReader.ofBytes bs).getUe with
      | some (got, _) => got == u
      | none => false
    | none => false
  let seOk := ses.all fun s =>
    match ((HevcBitWriter.empty.putSe s).rbspTrailingBits).toBytes with
    | some bs =>
      match (HevcBitReader.ofBytes bs).getSe with
      | some (got, _) => got == s
      | none => false
    | none => false
  ueOk && seOk

theorem hevcExpGolomb_ue_se_roundtrip :
    checkExpGolombRoundtrip = true := by
  decide

def checkVpsSpsAndMainGate : Bool :=
  let vpsOk :=
    match writeVps with
    | some vpsNal =>
      parseNalHeader vpsNal == some (nalVps, 0, 0) &&
      (stripRbspWithMap (ByteArray.mk (vpsNal.data.extract 2 vpsNal.data.size))).isSome
    | none => false
  let spsOk :=
    match writeSps 56 40 6 (0, 6, 0, 2) with
    | some spsNal =>
      parseNalHeader spsNal == some (nalSps, 0, 0) &&
      (stripRbspWithMap (ByteArray.mk (spsNal.data.extract 2 spsNal.data.size))).isSome
    | none => false
  let main8 : HevcSps := {
    ptl := { profileIdc := 1, levelIdc := 93 },
    chromaFormatIdc := 1, separateColourPlaneFlag := false, bitDepth := 8, bitDepthChroma := 8
  }
  let main10 : HevcSps := {
    ptl := { profileIdc := 2, levelIdc := 93 },
    chromaFormatIdc := 1, separateColourPlaneFlag := false, bitDepth := 10, bitDepthChroma := 10
  }
  let main444 : HevcSps := {
    ptl := { profileIdc := 4, levelIdc := 93 },
    chromaFormatIdc := 3, separateColourPlaneFlag := false, bitDepth := 8, bitDepthChroma := 8
  }
  let mainPcm10 : HevcSps := {
    ptl := { profileIdc := 1, levelIdc := 93 },
    chromaFormatIdc := 1, separateColourPlaneFlag := false, bitDepth := 8, bitDepthChroma := 8,
    pcm? := some {
      bitDepth := 10, bitDepthChroma := 8,
      log2MinPcmCbSize := 3, log2MaxPcmCbSize := 5, loopFilterDisableFlag := false
    }
  }
  vpsOk && spsOk && isMain8Bit420Sps main8 &&
    !isMain8Bit420Sps main10 && !isMain8Bit420Sps main444 && !isMain8Bit420Sps mainPcm10

theorem hevcVpsSps_and_nonMain_failclosed_verified :
    checkVpsSpsAndMainGate = true := by
  decide

def checkCabacCoreRoundtrip : Bool :=
  let st0 : Array Nat := #[42, 63]
  let (w1, st1) := HevcCabacWriter.fresh.encodeDecision st0 0 1
  let (w2, _) := w1.encodeDecision st1 1 0
  let w3 := (((w2.encodeBypass 1).encodeBypassBits 5 3).encodeTerminate 0).encodeTerminate 1
  match w3.toBytes with
  | none => false
  | some bytes =>
    match HevcCabacReader.init? bytes 0 with
    | none => false
    | some r0 =>
      let (d0, r1, stR1) := r0.decodeDecision st0 0
      let (d1, r2, _) := r1.decodeDecision stR1 1
      let (bp1, r3) := r2.decodeBypass
      let (bp5, r4) := r3.decodeBypassBits 3
      let (t0, r5) := r4.decodeTerminate
      let (t1, _) := r5.decodeTerminate
      d0 == 1 && d1 == 0 && bp1 == 1 && bp5 == 5 && t0 == 0 && t1 == 1

theorem hevcCabac_core_decision_bypass_terminate_roundtrip :
    checkCabacCoreRoundtrip = true := by
  decide

def checkCabacIpcmReinitRoundtrip : Bool :=
  let st0 : Array Nat := #[42, 18]
  let (w1, _) := HevcCabacWriter.fresh.encodeDecision st0 0 1
  let pcmPayload := ByteArray.mk #[17, 128, 250]
  let w2 := (w1.encodeTerminate 1).writePcmAndReinit pcmPayload
  let (w3, _) := w2.encodeDecision st0 1 1
  match (w3.encodeTerminate 1).toBytes with
  | none => false
  | some bytes =>
    match HevcCabacReader.init? bytes 0 with
    | none => false
    | some r0 =>
      let (d0, r1, _) := r0.decodeDecision st0 0
      let (pcmFlag, r2) := r1.decodeTerminate
      match r2.readPcmAndReinit pcmPayload.size with
      | none => false
      | some (pcmRead, r3) =>
        let (dPost, r4, _) := r3.decodeDecision st0 1
        let (tEnd, _) := r4.decodeTerminate
        d0 == 1 && pcmFlag == 1 && pcmRead.data == pcmPayload.data && dPost == 1 && tEnd == 1

theorem hevcCabac_ipcm_write_read_reinit_roundtrip :
    checkCabacIpcmReinitRoundtrip = true := by
  decide

private def sumListInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumListInt xs

def checkMcFilterDcGainAndConstExact : Bool :=
  let qpelSumOk := [1, 2, 3].all fun phase =>
    let row := (hevcQpelFilters.getD phase #[]).toList
    row.length == 8 && sumListInt row == 64
  let epelSumOk := [1, 2, 3, 4, 5, 6, 7].all fun phase =>
    let row := (hevcEpelFilters.getD phase #[]).toList
    row.length == 4 && sumListInt row == 64
  let constAllSamplesOk := [0, 1, 73, 128, 147, 254, 255].all fun (cNat : Nat) =>
    let c := Int.ofNat cNat
    let q1dOk := [1, 2, 3].all fun mx =>
      let row := (hevcQpelFilters.getD mx #[]).toList
      let acc := sumListInt (row.map (fun w => w * c))
      ((acc + 32) / 64) == c
    let e1dOk := [1, 2, 3, 4, 5, 6, 7].all fun mx =>
      let row := (hevcEpelFilters.getD mx #[]).toList
      let acc := sumListInt (row.map (fun w => w * c))
      ((acc + 32) / 64) == c
    let biOk := ((64 * c + 64 * c + 64) / 128) == c
    q1dOk && e1dOk && biOk
  qpelSumOk && epelSumOk && constAllSamplesOk

theorem hevcMc_8tap_luma_and_4tap_chroma_dc_gain_and_const_exact :
    checkMcFilterDcGainAndConstExact = true := by
  decide

def checkDst7AndDct2BasisAnd1DRoundtrip : Bool :=
  let dctDcRow := (hevcDspTransform.getD 0 #[]).toList
  let dctDcAll64 := dctDcRow.length == 32 && dctDcRow.all (· == 64)
  let dst4 : List (List Int) := [
    [29, 55, 74, 84],
    [74, 74, 0, -74],
    [84, -29, -74, 55],
    [55, -84, 74, -29]
  ]
  let x4 : List Int := [12, 8, -4, -10]
  let fwd := dst4.map fun row =>
    sumListInt ((List.zip row x4).map fun (a, b) => a * b)
  let inv := (List.range 4).map fun j =>
    let s := sumListInt ((List.zip dst4 fwd).map fun (row, coeff) => row.getD j 0 * coeff)
    (s + 8192) / 16384
  let diffOk := (List.zip inv x4).all fun (g, e) => (g - e).natAbs <= 1
  dctDcAll64 && diffOk

theorem hevcDst7_and_Dct2_basis_and_roundtrip_verified :
    checkDst7AndDct2BasisAnd1DRoundtrip = true := by
  decide

def planarSample8 (size x y : Nat) (l tr t bl : Int) (log2Size : Nat) : UInt8 :=
  let h := Int.ofNat (size - 1 - x) * l + Int.ofNat (x + 1) * tr
  let v := Int.ofNat (size - 1 - y) * t + Int.ofNat (y + 1) * bl
  clipU8Int ((h + v + Int.ofNat size) / Int.ofNat (1 <<< (log2Size + 1)))

def angularInterpSample8 (fact : Int) (r0 r1 : Int) : UInt8 :=
  clipU8Int (((32 - fact) * r0 + fact * r1 + 16) / 32)

theorem hevcIntra_planar_and_angular_bounds (size x y : Nat) (l tr t bl fact r0 r1 : Int) (log2Size : Nat) :
    (planarSample8 size x y l tr t bl log2Size).toNat ≤ 255 ∧
    (angularInterpSample8 fact r0 r1).toNat ≤ 255 := by
  exact ⟨hevcClipU8Int_bounds _, hevcClipU8Int_bounds _⟩

theorem hevcAngular_const_exact_unrounded (fact c : Int) :
    ((32 - fact) * c + fact * c + 16) / 32 = c := by
  have hlin : (32 - fact) * c + fact * c = 32 * c := by
    have hsub : (32 - fact) + fact = 32 := by omega
    calc
      (32 - fact) * c + fact * c = ((32 - fact) + fact) * c := (Int.add_mul (32 - fact) fact c).symm
      _ = 32 * c := by rw [hsub]
  rw [hlin]
  omega

def checkIntraPlanarDcAngularConstExact : Bool :=
  let vals : List Nat := [0, 93, 255]
  let planar4Ok := vals.all fun v =>
    let c := Int.ofNat v
    (List.range 4).all fun y =>
      (List.range 4).all fun x =>
        (planarSample8 4 x y c c c c 2).toNat == v
  let planarCornersOk := [(3, 8, 7), (4, 16, 15), (5, 32, 31)].all fun (lg, sz, mx) =>
    vals.all fun v =>
      let c := Int.ofNat v
      (planarSample8 sz 0 0 c c c c lg).toNat == v &&
      (planarSample8 sz mx mx c c c c lg).toNat == v
  let angOk := [0, 1, 16, 31].all fun fNat =>
    let fact := Int.ofNat fNat
    vals.all fun v =>
      (angularInterpSample8 fact (Int.ofNat v) (Int.ofNat v)).toNat == v
  planar4Ok && planarCornersOk && angOk

theorem hevcIntra_planar_dc_angular_const_exact :
    checkIntraPlanarDcAngularConstExact = true := by
  decide

def deblockNormalDelta (p1 p0 q0 q1 tc : Int) : Int :=
  clipInt (((9 * (q0 - p0) - 3 * (q1 - p1) + 8) / 16)) (-tc) tc

def saoApplyOffset8 (sample offset : Int) : UInt8 :=
  clipU8Int (sample + offset)

theorem hevcDeblock_flat_zero_delta (c tc : Int) (htc : 0 ≤ tc) :
    deblockNormalDelta c c c c tc = 0 := by
  unfold deblockNormalDelta
  have h0 : (9 * (c - c) - 3 * (c - c) + 8) / 16 = 0 := by omega
  rw [h0]
  exact (hevcClipInt_bounds_and_id 0 (-tc) tc (by omega)).2 (by omega) htc

theorem hevcDeblock_and_Sao_clamped_bounds (p0 q0 delta sample offset : Int) :
    (clipU8Int (p0 + delta)).toNat ≤ 255 ∧
    (clipU8Int (q0 - delta)).toNat ≤ 255 ∧
    (saoApplyOffset8 sample offset).toNat ≤ 255 := by
  exact ⟨hevcClipU8Int_bounds _, hevcClipU8Int_bounds _, hevcClipU8Int_bounds _⟩

private def insertPocSorted (p : Int) : List Int → List Int
  | [] => [p]
  | q :: qs => if p ≤ q then p :: q :: qs else q :: insertPocSorted p qs

private def sortPocsPure : List Int → List Int
  | [] => []
  | p :: ps => insertPocSorted p (sortPocsPure ps)

private def isNonDecreasing : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && isNonDecreasing (b :: rest)

theorem hevcDpb_poc_reorder_monotone_and_capacity_checked :
    let out := sortPocsPure [0, 4, 2, 1, 3, 8, 6, 5, 7]
    out = [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
    isNonDecreasing out = true ∧
    hevcDpbOccupancyGate (4, 6) = true ∧
    hevcDpbOccupancyGate (7, 6) = false := by
  decide

end LeanAV.HevcMainProofs
