import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Bitstream
import LeanAV.Video

namespace LeanAV.H264Entropy

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Bitstream
open LeanAV.Video

inductive EntropyMode where
  | preserve
  | cavlc
  | cabac
  deriving Repr, DecidableEq, Inhabited

def EntropyMode.parse : String → Option EntropyMode
  | "preserve" | "same" => some .preserve
  | "cavlc" => some .cavlc
  | "cabac" => some .cabac
  | _ => none

def EntropyMode.toString : EntropyMode → String
  | .preserve => "preserve"
  | .cavlc => "cavlc"
  | .cabac => "cabac"

def blk4XY : Array (Nat × Nat) := #[
  (0, 0), (1, 0), (0, 1), (1, 1),
  (2, 0), (3, 0), (2, 1), (3, 1),
  (0, 2), (1, 2), (0, 3), (1, 3),
  (2, 2), (3, 2), (2, 3), (3, 3)
]

def xyToBlk4 (x y : Nat) : Nat :=
  ((y / 2) * 8) + ((x / 2) * 4) + ((y % 2) * 2) + (x % 2)

private def addEpbLoop : List UInt8 → Nat → List UInt8 → List UInt8
  | [], _, accRev => accRev.reverse
  | b :: rest, z, accRev =>
    if z ≥ 2 && b ≤ 3 then
      let zNext := if b == 0 then 1 else 0
      addEpbLoop rest zNext (b :: (3 : UInt8) :: accRev)
    else
      let zNext := if b == 0 then z + 1 else 0
      addEpbLoop rest zNext (b :: accRev)

def addRbspEmulationBytes (rbspBody : ByteArray) : ByteArray :=
  { data := (addEpbLoop rbspBody.data.toList 0 []).toArray }

def stripNalEmulationBytes (nal : ByteArray) : ByteArray :=
  stripRbspEmulationBytes { ba := nal, off := 0, len := nal.data.size }

def packRawRbspToNal (raw : ByteArray) : ByteArray :=
  if raw.data.size == 0 then { data := #[] }
  else
    let body : ByteArray := { data := (raw.data.toList.drop 1).toArray }
    { data := #[raw.data.getD 0 0] ++ (addRbspEmulationBytes body).data }

private def splitAnnexBStarts : Nat → Nat → ByteArray → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, accRev => accRev.reverse
  | fuel + 1, i, ba, accRev =>
    let n := ba.data.size
    if i + 2 ≥ n then accRev.reverse
    else if i + 3 < n && ba.data.getD i 0 == 0 && ba.data.getD (i + 1) 0 == 0 &&
        ba.data.getD (i + 2) 0 == 0 && ba.data.getD (i + 3) 0 == 1 then
      splitAnnexBStarts fuel (i + 4) ba ((i, 4) :: accRev)
    else if ba.data.getD i 0 == 0 && ba.data.getD (i + 1) 0 == 0 && ba.data.getD (i + 2) 0 == 1 then
      splitAnnexBStarts fuel (i + 3) ba ((i, 3) :: accRev)
    else
      splitAnnexBStarts fuel (i + 1) ba accRev

private def sliceAnnexBNals (ba : ByteArray) : List (Nat × Nat) → List ByteArray
  | [] => []
  | (pos, slen) :: rest =>
    let stopPos := match rest with
      | (nextPos, _) :: _ => nextPos
      | [] => ba.data.size
    { data := ((ba.data.toList.drop (pos + slen)).take (stopPos - (pos + slen))).toArray } :: sliceAnnexBNals ba rest

def splitAnnexB (stream : ByteArray) : Array ByteArray :=
  if stream.data.size < 3 then #[]
  else
    let starts := splitAnnexBStarts stream.data.size 0 stream []
    (sliceAnnexBNals stream starts).toArray

def joinAnnexB (nals : Array ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let sc : ByteArray := { data := #[0, 0, 0, 1] }
  for nal in nals do
    out := out ++ sc ++ nal
  return out

private def byteTrailingZeros (b : UInt8) : Nat :=
  if (b &&& 1) != 0 then 0
  else if (b &&& 2) != 0 then 1
  else if (b &&& 4) != 0 then 2
  else if (b &&& 8) != 0 then 3
  else if (b &&& 16) != 0 then 4
  else if (b &&& 32) != 0 then 5
  else if (b &&& 64) != 0 then 6
  else 7

private def rbspEndPosLoop (rbsp : ByteArray) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let b := rbsp.data.getD k 0
    if b != 0 then k * 8 + (7 - byteTrailingZeros b)
    else rbspEndPosLoop rbsp k

def rbspEndBitPos (rbsp : ByteArray) : Nat :=
  rbspEndPosLoop rbsp rbsp.data.size

def moreRbspData (r : BitReader) (rbspEnd : Nat) : Bool :=
  r.bitOffset < rbspEnd

def readU1Nat (r : BitReader) : Option (Nat × BitReader) :=
  match r.readBit with
  | some (b, r') => some (b.toNat, r')
  | none => none

def readUNat (r : BitReader) (n : Nat) : Option (Nat × BitReader) :=
  match r.readBitsMSB n with
  | some (v, r') => some (v.toNat, r')
  | none => none

def readUENat (r : BitReader) : Option (Nat × BitReader) :=
  match r.readUE with
  | some (v, r') => some (v.toNat, r')
  | none => none

def readSEInt (r : BitReader) : Option (Int × BitReader) :=
  match r.readSE with
  | some (v, r') => some (v.toInt, r')
  | none => none

def extractBitArray (rbsp : ByteArray) (startBit endBit : Nat) : Array UInt8 := Id.run do
  if endBit ≤ startBit then return #[]
  let cnt := endBit - startBit
  let mut out : Array UInt8 := Array.emptyWithCapacity cnt
  for i in [:cnt] do
    let k := startBit + i
    let byteIdx := k / 8
    let shift := (7 - (k % 8)).toUInt8
    let b := if byteIdx < rbsp.size then rbsp.get! byteIdx else 0
    out := out.push ((b >>> shift) &&& 1)
  return out

def writeBitArray (w : BitWriter) (bits : Array UInt8) : BitWriter :=
  bits.foldl (fun acc b => acc.writeBit b) w

def writeU1Nat (w : BitWriter) (b : Nat) : BitWriter :=
  w.writeBit (if b != 0 then 1 else 0)

def writeUNat (w : BitWriter) (v n : Nat) : BitWriter :=
  w.writeBitsMSB v.toUInt64 n

def writeUENat (w : BitWriter) (v : Nat) : BitWriter :=
  w.writeUE v.toUInt64

def writeSEInt (w : BitWriter) (v : Int) : BitWriter :=
  let mag : UInt64 := v.natAbs.toUInt64
  let codeNum : UInt64 := if v > 0 then 2 * mag - 1 else 2 * mag
  w.writeUE codeNum

def alignWriterOnes (w : BitWriter) : BitWriter :=
  let rem := w.bitsUsed
  if rem == 0 then w
  else
    let pad := 8 - rem
    writeUNat w ((1 <<< pad) - 1) pad

def writeRbspTrailing (w : BitWriter) : BitWriter :=
  (w.writeBit 1).alignToByte

def writerToNal (w : BitWriter) : ByteArray :=
  packRawRbspToNal w.toByteArray

def readBytesAlignedLoop (r : BitReader) : Nat → Array UInt8 → Option (ByteArray × BitReader)
  | 0, acc => some ({ data := acc }, r)
  | k + 1, acc =>
    match r.readBitsMSB 8 with
    | some (v, r') => readBytesAlignedLoop r' k (acc.push v.toUInt8)
    | none => none

def writeBytesAligned (w : BitWriter) (ba : ByteArray) : BitWriter :=
  ba.data.foldl (fun cur b => cur.writeBitsMSB b.toUInt64 8) w.alignToByte

private def isHighProfileIdc (p : Nat) : Bool :=
  p == 100 || p == 110 || p == 122 || p == 244 || p == 44 || p == 83 ||
  p == 86 || p == 118 || p == 128 || p == 138 || p == 139 || p == 134

private def skipScalingListLoop (r : BitReader) : Nat → Int → Int → Option BitReader
  | 0, _, _ => some r
  | k + 1, lastScale, nextScale => do
    let (nextS, r') ←
      if nextScale != 0 then do
        let (delta, rd) ← readSEInt r
        pure (Int.emod (lastScale + delta + 256) 256, rd)
      else
        pure (nextScale, r)
    let lastS := if nextS == 0 then lastScale else nextS
    skipScalingListLoop r' k lastS nextS

private def skipScalingMatrixLoop (r : BitReader) (idx cnt : Nat) : Option BitReader :=
  if idx ≥ cnt then some r
  else
    match readU1Nat r with
    | none => none
    | some (present, r1) =>
      let afterList :=
        if present == 1 then
          skipScalingListLoop r1 (if idx < 6 then 16 else 64) 8 8
        else
          some r1
      match afterList with
      | none => none
      | some r2 => skipScalingMatrixLoop r2 (idx + 1) cnt
termination_by cnt - idx

private def skipSECountLoop (r : BitReader) : Nat → Option BitReader
  | 0 => some r
  | k + 1 => do
    let (_, r') ← readSEInt r
    skipSECountLoop r' k

structure SpsFull where
  profileIdc                       : Nat
  constraintFlags                  : Nat
  levelIdc                         : Nat
  spsId                            : Nat
  chromaFormatIdc                  : Nat
  separateColourPlaneFlag          : Nat
  bitDepthLumaMinus8               : Nat
  bitDepthChromaMinus8             : Nat
  qpprimeYZeroTransformBypassFlag  : Nat
  log2MaxFrameNum                  : Nat
  picOrderCntType                  : Nat
  log2MaxPocLsb                    : Nat
  deltaPicOrderAlwaysZeroFlag      : Nat
  maxNumRefFrames                  : Nat
  picWidthInMbs                    : Nat
  picHeightInMapUnits              : Nat
  frameMbsOnlyFlag                 : Nat
  direct8x8InferenceFlag           : Nat
  rawNal                           : ByteArray
  deriving Inhabited

def parseSpsFull (nal : ByteArray) : Option SpsFull := do
  let rbsp := stripNalEmulationBytes nal
  if rbsp.data.size < 4 then none
  else
    let hdr := rbsp.data.getD 0 0
    if (hdr &&& 0x1F) != 7 then none
    else
      let profileIdc := (rbsp.data.getD 1 0).toNat
      let constraintFlags := (rbsp.data.getD 2 0).toNat
      let levelIdc := (rbsp.data.getD 3 0).toNat
      let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.data.size }, bitOffset := 32 }
      let (spsId, r1) ← readUENat r0
      if spsId > 31 then none
      else
        let (chromaIdc, sep, bdLuma, bdChroma, bypass, r2) ←
          if isHighProfileIdc profileIdc then do
            let (cIdc, ra) ← readUENat r1
            let (sFlag, rb) ← if cIdc == 3 then readU1Nat ra else pure (0, ra)
            let (bdY, rc) ← readUENat rb
            let (bdC, rd) ← readUENat rc
            let (byp, re) ← readU1Nat rd
            let (matPresent, rf) ← readU1Nat re
            let rg ←
              if matPresent == 1 then
                skipScalingMatrixLoop rf 0 (if cIdc != 3 then 8 else 12)
              else
                some rf
            pure (cIdc, sFlag, bdY, bdC, byp, rg)
          else
            pure (1, 0, 0, 0, 0, r1)
        if (chromaIdc != 0 && chromaIdc != 1) || sep != 0 || bdLuma > 6 || bdChroma > 6 then none
        else do
          let (l2fnM4, r3) ← readUENat r2
          let (pocType, r4) ← readUENat r3
          let (l2poc, deltaZero, r5) ←
            if pocType == 0 then do
              let (v, ra) ← readUENat r4
              pure (v + 4, 0, ra)
            else if pocType == 1 then do
              let (dz, ra) ← readU1Nat r4
              let (_, rb) ← readSEInt ra
              let (_, rc) ← readSEInt rb
              let (nRefCycle, rd) ← readUENat rc
              if nRefCycle > 255 then none
              else do
                let re ← skipSECountLoop rd nRefCycle
                pure (4, dz, re)
            else if pocType == 2 then
              pure (4, 0, r4)
            else
              none
          let (maxRefs, r6) ← readUENat r5
          let (_, r7) ← readU1Nat r6
          let (wMbsM1, r8) ← readUENat r7
          let (hMapM1, r9) ← readUENat r8
          let (frameOnly, r10) ← readU1Nat r9
          if frameOnly != 1 then none
          else do
            let (direct8x8, _) ← readU1Nat r10
            pure {
              profileIdc := profileIdc
              constraintFlags := constraintFlags
              levelIdc := levelIdc
              spsId := spsId
              chromaFormatIdc := chromaIdc
              separateColourPlaneFlag := sep
              bitDepthLumaMinus8 := bdLuma
              bitDepthChromaMinus8 := bdChroma
              qpprimeYZeroTransformBypassFlag := bypass
              log2MaxFrameNum := l2fnM4 + 4
              picOrderCntType := pocType
              log2MaxPocLsb := l2poc
              deltaPicOrderAlwaysZeroFlag := deltaZero
              maxNumRefFrames := maxRefs
              picWidthInMbs := wMbsM1 + 1
              picHeightInMapUnits := hMapM1 + 1
              frameMbsOnlyFlag := frameOnly
              direct8x8InferenceFlag := direct8x8
              rawNal := nal
            }

def upgradeSpsForCabac (sps : SpsFull) : ByteArray :=
  let rbsp := stripNalEmulationBytes sps.rawNal
  if rbsp.data.size < 4 then sps.rawNal
  else
    let rbsp' : ByteArray :=
      if rbsp.data.getD 1 0 == 66 then
        let c' := (rbsp.data.getD 2 0) &&& (0x7F : UInt8)
        { data := (rbsp.data.set! 1 (77 : UInt8)).set! 2 c' }
      else
        rbsp
    packRawRbspToNal rbsp'

structure PpsFull where
  nalHdr                                   : Nat
  ppsId                                    : Nat
  spsId                                    : Nat
  entropyCodingModeFlag                    : Nat
  bottomFieldPicOrderInFramePresentFlag    : Nat
  numSliceGroupsMinus1                     : Nat
  numRefIdxL0DefaultActiveMinus1           : Nat
  numRefIdxL1DefaultActiveMinus1           : Nat
  weightedPredFlag                         : Nat
  weightedBipredIdc                        : Nat
  picInitQpMinus26                         : Int
  picInitQsMinus26                         : Int
  chromaQpIndexOffset                      : Int
  deblockingFilterControlPresentFlag       : Nat
  constrainedIntraPredFlag                 : Nat
  redundantPicCntPresentFlag               : Nat
  hasMoreRbsp                              : Bool
  transform8x8ModeFlag                     : Nat
  picScalingBits                           : Array UInt8
  secondChromaQpIndexOffset                : Int
  deriving Repr, Inhabited

def findSps (spsList : Array (Option SpsFull)) (spsId : Nat) : Option SpsFull :=
  if h : spsId < spsList.size then spsList[spsId] else none

def findPps (ppsList : Array (Option PpsFull)) (ppsId : Nat) : Option PpsFull :=
  if h : ppsId < ppsList.size then ppsList[ppsId] else none

def parsePpsFull (nal : ByteArray) (spsList : Array (Option SpsFull)) : Option PpsFull := do
  let rbsp := stripNalEmulationBytes nal
  if rbsp.data.size < 1 then none
  else
    let hdr := rbsp.data.getD 0 0
    if (hdr &&& 0x1F) != 8 then none
    else
      let rbspEnd := rbspEndBitPos rbsp
      let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.data.size }, bitOffset := 8 }
      let (ppsId, r1) ← readUENat r0
      let (spsId, r2) ← readUENat r1
      if ppsId > 255 || spsId > 31 then none
      else do
        let sps ← findSps spsList spsId
        let (cabac, r3) ← readU1Nat r2
        let (bfpo, r4) ← readU1Nat r3
        let (numSg, r5) ← readUENat r4
        if numSg != 0 then none
        else do
          let (l0Def, r6) ← readUENat r5
          let (l1Def, r7) ← readUENat r6
          if l0Def > 31 || l1Def > 31 then none
          else do
            let (wp, r8) ← readU1Nat r7
            let (wbp, r9) ← readUNat r8 2
            let (initQp, r10) ← readSEInt r9
            let (initQs, r11) ← readSEInt r10
            let (cqpOff, r12) ← readSEInt r11
            let (deblockCtrl, r13) ← readU1Nat r12
            let (constrIntra, r14) ← readU1Nat r13
            let (redPic, r15) ← readU1Nat r14
            let hasMore := moreRbspData r15 rbspEnd
            let (t8x8, scaleBits, secCqp) ←
              if hasMore then do
                let (t8, ra) ← readU1Nat r15
                let p0 := ra.bitOffset
                let (matPres, rb) ← readU1Nat ra
                let rc ←
                  if matPres == 1 then
                    let cnt := 6 + (if sps.chromaFormatIdc != 3 then 2 else 6) * t8
                    skipScalingMatrixLoop rb 0 cnt
                  else
                    some rb
                let p1 := rc.bitOffset
                let (sc, _) ← readSEInt rc
                pure (t8, extractBitArray rbsp p0 p1, sc)
              else
                pure (0, #[], cqpOff)
            pure {
              nalHdr := hdr.toNat
              ppsId := ppsId
              spsId := spsId
              entropyCodingModeFlag := cabac
              bottomFieldPicOrderInFramePresentFlag := bfpo
              numSliceGroupsMinus1 := numSg
              numRefIdxL0DefaultActiveMinus1 := l0Def
              numRefIdxL1DefaultActiveMinus1 := l1Def
              weightedPredFlag := wp
              weightedBipredIdc := wbp
              picInitQpMinus26 := initQp
              picInitQsMinus26 := initQs
              chromaQpIndexOffset := cqpOff
              deblockingFilterControlPresentFlag := deblockCtrl
              constrainedIntraPredFlag := constrIntra
              redundantPicCntPresentFlag := redPic
              hasMoreRbsp := hasMore
              transform8x8ModeFlag := t8x8
              picScalingBits := scaleBits
              secondChromaQpIndexOffset := secCqp
            }

def serializePps (pps : PpsFull) (cabacOverride : Option Nat) : ByteArray :=
  let cabac := cabacOverride.getD pps.entropyCodingModeFlag
  let w0 := BitWriter.empty
  let w1 := writeUNat w0 pps.nalHdr 8
  let w2 := writeUENat w1 pps.ppsId
  let w3 := writeUENat w2 pps.spsId
  let w4 := writeU1Nat w3 cabac
  let w5 := writeU1Nat w4 pps.bottomFieldPicOrderInFramePresentFlag
  let w6 := writeUENat w5 pps.numSliceGroupsMinus1
  let w7 := writeUENat w6 pps.numRefIdxL0DefaultActiveMinus1
  let w8 := writeUENat w7 pps.numRefIdxL1DefaultActiveMinus1
  let w9 := writeU1Nat w8 pps.weightedPredFlag
  let w10 := writeUNat w9 pps.weightedBipredIdc 2
  let w11 := writeSEInt w10 pps.picInitQpMinus26
  let w12 := writeSEInt w11 pps.picInitQsMinus26
  let w13 := writeSEInt w12 pps.chromaQpIndexOffset
  let w14 := writeU1Nat w13 pps.deblockingFilterControlPresentFlag
  let w15 := writeU1Nat w14 pps.constrainedIntraPredFlag
  let w16 := writeU1Nat w15 pps.redundantPicCntPresentFlag
  let w17 :=
    if pps.hasMoreRbsp then
      let wa := writeU1Nat w16 pps.transform8x8ModeFlag
      let wb := writeBitArray wa pps.picScalingBits
      writeSEInt wb pps.secondChromaQpIndexOffset
    else
      w16
  writerToNal (writeRbspTrailing w17)

structure SliceHeaderFull where
  nalHdr          : Nat
  firstMbInSlice  : Nat
  sliceType       : Nat
  sliceTypeNos    : Nat
  ppsId           : Nat
  prefixBits      : Array UInt8
  cabacInitIdc    : Nat
  sliceQpDelta    : Int
  suffixBits      : Array UInt8
  numRefL0        : Nat
  numRefL1        : Nat
  sliceQpY        : Int
  deriving Repr, Inhabited

private def skipRefPicListModOne (r : BitReader) : Nat → Option BitReader
  | 0 => none
  | fuel + 1 => do
    let (op, r1) ← readUENat r
    if op == 3 then some r1
    else if op > 3 then none
    else do
      let (_, r2) ← readUENat r1
      skipRefPicListModOne r2 fuel

private def skipRefPicListMod (r : BitReader) (sliceTypeNos : Nat) : Option BitReader := do
  let rA ←
    if sliceTypeNos == 0 || sliceTypeNos == 1 then do
      let (f0, r1) ← readU1Nat r
      if f0 == 1 then skipRefPicListModOne r1 (r1.bitsLeft + 1) else some r1
    else some r
  if sliceTypeNos == 1 then do
    let (f1, r2) ← readU1Nat rA
    if f1 == 1 then skipRefPicListModOne r2 (r2.bitsLeft + 1) else some r2
  else some rA

private def skipPredWeightList (r : BitReader) (chroma : Bool) : Nat → Option BitReader
  | 0 => some r
  | k + 1 => do
    let (lwFlag, r1) ← readU1Nat r
    let r2 ←
      if lwFlag == 1 then do
        let (_, ra) ← readSEInt r1
        let (_, rb) ← readSEInt ra
        pure rb
      else some r1
    let r3 ←
      if chroma then do
        let (cwFlag, rc) ← readU1Nat r2
        if cwFlag == 1 then do
          let (_, rd) ← readSEInt rc
          let (_, re) ← readSEInt rd
          let (_, rf) ← readSEInt re
          let (_, rg) ← readSEInt rf
          pure rg
        else some rc
      else some r2
    skipPredWeightList r3 chroma k

private def skipPredWeightTable (r : BitReader) (sps : SpsFull) (sliceTypeNos l0 l1 : Nat) : Option BitReader := do
  let (_, r1) ← readUENat r
  let chroma := sps.chromaFormatIdc != 0 && sps.separateColourPlaneFlag == 0
  let r2 ← if chroma then (readUENat r1).map Prod.snd else some r1
  let r3 ← skipPredWeightList r2 chroma l0
  if sliceTypeNos == 1 then skipPredWeightList r3 chroma l1 else some r3

private def skipMmcoLoop (r : BitReader) : Nat → Option BitReader
  | 0 => none
  | fuel + 1 => do
    let (mmco, r1) ← readUENat r
    if mmco == 0 then some r1
    else if mmco > 6 then none
    else do
      let r2 ← if mmco == 1 || mmco == 3 then (readUENat r1).map Prod.snd else some r1
      let r3 ← if mmco == 2 then (readUENat r2).map Prod.snd else some r2
      let r4 ← if mmco == 3 || mmco == 6 then (readUENat r3).map Prod.snd else some r3
      let r5 ← if mmco == 4 then (readUENat r4).map Prod.snd else some r4
      skipMmcoLoop r5 fuel

private def skipDecRefPicMarking (r : BitReader) (idr : Bool) : Option BitReader :=
  if idr then do
    let (_, r1) ← readU1Nat r
    let (_, r2) ← readU1Nat r1
    pure r2
  else do
    let (adapt, r1) ← readU1Nat r
    if adapt == 1 then skipMmcoLoop r1 (r1.bitsLeft + 1) else pure r1

def parseSliceHeaderFull (rbsp : ByteArray) (spsList : Array (Option SpsFull))
    (ppsList : Array (Option PpsFull)) : Option (SliceHeaderFull × Nat) := do
  if rbsp.size < 1 then none
  else
    let nalHdr := (rbsp.get! 0).toNat
    let nalType := nalHdr &&& 0x1F
    let nalRefIdc := (nalHdr >>> 5) &&& 3
    let idr := nalType == 5
    let r0 : BitReader := { slice := ByteSlice.ofByteArray rbsp, bitOffset := 8 }
    let (firstMb, r1) ← readUENat r0
    let (sliceType, r2) ← readUENat r1
    let stMod := sliceType % 5
    if stMod > 2 then none
    else do
      let (ppsId, r3) ← readUENat r2
      let pps ← findPps ppsList ppsId
      let sps ← findSps spsList pps.spsId
      if sps.frameMbsOnlyFlag != 1 || sps.separateColourPlaneFlag != 0 then none
      else do
        let totalMbs := sps.picWidthInMbs * sps.picHeightInMapUnits
        if firstMb ≥ totalMbs then none
        else do
          let pPrefixStart := r3.bitOffset
          let (_, r4) ← readUNat r3 sps.log2MaxFrameNum
          let r5 ← if idr then (readUENat r4).map Prod.snd else some r4
          let r6 ←
            if sps.picOrderCntType == 0 then do
              let (_, ra) ← readUNat r5 sps.log2MaxPocLsb
              if pps.bottomFieldPicOrderInFramePresentFlag != 0 then (readSEInt ra).map Prod.snd else some ra
            else if sps.picOrderCntType == 1 && sps.deltaPicOrderAlwaysZeroFlag == 0 then do
              let (_, ra) ← readSEInt r5
              if pps.bottomFieldPicOrderInFramePresentFlag != 0 then (readSEInt ra).map Prod.snd else some ra
            else some r5
          let r7 ← if pps.redundantPicCntPresentFlag != 0 then (readUENat r6).map Prod.snd else some r6
          let r8 ← if stMod == 1 then (readU1Nat r7).map Prod.snd else some r7
          let defL0 := pps.numRefIdxL0DefaultActiveMinus1 + 1
          let defL1 := pps.numRefIdxL1DefaultActiveMinus1 + 1
          let (numL0, numL1, r9) ←
            if stMod == 0 || stMod == 1 then do
              let (ov, ra) ← readU1Nat r8
              if ov == 1 then do
                let (l0m1, rb) ← readUENat ra
                if stMod == 1 then do
                  let (l1m1, rc) ← readUENat rb
                  pure (l0m1 + 1, l1m1 + 1, rc)
                else pure (l0m1 + 1, defL1, rb)
              else pure (defL0, defL1, ra)
            else pure (defL0, defL1, r8)
          if numL0 > 32 || numL1 > 32 then none
          else do
            let r10 ← skipRefPicListMod r9 stMod
            let r11 ←
              if (pps.weightedPredFlag != 0 && stMod == 0) || (pps.weightedBipredIdc == 1 && stMod == 1) then
                skipPredWeightTable r10 sps stMod numL0 numL1
              else some r10
            let r12 ← if nalRefIdc != 0 then skipDecRefPicMarking r11 idr else some r11
            let pPrefixEnd := r12.bitOffset
            let (cabacInitIdc, r13) ←
              if pps.entropyCodingModeFlag != 0 && stMod != 2 then readUENat r12 else pure (0, r12)
            if cabacInitIdc > 2 then none
            else do
              let (sliceQpDelta, r14) ← readSEInt r13
              let pSuffixStart := r14.bitOffset
              let r15 ←
                if pps.deblockingFilterControlPresentFlag != 0 then do
                  let (disDeblock, ra) ← readUENat r14
                  if disDeblock != 1 then do
                    let (_, rb) ← readSEInt ra
                    let (_, rc) ← readSEInt rb
                    pure rc
                  else pure ra
                else some r14
              let pSuffixEnd := r15.bitOffset
              let sliceQpY := (26 : Int) + pps.picInitQpMinus26 + sliceQpDelta
              pure ({
                nalHdr := nalHdr
                firstMbInSlice := firstMb
                sliceType := sliceType
                sliceTypeNos := stMod
                ppsId := ppsId
                prefixBits := extractBitArray rbsp pPrefixStart pPrefixEnd
                cabacInitIdc := cabacInitIdc
                sliceQpDelta := sliceQpDelta
                suffixBits := extractBitArray rbsp pSuffixStart pSuffixEnd
                numRefL0 := numL0
                numRefL1 := numL1
                sliceQpY := sliceQpY
              }, r15.bitOffset)

def writeSliceHeaderFull (w : BitWriter) (sh : SliceHeaderFull) (isCabac : Bool) : BitWriter :=
  let w1 := writeUNat w sh.nalHdr 8
  let w2 := writeUENat w1 sh.firstMbInSlice
  let w3 := writeUENat w2 sh.sliceType
  let w4 := writeUENat w3 sh.ppsId
  let w5 := writeBitArray w4 sh.prefixBits
  let w6 := if isCabac && sh.sliceTypeNos != 2 then writeUENat w5 sh.cabacInitIdc else w5
  let w7 := writeSEInt w6 sh.sliceQpDelta
  let w8 := writeBitArray w7 sh.suffixBits
  if isCabac then alignWriterOnes w8 else w8

def cavlcCtEnc0 : Array UInt32 := #[
  65537, 0, 0, 0, 393221, 131073, 0, 0, 524295, 393220, 196609, 0,
  589831, 524294, 458757, 327683, 655367, 589830, 524293, 393219, 720903, 655366, 589829, 458756,
  851983, 720902, 655365, 524292, 851979, 851982, 720901, 589828, 851976, 851978, 851981, 655364,
  917519, 917518, 851977, 720900, 917515, 917514, 917517, 851980, 983055, 983054, 917513, 917516,
  983051, 983050, 983053, 917512, 1048591, 983041, 983049, 983052, 1048587, 1048590, 1048589, 983048,
  1048583, 1048586, 1048585, 1048588, 1048580, 1048582, 1048581, 1048584
]

def cavlcCtEnc1 : Array UInt32 := #[
  131075, 0, 0, 0, 393227, 131074, 0, 0, 393223, 327687, 196611, 0,
  458759, 393226, 393225, 262149, 524295, 393222, 393221, 262148, 524292, 458758, 458757, 327686,
  589831, 524294, 524293, 393224, 720911, 589830, 589829, 393220, 720907, 720910, 720909, 458756,
  786447, 720906, 720905, 589828, 786443, 786446, 786445, 720908, 786440, 786442, 786441, 720904,
  851983, 851982, 851981, 786444, 851979, 851978, 851977, 851980, 851975, 917515, 851974, 851976,
  917513, 917512, 917514, 851969, 917511, 917510, 917509, 917508
]

def cavlcCtEnc2 : Array UInt32 := #[
  262159, 0, 0, 0, 393231, 262158, 0, 0, 393227, 327695, 262157, 0,
  393224, 327692, 327694, 262156, 458767, 327690, 327691, 262155, 458763, 327688, 327689, 262154,
  458761, 393230, 393229, 262153, 458760, 393226, 393225, 262152, 524303, 458766, 458765, 327693,
  524299, 524302, 458762, 393228, 589839, 524298, 524301, 458764, 589835, 589838, 524297, 524300,
  589832, 589834, 589837, 524296, 655373, 589831, 589833, 589836, 655369, 655372, 655371, 655370,
  655365, 655368, 655367, 655366, 655361, 655364, 655363, 655362
]

def cavlcCtEnc3 : Array UInt32 := #[
  393219, 0, 0, 0, 393216, 393217, 0, 0, 393220, 393221, 393222, 0,
  393224, 393225, 393226, 393227, 393228, 393229, 393230, 393231, 393232, 393233, 393234, 393235,
  393236, 393237, 393238, 393239, 393240, 393241, 393242, 393243, 393244, 393245, 393246, 393247,
  393248, 393249, 393250, 393251, 393252, 393253, 393254, 393255, 393256, 393257, 393258, 393259,
  393260, 393261, 393262, 393263, 393264, 393265, 393266, 393267, 393268, 393269, 393270, 393271,
  393272, 393273, 393274, 393275, 393276, 393277, 393278, 393279
]

def cavlcCtChromaDcEnc : Array UInt32 := #[
  131073, 0, 0, 0, 393223, 65537, 0, 0, 393220, 393222,
  196609, 0, 393219, 458755, 458754, 393221, 393218, 524291, 524290, 458752
]

def cavlcTz16Enc : Array UInt32 := #[
  65537, 196611, 196610, 262147, 262146, 327683, 327682, 393219, 393218, 458755, 458754, 524291,
  524290, 589827, 589826, 589825, 196615, 196614, 196613, 196612, 196611, 262149, 262148, 262147,
  262146, 327683, 327682, 393219, 393218, 393217, 393216, 0, 262149, 196615, 196614, 196613,
  262148, 262147, 196612, 196611, 262146, 327683, 327682, 393217, 327681, 393216, 0, 0,
  327683, 196615, 262149, 262148, 196614, 196613, 196612, 262147, 196611, 262146, 327682, 327681,
  327680, 0, 0, 0, 262149, 262148, 262147, 196615, 196614, 196613, 196612, 196611,
  262146, 327681, 262145, 327680, 0, 0, 0, 0, 393217, 327681, 196615, 196614,
  196613, 196612, 196611, 196610, 262145, 196609, 393216, 0, 0, 0, 0, 0,
  393217, 327681, 196613, 196612, 196611, 131075, 196610, 262145, 196609, 393216, 0, 0,
  0, 0, 0, 0, 393217, 262145, 327681, 196611, 131075, 131074, 196610, 196609,
  393216, 0, 0, 0, 0, 0, 0, 0, 393217, 393216, 262145, 131075,
  131074, 196609, 131073, 327681, 0, 0, 0, 0, 0, 0, 0, 0,
  327681, 327680, 196609, 131075, 131074, 131073, 262145, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 262144, 262145, 196609, 196610, 65537, 196611, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 262144, 262145, 131073, 65537,
  196609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  196608, 196609, 65537, 131073, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 131072, 131073, 65537, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 65536, 65537, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]

def cavlcTz4Enc : Array UInt32 := #[
  65537, 131073, 196609, 196608, 65537, 131073, 131072, 0, 65537, 65536, 0, 0
]

def cavlcRunBeforeEnc : Array UInt32 := #[
  65537, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 65537, 131073, 131072, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 131075, 131074, 131073, 131072, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 131075, 131074, 131073,
  196609, 196608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  131075, 131074, 196611, 196610, 196609, 196608, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 131075, 196608, 196609, 196611, 196610, 196613, 196612, 0, 0,
  0, 0, 0, 0, 0, 0, 196615, 196614, 196613, 196612, 196611, 196610,
  196609, 262145, 327681, 393217, 458753, 524289, 589825, 655361, 720897
]

def cavlcCbpIntraDec : Array Nat := #[
  47, 31, 15, 0, 23, 27, 29, 30, 7, 11, 13, 14, 39, 43, 45, 46,
  16, 3, 5, 10, 12, 19, 21, 26, 28, 35, 37, 42, 44, 1, 2, 4,
  8, 17, 18, 20, 24, 6, 9, 22, 25, 32, 33, 34, 36, 40, 38, 41
]

def cavlcCbpInterDec : Array Nat := #[
  0, 16, 1, 2, 4, 8, 32, 3, 5, 10, 12, 15, 47, 7, 11, 13,
  14, 6, 9, 31, 35, 37, 42, 44, 33, 34, 36, 40, 39, 43, 45, 46,
  17, 18, 20, 24, 19, 21, 26, 28, 23, 27, 29, 30, 22, 25, 38, 41
]

def cavlcCbpIntraGrayDec : Array Nat := #[
  15, 0, 7, 11, 13, 14, 3, 5, 10, 12, 1, 2, 4, 8, 6, 9
]

def cavlcCbpInterGrayDec : Array Nat := #[
  0, 1, 2, 4, 8, 3, 5, 10, 12, 15, 7, 11, 13, 14, 6, 9
]

def cabacRangeTabLPS : Array Nat := #[
  128, 176, 208, 240, 128, 167, 197, 227, 128, 158, 187, 216, 123, 150, 178, 205,
  116, 142, 169, 195, 111, 135, 160, 185, 105, 128, 152, 175, 100, 122, 144, 166,
  95, 116, 137, 158, 90, 110, 130, 150, 85, 104, 123, 142, 81, 99, 117, 135,
  77, 94, 111, 128, 73, 89, 105, 122, 69, 85, 100, 116, 66, 80, 95, 110,
  62, 76, 90, 104, 59, 72, 86, 99, 56, 69, 81, 94, 53, 65, 77, 89,
  51, 62, 73, 85, 48, 59, 69, 80, 46, 56, 66, 76, 43, 53, 63, 72,
  41, 50, 59, 69, 39, 48, 56, 65, 37, 45, 54, 62, 35, 43, 51, 59,
  33, 41, 48, 56, 32, 39, 46, 53, 30, 37, 43, 50, 29, 35, 41, 48,
  27, 33, 39, 45, 26, 31, 37, 43, 24, 30, 35, 41, 23, 28, 33, 39,
  22, 27, 32, 37, 21, 26, 30, 35, 20, 24, 29, 33, 19, 23, 27, 31,
  18, 22, 26, 30, 17, 21, 25, 28, 16, 20, 23, 27, 15, 19, 22, 25,
  14, 18, 21, 24, 14, 17, 20, 23, 13, 16, 19, 22, 12, 15, 18, 21,
  12, 14, 17, 20, 11, 14, 16, 19, 11, 13, 15, 18, 10, 12, 15, 17,
  10, 12, 14, 16, 9, 11, 13, 15, 9, 11, 12, 14, 8, 10, 12, 14,
  8, 9, 11, 13, 7, 9, 11, 12, 7, 9, 10, 12, 7, 8, 10, 11,
  6, 8, 9, 11, 6, 7, 9, 10, 6, 7, 8, 9, 2, 2, 2, 2
]

def cabacTransIdxLPS : Array Nat := #[
  0, 0, 1, 2, 2, 4, 4, 5, 6, 7, 8, 9, 9, 11, 11, 12,
  13, 13, 15, 15, 16, 16, 18, 18, 19, 19, 21, 21, 22, 22, 23, 24,
  24, 25, 26, 26, 27, 27, 28, 29, 29, 30, 30, 30, 31, 32, 32, 33,
  33, 33, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 63
]

def cabacTransIdxMPS : Array Nat := #[
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
  17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
  33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 62, 63
]

def cabacLast8x8 : Array Nat := #[
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4,
  5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8
]

def cabacSig8x8Frame : Array Nat := #[
  0, 1, 2, 3, 4, 5, 5, 4, 4, 3, 3, 4, 4, 4, 5, 5,
  4, 4, 4, 4, 3, 3, 6, 7, 7, 7, 8, 9, 10, 9, 8, 7,
  7, 6, 11, 12, 13, 11, 6, 7, 8, 9, 14, 10, 9, 8, 6, 11,
  12, 13, 11, 6, 9, 14, 10, 9, 11, 12, 13, 11, 14, 10, 12
]

def cabacInitI460 : Array Nat := #[
  38001, 33462, 33738, 38001, 33462, 33738, 25855, 27112, 31413, 32694, 34739, 32896, 32896, 32896, 32896, 32896,
  32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896,
  32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896,
  32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32896, 32937, 32959, 32959, 32959,
  30675, 34006, 32993, 31176, 36265, 33726, 32907, 33207, 32965, 28671, 29670, 32978, 31178, 27627, 26111, 25087,
  26879, 28383, 26111, 27634, 25343, 28667, 29939, 28922, 30195, 29887, 32452, 29140, 29672, 32198, 30941, 30426,
  25343, 32714, 31457, 31195, 27903, 31928, 31698, 31180, 27389, 31197, 30167, 32205, 31687, 31935, 31940, 29908,
  31166, 31169, 35005, 34232, 32450, 33216, 32957, 32462, 33202, 34740, 35491, 32940, 35750, 33197, 32942, 34220,
  40849, 33203, 34738, 40083, 37025, 36542, 29676, 29156, 29669, 29659, 29918, 30424, 28884, 30422, 31187, 29655,
  28126, 33222, 32968, 31690, 37563, 30950, 29156, 32991, 31947, 33480, 30155, 32199, 36782, 29637, 32958, 32961,
  38309, 29128, 35257, 37046, 32958, 36040, 39040, 36745, 34969, 36242, 36745, 36243, 35493, 35986, 34461, 38049,
  36766, 33965, 33210, 32958, 34749, 36006, 35757, 36775, 35754, 36268, 37037, 36009, 35505, 40610, 37546, 35511,
  37299, 37294, 32985, 39533, 38511, 39535, 40551, 40044, 41321, 42341, 41321, 43108, 42607, 41333, 43121, 43386,
  42625, 43409, 40570, 39811, 39574, 42352, 41852, 42616, 42621, 42371, 42629, 43648, 41872, 42902, 36528, 39845,
  38332, 36036, 33505, 32199, 31402, 31666, 32182, 32446, 32954, 33215, 32456, 32714, 30683, 31683, 31643, 32167,
  32428, 32942, 28864, 30916, 30414, 31437, 30422, 29916, 29111, 30396, 31422, 31937, 29897, 30924, 31184, 30680,
  28654, 30177, 27860, 30159, 31433, 31946, 29654, 29664, 30177, 28149, 30926, 31649, 31920, 32437, 32190, 29639,
  30415, 29910, 29658, 29409, 32896, 31453, 31444, 30927, 32962, 32711, 32958, 32444, 32443, 31691, 32190, 31930,
  30658, 32719, 32967, 33732, 35500, 31166, 36772, 36520, 37019, 35997, 33196, 38052, 37536, 34218, 33200, 35518,
  37294, 35264, 29928, 30177, 28896, 31192, 30933, 31189, 30677, 29656, 33986, 32205, 32204, 31436, 35514, 32716,
  32723, 31203, 29407, 33503, 32972, 31690, 32966, 30155, 33220, 32961, 29385, 33726, 33982, 32708, 29643, 35767,
  34240, 36038, 36742, 34451, 34704, 35982, 37517, 36235, 36239, 36752, 35991, 36247, 36756, 36506, 36524, 37288,
  37295, 39057, 38293, 39318, 40859, 38557, 37795, 36530, 35513, 34751, 32461, 31954, 32222, 35269, 29933, 42077,
  42078, 41062, 42338, 44128, 41582, 41585, 43121, 41337, 41851, 41344, 42626, 41357, 38819, 36282, 40317, 39552,
  38558, 40825, 41841, 41597, 41603, 42111, 41605, 41099, 41861, 41612, 42891, 40605, 41626, 40359, 37826, 40853,
  40863, 39346, 28664, 27888, 28402, 30165, 29148, 29401, 26311, 29137, 29392, 32964, 29382, 26808, 27076, 26802,
  30154, 38771, 39539, 43121, 45426, 44163, 44422, 44194, 41398, 37842, 32203, 32663, 33186, 33195, 32950, 32439,
  32957, 33216, 32964, 30684, 29418, 29665, 29146, 29914, 28376, 30409, 30671, 29398, 30409, 30406, 30405, 31682,
  30656, 31674, 33467, 38262, 39029, 40056, 40063, 40323, 40329, 41876, 40356, 36547
]

def cabacInitI1012 : Array Nat := #[
  32198, 30941, 30426, 25343, 32198, 30941, 30426, 25343, 32198, 30941, 30426, 25343
]

def cabacInitPB460_0 : Array Nat := #[
  38001, 33462, 33738, 38001, 33462, 33738, 25855, 27112, 31413, 32694, 34739, 38817, 38786, 38272, 33161, 32945,
  23542, 34233, 29646, 30145, 33214, 36017, 31945, 37298, 37568, 35243, 40320, 39619, 37082, 35304, 21247, 27880,
  33219, 29646, 30145, 33214, 31446, 28639, 31421, 35245, 32197, 31441, 30176, 34487, 34755, 31702, 33496, 32954,
  32204, 30430, 34230, 33989, 32209, 32984, 31171, 31690, 31946, 31696, 31176, 33210, 32937, 32959, 32959, 32959,
  30675, 34006, 32993, 31176, 36265, 33726, 32941, 31950, 32224, 26110, 25826, 26597, 27075, 25810, 27870, 28883,
  27374, 27611, 28390, 29661, 25599, 31196, 31705, 31200, 29676, 32174, 32705, 32697, 30685, 32202, 30684, 30935,
  27134, 34230, 34492, 34491, 34501, 32688, 32964, 31941, 30936, 32469, 31438, 32715, 31181, 33462, 34226, 32196,
  33202, 34474, 31953, 33215, 31942, 32963, 33465, 32460, 35747, 33984, 33213, 35747, 37529, 35992, 36253, 36260,
  30429, 31177, 32457, 36270, 35249, 31204, 35253, 33461, 34229, 32445, 32952, 32952, 29631, 31676, 32702, 33977,
  31429, 33977, 36519, 33971, 36292, 33728, 33213, 35263, 34738, 37031, 34220, 33972, 35760, 31676, 32699, 32955,
  38561, 34220, 36523, 32718, 32956, 35269, 35740, 33448, 33708, 32945, 32942, 33452, 33459, 32943, 33959, 33470,
  34478, 32950, 33718, 33466, 33983, 34483, 34489, 34741, 34484, 34487, 35757, 36516, 34997, 32722, 34743, 32206,
  36782, 38559, 32724, 39303, 40569, 40067, 40068, 41088, 41599, 40582, 40582, 41097, 40851, 39579, 39582, 42388,
  40098, 37318, 33219, 34235, 35267, 37022, 37536, 37539, 38557, 39071, 38822, 37547, 38057, 35775, 35259, 35264,
  32734, 32473, 30700, 31436, 32428, 32941, 32948, 32192, 32443, 31942, 31947, 30930, 28646, 30669, 33688, 32938,
  32944, 32951, 31419, 31175, 29907, 30167, 25335, 33210, 32157, 32676, 33190, 33451, 31415, 32954, 32960, 32202,
  30426, 32966, 31901, 34207, 34730, 33211, 32442, 32200, 32209, 30177, 32954, 34949, 35470, 36498, 36251, 33448,
  32954, 32198, 31439, 30933, 32896, 29674, 28906, 30423, 27634, 28398, 29410, 27374, 27626, 28391, 27627, 27116,
  26352, 30432, 29919, 31707, 30685, 27358, 31702, 35267, 31952, 30421, 32710, 34748, 35258, 34237, 36018, 36786,
  37553, 37302, 35497, 34734, 32691, 34737, 34996, 35241, 34479, 33463, 36265, 35500, 34482, 34229, 36273, 33983,
  34496, 32453, 32443, 34502, 35500, 35231, 36011, 33717, 36514, 35494, 32180, 36264, 37280, 34732, 34726, 36274,
  35513, 39595, 36491, 35726, 35211, 37515, 38281, 38782, 41073, 41073, 41579, 42857, 43615, 43361, 44644, 42612,
  38301, 44392, 46419, 45158, 49493, 43885, 42870, 40585, 37530, 38043, 32953, 29394, 31691, 28129, 24061, 39808,
  40064, 40828, 39814, 41608, 40586, 39062, 41363, 38560, 39583, 38313, 39596, 38831, 37057, 36551, 35004, 34495,
  37313, 38296, 38804, 39575, 39840, 40087, 40088, 38824, 39072, 40093, 38826, 37817, 38581, 38589, 35798, 36008,
  35763, 36539, 31951, 31175, 31685, 30662, 30914, 30404, 28105, 29893, 28870, 29123, 27838, 28102, 28866, 27329,
  27839, 35198, 39543, 41335, 42873, 43390, 44419, 45449, 44443, 42171, 31426, 31139, 31146, 30893, 31664, 29880,
  31420, 31678, 30914, 30924, 31701, 31441, 30413, 31185, 28624, 28361, 31946, 30419, 30663, 30659, 32701, 30914,
  29378, 32955, 33467, 38259, 41330, 42873, 44670, 45954, 48262, 48529, 47010, 43710
]

def cabacInitPB1012_0 : Array Nat := #[
  32202, 30684, 30935, 27134, 32202, 30684, 30935, 27134, 32202, 30684, 30935, 27134
]

def cabacInitPB460_1 : Array Nat := #[
  38001, 33462, 33738, 38001, 33462, 33738, 25855, 27112, 31413, 32694, 34739, 38553, 41600, 36992, 32393, 33961,
  25590, 33473, 31431, 29647, 34228, 35250, 32198, 35510, 39586, 37782, 43136, 47490, 43428, 39621, 21503, 29157,
  31948, 31431, 29647, 34228, 34501, 29658, 32948, 34987, 32453, 31698, 30432, 33467, 33483, 32215, 32228, 33208,
  32202, 31445, 32955, 32209, 31190, 31711, 32706, 32717, 33222, 32470, 31688, 32957, 32937, 32959, 32959, 32959,
  30675, 34006, 32993, 31176, 36265, 33726, 36239, 34739, 33488, 23039, 28379, 28640, 26321, 24034, 26854, 27105,
  26103, 26851, 27630, 28390, 23807, 32976, 31705, 31198, 31964, 32935, 32961, 29140, 24063, 32457, 29928, 30683,
  25087, 33719, 34744, 34743, 35005, 32181, 32964, 31178, 30680, 29671, 29659, 30681, 29404, 30924, 29911, 27118,
  26857, 30414, 27888, 28643, 13055, 15103, 20223, 21247, 31938, 31694, 31943, 30920, 33467, 32695, 31174, 31435,
  30937, 24311, 32203, 41108, 40598, 21759, 32950, 31677, 32954, 32700, 32189, 30915, 26580, 29386, 31681, 34228,
  33465, 32957, 30661, 30150, 37559, 31943, 32954, 34749, 35241, 37529, 35232, 34219, 35247, 32940, 32947, 33454,
  37798, 31938, 36774, 36010, 35234, 32985, 33965, 35484, 35487, 41333, 46165, 37519, 40064, 41834, 42599, 41600,
  42862, 41076, 58914, 32896, 47217, 41340, 40330, 42363, 45923, 42871, 46174, 50502, 49985, 44155, 41095, 46947,
  41089, 32896, 39844, 41319, 41570, 42084, 42596, 42597, 41582, 41840, 41586, 41080, 42362, 41856, 40586, 40082,
  39577, 40361, 32971, 33480, 35021, 36515, 37535, 37283, 38302, 37293, 38058, 37549, 39834, 37046, 34754, 37048,
  35785, 35523, 30452, 27120, 29127, 31165, 32949, 31682, 30157, 30672, 30676, 30423, 24319, 27621, 32167, 31669,
  31165, 30155, 29133, 28635, 26603, 26607, 25850, 30156, 30380, 30388, 30393, 30650, 28872, 31173, 31941, 31690,
  30678, 33474, 30626, 33184, 35743, 34228, 32439, 32451, 32969, 30937, 33716, 34692, 35464, 37256, 37011, 33701,
  32701, 31689, 32710, 31950, 32896, 27646, 27132, 27886, 26366, 26620, 28649, 26105, 26101, 28646, 26357, 26100,
  24570, 30431, 29412, 30943, 28655, 25842, 31449, 32464, 31954, 30677, 30929, 32712, 34240, 33219, 35256, 32965,
  33221, 34757, 31173, 31427, 28877, 32448, 33469, 31427, 32192, 33465, 32193, 32194, 32958, 35251, 32706, 32455,
  32459, 32710, 30664, 36540, 37029, 32943, 37539, 35749, 36009, 35497, 33456, 36009, 36265, 32955, 33714, 37800,
  33730, 37554, 37754, 37498, 36480, 39540, 40816, 41319, 41322, 42340, 42850, 43618, 44886, 44380, 45406, 43375,
  41097, 50489, 48961, 49728, 52534, 46681, 46173, 43382, 42112, 43135, 40590, 40090, 38821, 36023, 35777, 42335,
  42844, 43099, 42594, 44639, 43618, 43112, 45411, 42612, 43126, 42621, 44667, 40852, 40350, 39340, 36016, 35761,
  39597, 38550, 38806, 39829, 41364, 39580, 40600, 39842, 37546, 39335, 37554, 36038, 38326, 36551, 35795, 39328,
  38321, 38326, 31701, 31441, 30413, 31185, 28624, 28361, 31946, 30419, 30663, 30659, 32701, 30914, 29378, 32955,
  33467, 37238, 41075, 43639, 45435, 46464, 49283, 50314, 49819, 44985, 31687, 32920, 32676, 32426, 32436, 30649,
  31423, 31937, 31939, 31186, 32209, 32204, 31176, 31438, 29896, 29380, 32198, 31436, 31682, 31678, 32953, 31933,
  30652, 33206, 33466, 37238, 41075, 43639, 45435, 46464, 49283, 50314, 49819, 44985
]

def cabacInitPB1012_1 : Array Nat := #[
  32457, 29928, 30683, 25087, 32457, 29928, 30683, 25087, 32457, 29928, 30683, 25087
]

def cabacInitPB460_2 : Array Nat := #[
  38001, 33462, 33738, 38001, 33462, 33738, 25855, 27112, 31413, 32694, 34739, 40336, 39296, 36480, 30387, 32190,
  26083, 39568, 31957, 26854, 34233, 34489, 28617, 36537, 38056, 38026, 40320, 46720, 42410, 36065, 24831, 27381,
  32458, 31957, 26854, 34233, 31453, 29400, 31404, 33975, 30169, 29159, 27636, 37817, 38074, 34004, 34528, 33215,
  31701, 29674, 34239, 34507, 32218, 32741, 33719, 31951, 32459, 29921, 31154, 33212, 32937, 32959, 32959, 32959,
  30675, 34006, 32993, 31176, 36265, 33726, 34722, 30680, 27903, 23807, 28635, 29407, 26580, 26582, 29913, 28635,
  25087, 29388, 28391, 29658, 23551, 35792, 34252, 33492, 34254, 31415, 33981, 29395, 23551, 31695, 30184, 30171,
  25343, 32961, 32463, 32968, 31964, 31416, 33732, 30919, 29666, 31958, 29912, 31698, 32200, 31939, 30920, 28889,
  30661, 32699, 34242, 33977, 31943, 32455, 33466, 32714, 31916, 32709, 32958, 31155, 31919, 31402, 32169, 31413,
  35020, 30670, 30163, 35252, 32963, 31706, 33219, 29128, 31691, 30928, 27603, 27584, 29599, 26560, 25566, 35275,
  37311, 30922, 31651, 32411, 36315, 33729, 31173, 35021, 30402, 33726, 32196, 27857, 32926, 33159, 32151, 27594,
  37058, 27132, 37285, 44142, 45662, 27391, 33959, 32938, 34722, 35741, 34975, 34469, 34730, 33704, 34977, 36267,
  36260, 33967, 33719, 33466, 34492, 34988, 35756, 36522, 34736, 33976, 33972, 36261, 35249, 37818, 35504, 36013,
  32965, 38049, 35007, 41838, 41319, 40061, 39050, 39808, 41586, 46164, 42856, 37777, 40857, 42141, 39073, 41615,
  40596, 38601, 38050, 37791, 39852, 37776, 36772, 36772, 38300, 39317, 40596, 40844, 39824, 39082, 32989, 36536,
  36793, 39590, 26879, 26867, 27346, 30654, 32949, 32955, 29397, 29657, 29662, 30172, 25599, 27620, 29369, 29891,
  30151, 30413, 27605, 28888, 27112, 29154, 23551, 30418, 30896, 30909, 30914, 31174, 29387, 30415, 30675, 29916,
  28396, 31951, 27333, 28875, 32442, 33210, 29646, 30675, 31953, 29667, 29649, 31398, 29630, 31418, 32443, 28873,
  30412, 29654, 30675, 30423, 32896, 27391, 26623, 26616, 26111, 28146, 27125, 26614, 26357, 26865, 25846, 25080,
  23548, 30430, 29158, 30435, 29674, 20223, 31708, 37305, 31702, 29662, 29915, 32461, 32967, 32713, 33984, 31185,
  34240, 36793, 33219, 32964, 30403, 33220, 32973, 33472, 32964, 31694, 34743, 34235, 33473, 36534, 36780, 34236,
  33478, 32460, 28374, 36038, 34240, 29894, 35767, 34232, 32965, 33473, 31434, 34230, 34742, 31436, 30162, 32461,
  32461, 39338, 37235, 36983, 37236, 39787, 42338, 43352, 43607, 45137, 42848, 44632, 46157, 44631, 46169, 43885,
  41099, 48457, 47186, 48718, 53565, 44396, 41854, 40079, 41601, 42881, 40593, 38054, 37549, 36790, 32975, 42096,
  42354, 42351, 41089, 41615, 40335, 39065, 41622, 40848, 41874, 40860, 41385, 42140, 39855, 38334, 37535, 37786,
  42136, 39063, 39824, 39070, 40861, 38569, 38570, 37052, 36788, 36540, 33742, 28923, 38325, 38584, 39357, 38305,
  37810, 37309, 32206, 30922, 30664, 30408, 28363, 29895, 30143, 31686, 28619, 29384, 28867, 30901, 29371, 30644,
  30148, 35198, 40566, 40828, 41343, 41351, 40844, 42391, 40870, 38080, 30663, 31141, 30892, 30129, 30392, 29883,
  30911, 30659, 31428, 30415, 32206, 30922, 30664, 30408, 28363, 29895, 30143, 31686, 28619, 29384, 28867, 30901,
  29371, 30644, 30148, 35198, 40566, 40828, 41343, 41351, 40844, 42391, 40870, 38080
]

def cabacInitPB1012_2 : Array Nat := #[
  31695, 30184, 30171, 25343, 31695, 30184, 30171, 25343, 31695, 30184, 30171, 25343
]

private def writePackedVlc (w : BitWriter) (packed : UInt32) : Option BitWriter :=
  let len := (packed >>> 16).toNat
  if len == 0 then none
  else
    let code := (packed &&& 0xFFFF).toUInt64
    some (w.writeBitsMSB code len)

private def matchVlcScan (tab : Array UInt32) (base count len code : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
    let sym := count - 1 - rem
    let packed := tab.getD (base + sym) 0
    if (packed >>> 16).toNat == len && (packed &&& 0xFFFF).toNat == code then
      some sym
    else
      matchVlcScan tab base count len code rem

private def readPackedVlcLoop (tab : Array UInt32) (base count : Nat) :
    Nat → BitReader → Nat → Nat → Option (Nat × BitReader)
  | 0, _, _, _ => none
  | fuel + 1, r, len, code => do
    let (b, r') ← readU1Nat r
    let len' := len + 1
    let code' := (code <<< 1) ||| b
    match matchVlcScan tab base count len' code' count with
    | some sym => some (sym, r')
    | none => readPackedVlcLoop tab base count fuel r' len' code'

def readPackedVlc (r : BitReader) (tab : Array UInt32) (base count : Nat) : Option (Nat × BitReader) :=
  readPackedVlcLoop tab base count 16 r 0 0

def cavlcCtTable (nC : Nat) : Array UInt32 :=
  if nC < 2 then cavlcCtEnc0
  else if nC < 4 then cavlcCtEnc1
  else if nC < 8 then cavlcCtEnc2
  else cavlcCtEnc3

def cavlcLookupCbpCode (tab : Array Nat) (cbp : Nat) : Option Nat := Id.run do
  for idx in [:tab.size] do
    if tab.getD idx 999 == cbp then
      return some idx
  return none

private def readTrailingOnesSigns (r : BitReader) (t1 : Nat) :
    Nat → Array Int → Option (Array Int × BitReader)
  | 0, acc => some (acc, r)
  | k + 1, acc => do
    let (s, r') ← readU1Nat r
    let v : Int := if s != 0 then -1 else 1
    readTrailingOnesSigns r' t1 k (acc.push v)

private def readLevelPrefixLoop (r : BitReader) : Nat → Nat → Option (Nat × BitReader)
  | 0, _ => none
  | fuel + 1, pref => do
    let (b, r') ← readU1Nat r
    if b == 1 then some (pref, r')
    else readLevelPrefixLoop r' fuel (pref + 1)

private def decodeCavlcLevelsLoop (r : BitReader) (tc t1 : Nat) :
    Nat → Nat → Array Int → Option (Array Int × BitReader)
  | 0, _, acc => some (acc, r)
  | rem + 1, sl, acc => do
    let i := tc - 1 - rem
    let (pref, r1) ← readLevelPrefixLoop r (Nat.min 36 r.bitsLeft + 1) 0
    if pref > 35 then none
    else do
      let (lc0, r2) ←
        if pref == 14 && sl == 0 then do
          let (suf, ra) ← readUNat r1 4
          pure (14 + suf, ra)
        else if pref ≥ 15 then do
          let lsz := if pref == 15 then 12 else pref - 3
          let (lsuf0, ra) ← readUNat r1 lsz
          let lsuf := if pref ≥ 16 then lsuf0 + ((1 <<< (pref - 3)) - 4096) else lsuf0
          let baseLc := (15 <<< sl) + lsuf
          pure (if sl == 0 then baseLc + 15 else baseLc, ra)
        else do
          let (suf, ra) ← if sl > 0 then readUNat r1 sl else pure (0, r1)
          pure ((pref <<< sl) + suf, ra)
      let lc := if i == t1 && t1 < 3 then lc0 + 2 else lc0
      let mag : Int := Int.ofNat ((lc + 2) / 2)
      let val : Int := if lc % 2 == 1 then -mag else mag
      let sl1 := if sl == 0 then 1 else sl
      let thresh := 3 <<< (sl1 - 1)
      let slNext := if val.natAbs > thresh && sl1 < 6 then sl1 + 1 else sl1
      decodeCavlcLevelsLoop r2 tc t1 rem slNext (acc.push val)

private def decodeCavlcRunsLoop (r : BitReader) :
    Nat → Nat → Array Nat → Option (Array Nat × BitReader)
  | 0, zLeft, acc => some (acc.push zLeft, r)
  | rem + 1, zLeft, acc =>
    if zLeft == 0 then
      decodeCavlcRunsLoop r rem 0 (acc.push 0)
    else do
      let vlcIdx := Nat.min zLeft 7
      let (rb, r') ← readPackedVlc r cavlcRunBeforeEnc ((vlcIdx - 1) * 15) 15
      if rb > zLeft then none
      else decodeCavlcRunsLoop r' rem (zLeft - rb) (acc.push rb)

def cavlcDecodeBlock (r : BitReader) (maxCoeff nC : Nat) : Option (Array Int × Nat × BitReader) := do
  let (sym, r1) ←
    if maxCoeff == 4 then readPackedVlc r cavlcCtChromaDcEnc 0 20
    else readPackedVlc r (cavlcCtTable nC) 0 68
  let tc := sym >>> 2
  let t1 := sym &&& 3
  if tc > maxCoeff then none
  else if tc == 0 then
    some (Array.replicate maxCoeff 0, 0, r1)
  else do
    let (levels0, r2) ← readTrailingOnesSigns r1 t1 t1 (Array.emptyWithCapacity tc)
    let sl0 := if tc > 10 && t1 < 3 then 1 else 0
    let (levels, r3) ← decodeCavlcLevelsLoop r2 tc t1 (tc - t1) sl0 levels0
    let (zerosLeft, r4) ←
      if tc < maxCoeff then
        if maxCoeff == 4 then readPackedVlc r3 cavlcTz4Enc ((tc - 1) * 4) 4
        else readPackedVlc r3 cavlcTz16Enc ((tc - 1) * 16) 16
      else
        pure (0, r3)
    if tc + zerosLeft > maxCoeff then none
    else do
      let (runs, r5) ← decodeCavlcRunsLoop r4 (tc - 1) zerosLeft (Array.emptyWithCapacity tc)
      let coeffs := Id.run do
        let mut arr := Array.replicate maxCoeff (0 : Int)
        let mut pos : Nat := 0
        for step in [:tc] do
          let i := tc - 1 - step
          pos := pos + runs.getD i 0
          if pos < maxCoeff then
            arr := arr.set! pos (levels.getD i 0)
          pos := pos + 1
        return arr
      some (coeffs, tc, r5)

private def findLargeCavlcPrefix (rem p : Nat) : Nat → Nat
  | 0 => p
  | fuel + 1 =>
    if rem ≥ ((1 <<< (p - 2)) - 4096) then
      findLargeCavlcPrefix rem (p + 1) fuel
    else
      p

private def writeCavlcEscape (w : BitWriter) (rem : Nat) : BitWriter :=
  if rem < 4096 then
    let w1 := w.writeUnary0 15
    writeUNat w1 rem 12
  else
    let p := findLargeCavlcPrefix rem 16 20
    let w1 := w.writeUnary0 p
    let base := (1 <<< (p - 3)) - 4096
    writeUNat w1 (rem - base) (p - 3)

def cavlcEncodeBlock (w : BitWriter) (coeffs : Array Int) (maxCoeff nC : Nat) : Option (BitWriter × Nat) := do
  let nz := Id.run do
    let mut acc : Array (Nat × Int) := #[]
    for idx in [:Nat.min maxCoeff coeffs.size] do
      let c := coeffs.getD idx 0
      if c != 0 then acc := acc.push (idx, c)
    return acc
  let tc := nz.size
  if tc > maxCoeff then none
  else if tc == 0 then do
    let packed :=
      if maxCoeff == 4 then cavlcCtChromaDcEnc.getD 0 0
      else (cavlcCtTable nC).getD 0 0
    let w1 ← writePackedVlc w packed
    some (w1, 0)
  else do
    let rev := nz.reverse
    let t1 := Id.run do
      let mut cnt := 0
      for k in [:Nat.min 3 tc] do
        if (rev.getD k (0, 0)).2.natAbs == 1 then cnt := cnt + 1
        else break
      return cnt
    let sym := (tc <<< 2) ||| t1
    let packedCt :=
      if maxCoeff == 4 then cavlcCtChromaDcEnc.getD sym 0
      else (cavlcCtTable nC).getD sym 0
    let mut cur ← writePackedVlc w packedCt
    for i in [:t1] do
      let c := (rev.getD i (0, 0)).2
      cur := writeU1Nat cur (if c < 0 then 1 else 0)
    let mut sl := if tc > 10 && t1 < 3 then 1 else 0
    for off in [:tc - t1] do
      let i := t1 + off
      let val := (rev.getD i (0, 0)).2
      let absV := val.natAbs
      let lc0 := if val > 0 then 2 * absV - 2 else 2 * absV - 1
      let lc := if i == t1 && t1 < 3 then lc0 - 2 else lc0
      if sl == 0 then
        if lc < 14 then
          cur := cur.writeUnary0 lc
        else if lc < 30 then
          cur := writeUNat (cur.writeUnary0 14) (lc - 14) 4
        else
          cur := writeCavlcEscape cur (lc - 30)
      else
        if (lc >>> sl) < 15 then
          let p := lc >>> sl
          cur := writeUNat (cur.writeUnary0 p) (lc &&& ((1 <<< sl) - 1)) sl
        else
          cur := writeCavlcEscape cur (lc - (15 <<< sl))
      if sl == 0 then sl := 1
      if absV > (3 <<< (sl - 1)) && sl < 6 then sl := sl + 1
    let runs := Id.run do
      let mut rs : Array Nat := Array.emptyWithCapacity tc
      for k in [:tc - 1] do
        let p0 := (rev.getD k (0, 0)).1
        let p1 := (rev.getD (k + 1) (0, 0)).1
        rs := rs.push (p0 - p1 - 1)
      rs := rs.push (rev.getD (tc - 1) (0, 0)).1
      return rs
    let totalZeros := runs.foldl (· + ·) 0
    if tc < maxCoeff then
      let packedTz :=
        if maxCoeff == 4 then cavlcTz4Enc.getD ((tc - 1) * 4 + totalZeros) 0
        else cavlcTz16Enc.getD ((tc - 1) * 16 + totalZeros) 0
      cur ← writePackedVlc cur packedTz
    let mut zLeft := totalZeros
    for i in [:tc - 1] do
      if zLeft > 0 then
        let rVal := runs.getD i 0
        let vlcIdx := Nat.min zLeft 7
        let packedRb := cavlcRunBeforeEnc.getD ((vlcIdx - 1) * 15 + rVal) 0
        cur ← writePackedVlc cur packedRb
        zLeft := zLeft - rVal
    some (cur, tc)

private def unpackInitState (packed : Nat) (qp : Int) : UInt8 :=
  let m : Int := Int.ofNat (packed >>> 8) - 128
  let n : Int := Int.ofNat (packed &&& 0xFF) - 128
  let prod : Int := m * qp
  let shifted : Int := Int.ediv prod 16
  let raw : Int := shifted + n
  let pre : Nat := if raw ≤ 1 then 1 else if raw ≥ 126 then 126 else raw.toNat
  if pre ≤ 63 then (((63 - pre) <<< 1)).toUInt8
  else ((((pre - 64) <<< 1) ||| 1)).toUInt8

def initCabacStates (sliceTypeNos cabacInitIdc : Nat) (sliceQpY : Int) : Array UInt8 := Id.run do
  let qp : Int := if sliceQpY < 0 then 0 else if sliceQpY > 51 then 51 else sliceQpY
  let (tabLo, tabHi) :=
    if sliceTypeNos == 2 then (cabacInitI460, cabacInitI1012)
    else if cabacInitIdc == 0 then (cabacInitPB460_0, cabacInitPB1012_0)
    else if cabacInitIdc == 1 then (cabacInitPB460_1, cabacInitPB1012_1)
    else (cabacInitPB460_2, cabacInitPB1012_2)
  let mut st := Array.replicate 1024 (0 : UInt8)
  for idx in [:tabLo.size] do
    st := st.set! idx (unpackInitState (tabLo.getD idx 32896) qp)
  for k in [:tabHi.size] do
    st := st.set! (1012 + k) (unpackInitState (tabHi.getD k 32896) qp)
  return st

structure CabacDec where
  rbsp    : ByteArray
  pos     : Nat
  total   : Nat
  irange  : Nat
  ioffset : Nat
  deriving Inhabited

private def cabacReadRawBit (rbsp : ByteArray) (total pos : Nat) : Nat × Nat :=
  let nextPos := pos + 1
  if pos ≥ total then (0, nextPos)
  else
    let b := rbsp.data.getD (pos >>> 3) 0
    let shift := (7 - (pos &&& 7)).toUInt8
    (((b >>> shift) &&& 1).toNat, nextPos)

private def cabacInitOffsetLoop (rbsp : ByteArray) (total : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, pos, acc => (acc, pos)
  | k + 1, pos, acc =>
    let (bit, pos') := cabacReadRawBit rbsp total pos
    cabacInitOffsetLoop rbsp total k pos' ((acc <<< 1) ||| bit)

def CabacDec.init (rbsp : ByteArray) (bitPos : Nat) : CabacDec :=
  let aligned := if bitPos % 8 == 0 then bitPos else bitPos + (8 - (bitPos % 8))
  let total := rbsp.data.size * 8
  let (ioff, pos') := cabacInitOffsetLoop rbsp total 9 aligned 0
  { rbsp := rbsp, pos := pos', total := total, irange := 510, ioffset := ioff }

private def cabacDecRenormLoop (rbsp : ByteArray) (total : Nat) :
    Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, pos, rng, off => (pos, rng, off)
  | fuel + 1, pos, rng, off =>
    if rng ≥ 256 then (pos, rng, off)
    else
      let (bit, pos') := cabacReadRawBit rbsp total pos
      cabacDecRenormLoop rbsp total fuel pos' (rng <<< 1) ((off <<< 1) ||| bit)

def CabacDec.decodeDecision (dec : CabacDec) (st : Array UInt8) (ctxIdx : Nat) :
    Nat × CabacDec × Array UInt8 :=
  let entry := st.getD ctxIdx 0
  let p := (entry >>> 1).toNat
  let mps := (entry &&& 1).toNat
  let qIdx := (dec.irange >>> 6) &&& 3
  let rLps := cabacRangeTabLPS.getD (p * 4 + qIdx) 2
  let rMps := dec.irange - rLps
  if dec.ioffset ≥ rMps then
    let binVal := 1 - mps
    let mps' := if p == 0 then 1 - mps else mps
    let p' := cabacTransIdxLPS.getD p 0
    let st' := if ctxIdx < st.size then st.set! ctxIdx (((p' <<< 1) ||| mps').toUInt8) else st
    let (pos', rng', off') := cabacDecRenormLoop dec.rbsp dec.total 8 dec.pos rLps (dec.ioffset - rMps)
    (binVal, { dec with pos := pos', irange := rng', ioffset := off' }, st')
  else
    let binVal := mps
    let p' := cabacTransIdxMPS.getD p 0
    let st' := if ctxIdx < st.size then st.set! ctxIdx (((p' <<< 1) ||| mps).toUInt8) else st
    let (pos', rng', off') := cabacDecRenormLoop dec.rbsp dec.total 8 dec.pos rMps dec.ioffset
    (binVal, { dec with pos := pos', irange := rng', ioffset := off' }, st')

def CabacDec.decodeBypass (dec : CabacDec) : Nat × CabacDec :=
  let (bit, pos') := cabacReadRawBit dec.rbsp dec.total dec.pos
  let off := (dec.ioffset <<< 1) ||| bit
  if off ≥ dec.irange then
    (1, { dec with pos := pos', ioffset := off - dec.irange })
  else
    (0, { dec with pos := pos', ioffset := off })

def CabacDec.decodeTerminate (dec : CabacDec) : Nat × CabacDec :=
  let rng := dec.irange - 2
  if dec.ioffset ≥ rng then
    (1, dec)
  else
    let (pos', rng', off') := cabacDecRenormLoop dec.rbsp dec.total 8 dec.pos rng dec.ioffset
    (0, { dec with pos := pos', irange := rng', ioffset := off' })

def CabacDec.readPcmAndReinit (dec : CabacDec) (nbytes : Nat) : Option (ByteArray × CabacDec) :=
  let byteStart := (dec.pos + 7) >>> 3
  if byteStart + nbytes > dec.rbsp.data.size then none
  else
    let pcm : ByteArray := { data := ((dec.rbsp.data.toList.drop byteStart).take nbytes).toArray }
    let nextBitPos := (byteStart + nbytes) * 8
    let (ioff, pos') := cabacInitOffsetLoop dec.rbsp dec.total 9 nextBitPos 0
    some (pcm, { dec with pos := pos', irange := 510, ioffset := ioff })

structure CabacEnc where
  w               : BitWriter
  ilow            : Nat
  irange          : Nat
  bitsOutstanding : Nat
  firstBit        : Bool
  deriving Inhabited

def CabacEnc.init (w : BitWriter) : CabacEnc :=
  { w := w, ilow := 0, irange := 510, bitsOutstanding := 0, firstBit := true }

private def flushOutstandingLoop (w : BitWriter) (invBit : UInt8) : Nat → BitWriter
  | 0 => w
  | k + 1 => flushOutstandingLoop (w.writeBit invBit) invBit k

private def cabacEncPutBit (enc : CabacEnc) (b : Nat) : CabacEnc :=
  let bit8 : UInt8 := if b != 0 then 1 else 0
  let inv8 : UInt8 := if b != 0 then 0 else 1
  let w1 := if enc.firstBit then enc.w else enc.w.writeBit bit8
  let w2 := flushOutstandingLoop w1 inv8 enc.bitsOutstanding
  { enc with w := w2, bitsOutstanding := 0, firstBit := false }

private def cabacEncRenormLoop : Nat → CabacEnc → CabacEnc
  | 0, enc => enc
  | fuel + 1, enc =>
    if enc.irange ≥ 256 then enc
    else
      let enc1 :=
        if enc.ilow < 256 then
          cabacEncPutBit enc 0
        else if enc.ilow ≥ 512 then
          cabacEncPutBit { enc with ilow := enc.ilow - 512 } 1
        else
          { enc with ilow := enc.ilow - 256, bitsOutstanding := enc.bitsOutstanding + 1 }
      cabacEncRenormLoop fuel { enc1 with irange := enc1.irange <<< 1, ilow := enc1.ilow <<< 1 }

def CabacEnc.encodeDecision (enc : CabacEnc) (st : Array UInt8) (ctxIdx binVal : Nat) :
    CabacEnc × Array UInt8 :=
  let entry := st.getD ctxIdx 0
  let p := (entry >>> 1).toNat
  let mps := (entry &&& 1).toNat
  let qIdx := (enc.irange >>> 6) &&& 3
  let rLps := cabacRangeTabLPS.getD (p * 4 + qIdx) 2
  let rMps := enc.irange - rLps
  let b := if binVal != 0 then 1 else 0
  if b != mps then
    let mps' := if p == 0 then 1 - mps else mps
    let p' := cabacTransIdxLPS.getD p 0
    let st' := if ctxIdx < st.size then st.set! ctxIdx (((p' <<< 1) ||| mps').toUInt8) else st
    let enc' := cabacEncRenormLoop 8 { enc with ilow := enc.ilow + rMps, irange := rLps }
    (enc', st')
  else
    let p' := cabacTransIdxMPS.getD p 0
    let st' := if ctxIdx < st.size then st.set! ctxIdx (((p' <<< 1) ||| mps).toUInt8) else st
    let enc' := cabacEncRenormLoop 8 { enc with irange := rMps }
    (enc', st')

def CabacEnc.encodeBypass (enc : CabacEnc) (binVal : Nat) : CabacEnc :=
  let low1 := (enc.ilow <<< 1) + (if binVal != 0 then enc.irange else 0)
  if low1 ≥ 1024 then
    let e1 := cabacEncPutBit enc 1
    { e1 with ilow := low1 - 1024 }
  else if low1 < 512 then
    let e1 := cabacEncPutBit enc 0
    { e1 with ilow := low1 }
  else
    { enc with ilow := low1 - 512, bitsOutstanding := enc.bitsOutstanding + 1 }

def CabacEnc.encodeTerminate (enc : CabacEnc) (binVal : Nat) : CabacEnc :=
  let rng := enc.irange - 2
  if binVal != 0 then
    let e1 := cabacEncRenormLoop 8 { enc with ilow := enc.ilow + rng, irange := 2 }
    let e2 := cabacEncPutBit e1 ((e1.ilow >>> 9) &&& 1)
    let b8 : UInt8 := if ((e2.ilow >>> 8) &&& 1) != 0 then 1 else 0
    let wFinal := ((e2.w.writeBit b8).writeBit 1).alignToByte
    { e2 with w := wFinal }
  else
    cabacEncRenormLoop 8 { enc with irange := rng }

def CabacEnc.writePcmAndReinit (enc : CabacEnc) (pcm : ByteArray) : CabacEnc :=
  let wAligned := writeBytesAligned enc.w pcm
  { w := wAligned, ilow := 0, irange := 510, bitsOutstanding := 0, firstBit := true }

inductive MbKind where
  | skip
  | iNxN
  | i16x16
  | iPcm
  | pInter
  | bInter
  deriving Repr, DecidableEq, Inhabited

def MbKind.isIntra : MbKind → Bool
  | .iNxN | .i16x16 | .iPcm => true
  | _ => false

def MbKind.isInter : MbKind → Bool
  | .pInter | .bInter => true
  | _ => false

inductive PartShape where
  | direct
  | p16x16
  | p16x8
  | p8x16
  | p8x8
  deriving Repr, DecidableEq, Inhabited

inductive SubPartShape where
  | direct
  | s8x8
  | s8x4
  | s4x8
  | s4x4
  deriving Repr, DecidableEq, Inhabited

structure MbPartInfo where
  shape  : PartShape := .direct
  useL0  : Array Bool := #[]
  useL1  : Array Bool := #[]
  isRef0 : Bool := false
  deriving Repr, Inhabited

structure SubMbPartInfo where
  shape  : SubPartShape := .direct
  subCnt : Nat := 1
  useL0  : Bool := false
  useL1  : Bool := false
  deriving Repr, Inhabited

def pMbInfoTable : Array MbPartInfo := #[
  { shape := .p16x16, useL0 := #[true], useL1 := #[false], isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, true], useL1 := #[false, false], isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, true], useL1 := #[false, false], isRef0 := false },
  { shape := .p8x8,   useL0 := #[true, true, true, true], useL1 := #[false, false, false, false], isRef0 := false },
  { shape := .p8x8,   useL0 := #[true, true, true, true], useL1 := #[false, false, false, false], isRef0 := true }
]

def pSubInfoTable : Array SubMbPartInfo := #[
  { shape := .s8x8, subCnt := 1, useL0 := true, useL1 := false },
  { shape := .s8x4, subCnt := 2, useL0 := true, useL1 := false },
  { shape := .s4x8, subCnt := 2, useL0 := true, useL1 := false },
  { shape := .s4x4, subCnt := 4, useL0 := true, useL1 := false }
]

def bMbInfoTable : Array MbPartInfo := #[
  { shape := .direct, useL0 := #[false], useL1 := #[false], isRef0 := false },
  { shape := .p16x16, useL0 := #[true],  useL1 := #[false], isRef0 := false },
  { shape := .p16x16, useL0 := #[false], useL1 := #[true],  isRef0 := false },
  { shape := .p16x16, useL0 := #[true],  useL1 := #[true],  isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, true],   useL1 := #[false, false], isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, true],   useL1 := #[false, false], isRef0 := false },
  { shape := .p16x8,  useL0 := #[false, false], useL1 := #[true, true],   isRef0 := false },
  { shape := .p8x16,  useL0 := #[false, false], useL1 := #[true, true],   isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, false],  useL1 := #[false, true],  isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, false],  useL1 := #[false, true],  isRef0 := false },
  { shape := .p16x8,  useL0 := #[false, true],  useL1 := #[true, false],  isRef0 := false },
  { shape := .p8x16,  useL0 := #[false, true],  useL1 := #[true, false],  isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, true],   useL1 := #[false, true],  isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, true],   useL1 := #[false, true],  isRef0 := false },
  { shape := .p16x8,  useL0 := #[false, true],  useL1 := #[true, true],   isRef0 := false },
  { shape := .p8x16,  useL0 := #[false, true],  useL1 := #[true, true],   isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, true],   useL1 := #[true, false],  isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, true],   useL1 := #[true, false],  isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, false],  useL1 := #[true, true],   isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, false],  useL1 := #[true, true],   isRef0 := false },
  { shape := .p16x8,  useL0 := #[true, true],   useL1 := #[true, true],   isRef0 := false },
  { shape := .p8x16,  useL0 := #[true, true],   useL1 := #[true, true],   isRef0 := false },
  { shape := .p8x8,   useL0 := #[true, true, true, true], useL1 := #[true, true, true, true], isRef0 := false }
]

def bSubInfoTable : Array SubMbPartInfo := #[
  { shape := .direct, subCnt := 1, useL0 := false, useL1 := false },
  { shape := .s8x8,   subCnt := 1, useL0 := true,  useL1 := false },
  { shape := .s8x8,   subCnt := 1, useL0 := false, useL1 := true  },
  { shape := .s8x8,   subCnt := 1, useL0 := true,  useL1 := true  },
  { shape := .s8x4,   subCnt := 2, useL0 := true,  useL1 := false },
  { shape := .s4x8,   subCnt := 2, useL0 := true,  useL1 := false },
  { shape := .s8x4,   subCnt := 2, useL0 := false, useL1 := true  },
  { shape := .s4x8,   subCnt := 2, useL0 := false, useL1 := true  },
  { shape := .s8x4,   subCnt := 2, useL0 := true,  useL1 := true  },
  { shape := .s4x8,   subCnt := 2, useL0 := true,  useL1 := true  },
  { shape := .s4x4,   subCnt := 4, useL0 := true,  useL1 := false },
  { shape := .s4x4,   subCnt := 4, useL0 := false, useL1 := true  },
  { shape := .s4x4,   subCnt := 4, useL0 := true,  useL1 := true  }
]

structure MbSyntax where
  isSkip         : Bool := false
  kind           : MbKind := .iNxN
  intraIdx       : Nat := 0
  interIdx       : Nat := 0
  transform8x8   : Nat := 0
  intraPred      : Array (Nat × Nat) := #[]
  chromaPredMode : Nat := 0
  subMbTypes     : Array Nat := #[]
  refL0          : Array Nat := #[]
  refL1          : Array Nat := #[]
  mvdL0          : Array (Int × Int) := #[]
  mvdL1          : Array (Int × Int) := #[]
  cbp            : Nat := 0
  mbQpDelta      : Int := 0
  pcmBytes       : ByteArray := ByteArray.empty
  i16Dc          : Array Int := Array.replicate 16 0
  lumaAcOr4x4    : Array (Array Int) := Array.replicate 16 (Array.replicate 16 0)
  luma8x8        : Array (Array Int) := Array.replicate 4 (Array.replicate 64 0)
  chromaDc       : Array (Array Int) := #[Array.replicate 4 0, Array.replicate 4 0]
  chromaAc       : Array (Array Int) := Array.replicate 8 (Array.replicate 15 0)
  deriving Inhabited

structure MbGridRecord where
  inSlice       : Bool := false
  isSkip        : Bool := false
  isIntra       : Bool := false
  isI16x16      : Bool := false
  isIpcm        : Bool := false
  isDirectMb    : Bool := false
  is8x8Dct      : Bool := false
  cbpLuma       : Nat := 0
  cbpChroma     : Nat := 0
  chromaPredMode : Nat := 0
  i16DcNz       : Nat := 0
  cdcNz         : Array Nat := #[0, 0]
  lumaNnzCavlc  : Array Nat := Array.replicate 16 0
  lumaCbfCabac  : Array Nat := Array.replicate 16 0
  chromaNnz     : Array (Array Nat) := #[Array.replicate 4 0, Array.replicate 4 0]
  refGrid       : Array (Array Int) := #[Array.replicate 16 (-1), Array.replicate 16 (-1)]
  directPart    : Array Bool := Array.replicate 16 false
  mvdGrid       : Array (Array (Int × Int)) := #[Array.replicate 16 (0, 0), Array.replicate 16 (0, 0)]
  deriving Repr, Inhabited

structure MbGrid where
  w   : Nat
  h   : Nat
  mbs : Array MbGridRecord
  deriving Inhabited

def MbGrid.init (w h : Nat) : MbGrid :=
  { w := w, h := h, mbs := Array.replicate (w * h) {} }

def MbGrid.getMb (g : MbGrid) (mx my : Nat) : Option MbGridRecord :=
  if mx < g.w && my < g.h then
    let r := g.mbs.getD (my * g.w + mx) {}
    if r.inSlice then some r else none
  else
    none

def MbGrid.leftMb (g : MbGrid) (mx my : Nat) : Option MbGridRecord :=
  if mx > 0 then g.getMb (mx - 1) my else none

def MbGrid.topMb (g : MbGrid) (mx my : Nat) : Option MbGridRecord :=
  if my > 0 then g.getMb mx (my - 1) else none

def MbGrid.setMb (g : MbGrid) (mx my : Nat) (r : MbGridRecord) : MbGrid :=
  let idx := my * g.w + mx
  if idx < g.mbs.size then { g with mbs := g.mbs.set! idx r } else g

def pcmByteCount (sps : SpsFull) : Nat :=
  let lumaBits := 256 * (8 + sps.bitDepthLumaMinus8)
  let chromaBits := if sps.chromaFormatIdc == 0 then 0 else 128 * (8 + sps.bitDepthChromaMinus8)
  (lumaBits + chromaBits) / 8

def cavlcLumaNC (g : MbGrid) (mx my : Nat) (curNnz : Array Nat) (blkIdx : Nat) : Nat :=
  let (bx, by0) := blk4XY.getD blkIdx (0, 0)
  let naOpt : Option Nat :=
    if bx > 0 then some (curNnz.getD (xyToBlk4 (bx - 1) by0) 0)
    else (g.leftMb mx my).map (fun mba => mba.lumaNnzCavlc.getD (xyToBlk4 3 by0) 0)
  let nbOpt : Option Nat :=
    if by0 > 0 then some (curNnz.getD (xyToBlk4 bx (by0 - 1)) 0)
    else (g.topMb mx my).map (fun mbb => mbb.lumaNnzCavlc.getD (xyToBlk4 bx 3) 0)
  match naOpt, nbOpt with
  | some na, some nb => (na + nb + 1) >>> 1
  | some na, none => na
  | none, some nb => nb
  | none, none => 0

def cavlcChromaNC (g : MbGrid) (mx my : Nat) (curCnnz : Array Nat) (plane cidx : Nat) : Nat :=
  let cx := cidx &&& 1
  let cy := (cidx >>> 1) &&& 1
  let naOpt : Option Nat :=
    if cx > 0 then some (curCnnz.getD (cy * 2 + (cx - 1)) 0)
    else (g.leftMb mx my).map (fun mba => (mba.chromaNnz.getD plane #[]).getD (cy * 2 + 1) 0)
  let nbOpt : Option Nat :=
    if cy > 0 then some (curCnnz.getD ((cy - 1) * 2 + cx) 0)
    else (g.topMb mx my).map (fun mbb => (mbb.chromaNnz.getD plane #[]).getD (2 + cx) 0)
  match naOpt, nbOpt with
  | some na, some nb => (na + nb + 1) >>> 1
  | some na, none => na
  | none, some nb => nb
  | none, none => 0

def cabacCbfCtx (g : MbGrid) (mx my : Nat) (isCurIntra : Bool) (cat : Nat)
    (curCbfLuma : Array Nat) (curCbfChroma : Array (Array Nat)) (idx : Nat) : Nat :=
  let baseCtx := (#[85, 89, 93, 97, 101, 1012]).getD cat 85
  let unavail := if isCurIntra then 1 else 0
  if cat == 0 then
    let ca := match g.leftMb mx my with
      | none => unavail
      | some mba => if mba.isIpcm || mba.i16DcNz != 0 then 1 else 0
    let cb := match g.topMb mx my with
      | none => unavail
      | some mbb => if mbb.isIpcm || mbb.i16DcNz != 0 then 1 else 0
    baseCtx + ca + 2 * cb
  else if cat == 3 then
    let ca := match g.leftMb mx my with
      | none => unavail
      | some mba => if mba.isIpcm || mba.cdcNz.getD idx 0 != 0 then 1 else 0
    let cb := match g.topMb mx my with
      | none => unavail
      | some mbb => if mbb.isIpcm || mbb.cdcNz.getD idx 0 != 0 then 1 else 0
    baseCtx + ca + 2 * cb
  else if cat == 1 || cat == 2 then
    let (bx, by0) := blk4XY.getD idx (0, 0)
    let ca :=
      if bx > 0 then curCbfLuma.getD (xyToBlk4 (bx - 1) by0) 0
      else match g.leftMb mx my with
        | none => unavail
        | some mba => mba.lumaCbfCabac.getD (xyToBlk4 3 by0) 0
    let cb :=
      if by0 > 0 then curCbfLuma.getD (xyToBlk4 bx (by0 - 1)) 0
      else match g.topMb mx my with
        | none => unavail
        | some mbb => mbb.lumaCbfCabac.getD (xyToBlk4 bx 3) 0
    baseCtx + ca + 2 * cb
  else
    let plane := idx / 4
    let cidx := idx % 4
    let cx := cidx &&& 1
    let cy := (cidx >>> 1) &&& 1
    let ca :=
      if cx > 0 then (if (curCbfChroma.getD plane #[]).getD (cy * 2 + (cx - 1)) 0 > 0 then 1 else 0)
      else match g.leftMb mx my with
        | none => unavail
        | some mba => if (mba.chromaNnz.getD plane #[]).getD (cy * 2 + 1) 0 > 0 then 1 else 0
    let cb :=
      if cy > 0 then (if (curCbfChroma.getD plane #[]).getD ((cy - 1) * 2 + cx) 0 > 0 then 1 else 0)
      else match g.topMb mx my with
        | none => unavail
        | some mbb => if (mbb.chromaNnz.getD plane #[]).getD (2 + cx) 0 > 0 then 1 else 0
    baseCtx + ca + 2 * cb

def fillRect4x4 {α : Type} (arr : Array α) (blk0 bw bh : Nat) (val : α) : Array α := Id.run do
  let (bx0, by0) := blk4XY.getD blk0 (0, 0)
  let mut out := arr
  for dy in [:bh] do
    for dx in [:bw] do
      let idx := xyToBlk4 (bx0 + dx) (by0 + dy)
      if idx < out.size then
        out := out.set! idx val
  return out

def subPartGeom (subShape : SubPartShape) (j : Nat) : Nat × Nat × Nat :=
  match subShape with
  | .s8x8 | .direct => (0, 2, 2)
  | .s8x4 => (2 * j, 2, 1)
  | .s4x8 => (j, 1, 2)
  | .s4x4 => (j, 1, 1)

def interDct8x8Allowed (pps : PpsFull) (sps : SpsFull) (mb : MbSyntax) : Bool :=
  if pps.transform8x8ModeFlag == 0 then false
  else match mb.kind with
  | .pInter =>
    if mb.interIdx == 3 || mb.interIdx == 4 then
      mb.subMbTypes.size == 4 && mb.subMbTypes.all (· == 0)
    else
      true
  | .bInter =>
    if mb.interIdx == 0 then sps.direct8x8InferenceFlag != 0
    else if mb.interIdx == 22 then
      mb.subMbTypes.size == 4 && mb.subMbTypes.all (fun st =>
        let info := bSubInfoTable.getD st {}
        info.shape == .s8x8 || (info.shape == .direct && sps.direct8x8InferenceFlag != 0))
    else
      true
  | _ => false

def applyMbHeaderToRecord (mb : MbSyntax) (r0 : MbGridRecord) : MbGridRecord :=
  let r1 := { r0 with inSlice := true }
  if mb.isSkip then
    { r1 with isSkip := true, isDirectMb := true, directPart := Array.replicate 16 true }
  else if mb.kind.isIntra then
    let r2 := { r1 with
      isIntra := true
      isI16x16 := mb.kind == MbKind.i16x16
      isIpcm := mb.kind == MbKind.iPcm
      is8x8Dct := mb.transform8x8 != 0
      chromaPredMode := mb.chromaPredMode
    }
    if mb.kind == .iPcm then
      { r2 with
        cbpLuma := 0xF
        cbpChroma := 2
        lumaNnzCavlc := Array.replicate 16 16
        lumaCbfCabac := Array.replicate 16 1
        chromaNnz := #[Array.replicate 4 16, Array.replicate 4 16]
        i16DcNz := 1
        cdcNz := #[1, 1]
      }
    else
      { r2 with cbpLuma := mb.cbp &&& 0xF, cbpChroma := (mb.cbp >>> 4) &&& 0x3 }
  else
    let isDir := mb.kind == .bInter && mb.interIdx == 0
    { r1 with
      is8x8Dct := mb.transform8x8 != 0
      isDirectMb := isDir
      directPart := if isDir then Array.replicate 16 true else r1.directPart
      cbpLuma := mb.cbp &&& 0xF
      cbpChroma := (mb.cbp >>> 4) &&& 0x3
    }

def populateInterMotionGrid (mb : MbSyntax) (r0 : MbGridRecord) : MbGridRecord := Id.run do
  let (info, numLists) :=
    if mb.kind == .pInter then (pMbInfoTable.getD mb.interIdx {}, 1)
    else if mb.kind == .bInter then (bMbInfoTable.getD mb.interIdx {}, 2)
    else ({}, 0)
  if numLists == 0 then return r0
  if info.shape == .direct then
    return { r0 with directPart := Array.replicate 16 true }
  let refsSrc := #[mb.refL0, mb.refL1]
  let mvdsSrc := #[mb.mvdL0, mb.mvdL1]
  let useLists := #[info.useL0, info.useL1]
  let mut refG := r0.refGrid
  let mut dirP := r0.directPart
  let mut mvdG := r0.mvdGrid
  if info.shape == .p8x8 then
    for lst in [:numLists] do
      let mut rc := 0
      let mut mc := 0
      for i in [:4] do
        let st := mb.subMbTypes.getD i 0
        let sub := if mb.kind == .pInter then pSubInfoTable.getD st {} else bSubInfoTable.getD st {}
        if sub.shape == .direct then
          dirP := fillRect4x4 dirP (4 * i) 2 2 true
        else
          let sUse := if lst == 0 then sub.useL0 else sub.useL1
          if sUse then
            let rv : Int := if mb.kind == .pInter && mb.interIdx == 4 then 0
              else Int.ofNat ((refsSrc.getD lst #[]).getD rc 0)
            if !(mb.kind == .pInter && mb.interIdx == 4) then rc := rc + 1
            refG := refG.set! lst (fillRect4x4 (refG.getD lst #[]) (4 * i) 2 2 rv)
            for j in [:sub.subCnt] do
              let (off, bw, bh) := subPartGeom sub.shape j
              let mv := (mvdsSrc.getD lst #[]).getD mc (0, 0)
              mc := mc + 1
              mvdG := mvdG.set! lst (fillRect4x4 (mvdG.getD lst #[]) (4 * i + off) bw bh mv)
  else
    let nPart := info.useL0.size
    for lst in [:numLists] do
      let mut rc := 0
      let mut mc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (blk0, bw, bh) :=
            if info.shape == .p16x16 then (0, 4, 4)
            else if info.shape == .p16x8 then (8 * pi, 4, 2)
            else (4 * pi, 2, 4)
          let rv := Int.ofNat ((refsSrc.getD lst #[]).getD rc 0)
          let mv := (mvdsSrc.getD lst #[]).getD mc (0, 0)
          rc := rc + 1
          mc := mc + 1
          refG := refG.set! lst (fillRect4x4 (refG.getD lst #[]) blk0 bw bh rv)
          mvdG := mvdG.set! lst (fillRect4x4 (mvdG.getD lst #[]) blk0 bw bh mv)
  return { r0 with refGrid := refG, directPart := dirP, mvdGrid := mvdG }

private def countNonZeroPrefix (arr : Array Int) (limit : Nat) : Nat := Id.run do
  let mut cnt := 0
  for i in [:Nat.min limit arr.size] do
    if arr.getD i 0 != 0 then cnt := cnt + 1
  return cnt

def populateResidualGrid (mb : MbSyntax) (r0 : MbGridRecord) (hasChroma : Bool) : MbGridRecord := Id.run do
  if mb.isSkip || mb.kind == .iPcm then return r0
  let mut i16Nz := r0.i16DcNz
  let mut cdcNz := r0.cdcNz
  let mut lNnz := r0.lumaNnzCavlc
  let mut lCbf := r0.lumaCbfCabac
  let mut cNnz := r0.chromaNnz
  if mb.kind == .i16x16 then
    i16Nz := if countNonZeroPrefix mb.i16Dc 16 > 0 then 1 else 0
    if (mb.cbp &&& 0xF) != 0 then
      for idx in [:16] do
        let tc := countNonZeroPrefix (mb.lumaAcOr4x4.getD idx #[]) 15
        lNnz := lNnz.set! idx tc
        lCbf := lCbf.set! idx (if tc > 0 then 1 else 0)
  else
    for i8 in [:4] do
      if (mb.cbp &&& (1 <<< i8)) != 0 then
        if mb.transform8x8 != 0 then
          let c8 := mb.luma8x8.getD i8 #[]
          let mut tot := 0
          for sub in [:4] do
            let mut stc := 0
            for k in [:16] do
              if c8.getD (4 * k + sub) 0 != 0 then stc := stc + 1
            lNnz := lNnz.set! (4 * i8 + sub) stc
            tot := tot + stc
          let cbf := if tot > 0 then 1 else 0
          for sub in [:4] do
            lCbf := lCbf.set! (4 * i8 + sub) cbf
        else
          for sub in [:4] do
            let idx := 4 * i8 + sub
            let tc := countNonZeroPrefix (mb.lumaAcOr4x4.getD idx #[]) 16
            lNnz := lNnz.set! idx tc
            lCbf := lCbf.set! idx (if tc > 0 then 1 else 0)
  if hasChroma && (mb.cbp &&& 0x30) != 0 then
    for pl in [:2] do
      cdcNz := cdcNz.set! pl (if countNonZeroPrefix (mb.chromaDc.getD pl #[]) 4 > 0 then 1 else 0)
    if (mb.cbp &&& 0x20) != 0 then
      for pl in [:2] do
        let mut pArr := cNnz.getD pl (Array.replicate 4 0)
        for ci in [:4] do
          let tc := countNonZeroPrefix (mb.chromaAc.getD (pl * 4 + ci) #[]) 15
          pArr := pArr.set! ci tc
        cNnz := cNnz.set! pl pArr
  return { r0 with
    i16DcNz := i16Nz
    cdcNz := cdcNz
    lumaNnzCavlc := lNnz
    lumaCbfCabac := lCbf
    chromaNnz := cNnz
  }

def buildCompleteMbRecord (mb : MbSyntax) (hasChroma : Bool) : MbGridRecord :=
  let r1 := applyMbHeaderToRecord mb {}
  let r2 := populateInterMotionGrid mb r1
  populateResidualGrid mb r2 hasChroma

def cavlcReadRef (r : BitReader) (refCount : Nat) : Option (Nat × BitReader) :=
  if refCount ≤ 1 then some (0, r)
  else if refCount == 2 then do
    let (b, r') ← readU1Nat r
    some (1 - b, r')
  else do
    let (v, r') ← readUENat r
    if v ≥ refCount then none else some (v, r')

def cavlcWriteRef (w : BitWriter) (refCount val : Nat) : Option BitWriter :=
  if refCount ≤ 1 then
    if val == 0 then some w else none
  else if refCount == 2 then
    if val > 1 then none else some (writeU1Nat w (1 - val))
  else
    if val ≥ refCount then none else some (writeUENat w val)

private def readIntraPredCavlcLoop (r : BitReader) :
    Nat → Array (Nat × Nat) → Option (Array (Nat × Nat) × BitReader)
  | 0, acc => some (acc, r)
  | k + 1, acc => do
    let (pf, r1) ← readU1Nat r
    let (rem, r2) ← if pf == 1 then pure (0, r1) else readUNat r1 3
    readIntraPredCavlcLoop r2 k (acc.push (pf, rem))

private def readUENatCountLoop (r : BitReader) (maxVal : Nat) :
    Nat → Array Nat → Option (Array Nat × BitReader)
  | 0, acc => some (acc, r)
  | k + 1, acc => do
    let (v, r1) ← readUENat r
    if v > maxVal then none else readUENatCountLoop r1 maxVal k (acc.push v)

private def readMvdPairsLoop (r : BitReader) :
    Nat → Array (Int × Int) → Option (Array (Int × Int) × BitReader)
  | 0, acc => some (acc, r)
  | k + 1, acc => do
    let (mxv, r1) ← readSEInt r
    let (myv, r2) ← readSEInt r1
    readMvdPairsLoop r2 k (acc.push (mxv, myv))

private def cavlcDecodeInterMotion (r0 : BitReader) (sh : SliceHeaderFull)
    (kind : MbKind) (interIdx : Nat) :
    Option (Array Nat × Array Nat × Array Nat × Array (Int × Int) × Array (Int × Int) × BitReader) := do
  let (info, numLists) :=
    if kind == .pInter then (pMbInfoTable.getD interIdx {}, 1)
    else (bMbInfoTable.getD interIdx {}, 2)
  let rcActive := #[if info.isRef0 then 1 else sh.numRefL0, if info.isRef0 then 1 else sh.numRefL1]
  let useLists := #[info.useL0, info.useL1]
  if info.shape == .direct then
    some (#[], #[], #[], #[], #[], r0)
  else if info.shape == .p8x8 then do
    let maxSub := if kind == .pInter then 3 else 12
    let (subs, r1) ← readUENatCountLoop r0 maxSub 4 #[]
    let mut rCur := r1
    let mut refs := #[#[], #[]]
    let mut mvds := #[#[], #[]]
    for lst in [:numLists] do
      let mut rArr : Array Nat := #[]
      for si in [:4] do
        let st := subs.getD si 0
        let sub := if kind == .pInter then pSubInfoTable.getD st {} else bSubInfoTable.getD st {}
        let sUse := if lst == 0 then sub.useL0 else sub.useL1
        if sub.shape != .direct && sUse then
          let (rv, rn) ← cavlcReadRef rCur (rcActive.getD lst 1)
          rCur := rn
          rArr := rArr.push rv
      refs := refs.set! lst rArr
    for lst in [:numLists] do
      let mut mArr : Array (Int × Int) := #[]
      for si in [:4] do
        let st := subs.getD si 0
        let sub := if kind == .pInter then pSubInfoTable.getD st {} else bSubInfoTable.getD st {}
        let sUse := if lst == 0 then sub.useL0 else sub.useL1
        if sub.shape != .direct && sUse then
          let (mNext, rn) ← readMvdPairsLoop rCur sub.subCnt mArr
          rCur := rn
          mArr := mNext
      mvds := mvds.set! lst mArr
    some (subs, refs.getD 0 #[], refs.getD 1 #[], mvds.getD 0 #[], mvds.getD 1 #[], rCur)
  else do
    let nPart := info.useL0.size
    let mut rCur := r0
    let mut refs := #[#[], #[]]
    let mut mvds := #[#[], #[]]
    for lst in [:numLists] do
      let mut rArr : Array Nat := #[]
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (rv, rn) ← cavlcReadRef rCur (rcActive.getD lst 1)
          rCur := rn
          rArr := rArr.push rv
      refs := refs.set! lst rArr
    for lst in [:numLists] do
      let mut mArr : Array (Int × Int) := #[]
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (mNext, rn) ← readMvdPairsLoop rCur 1 mArr
          rCur := rn
          mArr := mNext
      mvds := mvds.set! lst mArr
    some (#[], refs.getD 0 #[], refs.getD 1 #[], mvds.getD 0 #[], mvds.getD 1 #[], rCur)

private def cavlcDecodeResidualMb (r0 : BitReader) (g : MbGrid) (mx my : Nat)
    (hasChroma : Bool) (mb0 : MbSyntax) : Option (MbSyntax × BitReader) := do
  if mb0.cbp == 0 && mb0.kind != .i16x16 then
    some (mb0, r0)
  else do
    let (dqp, r1) ← readSEInt r0
    let mut rCur := r1
    let mut curNnz := Array.replicate 16 0
    let mut curCnnz := #[Array.replicate 4 0, Array.replicate 4 0]
    let mut i16Dc := mb0.i16Dc
    let mut luma4 := mb0.lumaAcOr4x4
    let mut luma8 := mb0.luma8x8
    let mut cdc := mb0.chromaDc
    let mut cac := mb0.chromaAc
    if mb0.kind == .i16x16 then
      let nc0 := cavlcLumaNC g mx my curNnz 0
      let (dcCoeffs, _, rn) ← cavlcDecodeBlock rCur 16 nc0
      i16Dc := dcCoeffs
      rCur := rn
      if (mb0.cbp &&& 0xF) != 0 then
        for idx in [:16] do
          let nc := cavlcLumaNC g mx my curNnz idx
          let (acCoeffs, tc, rn2) ← cavlcDecodeBlock rCur 15 nc
          rCur := rn2
          luma4 := luma4.set! idx (acCoeffs.push 0)
          curNnz := curNnz.set! idx tc
    else
      for i8 in [:4] do
        if (mb0.cbp &&& (1 <<< i8)) != 0 then
          if mb0.transform8x8 != 0 then
            let mut c8 := Array.replicate 64 (0 : Int)
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let nc := cavlcLumaNC g mx my curNnz idx
              let (coeffs, tc, rn2) ← cavlcDecodeBlock rCur 16 nc
              rCur := rn2
              curNnz := curNnz.set! idx tc
              for k in [:16] do
                c8 := c8.set! (4 * k + sub) (coeffs.getD k 0)
            luma8 := luma8.set! i8 c8
          else
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let nc := cavlcLumaNC g mx my curNnz idx
              let (coeffs, tc, rn2) ← cavlcDecodeBlock rCur 16 nc
              rCur := rn2
              luma4 := luma4.set! idx coeffs
              curNnz := curNnz.set! idx tc
    if hasChroma && (mb0.cbp &&& 0x30) != 0 then
      for pl in [:2] do
        let (dcCoeffs, _, rn2) ← cavlcDecodeBlock rCur 4 0
        rCur := rn2
        cdc := cdc.set! pl dcCoeffs
      if (mb0.cbp &&& 0x20) != 0 then
        for pl in [:2] do
          let mut pNnz := curCnnz.getD pl (Array.replicate 4 0)
          for ci in [:4] do
            let nc := cavlcChromaNC g mx my pNnz pl ci
            let (coeffs, tc, rn2) ← cavlcDecodeBlock rCur 15 nc
            rCur := rn2
            cac := cac.set! (pl * 4 + ci) coeffs
            pNnz := pNnz.set! ci tc
          curCnnz := curCnnz.set! pl pNnz
    some ({ mb0 with
      mbQpDelta := dqp, i16Dc := i16Dc, lumaAcOr4x4 := luma4,
      luma8x8 := luma8, chromaDc := cdc, chromaAc := cac
    }, rCur)

private def cavlcDecodeNonSkipMb (r0 : BitReader) (sh : SliceHeaderFull) (sps : SpsFull)
    (pps : PpsFull) (g : MbGrid) (mx my : Nat) : Option (MbSyntax × BitReader) := do
  let hasChroma := sps.chromaFormatIdc == 1
  let (rawMbt, r1) ← readUENat r0
  let (isIntra, intraMbt, interKind, interIdx) ←
    if sh.sliceTypeNos == 2 then
      if rawMbt > 25 then none else pure (true, rawMbt, MbKind.iNxN, 0)
    else if sh.sliceTypeNos == 0 then
      if rawMbt < 5 then pure (false, 0, MbKind.pInter, rawMbt)
      else if rawMbt - 5 > 25 then none
      else pure (true, rawMbt - 5, MbKind.iNxN, 0)
    else
      if rawMbt < 23 then pure (false, 0, MbKind.bInter, rawMbt)
      else if rawMbt - 23 > 25 then none
      else pure (true, rawMbt - 23, MbKind.iNxN, 0)
  if isIntra then
    if intraMbt == 25 then do
      let nb := pcmByteCount sps
      let (pcm, r2) ← readBytesAlignedLoop r1.alignToByte nb (Array.emptyWithCapacity nb)
      some ({ kind := .iPcm, intraIdx := 25, pcmBytes := pcm }, r2)
    else do
      let kind : MbKind := if intraMbt == 0 then .iNxN else .i16x16
      let cbpInit :=
        if kind == .i16x16 then
          let t := intraMbt - 1
          (if t ≥ 12 then 15 else 0) ||| (((t / 4) % 3) <<< 4)
        else 0
      let (t8, preds, r2) ←
        if kind == .iNxN then do
          let (t8v, ra) ← if pps.transform8x8ModeFlag != 0 then readU1Nat r1 else pure (0, r1)
          let nModes := if t8v != 0 then 4 else 16
          let (ps, rb) ← readIntraPredCavlcLoop ra nModes #[]
          pure (t8v, ps, rb)
        else pure (0, #[], r1)
      let (cMode, r3) ← if hasChroma then readUENat r2 else pure (0, r2)
      if cMode > 3 then none
      else do
        let (cbpVal, r4) ←
          if kind == .i16x16 then
            if !hasChroma && cbpInit > 15 then none else pure (cbpInit, r3)
          else do
            let (code, ra) ← readUENat r3
            let tab := if hasChroma then cavlcCbpIntraDec else cavlcCbpIntraGrayDec
            if code ≥ tab.size then none else pure (tab.getD code 0, ra)
        if !hasChroma && cbpVal > 15 then none
        else
          let mb0 : MbSyntax := {
            kind := kind, intraIdx := intraMbt, transform8x8 := t8,
            intraPred := preds, chromaPredMode := cMode, cbp := cbpVal
          }
          cavlcDecodeResidualMb r4 g mx my hasChroma mb0
  else do
    let (subs, rl0, rl1, ml0, ml1, r2) ← cavlcDecodeInterMotion r1 sh interKind interIdx
    let (code, r3) ← readUENat r2
    let tab := if hasChroma then cavlcCbpInterDec else cavlcCbpInterGrayDec
    if code ≥ tab.size then none
    else do
      let cbpVal := tab.getD code 0
      let mbBase : MbSyntax := {
        kind := interKind, interIdx := interIdx, subMbTypes := subs,
        refL0 := rl0, refL1 := rl1, mvdL0 := ml0, mvdL1 := ml1, cbp := cbpVal
      }
      let (t8, r4) ←
        if (cbpVal &&& 0xF) != 0 && interDct8x8Allowed pps sps mbBase then readU1Nat r3
        else pure (0, r3)
      cavlcDecodeResidualMb r4 g mx my hasChroma { mbBase with transform8x8 := t8 }

private def decodeSliceCavlcLoop (sh : SliceHeaderFull) (sps : SpsFull) (pps : PpsFull)
    (rbspEnd totalMbs : Nat) :
    Nat → Nat → BitReader → MbGrid → Option Nat → Array MbSyntax → Option (Array MbSyntax)
  | 0, _, _, _, _, acc => some acc
  | fuel + 1, mbIdx, r, g, skipOpt, acc =>
    if mbIdx ≥ totalMbs then some acc
    else
      let mx := mbIdx % sps.picWidthInMbs
      let my := mbIdx / sps.picWidthInMbs
      let hasChroma := sps.chromaFormatIdc == 1
      if sh.sliceTypeNos != 2 then
        match skipOpt with
        | some (k + 1) =>
          let mb : MbSyntax := { isSkip := true, kind := .skip }
          let g' := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
          decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs fuel (mbIdx + 1) r g' (some k) (acc.push mb)
        | some 0 =>
          if !moreRbspData r rbspEnd then some acc
          else do
            let (mb, r') ← cavlcDecodeNonSkipMb r sh sps pps g mx my
            let g' := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
            decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs fuel (mbIdx + 1) r' g' none (acc.push mb)
        | none =>
          if !moreRbspData r rbspEnd then some acc
          else do
            let (srun, r1) ← readUENat r
            if srun > totalMbs - mbIdx then none
            else if srun > 0 then
              let mb : MbSyntax := { isSkip := true, kind := .skip }
              let g' := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
              decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs fuel (mbIdx + 1) r1 g' (some (srun - 1)) (acc.push mb)
            else if !moreRbspData r1 rbspEnd then
              some acc
            else do
              let (mb, r2) ← cavlcDecodeNonSkipMb r1 sh sps pps g mx my
              let g' := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
              decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs fuel (mbIdx + 1) r2 g' none (acc.push mb)
      else
        if acc.size > 0 && !moreRbspData r rbspEnd then some acc
        else do
          let (mb, r') ← cavlcDecodeNonSkipMb r sh sps pps g mx my
          let g' := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
          decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs fuel (mbIdx + 1) r' g' none (acc.push mb)

def decodeSliceCavlc (rbsp : ByteArray) (sh : SliceHeaderFull) (bitStart : Nat)
    (sps : SpsFull) (pps : PpsFull) : Option (Array MbSyntax) :=
  let totalMbs := sps.picWidthInMbs * sps.picHeightInMapUnits
  if sh.firstMbInSlice ≥ totalMbs then none
  else
    let r0 : BitReader := { slice := ByteSlice.ofByteArray rbsp, bitOffset := bitStart }
    let rbspEnd := rbspEndBitPos rbsp
    let g0 := MbGrid.init sps.picWidthInMbs sps.picHeightInMapUnits
    decodeSliceCavlcLoop sh sps pps rbspEnd totalMbs (totalMbs - sh.firstMbInSlice) sh.firstMbInSlice r0 g0 none #[]

private def cavlcEncodeInterMotion (w0 : BitWriter) (sh : SliceHeaderFull) (mb : MbSyntax) :
    Option BitWriter := do
  let (info, numLists) :=
    if mb.kind == .pInter then (pMbInfoTable.getD mb.interIdx {}, 1)
    else (bMbInfoTable.getD mb.interIdx {}, 2)
  let rcActive := #[if info.isRef0 then 1 else sh.numRefL0, if info.isRef0 then 1 else sh.numRefL1]
  let refsSrc := #[mb.refL0, mb.refL1]
  let mvdsSrc := #[mb.mvdL0, mb.mvdL1]
  let useLists := #[info.useL0, info.useL1]
  if info.shape == .direct then some w0
  else if info.shape == .p8x8 then do
    if mb.subMbTypes.size != 4 then none
    else do
      let mut wCur := w0
      for si in [:4] do
        wCur := writeUENat wCur (mb.subMbTypes.getD si 0)
      for lst in [:numLists] do
        let mut rc := 0
        for si in [:4] do
          let st := mb.subMbTypes.getD si 0
          let sub := if mb.kind == .pInter then pSubInfoTable.getD st {} else bSubInfoTable.getD st {}
          if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
            let rv := if info.isRef0 then 0 else (refsSrc.getD lst #[]).getD rc 0
            if !info.isRef0 then rc := rc + 1
            wCur ← cavlcWriteRef wCur (rcActive.getD lst 1) rv
      for lst in [:numLists] do
        let mut mc := 0
        for si in [:4] do
          let st := mb.subMbTypes.getD si 0
          let sub := if mb.kind == .pInter then pSubInfoTable.getD st {} else bSubInfoTable.getD st {}
          if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
            for _ in [:sub.subCnt] do
              let (mvx, mvy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
              mc := mc + 1
              wCur := writeSEInt (writeSEInt wCur mvx) mvy
      some wCur
  else do
    let nPart := info.useL0.size
    let mut wCur := w0
    for lst in [:numLists] do
      let mut rc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let rv := (refsSrc.getD lst #[]).getD rc 0
          rc := rc + 1
          wCur ← cavlcWriteRef wCur (rcActive.getD lst 1) rv
    for lst in [:numLists] do
      let mut mc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (mvx, mvy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
          mc := mc + 1
          wCur := writeSEInt (writeSEInt wCur mvx) mvy
    some wCur

private def cavlcEncodeResidualMb (w0 : BitWriter) (g : MbGrid) (mx my : Nat)
    (hasChroma : Bool) (mb : MbSyntax) : Option BitWriter := do
  if mb.cbp == 0 && mb.kind != .i16x16 then
    some w0
  else do
    let mut wCur := writeSEInt w0 mb.mbQpDelta
    let mut curNnz := Array.replicate 16 0
    let mut curCnnz := #[Array.replicate 4 0, Array.replicate 4 0]
    if mb.kind == .i16x16 then
      let nc0 := cavlcLumaNC g mx my curNnz 0
      let (wNext, _) ← cavlcEncodeBlock wCur mb.i16Dc 16 nc0
      wCur := wNext
      if (mb.cbp &&& 0xF) != 0 then
        for idx in [:16] do
          let nc := cavlcLumaNC g mx my curNnz idx
          let acArr := (mb.lumaAcOr4x4.getD idx #[]).extract 0 15
          let (wNext2, tc) ← cavlcEncodeBlock wCur acArr 15 nc
          wCur := wNext2
          curNnz := curNnz.set! idx tc
    else
      for i8 in [:4] do
        if (mb.cbp &&& (1 <<< i8)) != 0 then
          if mb.transform8x8 != 0 then
            let c8 := mb.luma8x8.getD i8 #[]
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let mut coeffs : Array Int := Array.emptyWithCapacity 16
              for k in [:16] do
                coeffs := coeffs.push (c8.getD (4 * k + sub) 0)
              let nc := cavlcLumaNC g mx my curNnz idx
              let (wNext2, tc) ← cavlcEncodeBlock wCur coeffs 16 nc
              wCur := wNext2
              curNnz := curNnz.set! idx tc
          else
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let nc := cavlcLumaNC g mx my curNnz idx
              let (wNext2, tc) ← cavlcEncodeBlock wCur (mb.lumaAcOr4x4.getD idx #[]) 16 nc
              wCur := wNext2
              curNnz := curNnz.set! idx tc
    if hasChroma && (mb.cbp &&& 0x30) != 0 then
      for pl in [:2] do
        let (wNext2, _) ← cavlcEncodeBlock wCur (mb.chromaDc.getD pl #[]) 4 0
        wCur := wNext2
      if (mb.cbp &&& 0x20) != 0 then
        for pl in [:2] do
          let mut pNnz := curCnnz.getD pl (Array.replicate 4 0)
          for ci in [:4] do
            let nc := cavlcChromaNC g mx my pNnz pl ci
            let (wNext2, tc) ← cavlcEncodeBlock wCur (mb.chromaAc.getD (pl * 4 + ci) #[]) 15 nc
            wCur := wNext2
            pNnz := pNnz.set! ci tc
          curCnnz := curCnnz.set! pl pNnz
    some wCur

private def cavlcEncodeNonSkipMb (w0 : BitWriter) (sh : SliceHeaderFull) (sps : SpsFull)
    (pps : PpsFull) (g : MbGrid) (mx my : Nat) (mb : MbSyntax) : Option BitWriter := do
  let hasChroma := sps.chromaFormatIdc == 1
  if mb.kind.isIntra then
    let off := if sh.sliceTypeNos == 2 then 0 else if sh.sliceTypeNos == 0 then 5 else 23
    let w1 := writeUENat w0 (mb.intraIdx + off)
    if mb.kind == .iPcm then
      some (writeBytesAligned w1 mb.pcmBytes)
    else do
      let mut wCur := w1
      if mb.kind == .iNxN then
        if pps.transform8x8ModeFlag != 0 then
          wCur := writeU1Nat wCur mb.transform8x8
        for idx in [:mb.intraPred.size] do
          let (pf, rem) := mb.intraPred.getD idx (0, 0)
          wCur := writeU1Nat wCur pf
          if pf == 0 then wCur := writeUNat wCur rem 3
      if hasChroma then
        wCur := writeUENat wCur mb.chromaPredMode
      if mb.kind != .i16x16 then
        let tab := if hasChroma then cavlcCbpIntraDec else cavlcCbpIntraGrayDec
        let cbpCode ← cavlcLookupCbpCode tab mb.cbp
        wCur := writeUENat wCur cbpCode
      cavlcEncodeResidualMb wCur g mx my hasChroma mb
  else do
    let w1 := writeUENat w0 mb.interIdx
    let w2 ← cavlcEncodeInterMotion w1 sh mb
    let tab := if hasChroma then cavlcCbpInterDec else cavlcCbpInterGrayDec
    let cbpCode ← cavlcLookupCbpCode tab mb.cbp
    let w3 := writeUENat w2 cbpCode
    let w4 :=
      if (mb.cbp &&& 0xF) != 0 && interDct8x8Allowed pps sps mb then writeU1Nat w3 mb.transform8x8
      else w3
    cavlcEncodeResidualMb w4 g mx my hasChroma mb

private def countSkipRunFrom (mbs : Array MbSyntax) (idx : Nat) : Nat → Nat → Nat
  | 0, run => run
  | fuel + 1, run =>
    if idx + run < mbs.size && (mbs.getD (idx + run) {}).isSkip then
      countSkipRunFrom mbs idx fuel (run + 1)
    else run

private def encodeSliceCavlcLoop (sh : SliceHeaderFull) (sps : SpsFull) (pps : PpsFull)
    (mbs : Array MbSyntax) :
    Nat → Nat → Nat → BitWriter → MbGrid → Option BitWriter
  | 0, _, _, w, _ => some w
  | fuel + 1, i, mbIdx, w, g =>
    if i ≥ mbs.size then some w
    else
      let hasChroma := sps.chromaFormatIdc == 1
      if sh.sliceTypeNos != 2 then
        let run := countSkipRunFrom mbs i (mbs.size - i) 0
        let w1 := writeUENat w run
        let g1 := Id.run do
          let mut gCur := g
          for k in [:run] do
            let curMbIdx := mbIdx + k
            let mxk := curMbIdx % sps.picWidthInMbs
            let myk := curMbIdx / sps.picWidthInMbs
            let mbSkip := mbs.getD (i + k) { isSkip := true, kind := .skip }
            gCur := gCur.setMb mxk myk (buildCompleteMbRecord mbSkip hasChroma)
          return gCur
        let iNext := i + run
        let mbIdxNext := mbIdx + run
        if iNext ≥ mbs.size then some w1
        else do
          let mb := mbs.getD iNext {}
          let mx := mbIdxNext % sps.picWidthInMbs
          let my := mbIdxNext / sps.picWidthInMbs
          let w2 ← cavlcEncodeNonSkipMb w1 sh sps pps g1 mx my mb
          let g2 := g1.setMb mx my (buildCompleteMbRecord mb hasChroma)
          encodeSliceCavlcLoop sh sps pps mbs fuel (iNext + 1) (mbIdxNext + 1) w2 g2
      else do
        let mb := mbs.getD i {}
        let mx := mbIdx % sps.picWidthInMbs
        let my := mbIdx / sps.picWidthInMbs
        let w1 ← cavlcEncodeNonSkipMb w sh sps pps g mx my mb
        let g1 := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
        encodeSliceCavlcLoop sh sps pps mbs fuel (i + 1) (mbIdx + 1) w1 g1

def encodeSliceCavlc (sh : SliceHeaderFull) (mbs : Array MbSyntax)
    (sps : SpsFull) (pps : PpsFull) : Option ByteArray := do
  let w0 := writeSliceHeaderFull BitWriter.empty sh false
  let g0 := MbGrid.init sps.picWidthInMbs sps.picHeightInMapUnits
  let wEnd ← encodeSliceCavlcLoop sh sps pps mbs (mbs.size + 1) 0 sh.firstMbInSlice w0 g0
  some (writerToNal (writeRbspTrailing wEnd))

def cabacSigBase : Array Nat := #[105, 120, 134, 149, 152, 402]
def cabacLastBase : Array Nat := #[166, 181, 195, 210, 213, 417]
def cabacLevelBase : Array Nat := #[227, 237, 247, 257, 266, 426]
def cabacLvl1Ctx : Array Nat := #[1, 2, 3, 4, 0, 0, 0, 0]
def cabacLvlGt1Ctx : Array Nat := #[5, 5, 5, 5, 6, 7, 8, 9]
def cabacLvlTr0 : Array Nat := #[1, 2, 3, 3, 4, 5, 6, 7]
def cabacLvlTr1 : Array Nat := #[4, 4, 4, 4, 5, 6, 7, 7]

private def cabacDecSigLastLoop (maxCoeff sigB lastB : Nat) :
    Nat → Nat → CabacDec → Array UInt8 → Array Nat → Array Nat × CabacDec × Array UInt8
  | 0, _, dec, st, acc => (acc.push (maxCoeff - 1), dec, st)
  | rem + 1, k, dec, st, acc =>
    let so := if maxCoeff == 64 then cabacSig8x8Frame.getD k 0 else k
    let lo := if maxCoeff == 64 then cabacLast8x8.getD k 0 else k
    let (sig, dec1, st1) := dec.decodeDecision st (sigB + so)
    if sig == 1 then
      let acc1 := acc.push k
      let (last, dec2, st2) := dec1.decodeDecision st1 (lastB + lo)
      if last == 1 then (acc1, dec2, st2)
      else cabacDecSigLastLoop maxCoeff sigB lastB rem (k + 1) dec2 st2 acc1
    else
      cabacDecSigLastLoop maxCoeff sigB lastB rem (k + 1) dec1 st1 acc

private def cabacDecBypassUnary : Nat → CabacDec → Nat → Option (Nat × CabacDec)
  | 0, _, _ => none
  | fuel + 1, dec, cnt =>
    let (b, dec1) := dec.decodeBypass
    if b == 1 then cabacDecBypassUnary fuel dec1 (cnt + 1)
    else some (cnt, dec1)

private def cabacDecBypassBits : Nat → CabacDec → Nat → Nat × CabacDec
  | 0, dec, acc => (acc, dec)
  | k + 1, dec, acc =>
    let (b, dec1) := dec.decodeBypass
    cabacDecBypassBits k dec1 ((acc <<< 1) ||| b)

private def cabacDecGt1Loop (gctx : Nat) :
    Nat → CabacDec → Array UInt8 → Nat → Nat × CabacDec × Array UInt8
  | 0, dec, st, absC => (absC, dec, st)
  | rem + 1, dec, st, absC =>
    let (b, dec1, st1) := dec.decodeDecision st gctx
    if b == 1 then cabacDecGt1Loop gctx rem dec1 st1 (absC + 1)
    else (absC, dec1, st1)

def cabacDecodeResidualBlock (dec0 : CabacDec) (st0 : Array UInt8) (cat maxCoeff : Nat)
    (cbfCtx : Option Nat) : Option (Array Int × Nat × CabacDec × Array UInt8) := do
  let (hasNz, dec1, st1) :=
    match cbfCtx with
    | none => (true, dec0, st0)
    | some cctx =>
      let (b, d', s') := dec0.decodeDecision st0 cctx
      (b == 1, d', s')
  if !hasNz then
    some (Array.replicate maxCoeff 0, 0, dec1, st1)
  else do
    let sigB := cabacSigBase.getD cat 105
    let lastB := cabacLastBase.getD cat 166
    let lvlB := cabacLevelBase.getD cat 227
    let (nzPos, dec2, st2) :=
      if maxCoeff ≤ 1 then (#[0], dec1, st1)
      else cabacDecSigLastLoop maxCoeff sigB lastB (maxCoeff - 1) 0 dec1 st1 #[]
    let mut coeffs := Array.replicate maxCoeff (0 : Int)
    let mut decCur := dec2
    let mut stCur := st2
    let mut node := 0
    for step in [:nzPos.size] do
      let pos := nzPos.getD (nzPos.size - 1 - step) 0
      let (gt1, dA, sA) := decCur.decodeDecision stCur (lvlB + cabacLvl1Ctx.getD node 0)
      let (absC, dB, sB) ←
        if gt1 == 0 then
          node := cabacLvlTr0.getD node 0
          pure (1, dA, sA)
        else do
          let gctx := lvlB + cabacLvlGt1Ctx.getD node 5
          node := cabacLvlTr1.getD node 4
          let (abs0, dG, sG) := cabacDecGt1Loop gctx 13 dA sA 2
          if abs0 == 15 then
            let (j, dU) ← cabacDecBypassUnary 32 dG 0
            let (suf, dS) := cabacDecBypassBits j dU 0
            pure (15 + ((1 <<< j) - 1) + suf, dS, sG)
          else
            pure (abs0, dG, sG)
      let (sgn, dC) := dB.decodeBypass
      decCur := dC
      stCur := sB
      let val : Int := if sgn == 1 then -Int.ofNat absC else Int.ofNat absC
      if pos < coeffs.size then coeffs := coeffs.set! pos val
    some (coeffs, 1, decCur, stCur)

private def cabacEncBypassExpGolomb :
    Nat → CabacEnc → Nat → Nat → Option CabacEnc
  | 0, _, _, _ => none
  | fuel + 1, enc, rem, j =>
    let span := 1 <<< j
    if rem ≥ span then
      cabacEncBypassExpGolomb fuel (enc.encodeBypass 1) (rem - span) (j + 1)
    else
      let e0 := enc.encodeBypass 0
      let eDone := Id.run do
        let mut eCur := e0
        for step in [:j] do
          let bitI := j - 1 - step
          eCur := eCur.encodeBypass ((rem >>> bitI) &&& 1)
        return eCur
      some eDone

def cabacEncodeResidualBlock (enc0 : CabacEnc) (st0 : Array UInt8) (coeffs : Array Int)
    (cat maxCoeff : Nat) (cbfCtx : Option Nat) : Option (Nat × CabacEnc × Array UInt8) := do
  let nz := Id.run do
    let mut acc : Array (Nat × Int) := #[]
    for k in [:Nat.min maxCoeff coeffs.size] do
      let c := coeffs.getD k 0
      if c != 0 then acc := acc.push (k, c)
    return acc
  match cbfCtx with
  | some cctx =>
    if nz.size == 0 then
      let (e1, s1) := enc0.encodeDecision st0 cctx 0
      return (0, e1, s1)
  | none =>
    if nz.size == 0 then none else pure ()
  let (enc1, st1) :=
    match cbfCtx with
    | some cctx => enc0.encodeDecision st0 cctx 1
    | none => (enc0, st0)
  let sigB := cabacSigBase.getD cat 105
  let lastB := cabacLastBase.getD cat 166
  let lvlB := cabacLevelBase.getD cat 227
  let lastPos := (nz.getD (nz.size - 1) (0, 0)).1
  let mut encCur := enc1
  let mut stCur := st1
  let mut nzCursor := 0
  if maxCoeff > 1 then
    for k in [:maxCoeff - 1] do
      if nzCursor < nz.size then
        let so := if maxCoeff == 64 then cabacSig8x8Frame.getD k 0 else k
        let lo := if maxCoeff == 64 then cabacLast8x8.getD k 0 else k
        let nextPos := (nz.getD nzCursor (maxCoeff, 0)).1
        if k == nextPos then
          nzCursor := nzCursor + 1
          let (eA, sA) := encCur.encodeDecision stCur (sigB + so) 1
          if k == lastPos then
            let (eB, sB) := eA.encodeDecision sA (lastB + lo) 1
            encCur := eB
            stCur := sB
            break
          else
            let (eB, sB) := eA.encodeDecision sA (lastB + lo) 0
            encCur := eB
            stCur := sB
        else
          let (eA, sA) := encCur.encodeDecision stCur (sigB + so) 0
          encCur := eA
          stCur := sA
  let mut node := 0
  for step in [:nz.size] do
    let val := (nz.getD (nz.size - 1 - step) (0, 0)).2
    let absC := val.natAbs
    if absC == 1 then
      let (eA, sA) := encCur.encodeDecision stCur (lvlB + cabacLvl1Ctx.getD node 0) 0
      encCur := eA
      stCur := sA
      node := cabacLvlTr0.getD node 0
    else
      let (eA, sA) := encCur.encodeDecision stCur (lvlB + cabacLvl1Ctx.getD node 0) 1
      let gctx := lvlB + cabacLvlGt1Ctx.getD node 5
      node := cabacLvlTr1.getD node 4
      let uOnes := Nat.min (absC - 2) 13
      let mut eG := eA
      let mut sG := sA
      for _ in [:uOnes] do
        let (en, sn) := eG.encodeDecision sG gctx 1
        eG := en
        sG := sn
      if absC < 15 then
        let (en, sn) := eG.encodeDecision sG gctx 0
        encCur := en
        stCur := sn
      else
        let eExp ← cabacEncBypassExpGolomb 32 eG (absC - 15) 0
        encCur := eExp
        stCur := sG
    encCur := encCur.encodeBypass (if val < 0 then 1 else 0)
  some (1, encCur, stCur)

def cabacDecodeIntraMbType (dec0 : CabacDec) (st0 : Array UInt8) (ctxBase : Nat)
    (intraSlice : Bool) (leftRec topRec : Option MbGridRecord) :
    Nat × CabacDec × Array UInt8 :=
  if intraSlice then
    let cL := match leftRec with | some r => if r.isI16x16 || r.isIpcm then 1 else 0 | none => 0
    let cT := match topRec with | some r => if r.isI16x16 || r.isIpcm then 1 else 0 | none => 0
    let (b0, d1, s1) := dec0.decodeDecision st0 (ctxBase + cL + cT)
    if b0 == 0 then (0, d1, s1)
    else
      let (term, d2) := d1.decodeTerminate
      if term == 1 then (25, d2, s1)
      else
        let b := ctxBase + 2
        let (c1, d3, s3) := d2.decodeDecision s1 (b + 1)
        let (c2, d4, s4) := d3.decodeDecision s3 (b + 2)
        let (ccAdd, d5, s5) :=
          if c2 == 1 then
            let (c3, da, sa) := d4.decodeDecision s4 (b + 3)
            (4 + 4 * c3, da, sa)
          else (0, d4, s4)
        let (p1, d6, s6) := d5.decodeDecision s5 (b + 4)
        let (p0, d7, s7) := d6.decodeDecision s6 (b + 5)
        (1 + 12 * c1 + ccAdd + 2 * p1 + p0, d7, s7)
  else
    let (b0, d1, s1) := dec0.decodeDecision st0 ctxBase
    if b0 == 0 then (0, d1, s1)
    else
      let (term, d2) := d1.decodeTerminate
      if term == 1 then (25, d2, s1)
      else
        let (c1, d3, s3) := d2.decodeDecision s1 (ctxBase + 1)
        let (c2, d4, s4) := d3.decodeDecision s3 (ctxBase + 2)
        let (ccAdd, d5, s5) :=
          if c2 == 1 then
            let (c3, da, sa) := d4.decodeDecision s4 (ctxBase + 2)
            (4 + 4 * c3, da, sa)
          else (0, d4, s4)
        let (p1, d6, s6) := d5.decodeDecision s5 (ctxBase + 3)
        let (p0, d7, s7) := d6.decodeDecision s6 (ctxBase + 3)
        (1 + 12 * c1 + ccAdd + 2 * p1 + p0, d7, s7)

def cabacEncodeIntraMbType (enc0 : CabacEnc) (st0 : Array UInt8) (mbt ctxBase : Nat)
    (intraSlice : Bool) (leftRec topRec : Option MbGridRecord) : CabacEnc × Array UInt8 :=
  if intraSlice then
    let cL := match leftRec with | some r => if r.isI16x16 || r.isIpcm then 1 else 0 | none => 0
    let cT := match topRec with | some r => if r.isI16x16 || r.isIpcm then 1 else 0 | none => 0
    if mbt == 0 then enc0.encodeDecision st0 (ctxBase + cL + cT) 0
    else
      let (e1, s1) := enc0.encodeDecision st0 (ctxBase + cL + cT) 1
      if mbt == 25 then (e1.encodeTerminate 1, s1)
      else
        let e2 := e1.encodeTerminate 0
        let b := ctxBase + 2
        let t := mbt - 1
        let (e3, s3) := e2.encodeDecision s1 (b + 1) (if t ≥ 12 then 1 else 0)
        let cc := (t % 12) / 4
        let (e4, s4) :=
          if cc == 0 then e3.encodeDecision s3 (b + 2) 0
          else
            let (ea, sa) := e3.encodeDecision s3 (b + 2) 1
            ea.encodeDecision sa (b + 3) (if cc == 2 then 1 else 0)
        let pm := t % 4
        let (e5, s5) := e4.encodeDecision s4 (b + 4) ((pm >>> 1) &&& 1)
        e5.encodeDecision s5 (b + 5) (pm &&& 1)
  else
    if mbt == 0 then enc0.encodeDecision st0 ctxBase 0
    else
      let (e1, s1) := enc0.encodeDecision st0 ctxBase 1
      if mbt == 25 then (e1.encodeTerminate 1, s1)
      else
        let e2 := e1.encodeTerminate 0
        let t := mbt - 1
        let (e3, s3) := e2.encodeDecision s1 (ctxBase + 1) (if t ≥ 12 then 1 else 0)
        let cc := (t % 12) / 4
        let (e4, s4) :=
          if cc == 0 then e3.encodeDecision s3 (ctxBase + 2) 0
          else
            let (ea, sa) := e3.encodeDecision s3 (ctxBase + 2) 1
            ea.encodeDecision sa (ctxBase + 2) (if cc == 2 then 1 else 0)
        let pm := t % 4
        let (e5, s5) := e4.encodeDecision s4 (ctxBase + 3) ((pm >>> 1) &&& 1)
        e5.encodeDecision s5 (ctxBase + 3) (pm &&& 1)

def cabacDecodeBMbType (dec0 : CabacDec) (st0 : Array UInt8)
    (leftRec topRec : Option MbGridRecord) : Option Nat × CabacDec × Array UInt8 :=
  let cL := match leftRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
  let cT := match topRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
  let (b0, d1, s1) := dec0.decodeDecision st0 (27 + cL + cT)
  if b0 == 0 then (some 0, d1, s1)
  else
    let (b1, d2, s2) := d1.decodeDecision s1 30
    if b1 == 0 then
      let (b2, d3, s3) := d2.decodeDecision s2 32
      (some (1 + b2), d3, s3)
    else
      let (a3, d3, s3) := d2.decodeDecision s2 31
      let (a2, d4, s4) := d3.decodeDecision s3 32
      let (a1, d5, s5) := d4.decodeDecision s4 32
      let (a0, d6, s6) := d5.decodeDecision s5 32
      let bits := (a3 <<< 3) + (a2 <<< 2) + (a1 <<< 1) + a0
      if bits < 8 then (some (bits + 3), d6, s6)
      else if bits == 13 then (none, d6, s6)
      else if bits == 14 then (some 11, d6, s6)
      else if bits == 15 then (some 22, d6, s6)
      else
        let (ax, d7, s7) := d6.decodeDecision s6 32
        (some (((bits <<< 1) + ax) - 4), d7, s7)

def cabacEncodeBMbType (enc0 : CabacEnc) (st0 : Array UInt8) (mbt : Nat)
    (leftRec topRec : Option MbGridRecord) : Option (CabacEnc × Array UInt8) :=
  let cL := match leftRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
  let cT := match topRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
  if mbt == 0 then some (enc0.encodeDecision st0 (27 + cL + cT) 0)
  else
    let (e1, s1) := enc0.encodeDecision st0 (27 + cL + cT) 1
    if mbt == 1 || mbt == 2 then
      let (e2, s2) := e1.encodeDecision s1 30 0
      some (e2.encodeDecision s2 32 (mbt - 1))
    else if mbt > 22 then none
    else
      let (e2, s2) := e1.encodeDecision s1 30 1
      let bits :=
        if mbt ≤ 10 then mbt - 3
        else if mbt == 11 then 14
        else if mbt == 22 then 15
        else (mbt + 4) >>> 1
      let (e3, s3) := e2.encodeDecision s2 31 ((bits >>> 3) &&& 1)
      let (e4, s4) := e3.encodeDecision s3 32 ((bits >>> 2) &&& 1)
      let (e5, s5) := e4.encodeDecision s4 32 ((bits >>> 1) &&& 1)
      let (e6, s6) := e5.encodeDecision s5 32 (bits &&& 1)
      if bits == 14 || bits == 15 || bits < 8 then some (e6, s6)
      else some (e6.encodeDecision s6 32 ((mbt + 4) &&& 1))

def cabacDecodePSub (dec0 : CabacDec) (st0 : Array UInt8) : Nat × CabacDec × Array UInt8 :=
  let (b0, d1, s1) := dec0.decodeDecision st0 21
  if b0 == 1 then (0, d1, s1)
  else
    let (b1, d2, s2) := d1.decodeDecision s1 22
    if b1 == 0 then (1, d2, s2)
    else
      let (b2, d3, s3) := d2.decodeDecision s2 23
      (if b2 == 1 then 2 else 3, d3, s3)

def cabacEncodePSub (enc0 : CabacEnc) (st0 : Array UInt8) (t : Nat) : CabacEnc × Array UInt8 :=
  if t == 0 then enc0.encodeDecision st0 21 1
  else
    let (e1, s1) := enc0.encodeDecision st0 21 0
    if t == 1 then e1.encodeDecision s1 22 0
    else
      let (e2, s2) := e1.encodeDecision s1 22 1
      e2.encodeDecision s2 23 (if t == 2 then 1 else 0)

def cabacDecodeBSub (dec0 : CabacDec) (st0 : Array UInt8) : Nat × CabacDec × Array UInt8 :=
  let (b0, d1, s1) := dec0.decodeDecision st0 36
  if b0 == 0 then (0, d1, s1)
  else
    let (b1, d2, s2) := d1.decodeDecision s1 37
    if b1 == 0 then
      let (b2, d3, s3) := d2.decodeDecision s2 39
      (1 + b2, d3, s3)
    else
      let (b2, d3, s3) := d2.decodeDecision s2 38
      if b2 == 1 then
        let (b3, d4, s4) := d3.decodeDecision s3 39
        if b3 == 1 then
          let (b4, d5, s5) := d4.decodeDecision s4 39
          (11 + b4, d5, s5)
        else
          let (x1, d5, s5) := d4.decodeDecision s4 39
          let (x0, d6, s6) := d5.decodeDecision s5 39
          (7 + 2 * x1 + x0, d6, s6)
      else
        let (x1, d4, s4) := d3.decodeDecision s3 39
        let (x0, d5, s5) := d4.decodeDecision s4 39
        (3 + 2 * x1 + x0, d5, s5)

def cabacEncodeBSub (enc0 : CabacEnc) (st0 : Array UInt8) (t : Nat) : CabacEnc × Array UInt8 :=
  if t == 0 then enc0.encodeDecision st0 36 0
  else
    let (e1, s1) := enc0.encodeDecision st0 36 1
    if t == 1 || t == 2 then
      let (e2, s2) := e1.encodeDecision s1 37 0
      e2.encodeDecision s2 39 (t - 1)
    else
      let (e2, s2) := e1.encodeDecision s1 37 1
      if t ≤ 6 then
        let v := t - 3
        let (e3, s3) := e2.encodeDecision s2 38 0
        let (e4, s4) := e3.encodeDecision s3 39 ((v >>> 1) &&& 1)
        e4.encodeDecision s4 39 (v &&& 1)
      else if t ≤ 10 then
        let v := t - 7
        let (e3, s3) := e2.encodeDecision s2 38 1
        let (e4, s4) := e3.encodeDecision s3 39 0
        let (e5, s5) := e4.encodeDecision s4 39 ((v >>> 1) &&& 1)
        e5.encodeDecision s5 39 (v &&& 1)
      else
        let (e3, s3) := e2.encodeDecision s2 38 1
        let (e4, s4) := e3.encodeDecision s3 39 1
        e4.encodeDecision s4 39 (t - 11)

def cabacRefCtx (g : MbGrid) (mx my : Nat) (curRec : MbGridRecord) (lst blk0 : Nat) (isB : Bool) : Nat :=
  let (bx, by0) := blk4XY.getD blk0 (0, 0)
  let (ra, da) :=
    if bx > 0 then
      let nbI := xyToBlk4 (bx - 1) by0
      ((curRec.refGrid.getD lst #[]).getD nbI (-1), curRec.directPart.getD nbI false)
    else match g.leftMb mx my with
      | none => (-1, false)
      | some mba =>
        let nbI := xyToBlk4 3 by0
        ((mba.refGrid.getD lst #[]).getD nbI (-1), mba.directPart.getD nbI false)
  let (rb, db) :=
    if by0 > 0 then
      let nbI := xyToBlk4 bx (by0 - 1)
      ((curRec.refGrid.getD lst #[]).getD nbI (-1), curRec.directPart.getD nbI false)
    else match g.topMb mx my with
      | none => (-1, false)
      | some mbb =>
        let nbI := xyToBlk4 bx 3
        ((mbb.refGrid.getD lst #[]).getD nbI (-1), mbb.directPart.getD nbI false)
  let ca := if ra > 0 && !(isB && da) then 1 else 0
  let cb := if rb > 0 && !(isB && db) then 1 else 0
  ca + 2 * cb

def cabacMvdAmvd (g : MbGrid) (mx my : Nat) (curRec : MbGridRecord) (lst blk0 : Nat) : Nat × Nat :=
  let (bx, by0) := blk4XY.getD blk0 (0, 0)
  let (ax, ay) :=
    if bx > 0 then (curRec.mvdGrid.getD lst #[]).getD (xyToBlk4 (bx - 1) by0) (0, 0)
    else match g.leftMb mx my with
      | none => (0, 0)
      | some mba => (mba.mvdGrid.getD lst #[]).getD (xyToBlk4 3 by0) (0, 0)
  let (bxv, byv) :=
    if by0 > 0 then (curRec.mvdGrid.getD lst #[]).getD (xyToBlk4 bx (by0 - 1)) (0, 0)
    else match g.topMb mx my with
      | none => (0, 0)
      | some mbb => (mbb.mvdGrid.getD lst #[]).getD (xyToBlk4 bx 3) (0, 0)
  (Nat.min ax.natAbs 70 + Nat.min bxv.natAbs 70, Nat.min ay.natAbs 70 + Nat.min byv.natAbs 70)

private def cabacDecRefLoop : Nat → CabacDec → Array UInt8 → Nat → Nat → Option (Nat × CabacDec × Array UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, dec, st, ctx, refVal =>
    let (b, d1, s1) := dec.decodeDecision st (54 + ctx)
    if b == 1 then cabacDecRefLoop fuel d1 s1 ((ctx >>> 2) + 4) (refVal + 1)
    else some (refVal, d1, s1)

def cabacDecodeRef (dec0 : CabacDec) (st0 : Array UInt8) (ctx rcMax : Nat) :
    Option (Nat × CabacDec × Array UInt8) := do
  let (rv, d1, s1) ← cabacDecRefLoop 64 dec0 st0 ctx 0
  if rv ≥ rcMax then none else some (rv, d1, s1)

def cabacEncodeRef (enc0 : CabacEnc) (st0 : Array UInt8) (ctx refVal : Nat) : CabacEnc × Array UInt8 := Id.run do
  let mut eCur := enc0
  let mut sCur := st0
  let mut cCur := ctx
  for _ in [:refVal] do
    let (en, sn) := eCur.encodeDecision sCur (54 + cCur) 1
    eCur := en
    sCur := sn
    cCur := (cCur >>> 2) + 4
  return eCur.encodeDecision sCur (54 + cCur) 0

private def cabacDecMvdUnaryLoop :
    Nat → CabacDec → Array UInt8 → Nat → Nat → Nat × CabacDec × Array UInt8
  | 0, dec, st, _, mvd => (mvd, dec, st)
  | rem + 1, dec, st, c, mvd =>
    let (b, d1, s1) := dec.decodeDecision st c
    if b == 1 then
      let cNext := if mvd < 4 then c + 1 else c
      cabacDecMvdUnaryLoop rem d1 s1 cNext (mvd + 1)
    else
      (mvd, d1, s1)

def cabacDecodeMvdComp (dec0 : CabacDec) (st0 : Array UInt8) (ctxBase amvd : Nat) :
    Option (Int × CabacDec × Array UInt8) := do
  let inc := (if amvd > 2 then 1 else 0) + (if amvd > 32 then 1 else 0)
  let (b0, d1, s1) := dec0.decodeDecision st0 (ctxBase + inc)
  if b0 == 0 then some (0, d1, s1)
  else do
    let (mvd0, d2, s2) := cabacDecMvdUnaryLoop 8 d1 s1 (ctxBase + 3) 1
    let (mvdMag, d3) ←
      if mvd0 ≥ 9 then do
        let (j, dU) ← cabacDecBypassUnary 24 d2 0
        let kBits := 3 + j
        let (suf, dS) := cabacDecBypassBits kBits dU 0
        pure (9 + (((1 <<< j) - 1) <<< 3) + suf, dS)
      else
        pure (mvd0, d2)
    let (sgn, d4) := d3.decodeBypass
    let v : Int := if sgn == 1 then -Int.ofNat mvdMag else Int.ofNat mvdMag
    some (v, d4, s2)

def cabacEncodeMvdComp (enc0 : CabacEnc) (st0 : Array UInt8) (ctxBase amvd : Nat) (val : Int) :
    Option (CabacEnc × Array UInt8) := do
  let inc := (if amvd > 2 then 1 else 0) + (if amvd > 32 then 1 else 0)
  if val == 0 then some (enc0.encodeDecision st0 (ctxBase + inc) 0)
  else do
    let (e1, s1) := enc0.encodeDecision st0 (ctxBase + inc) 1
    let m := val.natAbs
    let uOnes := Nat.min (m - 1) 8
    let mut eCur := e1
    let mut sCur := s1
    let mut c := ctxBase + 3
    for k in [:uOnes] do
      let (en, sn) := eCur.encodeDecision sCur c 1
      eCur := en
      sCur := sn
      if k < 3 then c := c + 1
    let eAfterMag ←
      if m < 9 then
        let (en, sn) := eCur.encodeDecision sCur c 0
        sCur := sn
        pure en
      else
        cabacEncBypassExpGolomb 24 eCur (m - 9) 3
    let eDone := eAfterMag.encodeBypass (if val < 0 then 1 else 0)
    some (eDone, sCur)

private def cabacDecodeInterMotion (dec0 : CabacDec) (st0 : Array UInt8) (sh : SliceHeaderFull)
    (g : MbGrid) (mx my : Nat) (kind : MbKind) (interIdx : Nat) :
    Option (Array Nat × Array Nat × Array Nat × Array (Int × Int) ×
      Array (Int × Int) × MbGridRecord × CabacDec × Array UInt8) := do
  let isB := kind == .bInter
  let (info, numLists) :=
    if kind == .pInter then (pMbInfoTable.getD interIdx {}, 1)
    else (bMbInfoTable.getD interIdx {}, 2)
  let rcActive := #[if info.isRef0 then 1 else sh.numRefL0, if info.isRef0 then 1 else sh.numRefL1]
  let useLists := #[info.useL0, info.useL1]
  let mut rCur : MbGridRecord := {}
  let mut decCur := dec0
  let mut stCur := st0
  if info.shape == .direct then
    rCur := { rCur with directPart := Array.replicate 16 true }
    some (#[], #[], #[], #[], #[], rCur, decCur, stCur)
  else if info.shape == .p8x8 then do
    let mut subs : Array Nat := Array.emptyWithCapacity 4
    for _ in [:4] do
      let (sv, dn, sn) := if isB then cabacDecodeBSub decCur stCur else cabacDecodePSub decCur stCur
      decCur := dn
      stCur := sn
      subs := subs.push sv
    for si in [:4] do
      let st := subs.getD si 0
      let sub := if isB then bSubInfoTable.getD st {} else pSubInfoTable.getD st {}
      if sub.shape == .direct then
        rCur := { rCur with directPart := fillRect4x4 rCur.directPart (4 * si) 2 2 true }
    let mut refs := #[#[], #[]]
    let mut mvds := #[#[], #[]]
    for lst in [:numLists] do
      let mut rArr : Array Nat := #[]
      for si in [:4] do
        let st := subs.getD si 0
        let sub := if isB then bSubInfoTable.getD st {} else pSubInfoTable.getD st {}
        if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
          let rcMax := rcActive.getD lst 1
          let (rv, dn, sn) ←
            if rcMax > 1 then cabacDecodeRef decCur stCur (cabacRefCtx g mx my rCur lst (4 * si) isB) rcMax
            else pure (0, decCur, stCur)
          decCur := dn
          stCur := sn
          rArr := rArr.push rv
          rCur := { rCur with refGrid := rCur.refGrid.set! lst (fillRect4x4 (rCur.refGrid.getD lst #[]) (4 * si) 2 2 (Int.ofNat rv)) }
      refs := refs.set! lst rArr
    for lst in [:numLists] do
      let mut mArr : Array (Int × Int) := #[]
      for si in [:4] do
        let st := subs.getD si 0
        let sub := if isB then bSubInfoTable.getD st {} else pSubInfoTable.getD st {}
        if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
          for j in [:sub.subCnt] do
            let (off, bw, bh) := subPartGeom sub.shape j
            let blk0 := 4 * si + off
            let (ax, ay) := cabacMvdAmvd g mx my rCur lst blk0
            let (mvx, d1, s1) ← cabacDecodeMvdComp decCur stCur 40 ax
            let (mvy, d2, s2) ← cabacDecodeMvdComp d1 s1 47 ay
            decCur := d2
            stCur := s2
            mArr := mArr.push (mvx, mvy)
            rCur := { rCur with mvdGrid := rCur.mvdGrid.set! lst (fillRect4x4 (rCur.mvdGrid.getD lst #[]) blk0 bw bh (mvx, mvy)) }
      mvds := mvds.set! lst mArr
    some (subs, refs.getD 0 #[], refs.getD 1 #[], mvds.getD 0 #[], mvds.getD 1 #[], rCur, decCur, stCur)
  else do
    let nPart := info.useL0.size
    let mut refs := #[#[], #[]]
    let mut mvds := #[#[], #[]]
    for lst in [:numLists] do
      let mut rArr : Array Nat := #[]
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (blk0, bw, bh) := if info.shape == .p16x16 then (0, 4, 4) else if info.shape == .p16x8 then (8 * pi, 4, 2) else (4 * pi, 2, 4)
          let rcMax := rcActive.getD lst 1
          let (rv, dn, sn) ←
            if rcMax > 1 then cabacDecodeRef decCur stCur (cabacRefCtx g mx my rCur lst blk0 isB) rcMax
            else pure (0, decCur, stCur)
          decCur := dn
          stCur := sn
          rArr := rArr.push rv
          rCur := { rCur with refGrid := rCur.refGrid.set! lst (fillRect4x4 (rCur.refGrid.getD lst #[]) blk0 bw bh (Int.ofNat rv)) }
      refs := refs.set! lst rArr
    for lst in [:numLists] do
      let mut mArr : Array (Int × Int) := #[]
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (blk0, bw, bh) := if info.shape == .p16x16 then (0, 4, 4) else if info.shape == .p16x8 then (8 * pi, 4, 2) else (4 * pi, 2, 4)
          let (ax, ay) := cabacMvdAmvd g mx my rCur lst blk0
          let (mvx, d1, s1) ← cabacDecodeMvdComp decCur stCur 40 ax
          let (mvy, d2, s2) ← cabacDecodeMvdComp d1 s1 47 ay
          decCur := d2
          stCur := s2
          mArr := mArr.push (mvx, mvy)
          rCur := { rCur with mvdGrid := rCur.mvdGrid.set! lst (fillRect4x4 (rCur.mvdGrid.getD lst #[]) blk0 bw bh (mvx, mvy)) }
      mvds := mvds.set! lst mArr
    some (#[], refs.getD 0 #[], refs.getD 1 #[], mvds.getD 0 #[], mvds.getD 1 #[], rCur, decCur, stCur)

private def cabacDecDqpLoop :
    Nat → CabacDec → Array UInt8 → Nat → Nat → Option (Nat × CabacDec × Array UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, dec, st, cIdx, v =>
    let (b, d1, s1) := dec.decodeDecision st cIdx
    if b == 1 then cabacDecDqpLoop fuel d1 s1 63 (v + 1)
    else some (v, d1, s1)

private def cabacDecodeResidualMb (dec0 : CabacDec) (st0 : Array UInt8) (g : MbGrid) (mx my : Nat)
    (hasChroma : Bool) (lastDqp : Int) (mb0 : MbSyntax) :
    Option (MbSyntax × Int × CabacDec × Array UInt8) := do
  if mb0.cbp == 0 && mb0.kind != .i16x16 then
    some (mb0, 0, dec0, st0)
  else do
    let (bDqp, d1, s1) := dec0.decodeDecision st0 (60 + (if lastDqp != 0 then 1 else 0))
    let (dqp, decA, stA) ←
      if bDqp == 0 then pure ((0 : Int), d1, s1)
      else do
        let (v, dU, sU) ← cabacDecDqpLoop 256 d1 s1 62 1
        let mag : Int := Int.ofNat ((v + 1) >>> 1)
        pure (if (v &&& 1) == 1 then mag else -mag, dU, sU)
    let mut decCur := decA
    let mut stCur := stA
    let mut curCbfL := Array.replicate 16 0
    let mut curCbfC := #[Array.replicate 4 0, Array.replicate 4 0]
    let mut i16Dc := mb0.i16Dc
    let mut luma4 := mb0.lumaAcOr4x4
    let mut luma8 := mb0.luma8x8
    let mut cdc := mb0.chromaDc
    let mut cac := mb0.chromaAc
    let isIntra := mb0.kind.isIntra
    if mb0.kind == .i16x16 then
      let c0 := cabacCbfCtx g mx my true 0 curCbfL curCbfC 0
      let (dcCoeffs, _, dn, sn) ← cabacDecodeResidualBlock decCur stCur 0 16 (some c0)
      i16Dc := dcCoeffs
      decCur := dn
      stCur := sn
      if (mb0.cbp &&& 0xF) != 0 then
        for idx in [:16] do
          let cc := cabacCbfCtx g mx my true 1 curCbfL curCbfC idx
          let (acCoeffs, nz, dn2, sn2) ← cabacDecodeResidualBlock decCur stCur 1 15 (some cc)
          decCur := dn2
          stCur := sn2
          luma4 := luma4.set! idx (acCoeffs.push 0)
          curCbfL := curCbfL.set! idx nz
    else
      for i8 in [:4] do
        if (mb0.cbp &&& (1 <<< i8)) != 0 then
          if mb0.transform8x8 != 0 then
            let (coeffs64, _, dn2, sn2) ← cabacDecodeResidualBlock decCur stCur 5 64 none
            decCur := dn2
            stCur := sn2
            luma8 := luma8.set! i8 coeffs64
            for sub in [:4] do
              curCbfL := curCbfL.set! (4 * i8 + sub) 1
          else
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let cc := cabacCbfCtx g mx my isIntra 2 curCbfL curCbfC idx
              let (coeffs, nz, dn2, sn2) ← cabacDecodeResidualBlock decCur stCur 2 16 (some cc)
              decCur := dn2
              stCur := sn2
              luma4 := luma4.set! idx coeffs
              curCbfL := curCbfL.set! idx nz
    if hasChroma && (mb0.cbp &&& 0x30) != 0 then
      for pl in [:2] do
        let cc := cabacCbfCtx g mx my isIntra 3 curCbfL curCbfC pl
        let (dcCoeffs, _, dn2, sn2) ← cabacDecodeResidualBlock decCur stCur 3 4 (some cc)
        decCur := dn2
        stCur := sn2
        cdc := cdc.set! pl dcCoeffs
      if (mb0.cbp &&& 0x20) != 0 then
        for pl in [:2] do
          for ci in [:4] do
            let cc := cabacCbfCtx g mx my isIntra 4 curCbfL curCbfC (pl * 4 + ci)
            let (coeffs, nz, dn2, sn2) ← cabacDecodeResidualBlock decCur stCur 4 15 (some cc)
            decCur := dn2
            stCur := sn2
            cac := cac.set! (pl * 4 + ci) coeffs
            let pArr := (curCbfC.getD pl (Array.replicate 4 0)).set! ci nz
            curCbfC := curCbfC.set! pl pArr
    some ({ mb0 with
      mbQpDelta := dqp, i16Dc := i16Dc, lumaAcOr4x4 := luma4,
      luma8x8 := luma8, chromaDc := cdc, chromaAc := cac
    }, dqp, decCur, stCur)

private def cabacDecodeCbp (dec0 : CabacDec) (st0 : Array UInt8) (hasChroma : Bool)
    (leftRec topRec : Option MbGridRecord) : Nat × CabacDec × Array UInt8 :=
  let ca := match leftRec with | some r => r.cbpLuma | none => 0xF
  let cb := match topRec with | some r => r.cbpLuma | none => 0xF
  let (b0, d1, s1) := dec0.decodeDecision st0 (73 + (if (ca &&& 2) != 0 then 0 else 1) + 2 * (if (cb &&& 4) != 0 then 0 else 1))
  let cbpL1 := b0
  let (b1, d2, s2) := d1.decodeDecision s1 (73 + (if (cbpL1 &&& 1) != 0 then 0 else 1) + 2 * (if (cb &&& 8) != 0 then 0 else 1))
  let cbpL2 := cbpL1 ||| (b1 <<< 1)
  let (b2, d3, s3) := d2.decodeDecision s2 (73 + (if (ca &&& 8) != 0 then 0 else 1) + 2 * (if (cbpL2 &&& 1) != 0 then 0 else 1))
  let cbpL3 := cbpL2 ||| (b2 <<< 2)
  let (b3, d4, s4) := d3.decodeDecision s3 (73 + (if (cbpL3 &&& 4) != 0 then 0 else 1) + 2 * (if (cbpL3 &&& 2) != 0 then 0 else 1))
  let cbpL := cbpL3 ||| (b3 <<< 3)
  if !hasChroma then (cbpL, d4, s4)
  else
    let cca := match leftRec with | some r => r.cbpChroma | none => 0
    let ccb := match topRec with | some r => r.cbpChroma | none => 0
    let ctx0 := (if cca > 0 then 1 else 0) + (if ccb > 0 then 2 else 0)
    let (bc0, d5, s5) := d4.decodeDecision s4 (77 + ctx0)
    if bc0 == 0 then (cbpL, d5, s5)
    else
      let ctx1 := 4 + (if cca == 2 then 1 else 0) + (if ccb == 2 then 2 else 0)
      let (bc1, d6, s6) := d5.decodeDecision s5 (77 + ctx1)
      (cbpL ||| ((1 + bc1) <<< 4), d6, s6)

private def cabacDecodeNonSkipMb (dec0 : CabacDec) (st0 : Array UInt8) (sh : SliceHeaderFull)
    (sps : SpsFull) (pps : PpsFull) (g : MbGrid) (mx my : Nat) (lastDqp : Int) :
    Option (MbSyntax × MbGridRecord × Int × CabacDec × Array UInt8) := do
  let hasChroma := sps.chromaFormatIdc == 1
  let leftRec := g.leftMb mx my
  let topRec := g.topMb mx my
  let (isIntra, intraMbt, interKind, interIdx, dec1, st1) :=
    if sh.sliceTypeNos == 2 then
      let (im, d, s) := cabacDecodeIntraMbType dec0 st0 3 true leftRec topRec
      (true, im, MbKind.iNxN, 0, d, s)
    else if sh.sliceTypeNos == 0 then
      let (bI, dA, sA) := dec0.decodeDecision st0 14
      if bI == 0 then
        let (bP, dB, sB) := dA.decodeDecision sA 15
        if bP == 0 then
          let (bS, dC, sC) := dB.decodeDecision sB 16
          (false, 0, MbKind.pInter, 3 * bS, dC, sC)
        else
          let (bS, dC, sC) := dB.decodeDecision sB 17
          (false, 0, MbKind.pInter, 2 - bS, dC, sC)
      else
        let (im, dB, sB) := cabacDecodeIntraMbType dA sA 17 false leftRec topRec
        (true, im, MbKind.iNxN, 0, dB, sB)
    else
      let (bmOpt, dA, sA) := cabacDecodeBMbType dec0 st0 leftRec topRec
      match bmOpt with
      | none =>
        let (im, dB, sB) := cabacDecodeIntraMbType dA sA 32 false leftRec topRec
        (true, im, MbKind.iNxN, 0, dB, sB)
      | some bm =>
        (false, 0, MbKind.bInter, bm, dA, sA)
  let t8CtxOff := (match leftRec with | some r => if r.is8x8Dct then 1 else 0 | none => 0) +
                  (match topRec with | some r => if r.is8x8Dct then 1 else 0 | none => 0)
  if isIntra then
    if intraMbt == 25 then do
      let (pcm, decPcm) ← dec1.readPcmAndReinit (pcmByteCount sps)
      let mbPcm : MbSyntax := { kind := .iPcm, intraIdx := 25, pcmBytes := pcm }
      some (mbPcm, applyMbHeaderToRecord mbPcm {}, 0, decPcm, st1)
    else do
      let kind : MbKind := if intraMbt == 0 then .iNxN else .i16x16
      let mut decCur := dec1
      let mut stCur := st1
      let mut t8 := 0
      let mut preds : Array (Nat × Nat) := #[]
      if kind == .iNxN then
        if pps.transform8x8ModeFlag != 0 then
          let (tv, dn, sn) := decCur.decodeDecision stCur (399 + t8CtxOff)
          t8 := tv; decCur := dn; stCur := sn
        let nModes := if t8 != 0 then 4 else 16
        for _ in [:nModes] do
          let (pf, dA, sA) := decCur.decodeDecision stCur 68
          if pf == 1 then
            preds := preds.push (1, 0); decCur := dA; stCur := sA
          else
            let (r0b, dB, sB) := dA.decodeDecision sA 69
            let (r1b, dC, sC) := dB.decodeDecision sB 69
            let (r2b, dD, sD) := dC.decodeDecision sC 69
            preds := preds.push (0, r0b + 2 * r1b + 4 * r2b); decCur := dD; stCur := sD
      let mut cMode := 0
      if hasChroma then
        let cCtx := (match leftRec with | some r => if r.isIntra && r.chromaPredMode != 0 then 1 else 0 | none => 0) +
                    (match topRec with | some r => if r.isIntra && r.chromaPredMode != 0 then 1 else 0 | none => 0)
        let (cm0, dA, sA) := decCur.decodeDecision stCur (64 + cCtx)
        if cm0 == 0 then decCur := dA; stCur := sA
        else
          let (cm1, dB, sB) := dA.decodeDecision sA 67
          if cm1 == 0 then cMode := 1; decCur := dB; stCur := sB
          else
            let (cm2, dC, sC) := dB.decodeDecision sB 67
            cMode := if cm2 == 0 then 2 else 3; decCur := dC; stCur := sC
      let cbpVal ←
        if kind == .i16x16 then
          let t := intraMbt - 1
          let cv := (if t ≥ 12 then 15 else 0) ||| (((t / 4) % 3) <<< 4)
          if !hasChroma && cv > 15 then none else pure cv
        else
          let (cv, dn, sn) := cabacDecodeCbp decCur stCur hasChroma leftRec topRec
          decCur := dn; stCur := sn
          pure cv
      let mb0 : MbSyntax := {
        kind := kind, intraIdx := intraMbt, transform8x8 := t8,
        intraPred := preds, chromaPredMode := cMode, cbp := cbpVal
      }
      let (mbDone, dqpOut, decEnd, stEnd) ← cabacDecodeResidualMb decCur stCur g mx my hasChroma lastDqp mb0
      let recDone := populateResidualGrid mbDone (applyMbHeaderToRecord mbDone {}) hasChroma
      some (mbDone, recDone, dqpOut, decEnd, stEnd)
  else do
    let (subs, rl0, rl1, ml0, ml1, recMot, dec2, st2) ← cabacDecodeInterMotion dec1 st1 sh g mx my interKind interIdx
    let (cbpVal, dec3, st3) := cabacDecodeCbp dec2 st2 hasChroma leftRec topRec
    let mbBase : MbSyntax := {
      kind := interKind, interIdx := interIdx, subMbTypes := subs,
      refL0 := rl0, refL1 := rl1, mvdL0 := ml0, mvdL1 := ml1, cbp := cbpVal
    }
    let (t8, dec4, st4) :=
      if (cbpVal &&& 0xF) != 0 && interDct8x8Allowed pps sps mbBase then
        dec3.decodeDecision st3 (399 + t8CtxOff)
      else (0, dec3, st3)
    let (mbDone, dqpOut, decEnd, stEnd) ←
      cabacDecodeResidualMb dec4 st4 g mx my hasChroma lastDqp { mbBase with transform8x8 := t8 }
    let recDone := populateResidualGrid mbDone (applyMbHeaderToRecord mbDone recMot) hasChroma
    some (mbDone, recDone, dqpOut, decEnd, stEnd)

def zigzagScan4x4 : Array Nat := #[
  0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15
]

def zigzagScan8x8 : Array Nat := #[
  0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5,
  12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14, 21, 28,
  35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51,
  58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63
]

def zigzagToRaster4x4 (scan : Array Int) : Array Int := Id.run do
  let mut out := Array.replicate 16 (0 : Int)
  for k in [:16] do
    let dst := zigzagScan4x4.getD k 0
    out := out.set! dst (scan.getD k 0)
  return out

def rasterToZigzag4x4 (raster : Array Int) : Array Int := Id.run do
  let mut out := Array.replicate 16 (0 : Int)
  for k in [:16] do
    let src := zigzagScan4x4.getD k 0
    out := out.set! k (raster.getD src 0)
  return out

def zigzagToRaster8x8 (scan : Array Int) : Array Int := Id.run do
  let mut out := Array.replicate 64 (0 : Int)
  for k in [:64] do
    let dst := zigzagScan8x8.getD k 0
    out := out.set! dst (scan.getD k 0)
  return out

def rasterToZigzag8x8 (raster : Array Int) : Array Int := Id.run do
  let mut out := Array.replicate 64 (0 : Int)
  for k in [:64] do
    let src := zigzagScan8x8.getD k 0
    out := out.set! k (raster.getD src 0)
  return out

private def decodeSliceCabacLoop (sh : SliceHeaderFull) (sps : SpsFull) (pps : PpsFull)
    (totalMbs : Nat) :
    Nat → Nat → Int → CabacDec → Array UInt8 → MbGrid → Array MbSyntax → Option (Array MbSyntax)
  | 0, _, _, _, _, _, acc => some acc
  | fuel + 1, mbIdx, lastDqp, dec, st, g, acc =>
    if mbIdx ≥ totalMbs then some acc
    else
      let mx := mbIdx % sps.picWidthInMbs
      let my := mbIdx / sps.picWidthInMbs
      let hasChroma := sps.chromaFormatIdc == 1
      let leftRec := g.leftMb mx my
      let topRec := g.topMb mx my
      let (isSkip, dec1, st1) :=
        if sh.sliceTypeNos != 2 then
          let sCtx := (match leftRec with | some r => if !r.isSkip then 1 else 0 | none => 0) +
                      (match topRec with | some r => if !r.isSkip then 1 else 0 | none => 0) +
                      (if sh.sliceTypeNos == 1 then 13 else 0)
          let (b, d', s') := dec.decodeDecision st (11 + sCtx)
          (b == 1, d', s')
        else (false, dec, st)
      if isSkip then
        let mb : MbSyntax := { isSkip := true, kind := .skip }
        let g1 := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
        let acc1 := acc.push mb
        let (term, dec2) := dec1.decodeTerminate
        if term == 1 then some acc1
        else decodeSliceCabacLoop sh sps pps totalMbs fuel (mbIdx + 1) 0 dec2 st1 g1 acc1
      else do
        let (mbDone, recDone, dqpOut, dec2, st2) ←
          cabacDecodeNonSkipMb dec1 st1 sh sps pps g mx my lastDqp
        let g1 := g.setMb mx my recDone
        let acc1 := acc.push mbDone
        let (term, dec3) := dec2.decodeTerminate
        if term == 1 then some acc1
        else decodeSliceCabacLoop sh sps pps totalMbs fuel (mbIdx + 1) dqpOut dec3 st2 g1 acc1

def decodeSliceCabac (rbsp : ByteArray) (sh : SliceHeaderFull) (bitStart : Nat)
    (sps : SpsFull) (pps : PpsFull) : Option (Array MbSyntax) :=
  let totalMbs := sps.picWidthInMbs * sps.picHeightInMapUnits
  if sh.firstMbInSlice ≥ totalMbs then none
  else
    let dec0 := CabacDec.init rbsp bitStart
    let st0 := initCabacStates sh.sliceTypeNos sh.cabacInitIdc sh.sliceQpY
    let g0 := MbGrid.init sps.picWidthInMbs sps.picHeightInMapUnits
    decodeSliceCabacLoop sh sps pps totalMbs (totalMbs - sh.firstMbInSlice) sh.firstMbInSlice 0 dec0 st0 g0 #[]

private def cabacEncodeInterMotion (enc0 : CabacEnc) (st0 : Array UInt8) (sh : SliceHeaderFull)
    (g : MbGrid) (mx my : Nat) (mb : MbSyntax) :
    Option (MbGridRecord × CabacEnc × Array UInt8) := do
  let isB := mb.kind == .bInter
  let pIdx := if mb.kind == .pInter && mb.interIdx == 4 then 3 else mb.interIdx
  let (info, numLists) :=
    if mb.kind == .pInter then (pMbInfoTable.getD pIdx {}, 1)
    else (bMbInfoTable.getD mb.interIdx {}, 2)
  let rcActive := #[sh.numRefL0, sh.numRefL1]
  let refsSrc := #[mb.refL0, mb.refL1]
  let mvdsSrc := #[mb.mvdL0, mb.mvdL1]
  let useLists := #[info.useL0, info.useL1]
  let mut rCur : MbGridRecord := {}
  let mut encCur := enc0
  let mut stCur := st0
  if info.shape == .direct then
    rCur := { rCur with directPart := Array.replicate 16 true }
    some (rCur, encCur, stCur)
  else if info.shape == .p8x8 then do
    if mb.subMbTypes.size != 4 then none
    else do
      for si in [:4] do
        let sv := mb.subMbTypes.getD si 0
        let (en, sn) := if isB then cabacEncodeBSub encCur stCur sv else cabacEncodePSub encCur stCur sv
        encCur := en; stCur := sn
      for si in [:4] do
        let sv := mb.subMbTypes.getD si 0
        let sub := if isB then bSubInfoTable.getD sv {} else pSubInfoTable.getD sv {}
        if sub.shape == .direct then
          rCur := { rCur with directPart := fillRect4x4 rCur.directPart (4 * si) 2 2 true }
      for lst in [:numLists] do
        let mut rc := 0
        for si in [:4] do
          let sv := mb.subMbTypes.getD si 0
          let sub := if isB then bSubInfoTable.getD sv {} else pSubInfoTable.getD sv {}
          if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
            let rv :=
              if mb.kind == .pInter && mb.interIdx == 4 then 0
              else (refsSrc.getD lst #[]).getD rc 0
            if !(mb.kind == .pInter && mb.interIdx == 4) then rc := rc + 1
            if rcActive.getD lst 1 > 1 then
              let (en, sn) := cabacEncodeRef encCur stCur (cabacRefCtx g mx my rCur lst (4 * si) isB) rv
              encCur := en; stCur := sn
            rCur := { rCur with refGrid := rCur.refGrid.set! lst (fillRect4x4 (rCur.refGrid.getD lst #[]) (4 * si) 2 2 (Int.ofNat rv)) }
      for lst in [:numLists] do
        let mut mc := 0
        for si in [:4] do
          let sv := mb.subMbTypes.getD si 0
          let sub := if isB then bSubInfoTable.getD sv {} else pSubInfoTable.getD sv {}
          if sub.shape != .direct && (if lst == 0 then sub.useL0 else sub.useL1) then
            for j in [:sub.subCnt] do
              let (off, bw, bh) := subPartGeom sub.shape j
              let blk0 := 4 * si + off
              let (ax, ay) := cabacMvdAmvd g mx my rCur lst blk0
              let (mvx, mvy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
              mc := mc + 1
              let (e1, s1) ← cabacEncodeMvdComp encCur stCur 40 ax mvx
              let (e2, s2) ← cabacEncodeMvdComp e1 s1 47 ay mvy
              encCur := e2; stCur := s2
              rCur := { rCur with mvdGrid := rCur.mvdGrid.set! lst (fillRect4x4 (rCur.mvdGrid.getD lst #[]) blk0 bw bh (mvx, mvy)) }
      some (rCur, encCur, stCur)
  else do
    let nPart := info.useL0.size
    for lst in [:numLists] do
      let mut rc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (blk0, bw, bh) := if info.shape == .p16x16 then (0, 4, 4) else if info.shape == .p16x8 then (8 * pi, 4, 2) else (4 * pi, 2, 4)
          let rv := (refsSrc.getD lst #[]).getD rc 0
          rc := rc + 1
          if rcActive.getD lst 1 > 1 then
            let (en, sn) := cabacEncodeRef encCur stCur (cabacRefCtx g mx my rCur lst blk0 isB) rv
            encCur := en; stCur := sn
          rCur := { rCur with refGrid := rCur.refGrid.set! lst (fillRect4x4 (rCur.refGrid.getD lst #[]) blk0 bw bh (Int.ofNat rv)) }
    for lst in [:numLists] do
      let mut mc := 0
      for pi in [:nPart] do
        if (useLists.getD lst #[]).getD pi false then
          let (blk0, bw, bh) := if info.shape == .p16x16 then (0, 4, 4) else if info.shape == .p16x8 then (8 * pi, 4, 2) else (4 * pi, 2, 4)
          let (ax, ay) := cabacMvdAmvd g mx my rCur lst blk0
          let (mvx, mvy) := (mvdsSrc.getD lst #[]).getD mc (0, 0)
          mc := mc + 1
          let (e1, s1) ← cabacEncodeMvdComp encCur stCur 40 ax mvx
          let (e2, s2) ← cabacEncodeMvdComp e1 s1 47 ay mvy
          encCur := e2; stCur := s2
          rCur := { rCur with mvdGrid := rCur.mvdGrid.set! lst (fillRect4x4 (rCur.mvdGrid.getD lst #[]) blk0 bw bh (mvx, mvy)) }
    some (rCur, encCur, stCur)

private def cabacEffectiveCbp (mb : MbSyntax) : Nat :=
  if mb.kind != .i16x16 && mb.transform8x8 != 0 then
    let lumaMask := Id.run do
      let mut m := 0
      for i8 in [:4] do
        if (mb.cbp &&& (1 <<< i8)) != 0 && countNonZeroPrefix (mb.luma8x8.getD i8 #[]) 64 > 0 then
          m := m ||| (1 <<< i8)
      return m
    (mb.cbp &&& 0x30) ||| lumaMask
  else
    mb.cbp

private def cabacEncodeCbp (enc0 : CabacEnc) (st0 : Array UInt8) (effCbp : Nat) (hasChroma : Bool)
    (leftRec topRec : Option MbGridRecord) : CabacEnc × Array UInt8 :=
  let ca := match leftRec with | some r => r.cbpLuma | none => 0xF
  let cb := match topRec with | some r => r.cbpLuma | none => 0xF
  let cbpL := effCbp &&& 0xF
  let ctxL0 := 73 + (if (ca &&& 2) != 0 then 0 else 1) + 2 * (if (cb &&& 4) != 0 then 0 else 1)
  let (e1, s1) := enc0.encodeDecision st0 ctxL0 (cbpL &&& 1)
  let ctxL1 := 73 + (if (cbpL &&& 1) != 0 then 0 else 1) + 2 * (if (cb &&& 8) != 0 then 0 else 1)
  let (e2, s2) := e1.encodeDecision s1 ctxL1 ((cbpL >>> 1) &&& 1)
  let ctxL2 := 73 + (if (ca &&& 8) != 0 then 0 else 1) + 2 * (if (cbpL &&& 1) != 0 then 0 else 1)
  let (e3, s3) := e2.encodeDecision s2 ctxL2 ((cbpL >>> 2) &&& 1)
  let ctxL3 := 73 + (if (cbpL &&& 4) != 0 then 0 else 1) + 2 * (if (cbpL &&& 2) != 0 then 0 else 1)
  let (e4, s4) := e3.encodeDecision s3 ctxL3 ((cbpL >>> 3) &&& 1)
  if !hasChroma then (e4, s4)
  else
    let cca := match leftRec with | some r => r.cbpChroma | none => 0
    let ccb := match topRec with | some r => r.cbpChroma | none => 0
    let cbpC := (effCbp >>> 4) &&& 3
    let ctx0 := (if cca > 0 then 1 else 0) + (if ccb > 0 then 2 else 0)
    if cbpC == 0 then e4.encodeDecision s4 (77 + ctx0) 0
    else
      let (e5, s5) := e4.encodeDecision s4 (77 + ctx0) 1
      let ctx1 := 4 + (if cca == 2 then 1 else 0) + (if ccb == 2 then 2 else 0)
      e5.encodeDecision s5 (77 + ctx1) (if cbpC == 2 then 1 else 0)

private def cabacEncodeResidualMb (enc0 : CabacEnc) (st0 : Array UInt8) (g : MbGrid) (mx my : Nat)
    (hasChroma : Bool) (lastDqp : Int) (effCbp : Nat) (mb : MbSyntax) :
    Option (Int × CabacEnc × Array UInt8) := do
  if effCbp == 0 && mb.kind != .i16x16 then
    some (0, enc0, st0)
  else do
    let dqp := mb.mbQpDelta
    let (encA, stA, dqpOut) :=
      if dqp == 0 then
        let (e1, s1) := enc0.encodeDecision st0 (60 + (if lastDqp != 0 then 1 else 0)) 0
        (e1, s1, (0 : Int))
      else
        let (e1, s1) := enc0.encodeDecision st0 (60 + (if lastDqp != 0 then 1 else 0)) 1
        let v : Nat := if dqp > 0 then 2 * dqp.natAbs - 1 else 2 * dqp.natAbs
        let (e2, s2, cEnd) := Id.run do
          let mut eCur := e1
          let mut sCur := s1
          let mut cIdx := 62
          for _ in [:v - 1] do
            let (en, sn) := eCur.encodeDecision sCur cIdx 1
            eCur := en; sCur := sn; cIdx := 63
          return (eCur, sCur, cIdx)
        let (e3, s3) := e2.encodeDecision s2 cEnd 0
        (e3, s3, dqp)
    let mut encCur := encA
    let mut stCur := stA
    let mut curCbfL := Array.replicate 16 0
    let mut curCbfC := #[Array.replicate 4 0, Array.replicate 4 0]
    let isIntra := mb.kind.isIntra
    if mb.kind == .i16x16 then
      let c0 := cabacCbfCtx g mx my true 0 curCbfL curCbfC 0
      let (_, en, sn) ← cabacEncodeResidualBlock encCur stCur mb.i16Dc 0 16 (some c0)
      encCur := en; stCur := sn
      if (effCbp &&& 0xF) != 0 then
        for idx in [:16] do
          let cc := cabacCbfCtx g mx my true 1 curCbfL curCbfC idx
          let acArr := (mb.lumaAcOr4x4.getD idx #[]).extract 0 15
          let (nz, en2, sn2) ← cabacEncodeResidualBlock encCur stCur acArr 1 15 (some cc)
          encCur := en2; stCur := sn2
          curCbfL := curCbfL.set! idx nz
    else
      for i8 in [:4] do
        if (effCbp &&& (1 <<< i8)) != 0 then
          if mb.transform8x8 != 0 then
            let (_, en2, sn2) ← cabacEncodeResidualBlock encCur stCur (mb.luma8x8.getD i8 #[]) 5 64 none
            encCur := en2; stCur := sn2
            for sub in [:4] do
              curCbfL := curCbfL.set! (4 * i8 + sub) 1
          else
            for sub in [:4] do
              let idx := 4 * i8 + sub
              let cc := cabacCbfCtx g mx my isIntra 2 curCbfL curCbfC idx
              let (nz, en2, sn2) ← cabacEncodeResidualBlock encCur stCur (mb.lumaAcOr4x4.getD idx #[]) 2 16 (some cc)
              encCur := en2; stCur := sn2
              curCbfL := curCbfL.set! idx nz
    if hasChroma && (effCbp &&& 0x30) != 0 then
      for pl in [:2] do
        let cc := cabacCbfCtx g mx my isIntra 3 curCbfL curCbfC pl
        let (_, en2, sn2) ← cabacEncodeResidualBlock encCur stCur (mb.chromaDc.getD pl #[]) 3 4 (some cc)
        encCur := en2; stCur := sn2
      if (effCbp &&& 0x20) != 0 then
        for pl in [:2] do
          for ci in [:4] do
            let cc := cabacCbfCtx g mx my isIntra 4 curCbfL curCbfC (pl * 4 + ci)
            let (nz, en2, sn2) ← cabacEncodeResidualBlock encCur stCur (mb.chromaAc.getD (pl * 4 + ci) #[]) 4 15 (some cc)
            encCur := en2; stCur := sn2
            let pArr := (curCbfC.getD pl (Array.replicate 4 0)).set! ci nz
            curCbfC := curCbfC.set! pl pArr
    some (dqpOut, encCur, stCur)

private def cabacEncodeNonSkipMb (enc0 : CabacEnc) (st0 : Array UInt8) (sh : SliceHeaderFull)
    (sps : SpsFull) (pps : PpsFull) (g : MbGrid) (mx my : Nat) (lastDqp : Int) (mb : MbSyntax) :
    Option (MbGridRecord × Int × CabacEnc × Array UInt8) := do
  let hasChroma := sps.chromaFormatIdc == 1
  let leftRec := g.leftMb mx my
  let topRec := g.topMb mx my
  let isIntra := mb.kind.isIntra
  let (enc1, st1) ←
    if sh.sliceTypeNos == 2 then
      some (cabacEncodeIntraMbType enc0 st0 mb.intraIdx 3 true leftRec topRec)
    else if sh.sliceTypeNos == 0 then
      if isIntra then
        let (eA, sA) := enc0.encodeDecision st0 14 1
        some (cabacEncodeIntraMbType eA sA mb.intraIdx 17 false leftRec topRec)
      else
        let (eA, sA) := enc0.encodeDecision st0 14 0
        let pIdx := if mb.interIdx == 4 then 3 else mb.interIdx
        if pIdx == 0 || pIdx == 3 then
          let (eB, sB) := eA.encodeDecision sA 15 0
          some (eB.encodeDecision sB 16 (if pIdx == 3 then 1 else 0))
        else
          let (eB, sB) := eA.encodeDecision sA 15 1
          some (eB.encodeDecision sB 17 (if pIdx == 1 then 1 else 0))
    else
      if isIntra then
        let cL := match leftRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
        let cT := match topRec with | some r => if !r.isDirectMb then 1 else 0 | none => 0
        let (e1, s1) := enc0.encodeDecision st0 (27 + cL + cT) 1
        let (e2, s2) := e1.encodeDecision s1 30 1
        let (e3, s3) := e2.encodeDecision s2 31 1
        let (e4, s4) := e3.encodeDecision s3 32 1
        let (e5, s5) := e4.encodeDecision s4 32 0
        let (e6, s6) := e5.encodeDecision s5 32 1
        some (cabacEncodeIntraMbType e6 s6 mb.intraIdx 32 false leftRec topRec)
      else
        cabacEncodeBMbType enc0 st0 mb.interIdx leftRec topRec
  let t8CtxOff := (match leftRec with | some r => if r.is8x8Dct then 1 else 0 | none => 0) +
                  (match topRec with | some r => if r.is8x8Dct then 1 else 0 | none => 0)
  let effCbp := cabacEffectiveCbp mb
  if isIntra then
    if mb.kind == MbKind.iPcm then
      let encPcm := enc1.writePcmAndReinit mb.pcmBytes
      some (applyMbHeaderToRecord mb {}, 0, encPcm, st1)
    else do
      let mut encCur := enc1
      let mut stCur := st1
      if mb.kind == MbKind.iNxN then
        if pps.transform8x8ModeFlag != 0 then
          let (en, sn) := encCur.encodeDecision stCur (399 + t8CtxOff) mb.transform8x8
          encCur := en; stCur := sn
        for idx in [:mb.intraPred.size] do
          let (pf, rem) := mb.intraPred.getD idx (0, 0)
          let (eA, sA) := encCur.encodeDecision stCur 68 pf
          if pf != 0 then encCur := eA; stCur := sA
          else
            let (eB, sB) := eA.encodeDecision sA 69 (rem &&& 1)
            let (eC, sC) := eB.encodeDecision sB 69 ((rem >>> 1) &&& 1)
            let (eD, sD) := eC.encodeDecision sC 69 ((rem >>> 2) &&& 1)
            encCur := eD; stCur := sD
      if hasChroma then
        let cCtx := (match leftRec with | some r => if r.isIntra && r.chromaPredMode != 0 then 1 else 0 | none => 0) +
                    (match topRec with | some r => if r.isIntra && r.chromaPredMode != 0 then 1 else 0 | none => 0)
        if mb.chromaPredMode == 0 then
          let (en, sn) := encCur.encodeDecision stCur (64 + cCtx) 0
          encCur := en; stCur := sn
        else
          let (eA, sA) := encCur.encodeDecision stCur (64 + cCtx) 1
          if mb.chromaPredMode == 1 then
            let (en, sn) := eA.encodeDecision sA 67 0
            encCur := en; stCur := sn
          else
            let (eB, sB) := eA.encodeDecision sA 67 1
            let (en, sn) := eB.encodeDecision sB 67 (if mb.chromaPredMode == 2 then 0 else 1)
            encCur := en; stCur := sn
      if mb.kind != MbKind.i16x16 then
        let (en, sn) := cabacEncodeCbp encCur stCur effCbp hasChroma leftRec topRec
        encCur := en; stCur := sn
      let (dqpOut, encEnd, stEnd) ← cabacEncodeResidualMb encCur stCur g mx my hasChroma lastDqp effCbp mb
      let mbRecCopy : MbSyntax := {
        mb with
        cbp := effCbp,
        transform8x8 := if mb.kind == MbKind.iNxN || (effCbp &&& 0xF) != 0 then mb.transform8x8 else 0
      }
      let recDone := populateResidualGrid mbRecCopy (applyMbHeaderToRecord mbRecCopy {}) hasChroma
      some (recDone, dqpOut, encEnd, stEnd)
  else do
    let (recMot, enc2, st2) ← cabacEncodeInterMotion enc1 st1 sh g mx my mb
    let (enc3, st3) := cabacEncodeCbp enc2 st2 effCbp hasChroma leftRec topRec
    let mbChk : MbSyntax :=
      if mb.kind == .pInter && mb.interIdx == 4 then { mb with interIdx := 3 } else mb
    let (enc4, st4) :=
      if (effCbp &&& 0xF) != 0 && interDct8x8Allowed pps sps mbChk then
        enc3.encodeDecision st3 (399 + t8CtxOff) mb.transform8x8
      else (enc3, st3)
    let (dqpOut, encEnd, stEnd) ← cabacEncodeResidualMb enc4 st4 g mx my hasChroma lastDqp effCbp mb
    let mbRecCopy : MbSyntax := {
      mb with
      interIdx := if mb.kind == .pInter && mb.interIdx == 4 then 3 else mb.interIdx,
      cbp := effCbp,
      transform8x8 := if (effCbp &&& 0xF) != 0 then mb.transform8x8 else 0
    }
    let recDone := populateResidualGrid mbRecCopy (applyMbHeaderToRecord mbRecCopy recMot) hasChroma
    some (recDone, dqpOut, encEnd, stEnd)

private def encodeSliceCabacLoop (sh : SliceHeaderFull) (sps : SpsFull) (pps : PpsFull)
    (mbs : Array MbSyntax) :
    Nat → Nat → Nat → Int → CabacEnc → Array UInt8 → MbGrid → Option CabacEnc
  | 0, _, _, _, enc, _, _ => some enc
  | fuel + 1, i, mbIdx, lastDqp, enc, st, g =>
    if i ≥ mbs.size then some enc
    else
      let isLast := i + 1 == mbs.size
      let mb := mbs.getD i {}
      let mx := mbIdx % sps.picWidthInMbs
      let my := mbIdx / sps.picWidthInMbs
      let hasChroma := sps.chromaFormatIdc == 1
      let leftRec := g.leftMb mx my
      let topRec := g.topMb mx my
      let sCtx := (match leftRec with | some r => if !r.isSkip then 1 else 0 | none => 0) +
                  (match topRec with | some r => if !r.isSkip then 1 else 0 | none => 0) +
                  (if sh.sliceTypeNos == 1 then 13 else 0)
      if sh.sliceTypeNos != 2 && mb.isSkip then
        let (enc1, st1) := enc.encodeDecision st (11 + sCtx) 1
        let g1 := g.setMb mx my (buildCompleteMbRecord mb hasChroma)
        let enc2 := enc1.encodeTerminate (if isLast then 1 else 0)
        encodeSliceCabacLoop sh sps pps mbs fuel (i + 1) (mbIdx + 1) 0 enc2 st1 g1
      else do
        let (enc1, st1) :=
          if sh.sliceTypeNos != 2 then enc.encodeDecision st (11 + sCtx) 0
          else (enc, st)
        let (recDone, dqpOut, enc2, st2) ←
          cabacEncodeNonSkipMb enc1 st1 sh sps pps g mx my lastDqp mb
        let g1 := g.setMb mx my recDone
        let enc3 := enc2.encodeTerminate (if isLast then 1 else 0)
        encodeSliceCabacLoop sh sps pps mbs fuel (i + 1) (mbIdx + 1) dqpOut enc3 st2 g1

def encodeSliceCabac (sh : SliceHeaderFull) (mbs : Array MbSyntax)
    (sps : SpsFull) (pps : PpsFull) : Option ByteArray := do
  if mbs.size == 0 then none
  else
    let w0 := writeSliceHeaderFull BitWriter.empty sh true
    let enc0 := CabacEnc.init w0
    let st0 := initCabacStates sh.sliceTypeNos sh.cabacInitIdc sh.sliceQpY
    let g0 := MbGrid.init sps.picWidthInMbs sps.picHeightInMapUnits
    let encEnd ← encodeSliceCabacLoop sh sps pps mbs mbs.size 0 sh.firstMbInSlice 0 enc0 st0 g0
    some (writerToNal encEnd.w)

def transcodeSliceNal (nal : ByteArray) (spsList : Array (Option SpsFull))
    (ppsList : Array (Option PpsFull)) (mode : EntropyMode) : Option ByteArray := do
  let rbsp := stripNalEmulationBytes nal
  let (sh, bitPos) ← parseSliceHeaderFull rbsp spsList ppsList
  let pps ← findPps ppsList sh.ppsId
  let sps ← findSps spsList pps.spsId
  let mbs ←
    if pps.entropyCodingModeFlag == 0 then decodeSliceCavlc rbsp sh bitPos sps pps
    else decodeSliceCabac rbsp sh bitPos sps pps
  let dstCabac :=
    match mode with
    | .preserve => pps.entropyCodingModeFlag != 0
    | .cavlc => false
    | .cabac => true
  if dstCabac then encodeSliceCabac sh mbs sps pps
  else encodeSliceCavlc sh mbs sps pps

private def transcodeAnnexBLoop (nals : Array ByteArray) (mode : EntropyMode) :
    Nat → Nat → Array (Option SpsFull) → Array (Option PpsFull) → Array ByteArray → Except String (Array ByteArray)
  | 0, _, _, _, out => .ok out
  | fuel + 1, idx, spsList, ppsList, out =>
    if idx ≥ nals.size then .ok out
    else
      let nal := nals.getD idx { data := #[] }
      if nal.data.size == 0 then
        .error "Empty H.264 NAL unit"
      else
        let nt := (nal.data.getD 0 0 &&& 0x1F).toNat
        if nt == 7 then
          match parseSpsFull nal with
          | none => .error "Unsupported or malformed H.264 SPS NAL"
          | some sps =>
            let spsList' := spsList.set! sps.spsId (some sps)
            let outNal := if mode == .cabac then upgradeSpsForCabac sps else nal
            transcodeAnnexBLoop nals mode fuel (idx + 1) spsList' ppsList (out.push outNal)
        else if nt == 8 then
          match parsePpsFull nal spsList with
          | none => .error "Unsupported or malformed H.264 PPS NAL"
          | some pps =>
            let ppsList' := ppsList.set! pps.ppsId (some pps)
            let ovr : Option Nat := match mode with
              | .cavlc => some 0
              | .cabac => some 1
              | .preserve => none
            let outNal := serializePps pps ovr
            transcodeAnnexBLoop nals mode fuel (idx + 1) spsList ppsList' (out.push outNal)
        else if nt == 1 || nt == 5 then
          match transcodeSliceNal nal spsList ppsList mode with
          | none => .error "Failed to entropy-transcode H.264 slice NAL"
          | some newNal =>
            transcodeAnnexBLoop nals mode fuel (idx + 1) spsList ppsList (out.push newNal)
        else if nt == 2 || nt == 3 || nt == 4 then
          .error "Unsupported H.264 data-partitioned slice NAL"
        else
          transcodeAnnexBLoop nals mode fuel (idx + 1) spsList ppsList (out.push nal)

def transcodeAnnexB (stream : ByteArray) (mode : EntropyMode := .preserve) : Except String ByteArray := do
  let nals := splitAnnexB stream
  if nals.size == 0 then
    .error "No H.264 Annex-B NAL units found"
  else
    let spsInit : Array (Option SpsFull) := Array.replicate 32 none
    let ppsInit : Array (Option PpsFull) := Array.replicate 256 none
    let outNals ← transcodeAnnexBLoop nals mode nals.size 0 spsInit ppsInit #[]
    .ok (joinAnnexB outNals)

end LeanAV.H264Entropy
