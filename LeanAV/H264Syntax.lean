/-
  LeanAV.H264Syntax: Verified H.264 / AVC NALU Framing, RBSP/EBSP, `avcC`,
  Sequence Parameter Set (`SPS`), Picture Parameter Set (`PPS`), Slice Header,
  and Picture Order Count (`POC` Type 0 & Type 2) Syntax Engine.
  (`ISO/IEC 14496-10` §7.3–7.4, §8.2.1, Annex E & `ISO/IEC 14496-15`)
-/
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Bitstream
import LeanAV.Video

namespace LeanAV.H264Syntax

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Bitstream
open LeanAV.Video

/-! ## 1. RBSP / EBSP Emulation Prevention (`0x000003`) & RBSP Trailing Stop-Bits -/

/-- Structural state-machine inserting H.264 `0x03` emulation prevention bytes
    whenever two consecutive `0x00` bytes precede `0x00`, `0x01`, `0x02`, or `0x03`. -/
def insertRbspEmulLoop (z0 z1 : Bool) : List UInt8 → List UInt8
  | [] => []
  | b :: rest =>
    if z0 && z1 && b ≤ 3 then
      (0x03 : UInt8) :: b :: insertRbspEmulLoop false (b == 0) rest
    else
      b :: insertRbspEmulLoop z1 (b == 0) rest

/-- Structural state-machine stripping H.264 `0x03` emulation prevention bytes
    after two consecutive `0x00` bytes (`ISO/IEC 14496-10` §7.4.1). -/
def stripRbspEmulLoop (z0 z1 : Bool) : List UInt8 → List UInt8
  | [] => []
  | b :: rest =>
    if z0 && z1 && b == 3 then
      stripRbspEmulLoop false false rest
    else
      b :: stripRbspEmulLoop z1 (b == 0) rest

/-- Pure list-level RBSP -> EBSP encoder (`insertRbspEmulationList`). -/
@[inline]
def insertRbspEmulationList (rbsp : List UInt8) : List UInt8 :=
  insertRbspEmulLoop false false rbsp

/-- Pure list-level EBSP -> RBSP decoder (`stripRbspEmulationList`). -/
@[inline]
def stripRbspEmulationList (ebsp : List UInt8) : List UInt8 :=
  stripRbspEmulLoop false false ebsp

/-- Insert `0x03` emulation prevention bytes into an RBSP `ByteArray` AFTER byte 0 (the 1-byte NAL header),
    or across the full payload when `hasNalHeader == false`. -/
def insertRbspEmulationBytes (rbsp : ByteArray) (hasNalHeader : Bool := true) : ByteArray :=
  if hasNalHeader then
    match rbsp.data.toList with
    | [] => ByteArray.empty
    | hdr :: body => ByteArray.mk (hdr :: insertRbspEmulationList body).toArray
  else
    ByteArray.mk (insertRbspEmulationList rbsp.data.toList).toArray

/-- Strip `0x03` emulation prevention bytes from an EBSP `ByteSlice` (preserving byte 0 NAL header when `hasNalHeader == true`). -/
def stripRbspEmulationBytesH264 (ebsp : ByteSlice) (hasNalHeader : Bool := true) : ByteArray :=
  let xs := (ebsp.ba.data.toList.drop ebsp.off).take ebsp.len
  if hasNalHeader then
    match xs with
    | [] => ByteArray.empty
    | hdr :: body => ByteArray.mk (hdr :: stripRbspEmulationList body).toArray
  else
    ByteArray.mk (stripRbspEmulationList xs).toArray

/-- Write `rbsp_trailing_bits()` (`1` stop bit followed by `0` alignment bits) and finalize `BitWriter`. -/
@[inline]
def finalizeRbspWriter (w : BitWriter) : ByteArray :=
  (w.writeBit 1).toByteArray

/-- Pure kernel-reducible byte lookup (`ByteArray.get!` is opaque under default transparency). -/
@[inline]
def byteAtPure (b : ByteArray) (i : Nat) : UInt8 :=
  b.data.getD i 0

/-- Compute the exact bit-length of an RBSP `ByteArray` BEFORE `rbsp_trailing_bits()` (`ISO/IEC 14496-10` §7.2 `more_rbsp_data`). -/
def rbspPayloadBitLen (rbsp : ByteArray) : Option Nat :=
  let n := rbsp.data.size
  let rec findLast (fuel : Nat) (idx : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if idx == 0 then none
      else if byteAtPure rbsp (idx - 1) == 0 then findLast fuel' (idx - 1)
      else some idx
  match findLast n n with
  | none => none
  | some idx =>
    let lastByte := byteAtPure rbsp (idx - 1)
    let rec countTz (fuel : Nat) (tz : Nat) : Nat :=
      match fuel with
      | 0 => tz
      | fuel' + 1 =>
        if tz < 8 && ((lastByte >>> tz.toUInt8) &&& 1) == 0 then countTz fuel' (tz + 1)
        else tz
    let tz := countTz 8 0
    some ((idx - 1) * 8 + (7 - tz))

/-- Implements `more_rbsp_data()` (`ISO/IEC 14496-10` §7.2): true iff unread payload bits precede the final RBSP `1` stop bit. -/
@[inline]
def moreRbspData (r : BitReader) (payloadBits : Nat) : Bool :=
  r.bitOffset < payloadBits

/-! ## 2. Annex-B <-> AVCC Framing & `ISO/IEC 14496-15` `AVCDecoderConfigurationRecord` (`avcC`) -/

/-- Validate AVCC length field size (`nalLengthSize ∈ {1, 2, 4}`). -/
@[inline]
def isValidAvccLengthSize (nalLengthSize : Nat) : Bool :=
  nalLengthSize == 1 || nalLengthSize == 2 || nalLengthSize == 4

/-- Read big-endian unsigned integer of `n` bytes (`n ∈ {1, 2, 4}`) at `off`. -/
def readBigEndianN (b : ByteArray) (off n : Nat) : Option Nat :=
  if off + n > b.data.size then none
  else if n == 1 then some (byteAtPure b off).toNat
  else if n == 2 then
    some (((byteAtPure b off).toNat <<< 8) ||| (byteAtPure b (off + 1)).toNat)
  else if n == 4 then
    some (((byteAtPure b off).toNat <<< 24) ||| ((byteAtPure b (off + 1)).toNat <<< 16) |||
          ((byteAtPure b (off + 2)).toNat <<< 8) ||| (byteAtPure b (off + 3)).toNat)
  else none

/-- Append a single byte using kernel-reducible `Array.push` (`ByteArray.push` is C-opaque to `decide`). -/
@[inline]
def pushBytePure (b : ByteArray) (v : UInt8) : ByteArray :=
  { data := b.data.push v }

/-- Empty `ByteArray` literal reducible in the kernel (`ByteArray.empty` uses C-opaque `mkEmpty`). -/
@[inline]
def emptyBytesPure : ByteArray :=
  { data := #[] }

/-- Append big-endian `val` in `n` bytes (`n ∈ {1, 2, 4}`) if `val` fits in `8 * n` bits. -/
def pushBigEndianN (out : ByteArray) (val n : Nat) : Option ByteArray :=
  if n == 1 then
    if val ≤ 0xFF then some (pushBytePure out val.toUInt8) else none
  else if n == 2 then
    if val ≤ 0xFFFF then
      some (pushBytePure (pushBytePure out ((val >>> 8) &&& 0xFF).toUInt8) (val &&& 0xFF).toUInt8)
    else none
  else if n == 4 then
    if val ≤ 0xFFFFFFFF then
      some (pushBytePure (pushBytePure (pushBytePure (pushBytePure out
              ((val >>> 24) &&& 0xFF).toUInt8) ((val >>> 16) &&& 0xFF).toUInt8)
              ((val >>> 8) &&& 0xFF).toUInt8) (val &&& 0xFF).toUInt8)
    else none
  else none

/-- Pure kernel-reducible sub-slice extraction `b[start .. stop)` (`ByteArray.extract` is C-opaque to `decide`). -/
@[inline]
def extractBytesPure (b : ByteArray) (start stop : Nat) : ByteArray :=
  { data := (b.data.toList.drop start |>.take (stop - start)).toArray }

/-- Pure kernel-reducible concatenation `a ++ b` (`ByteArray.append` is C-opaque to `decide`). -/
@[inline]
def appendBytesPure (a b : ByteArray) : ByteArray :=
  { data := a.data ++ b.data }

/-- Parse an AVCC length-prefixed packet (`nalLengthSize ∈ {1, 2, 4}`) into raw NALU `ByteArray`s
    (fails closed on truncation or zero length). -/
def splitAvccPacket (pkt : ByteArray) (nalLengthSize : Nat := 4) : Option (Array ByteArray) :=
  if !isValidAvccLengthSize nalLengthSize then none
  else
    let pktLen := pkt.data.size
    let rec loop (fuel : Nat) (off : Nat) (out : Array ByteArray) : Option (Array ByteArray) :=
      if off ≥ pktLen then
        if off == pktLen then some out else none
      else
        match fuel with
        | 0 => none
        | fuel' + 1 =>
          match readBigEndianN pkt off nalLengthSize with
          | none => none
          | some nalLen =>
            if nalLen == 0 || off + nalLengthSize + nalLen > pktLen then none
            else
              let start := off + nalLengthSize
              loop fuel' (start + nalLen) (out.push (extractBytesPure pkt start (start + nalLen)))
    loop (pktLen + 1) 0 #[]

/-- Pack an array of non-empty NALU `ByteArray`s into an AVCC length-prefixed packet (`nalLengthSize ∈ {1, 2, 4}`). -/
def packAvccPacket (nalus : Array ByteArray) (nalLengthSize : Nat := 4) : Option ByteArray := Id.run do
  if !isValidAvccLengthSize nalLengthSize then return none
  let mut out := emptyBytesPure
  for nal in nalus.toList do
    if nal.data.size == 0 then return none
    match pushBigEndianN out nal.data.size nalLengthSize with
    | none => return none
    | some nextOut => out := appendBytesPure nextOut nal
  return some out

/-- Pack NALU `ByteArray`s into a canonical 4-byte (`0x00000001`) Annex-B byte stream. -/
def packAnnexBPacket (nalus : Array ByteArray) : Option ByteArray := Id.run do
  let mut out := emptyBytesPure
  for nal in nalus.toList do
    if nal.data.size == 0 then return none
    out := appendBytesPure (pushBytePure (pushBytePure (pushBytePure (pushBytePure out 0) 0) 0) 1) nal
  return some out

/-- Extract raw NALU `ByteArray`s from an Annex-B byte stream (`0x000001` or `0x00000001` start codes). -/
def splitAnnexBPacket (annexB : ByteArray) : Array ByteArray := Id.run do
  let views := scanAnnexBNalUnitsFast (ByteSlice.ofByteArray annexB) false
  let mut out : Array ByteArray := #[]
  for v in views do
    out := out.push (extractBytesPure v.payload.ba v.payload.off (v.payload.off + v.payload.len))
  return out

/-- Convert an Annex-B byte stream into an AVCC packet (`nalLengthSize ∈ {1, 2, 4}`). -/
@[inline]
def annexBToAvccPacket (annexB : ByteArray) (nalLengthSize : Nat := 4) : Option ByteArray :=
  packAvccPacket (splitAnnexBPacket annexB) nalLengthSize

/-- Convert an AVCC packet (`nalLengthSize ∈ {1, 2, 4}`) into a canonical 4-byte Annex-B byte stream. -/
@[inline]
def avccToAnnexBPacket (avcc : ByteArray) (nalLengthSize : Nat := 4) : Option ByteArray := do
  let nalus ← splitAvccPacket avcc nalLengthSize
  packAnnexBPacket nalus

/-- True when `profileIdc` carries High-profile chroma/bit-depth/scaling extensions in `SPS` (`ISO/IEC 14496-10` §7.3.2.1.1). -/
@[inline]
def isH264HighExtProfile (profileIdc : UInt8) : Bool :=
  profileIdc == 100 || profileIdc == 110 || profileIdc == 122 || profileIdc == 244 ||
  profileIdc == 44  || profileIdc == 83  || profileIdc == 86  || profileIdc == 118 ||
  profileIdc == 128 || profileIdc == 138 || profileIdc == 139 || profileIdc == 134 ||
  profileIdc == 135

/-- True when `avcC` (`ISO/IEC 14496-15` §5.3.3.1.2) permits/requires the High-profile
    extension trailer (`100`, `110`, `122`, `144` / `244` etc.). -/
@[inline]
def isAvccExtProfile (profileIdc : UInt8) : Bool :=
  profileIdc == 100 || profileIdc == 110 || profileIdc == 122 || profileIdc == 144 ||
  profileIdc == 244 || profileIdc == 44  || profileIdc == 83  || profileIdc == 86  ||
  profileIdc == 118 || profileIdc == 128

/-- `ISO/IEC 14496-15` `AVCDecoderConfigurationRecord` (`avcC` box payload). -/
structure AvcDecoderConfigRecord where
  configurationVersion : UInt8 := 1
  avcProfileIndication : UInt8
  profileCompatibility : UInt8
  avcLevelIndication   : UInt8
  lengthSizeMinusOne   : UInt8 := 3
  spsNalus             : Array ByteArray
  ppsNalus             : Array ByteArray
  hasHighExt           : Bool := false
  chromaFormatIdc      : UInt8 := 1
  bitDepthLumaMinus8   : UInt8 := 0
  bitDepthChromaMinus8 : UInt8 := 0
  spsExtNalus          : Array ByteArray := #[]
  deriving DecidableEq, Inhabited

/-- Structural validation predicate for `AvcDecoderConfigRecord`. -/
def AvcDecoderConfigRecord.isValid (rec : AvcDecoderConfigRecord) : Bool :=
  let nls := rec.lengthSizeMinusOne.toNat + 1
  rec.configurationVersion == 1 &&
  isValidAvccLengthSize nls &&
  rec.spsNalus.size ≤ 31 &&
  rec.ppsNalus.size ≤ 255 &&
  rec.spsNalus.toList.all (fun b => b.data.size > 0 && b.data.size ≤ 0xFFFF) &&
  rec.ppsNalus.toList.all (fun b => b.data.size > 0 && b.data.size ≤ 0xFFFF) &&
  (!rec.hasHighExt ||
    (isAvccExtProfile rec.avcProfileIndication &&
     rec.chromaFormatIdc ≤ 3 &&
     rec.bitDepthLumaMinus8 ≤ 7 &&
     rec.bitDepthChromaMinus8 ≤ 7 &&
     rec.spsExtNalus.size ≤ 255 &&
     rec.spsExtNalus.toList.all (fun b => b.data.size > 0 && b.data.size ≤ 0xFFFF)))

/-- Parse `count` length-prefixed (`2`-byte big-endian) NALU slices starting at `off`. -/
def parseAvccNaluList (buf : ByteArray) (count : Nat) (off : Nat) (acc : Array ByteArray)
    : Option (Array ByteArray × Nat) :=
  match count with
  | 0 => some (acc, off)
  | count' + 1 =>
    match readBigEndianN buf off 2 with
    | none => none
    | some nlen =>
      if nlen == 0 || off + 2 + nlen > buf.data.size then none
      else
        parseAvccNaluList buf count' (off + 2 + nlen)
          (acc.push (extractBytesPure buf (off + 2) (off + 2 + nlen)))

/-- Parse an `AVCDecoderConfigurationRecord` (`avcC`) payload (`ISO/IEC 14496-15` §5.3.3.1.2). -/
def parseAvcDecoderConfigRecord (buf : ByteArray) : Option AvcDecoderConfigRecord :=
  let bufLen := buf.data.size
  if bufLen < 7 then none
  else
    let ver := byteAtPure buf 0
    if ver != 1 then none
    else
      let prof := byteAtPure buf 1
      let compat := byteAtPure buf 2
      let lvl := byteAtPure buf 3
      let lenMinusOne := byteAtPure buf 4 &&& 0x03
      if !isValidAvccLengthSize (lenMinusOne.toNat + 1) then none
      else
        let numSps := (byteAtPure buf 5 &&& 0x1F).toNat
        match parseAvccNaluList buf numSps 6 #[] with
        | none => none
        | some (spsArr, off1) =>
          if off1 ≥ bufLen then none
          else
            let numPps := (byteAtPure buf off1).toNat
            match parseAvccNaluList buf numPps (off1 + 1) #[] with
            | none => none
            | some (ppsArr, off2) =>
              if off2 == bufLen then
                some {
                  configurationVersion := ver, avcProfileIndication := prof,
                  profileCompatibility := compat, avcLevelIndication := lvl,
                  lengthSizeMinusOne := lenMinusOne, spsNalus := spsArr, ppsNalus := ppsArr
                }
              else if !isAvccExtProfile prof || off2 + 4 > bufLen then none
              else
                let chromaFmt := byteAtPure buf off2 &&& 0x03
                let bdLuma := byteAtPure buf (off2 + 1) &&& 0x07
                let bdChroma := byteAtPure buf (off2 + 2) &&& 0x07
                let numSpsExt := (byteAtPure buf (off2 + 3)).toNat
                match parseAvccNaluList buf numSpsExt (off2 + 4) #[] with
                | none => none
                | some (spsExtArr, off3) =>
                  if off3 != bufLen then none
                  else
                    some {
                      configurationVersion := ver, avcProfileIndication := prof,
                      profileCompatibility := compat, avcLevelIndication := lvl,
                      lengthSizeMinusOne := lenMinusOne, spsNalus := spsArr, ppsNalus := ppsArr,
                      hasHighExt := true, chromaFormatIdc := chromaFmt,
                      bitDepthLumaMinus8 := bdLuma, bitDepthChromaMinus8 := bdChroma,
                      spsExtNalus := spsExtArr
                    }

/-- Deterministically serialize an `AvcDecoderConfigRecord` into an `ISO/IEC 14496-15` `avcC` payload. -/
def serializeAvcDecoderConfigRecord (rec : AvcDecoderConfigRecord) : Option ByteArray := Id.run do
  if !rec.isValid then return none
  let mut out := emptyBytesPure
  out := pushBytePure out 1
  out := pushBytePure out rec.avcProfileIndication
  out := pushBytePure out rec.profileCompatibility
  out := pushBytePure out rec.avcLevelIndication
  out := pushBytePure out (0xFC ||| (rec.lengthSizeMinusOne &&& 0x03))
  out := pushBytePure out (0xE0 ||| rec.spsNalus.size.toUInt8)
  for sps in rec.spsNalus.toList do
    match pushBigEndianN out sps.data.size 2 with
    | none => return none
    | some nextOut => out := appendBytesPure nextOut sps
  out := pushBytePure out rec.ppsNalus.size.toUInt8
  for pps in rec.ppsNalus.toList do
    match pushBigEndianN out pps.data.size 2 with
    | none => return none
    | some nextOut => out := appendBytesPure nextOut pps
  if rec.hasHighExt then
    out := pushBytePure out (0xFC ||| (rec.chromaFormatIdc &&& 0x03))
    out := pushBytePure out (0xF8 ||| (rec.bitDepthLumaMinus8 &&& 0x07))
    out := pushBytePure out (0xF8 ||| (rec.bitDepthChromaMinus8 &&& 0x07))
    out := pushBytePure out rec.spsExtNalus.size.toUInt8
    for ext in rec.spsExtNalus.toList do
      match pushBigEndianN out ext.data.size 2 with
      | none => return none
      | some nextOut => out := appendBytesPure nextOut ext
  return some out

/-! ## 3. Default & Delta-Coded Scaling Matrices (`ISO/IEC 14496-10` Tables 7-2, 7-3, 7-4) -/

/-- Default 4x4 Intra scaling list (`Default_4x4_Intra`, `ISO/IEC 14496-10` Table 7-3). -/
def defaultScalingList4x4Intra : Array UInt8 := #[
  6, 13, 13, 20, 20, 20, 28, 28, 28, 28, 32, 32, 32, 37, 37, 42
]

/-- Default 4x4 Inter scaling list (`Default_4x4_Inter`, `ISO/IEC 14496-10` Table 7-3). -/
def defaultScalingList4x4Inter : Array UInt8 := #[
  10, 14, 14, 20, 20, 20, 24, 24, 24, 24, 27, 27, 27, 30, 30, 34
]

/-- Default 8x8 Intra scaling list (`Default_8x8_Intra`, `ISO/IEC 14496-10` Table 7-4). -/
def defaultScalingList8x8Intra : Array UInt8 := #[
  6, 10, 10, 13, 11, 13, 16, 16, 16, 16, 18, 18, 18, 18, 18, 23,
  23, 23, 23, 23, 23, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27,
  27, 27, 27, 27, 29, 29, 29, 29, 29, 29, 29, 31, 31, 31, 31, 31,
  31, 33, 33, 33, 33, 33, 36, 36, 36, 36, 38, 38, 38, 40, 40, 42
]

/-- Default 8x8 Inter scaling list (`Default_8x8_Inter`, `ISO/IEC 14496-10` Table 7-4). -/
def defaultScalingList8x8Inter : Array UInt8 := #[
  9, 13, 13, 15, 13, 15, 17, 17, 17, 17, 19, 19, 19, 19, 19, 21,
  21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 24, 24, 24, 24,
  24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27,
  27, 28, 28, 28, 28, 28, 30, 30, 30, 30, 32, 32, 32, 33, 33, 35
]

/-- Flat (all `16`) 4x4 scaling list when `seq_scaling_matrix_present_flag == 0`. -/
def flatScalingList4x4 : Array UInt8 := Array.replicate 16 (16 : UInt8)

/-- Flat (all `16`) 8x8 scaling list when `seq_scaling_matrix_present_flag == 0`. -/
def flatScalingList8x8 : Array UInt8 := Array.replicate 64 (16 : UInt8)

/-- Signalled scaling-list entry in an SPS or PPS (`absent`, `useDefault`, or explicit `custom` weights in `1..255`). -/
inductive ScalingListSyntax where
  | absent
  | useDefault
  | custom (weights : Array UInt8)
  deriving Repr, DecidableEq, Inhabited

/-- Parse `scaling_list(scalingList, sizeOfScalingList, useDefaultScalingMatrixFlag)` (`ISO/IEC 14496-10` §7.3.2.1.1.1). -/
def parseScalingListSyntax (r0 : BitReader) (size : Nat) : Option (ScalingListSyntax × BitReader) := Id.run do
  let mut r := r0
  let mut lastScale : Int := 8
  let mut nextScale : Int := 8
  let mut useDefault := false
  let mut out : Array UInt8 := #[]
  for j in [:size] do
    if nextScale != 0 then
      match r.readSE with
      | none => return none
      | some (deltaScale, rNext) =>
        r := rNext
        let d : Int := deltaScale.toInt
        if d < -128 || d > 127 then return none
        nextScale := (lastScale + d + 256) % 256
        if j == 0 && nextScale == 0 then
          useDefault := true
    let curScale : Int := if nextScale == 0 then lastScale else nextScale
    out := out.push curScale.toNat.toUInt8
    lastScale := curScale
  if useDefault then
    return some (.useDefault, r)
  else
    return some (.custom out, r)

/-- Serialize `ScalingListSyntax` (`present_flag` + `scaling_list` `se(v)` deltas) deterministically. -/
def writeScalingListSyntax (w0 : BitWriter) (entry : ScalingListSyntax) (size : Nat) : Option BitWriter := Id.run do
  match entry with
  | .absent => return some (w0.writeBit 0)
  | .useDefault =>
    let w1 := w0.writeBit 1
    return some (w1.writeSE (-8))
  | .custom weights =>
    if weights.size != size then return none
    if weights.toList.any (fun v => v == 0) then return none
    let mut w := w0.writeBit 1
    let mut lastScale : Int := 8
    for j in [:size] do
      let target : Int := (weights.getD j 16).toNat
      let mut tailConst : Bool := decide (j > 0)
      if tailConst then
        for k in [j:size] do
          if ((weights.getD k 16).toNat : Int) != lastScale then
            tailConst := false
      if tailConst then
        let rawDelta : Int := (0 - lastScale) % 256
        let signedDelta : Int := if rawDelta > 127 then rawDelta - 256 else rawDelta
        w := w.writeSE (Int32.ofInt signedDelta)
        return some w
      else
        let rawDelta : Int := (target - lastScale) % 256
        let signedDelta : Int := if rawDelta > 127 then rawDelta - 256 else rawDelta
        w := w.writeSE (Int32.ofInt signedDelta)
        lastScale := target
    return some w

/-- Resolve the effective 6×16 (`4x4`) and 6×64 (`8x8`) SPS scaling matrices (`ISO/IEC 14496-10` Table 7-2 Rule A). -/
def resolveSpsScalingMatrices (seqPresent : Bool) (lists4x4 : Array ScalingListSyntax) (lists8x8 : Array ScalingListSyntax)
    : Array (Array UInt8) × Array (Array UInt8) := Id.run do
  if !seqPresent then
    return (Array.replicate 6 flatScalingList4x4, Array.replicate 6 flatScalingList8x8)
  let mut eff4 : Array (Array UInt8) := #[]
  for i in [:6] do
    let defList := if i < 3 then defaultScalingList4x4Intra else defaultScalingList4x4Inter
    let resolved := match lists4x4.getD i .absent with
      | .custom w => w
      | .useDefault => defList
      | .absent =>
        if i == 0 then defaultScalingList4x4Intra
        else if i == 3 then defaultScalingList4x4Inter
        else eff4.getD (i - 1) defList
    eff4 := eff4.push resolved
  let mut eff8 : Array (Array UInt8) := #[]
  for k in [:6] do
    let defList := if k % 2 == 0 then defaultScalingList8x8Intra else defaultScalingList8x8Inter
    let resolved := match lists8x8.getD k .absent with
      | .custom w => w
      | .useDefault => defList
      | .absent =>
        if k < 2 then defList
        else eff8.getD (k - 2) defList
    eff8 := eff8.push resolved
  return (eff4, eff8)

/-- Resolve the effective PPS scaling matrices on top of SPS (`ISO/IEC 14496-10` Table 7-2 Rule B). -/
def resolvePpsScalingMatrices (spsSeqPresent : Bool) (spsEff4 spsEff8 : Array (Array UInt8))
    (picPresent : Bool) (lists4x4 : Array ScalingListSyntax) (lists8x8 : Array ScalingListSyntax)
    : Array (Array UInt8) × Array (Array UInt8) := Id.run do
  if !picPresent then
    return (spsEff4, spsEff8)
  let mut eff4 : Array (Array UInt8) := #[]
  for i in [:6] do
    let defList := if i < 3 then defaultScalingList4x4Intra else defaultScalingList4x4Inter
    let resolved := match lists4x4.getD i .absent with
      | .custom w => w
      | .useDefault => defList
      | .absent =>
        if i == 0 then (if spsSeqPresent then spsEff4.getD 0 defaultScalingList4x4Intra else defaultScalingList4x4Intra)
        else if i == 3 then (if spsSeqPresent then spsEff4.getD 3 defaultScalingList4x4Inter else defaultScalingList4x4Inter)
        else eff4.getD (i - 1) defList
    eff4 := eff4.push resolved
  let mut eff8 : Array (Array UInt8) := #[]
  for k in [:6] do
    let defList := if k % 2 == 0 then defaultScalingList8x8Intra else defaultScalingList8x8Inter
    let resolved := match lists8x8.getD k .absent with
      | .custom w => w
      | .useDefault => defList
      | .absent =>
        if k < 2 then (if spsSeqPresent then spsEff8.getD k defList else defList)
        else eff8.getD (k - 2) defList
    eff8 := eff8.push resolved
  return (eff4, eff8)

/-! ## 4. Full Sequence Parameter Set (`SPS`, `nal_unit_type = 7`, `ISO/IEC 14496-10` §7.3.2.1.1 & Annex E VUI) -/

/-- `hrd_parameters()` syntax (`ISO/IEC 14496-10` Annex E §E.1.2). -/
structure H264HrdParameters where
  cpbCntMinus1                       : UInt8 := 0
  bitRateScale                       : UInt8 := 0
  cpbSizeScale                       : UInt8 := 0
  bitRateValueMinus1                 : Array UInt32 := #[0]
  cpbSizeValueMinus1                 : Array UInt32 := #[0]
  cbrFlag                            : Array Bool := #[false]
  initialCpbRemovalDelayLengthMinus1 : UInt8 := 23
  cpbRemovalDelayLengthMinus1        : UInt8 := 23
  dpbOutputDelayLengthMinus1         : UInt8 := 23
  timeOffsetLength                   : UInt8 := 24
  deriving Repr, DecidableEq, Inhabited

/-- `vui_parameters()` syntax (`ISO/IEC 14496-10` Annex E §E.1.1). -/
structure H264VuiParameters where
  aspectRatioInfoPresentFlag         : Bool := false
  aspectRatioIdc                     : UInt8 := 0
  sarWidth                           : UInt16 := 0
  sarHeight                          : UInt16 := 0
  overscanInfoPresentFlag            : Bool := false
  overscanAppropriateFlag            : Bool := false
  videoSignalTypePresentFlag         : Bool := false
  videoFormat                        : UInt8 := 5
  videoFullRangeFlag                 : Bool := false
  colourDescriptionPresentFlag       : Bool := false
  colourPrimaries                    : UInt8 := 2
  transferCharacteristics            : UInt8 := 2
  matrixCoefficients                 : UInt8 := 2
  chromaLocInfoPresentFlag           : Bool := false
  chromaSampleLocTypeTopField        : UInt8 := 0
  chromaSampleLocTypeBottomField     : UInt8 := 0
  timingInfoPresentFlag              : Bool := false
  numUnitsInTick                     : UInt32 := 0
  timeScale                          : UInt32 := 0
  fixedFrameRateFlag                 : Bool := false
  nalHrdParametersPresentFlag        : Bool := false
  nalHrd                             : H264HrdParameters := {}
  vclHrdParametersPresentFlag        : Bool := false
  vclHrd                             : H264HrdParameters := {}
  lowDelayHrdFlag                    : Bool := false
  picStructPresentFlag               : Bool := false
  bitstreamRestrictionFlag           : Bool := false
  motionVectorsOverPicBoundariesFlag : Bool := true
  maxBytesPerPicDenom                : UInt8 := 2
  maxBitsPerMbDenom                  : UInt8 := 1
  log2MaxMvLengthHorizontal          : UInt8 := 16
  log2MaxMvLengthVertical            : UInt8 := 16
  maxNumReorderFrames                : UInt8 := 0
  maxDecFrameBuffering               : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Parse `hrd_parameters()` (`ISO/IEC 14496-10` Annex E §E.1.2). -/
def parseH264HrdParameters (r0 : BitReader) : Option (H264HrdParameters × BitReader) := Id.run do
  match r0.readUE with
  | none => return none
  | some (cpbCntM1, r1) =>
    if cpbCntM1 > 31 then return none
    match r1.readBitsMSB 4 with
    | none => return none
    | some (brScale, r2) =>
      match r2.readBitsMSB 4 with
      | none => return none
      | some (csScale, r3) =>
        let cnt := cpbCntM1.toNat + 1
        let mut r := r3
        let mut brVals : Array UInt32 := #[]
        let mut csVals : Array UInt32 := #[]
        let mut cbrFlags : Array Bool := #[]
        for _ in [:cnt] do
          match r.readUE with
          | none => return none
          | some (brM1, rA) =>
            if brM1 > 0xFFFFFFFE then return none
            match rA.readUE with
            | none => return none
            | some (csM1, rB) =>
              if csM1 > 0xFFFFFFFE then return none
              match rB.readBit with
              | none => return none
              | some (cbrBit, rC) =>
                brVals := brVals.push brM1.toUInt32
                csVals := csVals.push csM1.toUInt32
                cbrFlags := cbrFlags.push (cbrBit == 1)
                r := rC
        match r.readBitsMSB 20 with
        | none => return none
        | some (lens, rEnd) =>
          let initLen := ((lens >>> 15) &&& 0x1F).toUInt8
          let cpbLen  := ((lens >>> 10) &&& 0x1F).toUInt8
          let dpbLen  := ((lens >>> 5) &&& 0x1F).toUInt8
          let toLen   := (lens &&& 0x1F).toUInt8
          return some ({
            cpbCntMinus1 := cpbCntM1.toUInt8, bitRateScale := brScale.toUInt8,
            cpbSizeScale := csScale.toUInt8, bitRateValueMinus1 := brVals,
            cpbSizeValueMinus1 := csVals, cbrFlag := cbrFlags,
            initialCpbRemovalDelayLengthMinus1 := initLen,
            cpbRemovalDelayLengthMinus1 := cpbLen,
            dpbOutputDelayLengthMinus1 := dpbLen,
            timeOffsetLength := toLen
          }, rEnd)

/-- Serialize `H264HrdParameters` (`ISO/IEC 14496-10` Annex E §E.1.2). -/
def writeH264HrdParameters (w0 : BitWriter) (hrd : H264HrdParameters) : Option BitWriter := Id.run do
  let cnt := hrd.cpbCntMinus1.toNat + 1
  if hrd.cpbCntMinus1 > 31 || hrd.bitRateScale > 15 || hrd.cpbSizeScale > 15 then return none
  if hrd.bitRateValueMinus1.size != cnt || hrd.cpbSizeValueMinus1.size != cnt || hrd.cbrFlag.size != cnt then return none
  if hrd.initialCpbRemovalDelayLengthMinus1 > 31 || hrd.cpbRemovalDelayLengthMinus1 > 31 ||
     hrd.dpbOutputDelayLengthMinus1 > 31 || hrd.timeOffsetLength > 31 then return none
  let mut w := w0.writeUE hrd.cpbCntMinus1.toUInt64
  w := w.writeBitsMSB hrd.bitRateScale.toUInt64 4
  w := w.writeBitsMSB hrd.cpbSizeScale.toUInt64 4
  for i in [:cnt] do
    let br := hrd.bitRateValueMinus1.getD i 0
    let cs := hrd.cpbSizeValueMinus1.getD i 0
    if br == 0xFFFFFFFF || cs == 0xFFFFFFFF then return none
    w := w.writeUE br.toUInt64
    w := w.writeUE cs.toUInt64
    w := w.writeBit (if hrd.cbrFlag.getD i false then 1 else 0)
  w := w.writeBitsMSB hrd.initialCpbRemovalDelayLengthMinus1.toUInt64 5
  w := w.writeBitsMSB hrd.cpbRemovalDelayLengthMinus1.toUInt64 5
  w := w.writeBitsMSB hrd.dpbOutputDelayLengthMinus1.toUInt64 5
  w := w.writeBitsMSB hrd.timeOffsetLength.toUInt64 5
  return some w

/-- Parse `vui_parameters()` (`ISO/IEC 14496-10` Annex E §E.1.1). -/
def parseH264VuiParameters (r0 : BitReader) : Option (H264VuiParameters × BitReader) := Id.run do
  let mut vui : H264VuiParameters := {}
  let mut r := r0
  let some (arPresent, r1) := r.readBit | return none
  vui := { vui with aspectRatioInfoPresentFlag := arPresent == 1 }
  r := r1
  if vui.aspectRatioInfoPresentFlag then
    let some (arIdc, r2) := r.readBitsMSB 8 | return none
    vui := { vui with aspectRatioIdc := arIdc.toUInt8 }
    r := r2
    if vui.aspectRatioIdc == 255 then
      let some (sw, r3) := r.readBitsMSB 16 | return none
      let some (sh, r4) := r3.readBitsMSB 16 | return none
      vui := { vui with sarWidth := sw.toUInt16, sarHeight := sh.toUInt16 }
      r := r4
  let some (osPresent, rOs) := r.readBit | return none
  vui := { vui with overscanInfoPresentFlag := osPresent == 1 }
  r := rOs
  if vui.overscanInfoPresentFlag then
    let some (osApp, rOs2) := r.readBit | return none
    vui := { vui with overscanAppropriateFlag := osApp == 1 }
    r := rOs2
  let some (vsPresent, rVs) := r.readBit | return none
  vui := { vui with videoSignalTypePresentFlag := vsPresent == 1 }
  r := rVs
  if vui.videoSignalTypePresentFlag then
    let some (vFmt, rVf) := r.readBitsMSB 3 | return none
    let some (vFull, rVfr) := rVf.readBit | return none
    let some (cdPres, rCd) := rVfr.readBit | return none
    vui := { vui with videoFormat := vFmt.toUInt8, videoFullRangeFlag := vFull == 1,
                      colourDescriptionPresentFlag := cdPres == 1 }
    r := rCd
    if vui.colourDescriptionPresentFlag then
      let some (cp, rCp) := r.readBitsMSB 8 | return none
      let some (tc, rTc) := rCp.readBitsMSB 8 | return none
      let some (mc, rMc) := rTc.readBitsMSB 8 | return none
      vui := { vui with colourPrimaries := cp.toUInt8, transferCharacteristics := tc.toUInt8,
                        matrixCoefficients := mc.toUInt8 }
      r := rMc
  let some (clPres, rCl) := r.readBit | return none
  vui := { vui with chromaLocInfoPresentFlag := clPres == 1 }
  r := rCl
  if vui.chromaLocInfoPresentFlag then
    let some (clTop, rCl1) := r.readUE | return none
    let some (clBot, rCl2) := rCl1.readUE | return none
    if clTop > 5 || clBot > 5 then return none
    vui := { vui with chromaSampleLocTypeTopField := clTop.toUInt8, chromaSampleLocTypeBottomField := clBot.toUInt8 }
    r := rCl2
  let some (tiPres, rTi) := r.readBit | return none
  vui := { vui with timingInfoPresentFlag := tiPres == 1 }
  r := rTi
  if vui.timingInfoPresentFlag then
    let some (nut, rNut) := r.readBitsMSB 32 | return none
    let some (ts, rTs) := rNut.readBitsMSB 32 | return none
    let some (ffr, rFfr) := rTs.readBit | return none
    if nut == 0 || ts == 0 then return none
    vui := { vui with numUnitsInTick := nut.toUInt32, timeScale := ts.toUInt32, fixedFrameRateFlag := ffr == 1 }
    r := rFfr
  let some (nalHrdPres, rNh) := r.readBit | return none
  vui := { vui with nalHrdParametersPresentFlag := nalHrdPres == 1 }
  r := rNh
  if vui.nalHrdParametersPresentFlag then
    let some (nhrd, rNh2) := parseH264HrdParameters r | return none
    vui := { vui with nalHrd := nhrd }
    r := rNh2
  let some (vclHrdPres, rVh) := r.readBit | return none
  vui := { vui with vclHrdParametersPresentFlag := vclHrdPres == 1 }
  r := rVh
  if vui.vclHrdParametersPresentFlag then
    let some (vhrd, rVh2) := parseH264HrdParameters r | return none
    vui := { vui with vclHrd := vhrd }
    r := rVh2
  if vui.nalHrdParametersPresentFlag || vui.vclHrdParametersPresentFlag then
    let some (ldBit, rLd) := r.readBit | return none
    vui := { vui with lowDelayHrdFlag := ldBit == 1 }
    r := rLd
  let some (psPres, rPs) := r.readBit | return none
  let some (brPres, rBr) := rPs.readBit | return none
  vui := { vui with picStructPresentFlag := psPres == 1, bitstreamRestrictionFlag := brPres == 1 }
  r := rBr
  if vui.bitstreamRestrictionFlag then
    let some (mvb, rB1) := r.readBit | return none
    let some (mbpd, rB2) := rB1.readUE | return none
    let some (mbmd, rB3) := rB2.readUE | return none
    let some (l2h, rB4) := rB3.readUE | return none
    let some (l2v, rB5) := rB4.readUE | return none
    let some (mrf, rB6) := rB5.readUE | return none
    let some (mdfb, rB7) := rB6.readUE | return none
    if mbpd > 16 || mbmd > 16 || l2h > 16 || l2v > 16 || mrf > 16 || mdfb > 16 then return none
    vui := { vui with motionVectorsOverPicBoundariesFlag := mvb == 1,
                      maxBytesPerPicDenom := mbpd.toUInt8, maxBitsPerMbDenom := mbmd.toUInt8,
                      log2MaxMvLengthHorizontal := l2h.toUInt8, log2MaxMvLengthVertical := l2v.toUInt8,
                      maxNumReorderFrames := mrf.toUInt8, maxDecFrameBuffering := mdfb.toUInt8 }
    r := rB7
  return some (vui, r)

/-- Serialize `H264VuiParameters` (`ISO/IEC 14496-10` Annex E §E.1.1). -/
def writeH264VuiParameters (w0 : BitWriter) (vui : H264VuiParameters) : Option BitWriter := Id.run do
  let mut w := w0.writeBit (if vui.aspectRatioInfoPresentFlag then 1 else 0)
  if vui.aspectRatioInfoPresentFlag then
    w := w.writeBitsMSB vui.aspectRatioIdc.toUInt64 8
    if vui.aspectRatioIdc == 255 then
      w := w.writeBitsMSB vui.sarWidth.toUInt64 16
      w := w.writeBitsMSB vui.sarHeight.toUInt64 16
  w := w.writeBit (if vui.overscanInfoPresentFlag then 1 else 0)
  if vui.overscanInfoPresentFlag then
    w := w.writeBit (if vui.overscanAppropriateFlag then 1 else 0)
  w := w.writeBit (if vui.videoSignalTypePresentFlag then 1 else 0)
  if vui.videoSignalTypePresentFlag then
    if vui.videoFormat > 7 then return none
    w := w.writeBitsMSB vui.videoFormat.toUInt64 3
    w := w.writeBit (if vui.videoFullRangeFlag then 1 else 0)
    w := w.writeBit (if vui.colourDescriptionPresentFlag then 1 else 0)
    if vui.colourDescriptionPresentFlag then
      w := w.writeBitsMSB vui.colourPrimaries.toUInt64 8
      w := w.writeBitsMSB vui.transferCharacteristics.toUInt64 8
      w := w.writeBitsMSB vui.matrixCoefficients.toUInt64 8
  w := w.writeBit (if vui.chromaLocInfoPresentFlag then 1 else 0)
  if vui.chromaLocInfoPresentFlag then
    if vui.chromaSampleLocTypeTopField > 5 || vui.chromaSampleLocTypeBottomField > 5 then return none
    w := w.writeUE vui.chromaSampleLocTypeTopField.toUInt64
    w := w.writeUE vui.chromaSampleLocTypeBottomField.toUInt64
  w := w.writeBit (if vui.timingInfoPresentFlag then 1 else 0)
  if vui.timingInfoPresentFlag then
    if vui.numUnitsInTick == 0 || vui.timeScale == 0 then return none
    w := w.writeBitsMSB vui.numUnitsInTick.toUInt64 32
    w := w.writeBitsMSB vui.timeScale.toUInt64 32
    w := w.writeBit (if vui.fixedFrameRateFlag then 1 else 0)
  w := w.writeBit (if vui.nalHrdParametersPresentFlag then 1 else 0)
  if vui.nalHrdParametersPresentFlag then
    let some wNh := writeH264HrdParameters w vui.nalHrd | return none
    w := wNh
  w := w.writeBit (if vui.vclHrdParametersPresentFlag then 1 else 0)
  if vui.vclHrdParametersPresentFlag then
    let some wVh := writeH264HrdParameters w vui.vclHrd | return none
    w := wVh
  if vui.nalHrdParametersPresentFlag || vui.vclHrdParametersPresentFlag then
    w := w.writeBit (if vui.lowDelayHrdFlag then 1 else 0)
  w := w.writeBit (if vui.picStructPresentFlag then 1 else 0)
  w := w.writeBit (if vui.bitstreamRestrictionFlag then 1 else 0)
  if vui.bitstreamRestrictionFlag then
    if vui.maxBytesPerPicDenom > 16 || vui.maxBitsPerMbDenom > 16 ||
       vui.log2MaxMvLengthHorizontal > 16 || vui.log2MaxMvLengthVertical > 16 ||
       vui.maxNumReorderFrames > 16 || vui.maxDecFrameBuffering > 16 then return none
    w := w.writeBit (if vui.motionVectorsOverPicBoundariesFlag then 1 else 0)
    w := w.writeUE vui.maxBytesPerPicDenom.toUInt64
    w := w.writeUE vui.maxBitsPerMbDenom.toUInt64
    w := w.writeUE vui.log2MaxMvLengthHorizontal.toUInt64
    w := w.writeUE vui.log2MaxMvLengthVertical.toUInt64
    w := w.writeUE vui.maxNumReorderFrames.toUInt64
    w := w.writeUE vui.maxDecFrameBuffering.toUInt64
  return some w

/-- Compute `CropUnitX` and `CropUnitY` (`ISO/IEC 14496-10` §7.4.2.1.1 Equations 7-19..7-22). -/
def h264CropUnits (chromaFormatIdc : UInt8) (separateColourPlaneFlag : Bool) (frameMbsOnlyFlag : Bool) : Nat × Nat :=
  let chromaArrayType := if separateColourPlaneFlag then 0 else chromaFormatIdc.toNat
  let mbsMul := if frameMbsOnlyFlag then 1 else 2
  if chromaArrayType == 0 then
    (1, mbsMul)
  else
    let subWidthC  := if chromaArrayType == 1 || chromaArrayType == 2 then 2 else 1
    let subHeightC := if chromaArrayType == 1 then 2 else 1
    (subWidthC, subHeightC * mbsMul)

/-- Complete parsed H.264 Sequence Parameter Set (`SPS`, `nal_unit_type = 7`, `ISO/IEC 14496-10` §7.3.2.1.1). -/
structure H264SpsFull where
  nalRefIdc                      : UInt8 := 3
  profileIdc                     : UInt8 := 100
  constraintSet0Flag             : Bool := false
  constraintSet1Flag             : Bool := false
  constraintSet2Flag             : Bool := false
  constraintSet3Flag             : Bool := false
  constraintSet4Flag             : Bool := false
  constraintSet5Flag             : Bool := false
  reservedZero2Bits              : UInt8 := 0
  levelIdc                       : UInt8 := 40
  spsId                          : UInt8 := 0
  chromaFormatIdc                : UInt8 := 1
  separateColourPlaneFlag        : Bool := false
  bitDepthLumaMinus8             : UInt8 := 0
  bitDepthChromaMinus8           : UInt8 := 0
  qpprimeYZeroTransformBypass    : Bool := false
  seqScalingMatrixPresentFlag    : Bool := false
  scalingListSyntax4x4           : Array ScalingListSyntax := Array.replicate 6 .absent
  scalingListSyntax8x8           : Array ScalingListSyntax := Array.replicate 6 .absent
  effectiveScaling4x4            : Array (Array UInt8) := Array.replicate 6 flatScalingList4x4
  effectiveScaling8x8            : Array (Array UInt8) := Array.replicate 6 flatScalingList8x8
  log2MaxFrameNumMinus4          : UInt8 := 0
  picOrderCntType                : UInt8 := 0
  log2MaxPicOrderCntLsbMinus4    : UInt8 := 0
  deltaPicOrderAlwaysZeroFlag    : Bool := false
  offsetForNonRefPic             : Int32 := 0
  offsetForTopToBottomField      : Int32 := 0
  offsetForRefFrame              : Array Int32 := #[]
  maxNumRefFrames                : UInt8 := 1
  gapsInFrameNumValueAllowedFlag : Bool := false
  picWidthInMbsMinus1            : UInt16 := 0
  picHeightInMapUnitsMinus1      : UInt16 := 0
  frameMbsOnlyFlag               : Bool := true
  mbAdaptiveFrameFieldFlag       : Bool := false
  direct8x8InferenceFlag         : Bool := true
  frameCroppingFlag              : Bool := false
  frameCropLeftOffset            : UInt16 := 0
  frameCropRightOffset           : UInt16 := 0
  frameCropTopOffset             : UInt16 := 0
  frameCropBottomOffset          : UInt16 := 0
  widthPx                        : UInt32 := 16
  heightPx                       : UInt32 := 16
  vuiParametersPresentFlag       : Bool := false
  vui                            : H264VuiParameters := {}
  deriving Repr, DecidableEq, Inhabited

/-- Reassemble the 8-bit `constraint_set0..5` + `reserved_zero_2bits` byte of `H264SpsFull`. -/
def H264SpsFull.constraintByte (sps : H264SpsFull) : UInt8 :=
  (if sps.constraintSet0Flag then (0x80 : UInt8) else 0) |||
  (if sps.constraintSet1Flag then (0x40 : UInt8) else 0) |||
  (if sps.constraintSet2Flag then (0x20 : UInt8) else 0) |||
  (if sps.constraintSet3Flag then (0x10 : UInt8) else 0) |||
  (if sps.constraintSet4Flag then (0x08 : UInt8) else 0) |||
  (if sps.constraintSet5Flag then (0x04 : UInt8) else 0) |||
  (sps.reservedZero2Bits &&& 0x03)

/-- Parse a complete H.264 `SPS` NALU (`nal_unit_type = 7`, EBSP input including 1-byte NAL header). -/
def parseH264SpsFull (nalPayload : ByteSlice) : Option H264SpsFull := Id.run do
  let rbsp := stripRbspEmulationBytesH264 nalPayload true
  if rbsp.size < 4 then return none
  let hdr := rbsp.get! 0
  if (hdr &&& 0x80) != 0 || (hdr &&& 0x1F) != 7 then return none
  let some payloadBits := rbspPayloadBitLen rbsp | return none
  let nalRefIdc := (hdr >>> 5) &&& 0x03
  let profileIdc := rbsp.get! 1
  let cByte := rbsp.get! 2
  let levelIdc := rbsp.get! 3
  let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 32 }
  let some (spsId64, r1) := r0.readUE | return none
  if spsId64 > 31 then return none
  let mut r := r1
  let mut chromaIdc : UInt8 := 1
  let mut sepPlane := false
  let mut bdLuma : UInt8 := 0
  let mut bdChroma : UInt8 := 0
  let mut qpBypass := false
  let mut seqScalePres := false
  let mut syn4 : Array ScalingListSyntax := Array.replicate 6 .absent
  let mut syn8 : Array ScalingListSyntax := Array.replicate 6 .absent
  if isH264HighExtProfile profileIdc then
    let some (ch64, rA) := r.readUE | return none
    if ch64 > 3 then return none
    chromaIdc := ch64.toUInt8
    r := rA
    if chromaIdc == 3 then
      let some (sepBit, rSep) := r.readBit | return none
      sepPlane := sepBit == 1
      r := rSep
    let some (bdL64, rB) := r.readUE | return none
    let some (bdC64, rC) := rB.readUE | return none
    if bdL64 > 6 || bdC64 > 6 then return none
    bdLuma := bdL64.toUInt8
    bdChroma := bdC64.toUInt8
    let some (qpbBit, rD) := rC.readBit | return none
    let some (sspBit, rE) := rD.readBit | return none
    qpBypass := qpbBit == 1
    seqScalePres := sspBit == 1
    r := rE
    if seqScalePres then
      let cnt := if chromaIdc != 3 then 8 else 12
      let mut s4 := Array.replicate 6 ScalingListSyntax.absent
      let mut s8 := Array.replicate 6 ScalingListSyntax.absent
      for idx in [:cnt] do
        let some (presBit, rP) := r.readBit | return none
        r := rP
        if presBit == 1 then
          if idx < 6 then
            let some (ent, rNext) := parseScalingListSyntax r 16 | return none
            s4 := s4.set! idx ent
            r := rNext
          else
            let some (ent, rNext) := parseScalingListSyntax r 64 | return none
            s8 := s8.set! (idx - 6) ent
            r := rNext
      syn4 := s4
      syn8 := s8
  let (eff4, eff8) := resolveSpsScalingMatrices seqScalePres syn4 syn8
  let some (l2FnM4, rFn) := r.readUE | return none
  if l2FnM4 > 12 then return none
  let some (pocT, rPoc) := rFn.readUE | return none
  if pocT > 2 then return none
  r := rPoc
  let mut l2PocLsbM4 : UInt8 := 0
  let mut deltaZero := false
  let mut offNonRef : Int32 := 0
  let mut offTopBot : Int32 := 0
  let mut offRefArr : Array Int32 := #[]
  if pocT == 0 then
    let some (l2Lsb, rP0) := r.readUE | return none
    if l2Lsb > 12 then return none
    l2PocLsbM4 := l2Lsb.toUInt8
    r := rP0
  else if pocT == 1 then
    let some (dzBit, rP1) := r.readBit | return none
    let some (onr, rP2) := rP1.readSE | return none
    let some (otb, rP3) := rP2.readSE | return none
    let some (nRefCycle, rP4) := rP3.readUE | return none
    if nRefCycle > 255 then return none
    deltaZero := dzBit == 1
    offNonRef := onr
    offTopBot := otb
    r := rP4
    let mut arr : Array Int32 := #[]
    for _ in [:nRefCycle.toNat] do
      let some (ov, rNext) := r.readSE | return none
      arr := arr.push ov
      r := rNext
    offRefArr := arr
  let some (maxRef, rMr) := r.readUE | return none
  if maxRef > 16 then return none
  let some (gapsBit, rG) := rMr.readBit | return none
  let some (wMbsM1, rW) := rG.readUE | return none
  let some (hMapM1, rH) := rW.readUE | return none
  if wMbsM1 > 1023 || hMapM1 > 1023 then return none
  let some (fmoBit, rFmo) := rH.readBit | return none
  let frameMbsOnly := fmoBit == 1
  r := rFmo
  let mut mbaff := false
  if !frameMbsOnly then
    let some (mbaffBit, rMb) := r.readBit | return none
    mbaff := mbaffBit == 1
    r := rMb
  let some (dir8Bit, rD8) := r.readBit | return none
  let some (cropBit, rCr) := rD8.readBit | return none
  r := rCr
  let mut cLeft : UInt16 := 0
  let mut cRight : UInt16 := 0
  let mut cTop : UInt16 := 0
  let mut cBot : UInt16 := 0
  if cropBit == 1 then
    let some (cl, rC1) := r.readUE | return none
    let some (cr, rC2) := rC1.readUE | return none
    let some (ct, rC3) := rC2.readUE | return none
    let some (cb, rC4) := rC3.readUE | return none
    if cl > 0xFFFF || cr > 0xFFFF || ct > 0xFFFF || cb > 0xFFFF then return none
    cLeft := cl.toUInt16
    cRight := cr.toUInt16
    cTop := ct.toUInt16
    cBot := cb.toUInt16
    r := rC4
  let rawWidth := (wMbsM1.toNat + 1) * 16
  let rawHeight := (hMapM1.toNat + 1) * (if frameMbsOnly then 16 else 32)
  let (cropUnitX, cropUnitY) := h264CropUnits chromaIdc sepPlane frameMbsOnly
  let cropW := (cLeft.toNat + cRight.toNat) * cropUnitX
  let cropH := (cTop.toNat + cBot.toNat) * cropUnitY
  if cropW ≥ rawWidth || cropH ≥ rawHeight then return none
  let widthPx := (rawWidth - cropW).toUInt32
  let heightPx := (rawHeight - cropH).toUInt32
  let some (vuiBit, rVui0) := r.readBit | return none
  r := rVui0
  let mut vuiVal : H264VuiParameters := {}
  if vuiBit == 1 then
    let some (vp, rVuiEnd) := parseH264VuiParameters r | return none
    vuiVal := vp
    r := rVuiEnd
  if r.bitOffset > payloadBits then return none
  return some {
    nalRefIdc, profileIdc,
    constraintSet0Flag := (cByte &&& 0x80) != 0,
    constraintSet1Flag := (cByte &&& 0x40) != 0,
    constraintSet2Flag := (cByte &&& 0x20) != 0,
    constraintSet3Flag := (cByte &&& 0x10) != 0,
    constraintSet4Flag := (cByte &&& 0x08) != 0,
    constraintSet5Flag := (cByte &&& 0x04) != 0,
    reservedZero2Bits  := cByte &&& 0x03,
    levelIdc, spsId := spsId64.toUInt8,
    chromaFormatIdc := chromaIdc, separateColourPlaneFlag := sepPlane,
    bitDepthLumaMinus8 := bdLuma, bitDepthChromaMinus8 := bdChroma,
    qpprimeYZeroTransformBypass := qpBypass,
    seqScalingMatrixPresentFlag := seqScalePres,
    scalingListSyntax4x4 := syn4, scalingListSyntax8x8 := syn8,
    effectiveScaling4x4 := eff4, effectiveScaling8x8 := eff8,
    log2MaxFrameNumMinus4 := l2FnM4.toUInt8,
    picOrderCntType := pocT.toUInt8,
    log2MaxPicOrderCntLsbMinus4 := l2PocLsbM4,
    deltaPicOrderAlwaysZeroFlag := deltaZero,
    offsetForNonRefPic := offNonRef, offsetForTopToBottomField := offTopBot,
    offsetForRefFrame := offRefArr,
    maxNumRefFrames := maxRef.toUInt8,
    gapsInFrameNumValueAllowedFlag := gapsBit == 1,
    picWidthInMbsMinus1 := wMbsM1.toUInt16,
    picHeightInMapUnitsMinus1 := hMapM1.toUInt16,
    frameMbsOnlyFlag := frameMbsOnly, mbAdaptiveFrameFieldFlag := mbaff,
    direct8x8InferenceFlag := dir8Bit == 1,
    frameCroppingFlag := cropBit == 1,
    frameCropLeftOffset := cLeft, frameCropRightOffset := cRight,
    frameCropTopOffset := cTop, frameCropBottomOffset := cBot,
    widthPx, heightPx,
    vuiParametersPresentFlag := vuiBit == 1, vui := vuiVal
  }

/-- Deterministically serialize an `H264SpsFull` into a complete H.264 `SPS` EBSP NALU
    (`(nalRefIdc <<< 5) ||| 7` + RBSP + `rbsp_trailing_bits()` + `0x000003` emulation prevention). -/
def serializeH264SpsFull (sps : H264SpsFull) : Option ByteArray := Id.run do
  if sps.nalRefIdc > 3 || sps.spsId > 31 || sps.log2MaxFrameNumMinus4 > 12 || sps.picOrderCntType > 2 then return none
  if sps.maxNumRefFrames > 16 || sps.picWidthInMbsMinus1 > 1023 || sps.picHeightInMapUnitsMinus1 > 1023 then return none
  let hdrByte : UInt8 := ((sps.nalRefIdc &&& 0x03) <<< 5) ||| 7
  let mut w := BitWriter.empty 64
  w := w.writeBitsMSB hdrByte.toUInt64 8
  w := w.writeBitsMSB sps.profileIdc.toUInt64 8
  w := w.writeBitsMSB sps.constraintByte.toUInt64 8
  w := w.writeBitsMSB sps.levelIdc.toUInt64 8
  w := w.writeUE sps.spsId.toUInt64
  if isH264HighExtProfile sps.profileIdc then
    if sps.chromaFormatIdc > 3 || sps.bitDepthLumaMinus8 > 6 || sps.bitDepthChromaMinus8 > 6 then return none
    if sps.chromaFormatIdc != 3 && sps.separateColourPlaneFlag then return none
    w := w.writeUE sps.chromaFormatIdc.toUInt64
    if sps.chromaFormatIdc == 3 then
      w := w.writeBit (if sps.separateColourPlaneFlag then 1 else 0)
    w := w.writeUE sps.bitDepthLumaMinus8.toUInt64
    w := w.writeUE sps.bitDepthChromaMinus8.toUInt64
    w := w.writeBit (if sps.qpprimeYZeroTransformBypass then 1 else 0)
    w := w.writeBit (if sps.seqScalingMatrixPresentFlag then 1 else 0)
    if sps.seqScalingMatrixPresentFlag then
      if sps.scalingListSyntax4x4.size != 6 || sps.scalingListSyntax8x8.size != 6 then return none
      let cnt := if sps.chromaFormatIdc != 3 then 8 else 12
      if cnt == 8 then
        for extra in [2:6] do
          if sps.scalingListSyntax8x8.getD extra ScalingListSyntax.absent != ScalingListSyntax.absent then return none
      for idx in [:cnt] do
        if idx < 6 then
          let some wNext := writeScalingListSyntax w (sps.scalingListSyntax4x4.getD idx ScalingListSyntax.absent) 16 | return none
          w := wNext
        else
          let some wNext := writeScalingListSyntax w (sps.scalingListSyntax8x8.getD (idx - 6) ScalingListSyntax.absent) 64 | return none
          w := wNext
  else
    if sps.chromaFormatIdc != 1 || sps.separateColourPlaneFlag || sps.bitDepthLumaMinus8 != 0 ||
       sps.bitDepthChromaMinus8 != 0 || sps.qpprimeYZeroTransformBypass || sps.seqScalingMatrixPresentFlag then
      return none
  w := w.writeUE sps.log2MaxFrameNumMinus4.toUInt64
  w := w.writeUE sps.picOrderCntType.toUInt64
  if sps.picOrderCntType == 0 then
    if sps.log2MaxPicOrderCntLsbMinus4 > 12 then return none
    w := w.writeUE sps.log2MaxPicOrderCntLsbMinus4.toUInt64
  else if sps.picOrderCntType == 1 then
    if sps.offsetForRefFrame.size > 255 then return none
    w := w.writeBit (if sps.deltaPicOrderAlwaysZeroFlag then 1 else 0)
    w := w.writeSE sps.offsetForNonRefPic
    w := w.writeSE sps.offsetForTopToBottomField
    w := w.writeUE sps.offsetForRefFrame.size.toUInt64
    for ov in sps.offsetForRefFrame do
      w := w.writeSE ov
  w := w.writeUE sps.maxNumRefFrames.toUInt64
  w := w.writeBit (if sps.gapsInFrameNumValueAllowedFlag then 1 else 0)
  w := w.writeUE sps.picWidthInMbsMinus1.toUInt64
  w := w.writeUE sps.picHeightInMapUnitsMinus1.toUInt64
  w := w.writeBit (if sps.frameMbsOnlyFlag then 1 else 0)
  if !sps.frameMbsOnlyFlag then
    w := w.writeBit (if sps.mbAdaptiveFrameFieldFlag then 1 else 0)
  else if sps.mbAdaptiveFrameFieldFlag then
    return none
  w := w.writeBit (if sps.direct8x8InferenceFlag then 1 else 0)
  let cLeft := if sps.frameCroppingFlag then sps.frameCropLeftOffset else 0
  let cRight := if sps.frameCroppingFlag then sps.frameCropRightOffset else 0
  let cTop := if sps.frameCroppingFlag then sps.frameCropTopOffset else 0
  let cBot := if sps.frameCroppingFlag then sps.frameCropBottomOffset else 0
  let rawWidth := (sps.picWidthInMbsMinus1.toNat + 1) * 16
  let rawHeight := (sps.picHeightInMapUnitsMinus1.toNat + 1) * (if sps.frameMbsOnlyFlag then 16 else 32)
  let (cropUnitX, cropUnitY) := h264CropUnits sps.chromaFormatIdc sps.separateColourPlaneFlag sps.frameMbsOnlyFlag
  let cropW := (cLeft.toNat + cRight.toNat) * cropUnitX
  let cropH := (cTop.toNat + cBot.toNat) * cropUnitY
  if cropW ≥ rawWidth || cropH ≥ rawHeight then return none
  if sps.widthPx != (rawWidth - cropW).toUInt32 || sps.heightPx != (rawHeight - cropH).toUInt32 then return none
  w := w.writeBit (if sps.frameCroppingFlag then 1 else 0)
  if sps.frameCroppingFlag then
    w := w.writeUE cLeft.toUInt64
    w := w.writeUE cRight.toUInt64
    w := w.writeUE cTop.toUInt64
    w := w.writeUE cBot.toUInt64
  w := w.writeBit (if sps.vuiParametersPresentFlag then 1 else 0)
  if sps.vuiParametersPresentFlag then
    let some wVui := writeH264VuiParameters w sps.vui | return none
    w := wVui
  let rbsp := finalizeRbspWriter w
  return some (insertRbspEmulationBytes rbsp true)

/-! ## 5. Full Picture Parameter Set (`PPS`, `nal_unit_type = 8`, `ISO/IEC 14496-10` §7.3.2.2) -/

/-- Complete parsed H.264 Picture Parameter Set (`PPS`, `nal_unit_type = 8`, `ISO/IEC 14496-10` §7.3.2.2).
    Fails closed when `num_slice_groups_minus1 > 0` (FMO excluded). -/
structure H264PpsFull where
  nalRefIdc                          : UInt8 := 3
  ppsId                              : UInt8 := 0
  spsId                              : UInt8 := 0
  entropyCodingModeFlag              : Bool := true
  bottomFieldPicOrderInFramePresent  : Bool := false
  numSliceGroupsMinus1               : UInt8 := 0
  numRefIdxL0DefaultActiveMinus1     : UInt8 := 0
  numRefIdxL1DefaultActiveMinus1     : UInt8 := 0
  weightedPredFlag                   : Bool := false
  weightedBipredIdc                  : UInt8 := 0
  picInitQpMinus26                   : Int32 := 0
  picInitQsMinus26                   : Int32 := 0
  chromaQpIndexOffset                : Int32 := 0
  deblockingFilterControlPresentFlag : Bool := true
  constrainedIntraPredFlag           : Bool := false
  redundantPicCntPresentFlag         : Bool := false
  hasMoreRbspDataExt                 : Bool := false
  transform8x8ModeFlag               : Bool := false
  picScalingMatrixPresentFlag        : Bool := false
  scalingListSyntax4x4               : Array ScalingListSyntax := Array.replicate 6 .absent
  scalingListSyntax8x8               : Array ScalingListSyntax := Array.replicate 6 .absent
  effectiveScaling4x4                : Array (Array UInt8) := Array.replicate 6 flatScalingList4x4
  effectiveScaling8x8                : Array (Array UInt8) := Array.replicate 6 flatScalingList8x8
  secondChromaQpIndexOffset          : Int32 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Parse a complete H.264 `PPS` NALU (`nal_unit_type = 8`), linked to its active `H264SpsFull` (or default `chroma_format_idc = 1`).
    Fails closed when `num_slice_groups_minus1 > 0` or any syntax range check fails. -/
def parseH264PpsFull (nalPayload : ByteSlice) (spsOpt : Option H264SpsFull := none) : Option H264PpsFull := Id.run do
  let rbsp := stripRbspEmulationBytesH264 nalPayload true
  if rbsp.size < 2 then return none
  let hdr := rbsp.get! 0
  if (hdr &&& 0x80) != 0 || (hdr &&& 0x1F) != 8 then return none
  let nalRefIdc := (hdr >>> 5) &&& 0x03
  let some payloadBits := rbspPayloadBitLen rbsp | return none
  let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 8 }
  let some (ppsId64, r1) := r0.readUE | return none
  let some (spsId64, r2) := r1.readUE | return none
  if ppsId64 > 255 || spsId64 > 31 then return none
  if let some sps := spsOpt then
    if sps.spsId.toUInt64 != spsId64 then return none
  let bdLuma : Int := match spsOpt with | some s => s.bitDepthLumaMinus8.toNat | none => 0
  let minInitQp : Int := -(26 + 6 * bdLuma)
  let some (entBit, r3) := r2.readBit | return none
  let some (bfpoBit, r4) := r3.readBit | return none
  let some (numSg, r5) := r4.readUE | return none
  if numSg != 0 then return none
  let some (l0DefM1, r6) := r5.readUE | return none
  let some (l1DefM1, r7) := r6.readUE | return none
  if l0DefM1 > 31 || l1DefM1 > 31 then return none
  let some (wpBit, r8) := r7.readBit | return none
  let some (wbIdc, r9) := r8.readBitsMSB 2 | return none
  if wbIdc > 2 then return none
  let some (initQp, r10) := r9.readSE | return none
  let some (initQs, r11) := r10.readSE | return none
  let some (cQpOff, r12) := r11.readSE | return none
  if initQp.toInt < minInitQp || initQp.toInt > 25 then return none
  if initQs.toInt < -26 || initQs.toInt > 25 then return none
  if cQpOff.toInt < -12 || cQpOff.toInt > 12 then return none
  let some (dbfBit, r13) := r12.readBit | return none
  let some (cipBit, r14) := r13.readBit | return none
  let some (rpcBit, r15) := r14.readBit | return none
  if r15.bitOffset > payloadBits then return none
  let mut r := r15
  let mut hasExt := false
  let mut tr8x8 := false
  let mut picScalePres := false
  let mut syn4 : Array ScalingListSyntax := Array.replicate 6 .absent
  let mut syn8 : Array ScalingListSyntax := Array.replicate 6 .absent
  let mut secCqp : Int32 := cQpOff
  let chromaIdc : UInt8 := match spsOpt with | some s => s.chromaFormatIdc | none => 1
  if moreRbspData r payloadBits then
    hasExt := true
    let some (t8Bit, rE1) := r.readBit | return none
    let some (psBit, rE2) := rE1.readBit | return none
    tr8x8 := t8Bit == 1
    picScalePres := psBit == 1
    r := rE2
    if picScalePres then
      let cnt := 6 + (if tr8x8 then (if chromaIdc != 3 then 2 else 6) else 0)
      let mut s4 := Array.replicate 6 ScalingListSyntax.absent
      let mut s8 := Array.replicate 6 ScalingListSyntax.absent
      for idx in [:cnt] do
        let some (presBit, rP) := r.readBit | return none
        r := rP
        if presBit == 1 then
          if idx < 6 then
            let some (ent, rNext) := parseScalingListSyntax r 16 | return none
            s4 := s4.set! idx ent
            r := rNext
          else
            let some (ent, rNext) := parseScalingListSyntax r 64 | return none
            s8 := s8.set! (idx - 6) ent
            r := rNext
      syn4 := s4
      syn8 := s8
    let some (scOff, rE3) := r.readSE | return none
    if scOff.toInt < -12 || scOff.toInt > 12 then return none
    secCqp := scOff
    r := rE3
  if r.bitOffset != payloadBits then return none
  let spsSeqPres := match spsOpt with | some s => s.seqScalingMatrixPresentFlag | none => false
  let spsEff4 := match spsOpt with | some s => s.effectiveScaling4x4 | none => Array.replicate 6 flatScalingList4x4
  let spsEff8 := match spsOpt with | some s => s.effectiveScaling8x8 | none => Array.replicate 6 flatScalingList8x8
  let (eff4, eff8) := resolvePpsScalingMatrices spsSeqPres spsEff4 spsEff8 picScalePres syn4 syn8
  return some {
    nalRefIdc, ppsId := ppsId64.toUInt8, spsId := spsId64.toUInt8,
    entropyCodingModeFlag := entBit == 1,
    bottomFieldPicOrderInFramePresent := bfpoBit == 1,
    numSliceGroupsMinus1 := 0,
    numRefIdxL0DefaultActiveMinus1 := l0DefM1.toUInt8,
    numRefIdxL1DefaultActiveMinus1 := l1DefM1.toUInt8,
    weightedPredFlag := wpBit == 1,
    weightedBipredIdc := wbIdc.toUInt8,
    picInitQpMinus26 := initQp, picInitQsMinus26 := initQs,
    chromaQpIndexOffset := cQpOff,
    deblockingFilterControlPresentFlag := dbfBit == 1,
    constrainedIntraPredFlag := cipBit == 1,
    redundantPicCntPresentFlag := rpcBit == 1,
    hasMoreRbspDataExt := hasExt,
    transform8x8ModeFlag := tr8x8,
    picScalingMatrixPresentFlag := picScalePres,
    scalingListSyntax4x4 := syn4, scalingListSyntax8x8 := syn8,
    effectiveScaling4x4 := eff4, effectiveScaling8x8 := eff8,
    secondChromaQpIndexOffset := secCqp
  }

/-- Deterministically serialize an `H264PpsFull` into a complete H.264 `PPS` EBSP NALU
    (`(nalRefIdc <<< 5) ||| 8` + RBSP + `rbsp_trailing_bits()` + `0x000003` emulation prevention). -/
def serializeH264PpsFull (pps : H264PpsFull) (chromaFormatIdc : UInt8 := 1)
    (bitDepthLumaMinus8 : UInt8 := 0) : Option ByteArray := Id.run do
  if pps.nalRefIdc > 3 || pps.spsId > 31 || pps.numSliceGroupsMinus1 != 0 then return none
  if pps.numRefIdxL0DefaultActiveMinus1 > 31 || pps.numRefIdxL1DefaultActiveMinus1 > 31 || pps.weightedBipredIdc > 2 then return none
  let minInitQp : Int := -(26 + 6 * bitDepthLumaMinus8.toNat)
  if pps.picInitQpMinus26.toInt < minInitQp || pps.picInitQpMinus26.toInt > 25 then return none
  if pps.picInitQsMinus26.toInt < -26 || pps.picInitQsMinus26.toInt > 25 then return none
  if pps.chromaQpIndexOffset.toInt < -12 || pps.chromaQpIndexOffset.toInt > 12 then return none
  let hdrByte : UInt8 := ((pps.nalRefIdc &&& 0x03) <<< 5) ||| 8
  let mut w := BitWriter.empty 32
  w := w.writeBitsMSB hdrByte.toUInt64 8
  w := w.writeUE pps.ppsId.toUInt64
  w := w.writeUE pps.spsId.toUInt64
  w := w.writeBit (if pps.entropyCodingModeFlag then 1 else 0)
  w := w.writeBit (if pps.bottomFieldPicOrderInFramePresent then 1 else 0)
  w := w.writeUE 0
  w := w.writeUE pps.numRefIdxL0DefaultActiveMinus1.toUInt64
  w := w.writeUE pps.numRefIdxL1DefaultActiveMinus1.toUInt64
  w := w.writeBit (if pps.weightedPredFlag then 1 else 0)
  w := w.writeBitsMSB pps.weightedBipredIdc.toUInt64 2
  w := w.writeSE pps.picInitQpMinus26
  w := w.writeSE pps.picInitQsMinus26
  w := w.writeSE pps.chromaQpIndexOffset
  w := w.writeBit (if pps.deblockingFilterControlPresentFlag then 1 else 0)
  w := w.writeBit (if pps.constrainedIntraPredFlag then 1 else 0)
  w := w.writeBit (if pps.redundantPicCntPresentFlag then 1 else 0)
  if pps.hasMoreRbspDataExt then
    if pps.secondChromaQpIndexOffset.toInt < -12 || pps.secondChromaQpIndexOffset.toInt > 12 then return none
    w := w.writeBit (if pps.transform8x8ModeFlag then 1 else 0)
    w := w.writeBit (if pps.picScalingMatrixPresentFlag then 1 else 0)
    if pps.picScalingMatrixPresentFlag then
      if pps.scalingListSyntax4x4.size != 6 || pps.scalingListSyntax8x8.size != 6 then return none
      let cnt := 6 + (if pps.transform8x8ModeFlag then (if chromaFormatIdc != 3 then 2 else 6) else 0)
      for extra in [cnt - 6 : 6] do
        if pps.scalingListSyntax8x8.getD extra ScalingListSyntax.absent != ScalingListSyntax.absent then return none
      for idx in [:cnt] do
        if idx < 6 then
          let some wNext := writeScalingListSyntax w (pps.scalingListSyntax4x4.getD idx ScalingListSyntax.absent) 16 | return none
          w := wNext
        else
          let some wNext := writeScalingListSyntax w (pps.scalingListSyntax8x8.getD (idx - 6) ScalingListSyntax.absent) 64 | return none
          w := wNext
    w := w.writeSE pps.secondChromaQpIndexOffset
  else
    if pps.transform8x8ModeFlag || pps.picScalingMatrixPresentFlag || pps.secondChromaQpIndexOffset != pps.chromaQpIndexOffset then
      return none
  let rbsp := finalizeRbspWriter w
  return some (insertRbspEmulationBytes rbsp true)

/-! ## 6. Full Slice Header (`nal_unit_type ∈ {1, 5}`) & POC Type 0 / Type 2 (`ISO/IEC 14496-10` §7.3.3, §8.2.1) -/

/-- Canonical H.264 slice family (`P`, `B`, `I`, `SP`, `SI`, derived from `slice_type % 5`). -/
inductive H264SliceKind where
  | P
  | B
  | I
  | SP
  | SI
  deriving Repr, DecidableEq, Inhabited

/-- Map `slice_type ∈ [0, 9]` (`ISO/IEC 14496-10` Table 7-6) to `H264SliceKind`. -/
def classifyH264SliceType (sliceType : UInt8) : Option H264SliceKind :=
  if sliceType > 9 then none
  else
    match sliceType.toNat % 5 with
    | 0 => some .P
    | 1 => some .B
    | 2 => some .I
    | 3 => some .SP
    | _ => some .SI

/-- Reference picture list modification entry (`ISO/IEC 14496-10` §7.3.3.1). -/
structure RefPicListModOp where
  modificationOfPicNumsIdc : UInt8
  param                    : UInt32
  deriving Repr, DecidableEq, Inhabited

/-- Explicit weighted prediction entry for one reference index (`ISO/IEC 14496-10` §7.3.3.2). -/
structure PredWeightEntry where
  lumaWeightFlag   : Bool := false
  lumaWeight       : Int32 := 0
  lumaOffset       : Int32 := 0
  chromaWeightFlag : Bool := false
  cbWeight         : Int32 := 0
  cbOffset         : Int32 := 0
  crWeight         : Int32 := 0
  crOffset         : Int32 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Explicit `pred_weight_table()` (`ISO/IEC 14496-10` §7.3.3.2). -/
structure PredWeightTable where
  lumaLog2WeightDenom   : UInt8 := 0
  chromaLog2WeightDenom : UInt8 := 0
  l0Weights             : Array PredWeightEntry := #[]
  l1Weights             : Array PredWeightEntry := #[]
  deriving Repr, DecidableEq, Inhabited

/-- Adaptive Memory Management Control Operation (`MMCO`, `op ∈ 1..6`, `ISO/IEC 14496-10` §7.3.3.3). -/
structure MmcoOp where
  opcode : UInt8
  arg0   : UInt32 := 0
  arg1   : UInt32 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Complete parsed H.264 Slice Header (`nal_unit_type ∈ {1, 5}`, `ISO/IEC 14496-10` §7.3.3). -/
structure H264SliceHeaderFull where
  nalRefIdc                     : UInt8 := 3
  nalUnitType                   : UInt8 := 5
  firstMbInSlice                : UInt32 := 0
  sliceType                     : UInt8 := 2
  sliceKind                     : H264SliceKind := .I
  ppsId                         : UInt8 := 0
  colourPlaneId                 : UInt8 := 0
  frameNum                      : UInt32 := 0
  fieldPicFlag                  : Bool := false
  bottomFieldFlag               : Bool := false
  idrPicId                      : UInt16 := 0
  picOrderCntLsb                : UInt32 := 0
  deltaPicOrderCntBottom        : Int32 := 0
  deltaPicOrderCnt0             : Int32 := 0
  deltaPicOrderCnt1             : Int32 := 0
  redundantPicCnt               : UInt8 := 0
  directSpatialMvPredFlag       : Bool := false
  numRefIdxActiveOverrideFlag   : Bool := false
  numRefIdxL0ActiveMinus1       : UInt8 := 0
  numRefIdxL1ActiveMinus1       : UInt8 := 0
  refPicListModFlagL0           : Bool := false
  refPicListModL0               : Array RefPicListModOp := #[]
  refPicListModFlagL1           : Bool := false
  refPicListModL1               : Array RefPicListModOp := #[]
  hasPredWeightTable            : Bool := false
  predWeightTable               : PredWeightTable := {}
  noOutputOfPriorPicsFlag       : Bool := false
  longTermReferenceFlag         : Bool := false
  adaptiveRefPicMarkingModeFlag : Bool := false
  mmcoOps                       : Array MmcoOp := #[]
  cabacInitIdc                  : UInt8 := 0
  sliceQpDelta                  : Int32 := 0
  sliceQpY                      : Int32 := 26
  spForSwitchFlag               : Bool := false
  sliceQsDelta                  : Int32 := 0
  disableDeblockingFilterIdc    : UInt8 := 0
  sliceAlphaC0OffsetDiv2        : Int32 := 0
  sliceBetaOffsetDiv2           : Int32 := 0
  sliceDataBitOffset            : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Parse one `ref_pic_list_modification` list (`ISO/IEC 14496-10` §7.3.3.1), bounded by `maxOps ≤ 33`. -/
def parseRefPicListModLoop (r0 : BitReader) : Option (Array RefPicListModOp × BitReader) := Id.run do
  let mut r := r0
  let mut ops : Array RefPicListModOp := #[]
  for _ in [:33] do
    let some (idc, r1) := r.readUE | return none
    if idc == 3 then
      return some (ops, r1)
    if idc > 2 then return none
    let some (param, r2) := r1.readUE | return none
    if param > 0xFFFFFFFF then return none
    ops := ops.push { modificationOfPicNumsIdc := idc.toUInt8, param := param.toUInt32 }
    r := r2
  return none

/-- Parse one `pred_weight_table` reference list (`ISO/IEC 14496-10` §7.3.3.2). -/
def parsePredWeightList (r0 : BitReader) (count : Nat) (chromaArrayType : Nat) : Option (Array PredWeightEntry × BitReader) := Id.run do
  let mut r := r0
  let mut arr : Array PredWeightEntry := #[]
  for _ in [:count] do
    let some (lwBit, r1) := r.readBit | return none
    r := r1
    let mut e : PredWeightEntry := { lumaWeightFlag := lwBit == 1 }
    if e.lumaWeightFlag then
      let some (lw, r2) := r.readSE | return none
      let some (lo, r3) := r2.readSE | return none
      if lw.toInt < -128 || lw.toInt > 127 || lo.toInt < -128 || lo.toInt > 127 then return none
      e := { e with lumaWeight := lw, lumaOffset := lo }
      r := r3
    if chromaArrayType != 0 then
      let some (cwBit, r4) := r.readBit | return none
      r := r4
      e := { e with chromaWeightFlag := cwBit == 1 }
      if e.chromaWeightFlag then
        let some (cbW, r5) := r.readSE | return none
        let some (cbO, r6) := r5.readSE | return none
        let some (crW, r7) := r6.readSE | return none
        let some (crO, r8) := r7.readSE | return none
        if cbW.toInt < -128 || cbW.toInt > 127 || cbO.toInt < -128 || cbO.toInt > 127 ||
           crW.toInt < -128 || crW.toInt > 127 || crO.toInt < -128 || crO.toInt > 127 then return none
        e := { e with cbWeight := cbW, cbOffset := cbO, crWeight := crW, crOffset := crO }
        r := r8
    arr := arr.push e
  return some (arr, r)

/-- Parse `pred_weight_table()` (`ISO/IEC 14496-10` §7.3.3.2). -/
def parsePredWeightTable (r0 : BitReader) (isBSlice : Bool) (numRefL0M1 numRefL1M1 : UInt8) (chromaArrayType : Nat)
    : Option (PredWeightTable × BitReader) := Id.run do
  let some (lDen, r1) := r0.readUE | return none
  if lDen > 7 then return none
  let mut r := r1
  let mut cDen : UInt8 := 0
  if chromaArrayType != 0 then
    let some (cd, r2) := r.readUE | return none
    if cd > 7 then return none
    cDen := cd.toUInt8
    r := r2
  let some (l0Arr, r3) := parsePredWeightList r (numRefL0M1.toNat + 1) chromaArrayType | return none
  r := r3
  let mut l1Arr : Array PredWeightEntry := #[]
  if isBSlice then
    let some (arr1, r4) := parsePredWeightList r (numRefL1M1.toNat + 1) chromaArrayType | return none
    l1Arr := arr1
    r := r4
  return some ({ lumaLog2WeightDenom := lDen.toUInt8, chromaLog2WeightDenom := cDen,
                 l0Weights := l0Arr, l1Weights := l1Arr }, r)

/-- Parse `dec_ref_pic_marking()` adaptive MMCO loop (`ISO/IEC 14496-10` §7.3.3.3), bounded by `maxOps ≤ 64`. -/
def parseMmcoOpsLoop (r0 : BitReader) : Option (Array MmcoOp × BitReader) := Id.run do
  let mut r := r0
  let mut ops : Array MmcoOp := #[]
  for _ in [:64] do
    let some (op, r1) := r.readUE | return none
    if op == 0 then
      return some (ops, r1)
    if op > 6 then return none
    if op == 1 || op == 2 || op == 4 || op == 6 then
      let some (a0, r2) := r1.readUE | return none
      if a0 > 0xFFFFFFFF then return none
      ops := ops.push { opcode := op.toUInt8, arg0 := a0.toUInt32 }
      r := r2
    else if op == 3 then
      let some (a0, r2) := r1.readUE | return none
      let some (a1, r3) := r2.readUE | return none
      if a0 > 0xFFFFFFFF || a1 > 0xFFFFFFFF then return none
      ops := ops.push { opcode := 3, arg0 := a0.toUInt32, arg1 := a1.toUInt32 }
      r := r3
    else
      ops := ops.push { opcode := 5 }
      r := r1
  return none

/-- Parse a complete H.264 Slice Header (`nal_unit_type ∈ {1, 5}`, `ISO/IEC 14496-10` §7.3.3) from an EBSP NALU slice. -/
def parseH264SliceHeaderFull (nalPayload : ByteSlice) (sps : H264SpsFull) (pps : H264PpsFull) : Option H264SliceHeaderFull := Id.run do
  if pps.spsId != sps.spsId then return none
  let rbsp := stripRbspEmulationBytesH264 nalPayload true
  if rbsp.size < 2 then return none
  let hdr := rbsp.get! 0
  if (hdr &&& 0x80) != 0 then return none
  let nalRefIdc := (hdr >>> 5) &&& 0x03
  let nalUnitType := hdr &&& 0x1F
  if nalUnitType != 1 && nalUnitType != 5 then return none
  if nalUnitType == 5 && nalRefIdc == 0 then return none
  let r0 : BitReader := { slice := { ba := rbsp, off := 0, len := rbsp.size }, bitOffset := 8 }
  let some (firstMb, r1) := r0.readUE | return none
  let some (st64, r2) := r1.readUE | return none
  let some (ppsId64, r3) := r2.readUE | return none
  if st64 > 9 || ppsId64 != pps.ppsId.toUInt64 then return none
  let some kind := classifyH264SliceType st64.toUInt8 | return none
  if nalUnitType == 5 && kind != .I && kind != .SI then return none
  let mbsMul := if sps.frameMbsOnlyFlag then 1 else 2
  let picSizeInMbs := (sps.picWidthInMbsMinus1.toNat + 1) * (sps.picHeightInMapUnitsMinus1.toNat + 1) * mbsMul
  if firstMb.toNat ≥ picSizeInMbs then return none
  let mut r := r3
  let mut colPlane : UInt8 := 0
  if sps.separateColourPlaneFlag then
    let some (cp, rCp) := r.readBitsMSB 2 | return none
    if cp > 2 then return none
    colPlane := cp.toUInt8
    r := rCp
  let fnBits := sps.log2MaxFrameNumMinus4.toNat + 4
  let some (fn64, rFn) := r.readBitsMSB fnBits | return none
  r := rFn
  let mut fieldPic := false
  let mut bottomField := false
  if !sps.frameMbsOnlyFlag then
    let some (fpBit, rFp) := r.readBit | return none
    fieldPic := fpBit == 1
    r := rFp
    if fieldPic then
      let some (bfBit, rBf) := r.readBit | return none
      bottomField := bfBit == 1
      r := rBf
  let mut idrId : UInt16 := 0
  if nalUnitType == 5 then
    let some (idv, rIdr) := r.readUE | return none
    if idv > 65535 then return none
    idrId := idv.toUInt16
    r := rIdr
  let mut pocLsb : UInt32 := 0
  let mut dPocBot : Int32 := 0
  let mut dPoc0 : Int32 := 0
  let mut dPoc1 : Int32 := 0
  if sps.picOrderCntType == 0 then
    let lsbBits := sps.log2MaxPicOrderCntLsbMinus4.toNat + 4
    let some (lsb64, rLsb) := r.readBitsMSB lsbBits | return none
    pocLsb := lsb64.toUInt32
    r := rLsb
    if pps.bottomFieldPicOrderInFramePresent && !fieldPic then
      let some (dpb, rDpb) := r.readSE | return none
      dPocBot := dpb
      r := rDpb
  else if sps.picOrderCntType == 1 && !sps.deltaPicOrderAlwaysZeroFlag then
    let some (dp0, rDp0) := r.readSE | return none
    dPoc0 := dp0
    r := rDp0
    if pps.bottomFieldPicOrderInFramePresent && !fieldPic then
      let some (dp1, rDp1) := r.readSE | return none
      dPoc1 := dp1
      r := rDp1
  let mut redPicCnt : UInt8 := 0
  if pps.redundantPicCntPresentFlag then
    let some (rpc, rRpc) := r.readUE | return none
    if rpc > 127 then return none
    redPicCnt := rpc.toUInt8
    r := rRpc
  let mut dirSpatial := false
  if kind == .B then
    let some (dsBit, rDs) := r.readBit | return none
    dirSpatial := dsBit == 1
    r := rDs
  let mut numRefOver := false
  let mut numL0M1 : UInt8 := pps.numRefIdxL0DefaultActiveMinus1
  let mut numL1M1 : UInt8 := pps.numRefIdxL1DefaultActiveMinus1
  if kind == .P || kind == .SP || kind == .B then
    let some (ovBit, rOv) := r.readBit | return none
    numRefOver := ovBit == 1
    r := rOv
    if numRefOver then
      let some (l0v, rL0) := r.readUE | return none
      if l0v > 31 then return none
      numL0M1 := l0v.toUInt8
      r := rL0
      if kind == .B then
        let some (l1v, rL1) := r.readUE | return none
        if l1v > 31 then return none
        numL1M1 := l1v.toUInt8
        r := rL1
  let mut modFlagL0 := false
  let mut modOpsL0 : Array RefPicListModOp := #[]
  let mut modFlagL1 := false
  let mut modOpsL1 : Array RefPicListModOp := #[]
  if kind != .I && kind != .SI then
    let some (m0Bit, rM0) := r.readBit | return none
    modFlagL0 := m0Bit == 1
    r := rM0
    if modFlagL0 then
      let some (ops0, rOps0) := parseRefPicListModLoop r | return none
      modOpsL0 := ops0
      r := rOps0
  if kind == .B then
    let some (m1Bit, rM1) := r.readBit | return none
    modFlagL1 := m1Bit == 1
    r := rM1
    if modFlagL1 then
      let some (ops1, rOps1) := parseRefPicListModLoop r | return none
      modOpsL1 := ops1
      r := rOps1
  let hasPwt := (pps.weightedPredFlag && (kind == .P || kind == .SP)) || (pps.weightedBipredIdc == 1 && kind == .B)
  let mut pwtVal : PredWeightTable := {}
  if hasPwt then
    let chromaArrayType := if sps.separateColourPlaneFlag then 0 else sps.chromaFormatIdc.toNat
    let some (pw, rPw) := parsePredWeightTable r (kind == .B) numL0M1 numL1M1 chromaArrayType | return none
    pwtVal := pw
    r := rPw
  let mut noOutPrior := false
  let mut longTermRef := false
  let mut adaptMark := false
  let mut mmcoArr : Array MmcoOp := #[]
  if nalRefIdc != 0 then
    if nalUnitType == 5 then
      let some (noBit, rNo) := r.readBit | return none
      let some (ltBit, rLt) := rNo.readBit | return none
      noOutPrior := noBit == 1
      longTermRef := ltBit == 1
      r := rLt
    else
      let some (adBit, rAd) := r.readBit | return none
      adaptMark := adBit == 1
      r := rAd
      if adaptMark then
        let some (mOps, rMm) := parseMmcoOpsLoop r | return none
        mmcoArr := mOps
        r := rMm
  let mut cabacIdc : UInt8 := 0
  if pps.entropyCodingModeFlag && kind != .I && kind != .SI then
    let some (ci, rCi) := r.readUE | return none
    if ci > 2 then return none
    cabacIdc := ci.toUInt8
    r := rCi
  let some (qpDelta, rQp) := r.readSE | return none
  r := rQp
  let sliceQpYInt : Int := 26 + pps.picInitQpMinus26.toInt + qpDelta.toInt
  let minSliceQpY : Int := -(6 * sps.bitDepthLumaMinus8.toNat)
  if sliceQpYInt < minSliceQpY || sliceQpYInt > 51 then return none
  let mut spSwitch := false
  let mut qsDelta : Int32 := 0
  if kind == .SP || kind == .SI then
    if kind == .SP then
      let some (swBit, rSw) := r.readBit | return none
      spSwitch := swBit == 1
      r := rSw
    let some (qsd, rQs) := r.readSE | return none
    let sliceQsY : Int := 26 + pps.picInitQsMinus26.toInt + qsd.toInt
    if sliceQsY < 0 || sliceQsY > 51 then return none
    qsDelta := qsd
    r := rQs
  let mut disDbf : UInt8 := 0
  let mut alphaDiv2 : Int32 := 0
  let mut betaDiv2 : Int32 := 0
  if pps.deblockingFilterControlPresentFlag then
    let some (dd, rDd) := r.readUE | return none
    if dd > 2 then return none
    disDbf := dd.toUInt8
    r := rDd
    if disDbf != 1 then
      let some (al, rAl) := r.readSE | return none
      let some (be, rBe) := rAl.readSE | return none
      if al.toInt < -6 || al.toInt > 6 || be.toInt < -6 || be.toInt > 6 then return none
      alphaDiv2 := al
      betaDiv2 := be
      r := rBe
  if pps.entropyCodingModeFlag then
    for _ in [:8] do
      if r.bitOffset % 8 != 0 then
        let some (alignBit, rAln) := r.readBit | return none
        if alignBit != 1 then return none
        r := rAln
  return some {
    nalRefIdc, nalUnitType, firstMbInSlice := firstMb.toUInt32,
    sliceType := st64.toUInt8, sliceKind := kind, ppsId := pps.ppsId,
    colourPlaneId := colPlane, frameNum := fn64.toUInt32,
    fieldPicFlag := fieldPic, bottomFieldFlag := bottomField,
    idrPicId := idrId, picOrderCntLsb := pocLsb,
    deltaPicOrderCntBottom := dPocBot, deltaPicOrderCnt0 := dPoc0, deltaPicOrderCnt1 := dPoc1,
    redundantPicCnt := redPicCnt, directSpatialMvPredFlag := dirSpatial,
    numRefIdxActiveOverrideFlag := numRefOver,
    numRefIdxL0ActiveMinus1 := numL0M1, numRefIdxL1ActiveMinus1 := numL1M1,
    refPicListModFlagL0 := modFlagL0, refPicListModL0 := modOpsL0,
    refPicListModFlagL1 := modFlagL1, refPicListModL1 := modOpsL1,
    hasPredWeightTable := hasPwt, predWeightTable := pwtVal,
    noOutputOfPriorPicsFlag := noOutPrior, longTermReferenceFlag := longTermRef,
    adaptiveRefPicMarkingModeFlag := adaptMark, mmcoOps := mmcoArr,
    cabacInitIdc := cabacIdc, sliceQpDelta := qpDelta, sliceQpY := Int32.ofInt sliceQpYInt,
    spForSwitchFlag := spSwitch, sliceQsDelta := qsDelta,
    disableDeblockingFilterIdc := disDbf, sliceAlphaC0OffsetDiv2 := alphaDiv2,
    sliceBetaOffsetDiv2 := betaDiv2, sliceDataBitOffset := r.bitOffset
  }

/-- Serialize one `ref_pic_list_modification` list (`ISO/IEC 14496-10` §7.3.3.1). -/
def writeRefPicListModLoop (w0 : BitWriter) (ops : Array RefPicListModOp) : Option BitWriter := Id.run do
  if ops.size > 32 then return none
  let mut w := w0
  for op in ops do
    if op.modificationOfPicNumsIdc > 2 then return none
    w := w.writeUE op.modificationOfPicNumsIdc.toUInt64
    w := w.writeUE op.param.toUInt64
  return some (w.writeUE 3)

/-- Serialize one `pred_weight_table` reference list (`ISO/IEC 14496-10` §7.3.3.2). -/
def writePredWeightList (w0 : BitWriter) (arr : Array PredWeightEntry) (chromaArrayType : Nat) : Option BitWriter := Id.run do
  let mut w := w0
  for e in arr do
    w := w.writeBit (if e.lumaWeightFlag then 1 else 0)
    if e.lumaWeightFlag then
      if e.lumaWeight.toInt < -128 || e.lumaWeight.toInt > 127 || e.lumaOffset.toInt < -128 || e.lumaOffset.toInt > 127 then return none
      w := w.writeSE e.lumaWeight
      w := w.writeSE e.lumaOffset
    if chromaArrayType != 0 then
      w := w.writeBit (if e.chromaWeightFlag then 1 else 0)
      if e.chromaWeightFlag then
        if e.cbWeight.toInt < -128 || e.cbWeight.toInt > 127 || e.cbOffset.toInt < -128 || e.cbOffset.toInt > 127 ||
           e.crWeight.toInt < -128 || e.crWeight.toInt > 127 || e.crOffset.toInt < -128 || e.crOffset.toInt > 127 then return none
        w := w.writeSE e.cbWeight
        w := w.writeSE e.cbOffset
        w := w.writeSE e.crWeight
        w := w.writeSE e.crOffset
  return some w

/-- Serialize `pred_weight_table()` (`ISO/IEC 14496-10` §7.3.3.2). -/
def writePredWeightTable (w0 : BitWriter) (pwt : PredWeightTable) (isBSlice : Bool) (numRefL0M1 numRefL1M1 : UInt8) (chromaArrayType : Nat)
    : Option BitWriter := Id.run do
  if pwt.lumaLog2WeightDenom > 7 || pwt.l0Weights.size != numRefL0M1.toNat + 1 then return none
  if isBSlice && pwt.l1Weights.size != numRefL1M1.toNat + 1 then return none
  let mut w := w0.writeUE pwt.lumaLog2WeightDenom.toUInt64
  if chromaArrayType != 0 then
    if pwt.chromaLog2WeightDenom > 7 then return none
    w := w.writeUE pwt.chromaLog2WeightDenom.toUInt64
  let some w1 := writePredWeightList w pwt.l0Weights chromaArrayType | return none
  if isBSlice then
    writePredWeightList w1 pwt.l1Weights chromaArrayType
  else
    some w1

/-- Serialize `dec_ref_pic_marking()` adaptive MMCO loop (`ISO/IEC 14496-10` §7.3.3.3). -/
def writeMmcoOpsLoop (w0 : BitWriter) (ops : Array MmcoOp) : Option BitWriter := Id.run do
  if ops.size > 64 then return none
  let mut w := w0
  for op in ops do
    if op.opcode == 0 || op.opcode > 6 then return none
    w := w.writeUE op.opcode.toUInt64
    if op.opcode == 1 || op.opcode == 2 || op.opcode == 4 || op.opcode == 6 then
      w := w.writeUE op.arg0.toUInt64
    else if op.opcode == 3 then
      w := w.writeUE op.arg0.toUInt64
      w := w.writeUE op.arg1.toUInt64
  return some (w.writeUE 0)

/-- Deterministically serialize an `H264SliceHeaderFull` into an H.264 Slice Header EBSP NALU
    (with `cabac_alignment_one_bit` when CABAC, or `rbsp_trailing_bits()` when CAVLC header-only). -/
def serializeH264SliceHeaderFull (sh : H264SliceHeaderFull) (sps : H264SpsFull) (pps : H264PpsFull) : Option ByteArray := Id.run do
  if pps.spsId != sps.spsId || sh.ppsId != pps.ppsId then return none
  if sh.nalRefIdc > 3 || (sh.nalUnitType != 1 && sh.nalUnitType != 5) then return none
  if sh.nalUnitType == 5 && sh.nalRefIdc == 0 then return none
  let some kind := classifyH264SliceType sh.sliceType | return none
  if kind != sh.sliceKind then return none
  if sh.nalUnitType == 5 && kind != .I && kind != .SI then return none
  let mbsMul := if sps.frameMbsOnlyFlag then 1 else 2
  let picSizeInMbs := (sps.picWidthInMbsMinus1.toNat + 1) * (sps.picHeightInMapUnitsMinus1.toNat + 1) * mbsMul
  if sh.firstMbInSlice.toNat ≥ picSizeInMbs then return none
  let hdrByte : UInt8 := ((sh.nalRefIdc &&& 0x03) <<< 5) ||| (sh.nalUnitType &&& 0x1F)
  let mut w := BitWriter.empty 32
  w := w.writeBitsMSB hdrByte.toUInt64 8
  w := w.writeUE sh.firstMbInSlice.toUInt64
  w := w.writeUE sh.sliceType.toUInt64
  w := w.writeUE sh.ppsId.toUInt64
  if sps.separateColourPlaneFlag then
    if sh.colourPlaneId > 2 then return none
    w := w.writeBitsMSB sh.colourPlaneId.toUInt64 2
  let fnBits := sps.log2MaxFrameNumMinus4.toNat + 4
  if sh.frameNum.toNat ≥ (1 <<< fnBits) then return none
  w := w.writeBitsMSB sh.frameNum.toUInt64 fnBits
  if !sps.frameMbsOnlyFlag then
    w := w.writeBit (if sh.fieldPicFlag then 1 else 0)
    if sh.fieldPicFlag then
      w := w.writeBit (if sh.bottomFieldFlag then 1 else 0)
  else if sh.fieldPicFlag || sh.bottomFieldFlag then return none
  if sh.nalUnitType == 5 then
    w := w.writeUE sh.idrPicId.toUInt64
  if sps.picOrderCntType == 0 then
    let lsbBits := sps.log2MaxPicOrderCntLsbMinus4.toNat + 4
    if sh.picOrderCntLsb.toNat ≥ (1 <<< lsbBits) then return none
    w := w.writeBitsMSB sh.picOrderCntLsb.toUInt64 lsbBits
    if pps.bottomFieldPicOrderInFramePresent && !sh.fieldPicFlag then
      w := w.writeSE sh.deltaPicOrderCntBottom
  else if sps.picOrderCntType == 1 && !sps.deltaPicOrderAlwaysZeroFlag then
    w := w.writeSE sh.deltaPicOrderCnt0
    if pps.bottomFieldPicOrderInFramePresent && !sh.fieldPicFlag then
      w := w.writeSE sh.deltaPicOrderCnt1
  if pps.redundantPicCntPresentFlag then
    if sh.redundantPicCnt > 127 then return none
    w := w.writeUE sh.redundantPicCnt.toUInt64
  if kind == .B then
    w := w.writeBit (if sh.directSpatialMvPredFlag then 1 else 0)
  if kind == .P || kind == .SP || kind == .B then
    w := w.writeBit (if sh.numRefIdxActiveOverrideFlag then 1 else 0)
    if sh.numRefIdxActiveOverrideFlag then
      if sh.numRefIdxL0ActiveMinus1 > 31 then return none
      w := w.writeUE sh.numRefIdxL0ActiveMinus1.toUInt64
      if kind == .B then
        if sh.numRefIdxL1ActiveMinus1 > 31 then return none
        w := w.writeUE sh.numRefIdxL1ActiveMinus1.toUInt64
  if kind != .I && kind != .SI then
    w := w.writeBit (if sh.refPicListModFlagL0 then 1 else 0)
    if sh.refPicListModFlagL0 then
      let some wM0 := writeRefPicListModLoop w sh.refPicListModL0 | return none
      w := wM0
  if kind == .B then
    w := w.writeBit (if sh.refPicListModFlagL1 then 1 else 0)
    if sh.refPicListModFlagL1 then
      let some wM1 := writeRefPicListModLoop w sh.refPicListModL1 | return none
      w := wM1
  let expectPwt := (pps.weightedPredFlag && (kind == .P || kind == .SP)) || (pps.weightedBipredIdc == 1 && kind == .B)
  if sh.hasPredWeightTable != expectPwt then return none
  if expectPwt then
    let chromaArrayType := if sps.separateColourPlaneFlag then 0 else sps.chromaFormatIdc.toNat
    let some wPw := writePredWeightTable w sh.predWeightTable (kind == .B)
      sh.numRefIdxL0ActiveMinus1 sh.numRefIdxL1ActiveMinus1 chromaArrayType | return none
    w := wPw
  if sh.nalRefIdc != 0 then
    if sh.nalUnitType == 5 then
      w := w.writeBit (if sh.noOutputOfPriorPicsFlag then 1 else 0)
      w := w.writeBit (if sh.longTermReferenceFlag then 1 else 0)
    else
      w := w.writeBit (if sh.adaptiveRefPicMarkingModeFlag then 1 else 0)
      if sh.adaptiveRefPicMarkingModeFlag then
        let some wMm := writeMmcoOpsLoop w sh.mmcoOps | return none
        w := wMm
  if pps.entropyCodingModeFlag && kind != .I && kind != .SI then
    if sh.cabacInitIdc > 2 then return none
    w := w.writeUE sh.cabacInitIdc.toUInt64
  let sliceQpYInt : Int := 26 + pps.picInitQpMinus26.toInt + sh.sliceQpDelta.toInt
  let minSliceQpY : Int := -(6 * sps.bitDepthLumaMinus8.toNat)
  if sliceQpYInt < minSliceQpY || sliceQpYInt > 51 || sh.sliceQpY.toInt != sliceQpYInt then return none
  w := w.writeSE sh.sliceQpDelta
  if kind == .SP || kind == .SI then
    if kind == .SP then
      w := w.writeBit (if sh.spForSwitchFlag then 1 else 0)
    let sliceQsY : Int := 26 + pps.picInitQsMinus26.toInt + sh.sliceQsDelta.toInt
    if sliceQsY < 0 || sliceQsY > 51 then return none
    w := w.writeSE sh.sliceQsDelta
  if pps.deblockingFilterControlPresentFlag then
    if sh.disableDeblockingFilterIdc > 2 then return none
    w := w.writeUE sh.disableDeblockingFilterIdc.toUInt64
    if sh.disableDeblockingFilterIdc != 1 then
      if sh.sliceAlphaC0OffsetDiv2.toInt < -6 || sh.sliceAlphaC0OffsetDiv2.toInt > 6 ||
         sh.sliceBetaOffsetDiv2.toInt < -6 || sh.sliceBetaOffsetDiv2.toInt > 6 then return none
      w := w.writeSE sh.sliceAlphaC0OffsetDiv2
      w := w.writeSE sh.sliceBetaOffsetDiv2
  if pps.entropyCodingModeFlag then
    for _ in [:8] do
      if w.bitsUsed != 0 then
        w := w.writeBit 1
    w := w.writeBitsMSB 0x80 8
    return some (insertRbspEmulationBytes w.toByteArray true)
  else
    let rbsp := finalizeRbspWriter w
    return some (insertRbspEmulationBytes rbsp true)

/-! ## 7. Picture Order Count (`POC` Type 0 & Type 2, `ISO/IEC 14496-10` §8.2.1.1 & §8.2.1.3) -/

/-- State carried across pictures for `pic_order_cnt_type == 0` (`ISO/IEC 14496-10` §8.2.1.1). -/
structure PocType0State where
  prevPicOrderCntMsb : Int := 0
  prevPicOrderCntLsb : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Pure POC Type 0 derivation (`ISO/IEC 14496-10` §8.2.1.1 Equations 8-3..8-5).
    Returns `(topFieldOrderCnt, bottomFieldOrderCnt, picOrderCnt, nextState)`. -/
def derivePicOrderCntType0 (st : PocType0State) (log2MaxPicOrderCntLsbMinus4 : UInt8)
    (isIdr : Bool) (nalRefIdc : UInt8) (hasMmco5 : Bool)
    (fieldPicFlag bottomFieldFlag bottomFieldPicOrderInFramePresent : Bool)
    (picOrderCntLsb : UInt32) (deltaPicOrderCntBottom : Int32)
    : Int × Int × Int × PocType0State :=
  let maxLsbNat : Nat := 1 <<< (log2MaxPicOrderCntLsbMinus4.toNat + 4)
  let maxLsb : Int := Int.ofNat maxLsbNat
  let prevMsb : Int := if isIdr then 0 else st.prevPicOrderCntMsb
  let prevLsb : Int := if isIdr then 0 else Int.ofNat st.prevPicOrderCntLsb
  let curLsb : Int := Int.ofNat (picOrderCntLsb.toNat % maxLsbNat)
  let picOrderCntMsb : Int :=
    if curLsb < prevLsb && (prevLsb - curLsb) ≥ (maxLsb / 2) then
      prevMsb + maxLsb
    else if curLsb > prevLsb && (curLsb - prevLsb) > (maxLsb / 2) then
      prevMsb - maxLsb
    else
      prevMsb
  let topPoc : Int := picOrderCntMsb + curLsb
  let botPoc : Int :=
    if !fieldPicFlag then
      topPoc + (if bottomFieldPicOrderInFramePresent then deltaPicOrderCntBottom.toInt else 0)
    else
      picOrderCntMsb + curLsb
  let picPoc : Int :=
    if !fieldPicFlag then min topPoc botPoc
    else if bottomFieldFlag then botPoc else topPoc
  let nextSt : PocType0State :=
    if nalRefIdc != 0 then
      if hasMmco5 then
        let tempPicOrderCnt := if !fieldPicFlag || !bottomFieldFlag then topPoc else 0
        { prevPicOrderCntMsb := 0, prevPicOrderCntLsb := (if tempPicOrderCnt ≥ 0 then tempPicOrderCnt.toNat else 0) }
      else
        { prevPicOrderCntMsb := picOrderCntMsb, prevPicOrderCntLsb := curLsb.toNat }
    else
      if isIdr then { prevPicOrderCntMsb := 0, prevPicOrderCntLsb := 0 } else st
  (topPoc, botPoc, picPoc, nextSt)

/-- State carried across pictures for `pic_order_cnt_type == 2` (`ISO/IEC 14496-10` §8.2.1.3). -/
structure PocType2State where
  prevFrameNum       : Nat := 0
  prevFrameNumOffset : Int := 0
  deriving Repr, DecidableEq, Inhabited

/-- Pure POC Type 2 derivation (`ISO/IEC 14496-10` §8.2.1.3 Equations 8-11..8-13).
    Returns `(topFieldOrderCnt, bottomFieldOrderCnt, picOrderCnt, nextState)`. -/
def derivePicOrderCntType2 (st : PocType2State) (log2MaxFrameNumMinus4 : UInt8)
    (isIdr : Bool) (nalRefIdc : UInt8) (hasMmco5 : Bool)
    (frameNum : UInt32) : Int × Int × Int × PocType2State :=
  let maxFrameNumNat : Nat := 1 <<< (log2MaxFrameNumMinus4.toNat + 4)
  let maxFrameNum : Int := Int.ofNat maxFrameNumNat
  let fnNat : Nat := frameNum.toNat % maxFrameNumNat
  let frameNumOffset : Int :=
    if isIdr then 0
    else if st.prevFrameNum > fnNat then st.prevFrameNumOffset + maxFrameNum
    else st.prevFrameNumOffset
  let tempPicOrderCnt : Int :=
    if isIdr then 0
    else if nalRefIdc == 0 then 2 * (frameNumOffset + Int.ofNat fnNat) - 1
    else 2 * (frameNumOffset + Int.ofNat fnNat)
  let nextOffset : Int := if hasMmco5 then 0 else frameNumOffset
  let nextFn : Nat := if hasMmco5 then 0 else fnNat
  (tempPicOrderCnt, tempPicOrderCnt, tempPicOrderCnt, { prevFrameNum := nextFn, prevFrameNumOffset := nextOffset })

/-! ## 8. Stream & Container Probe (`Annex-B` / `MP4 avcC`) + JSON Reporter for CLI & Differential Harness -/

/-- Find the first 4-byte ASCII FourCC box payload inside `buf` (used to locate `avcC` in ISOBMFF `moov`/`stsd`). -/
def findIsoBoxPayload (buf : ByteArray) (tag0 tag1 tag2 tag3 : UInt8) : Option ByteArray := Id.run do
  if buf.size < 8 then return none
  let mut i : Nat := 4
  while i + 4 ≤ buf.size do
    if buf.get! i == tag0 && buf.get! (i + 1) == tag1 &&
       buf.get! (i + 2) == tag2 && buf.get! (i + 3) == tag3 then
      if let some boxLen := readBigEndianN buf (i - 4) 4 then
        if boxLen ≥ 8 && (i - 4) + boxLen ≤ buf.size then
          return some (buf.extract (i + 4) (i - 4 + boxLen))
    i := i + 1
  return none

/-- Format `H264SliceKind` as `"I"`, `"P"`, `"B"`, `"SP"`, or `"SI"`. -/
def H264SliceKind.toString : H264SliceKind → String
  | .I  => "I"
  | .P  => "P"
  | .B  => "B"
  | .SP => "SP"
  | .SI => "SI"

/-- Probe an Annex-B `.264` stream OR an ISOBMFF `.mp4` (via `avcC` + `mdat` or raw `avcC` bytes)
    and return a deterministic JSON report covering SPS, PPS, `avcC` round-trip, Annex-B <-> AVCC round-trip,
    and per-slice `(nal_unit_type, slice_type, frame_num, slice_qp_y, poc, slice_data_bit_offset)`. -/
def probeH264SyntaxJson (raw : ByteArray) : Option String := Id.run do
  let mut spsList : Array H264SpsFull := #[]
  let mut ppsList : Array H264PpsFull := #[]
  let mut vclNalus : Array ByteArray := #[]
  let mut avccRoundtripOk := true
  let mut framingRoundtripOk := true
  if let some avccRaw := findIsoBoxPayload raw 0x61 0x76 0x63 0x43 then
    let some avccRec := parseAvcDecoderConfigRecord avccRaw | return none
    let some avccReenc := serializeAvcDecoderConfigRecord avccRec | return none
    avccRoundtripOk := parseAvcDecoderConfigRecord avccReenc == some avccRec && avccReenc == avccRaw
    for sNal in avccRec.spsNalus do
      let some sps := parseH264SpsFull (ByteSlice.ofByteArray sNal) | return none
      if let some sRe := serializeH264SpsFull sps then
        if parseH264SpsFull (ByteSlice.ofByteArray sRe) != some sps then return none
      else return none
      spsList := spsList.push sps
    for pNal in avccRec.ppsNalus do
      let activeSps := spsList[0]?
      let some pps := parseH264PpsFull (ByteSlice.ofByteArray pNal) activeSps | return none
      let chIdc := match activeSps with | some s => s.chromaFormatIdc | none => 1
      let bdL := match activeSps with | some s => s.bitDepthLumaMinus8 | none => 0
      if let some pRe := serializeH264PpsFull pps chIdc bdL then
        if parseH264PpsFull (ByteSlice.ofByteArray pRe) activeSps != some pps then return none
      else return none
      ppsList := ppsList.push pps
    let nls := avccRec.lengthSizeMinusOne.toNat + 1
    if let some mdatRaw := findIsoBoxPayload raw 0x6D 0x64 0x61 0x74 then
      if let some pkts := splitAvccPacket mdatRaw nls then
        for nal in pkts do
          let nt := nal.data.getD 0 0 &&& 0x1F
          if nt == 1 || nt == 5 then vclNalus := vclNalus.push nal
        if let some ab := packAnnexBPacket pkts then
          framingRoundtripOk := annexBToAvccPacket ab nls == some mdatRaw
  else
    let nalus := splitAnnexBPacket raw
    if nalus.isEmpty then return none
    if let some avcc4 := packAvccPacket nalus 4 then
      framingRoundtripOk := splitAvccPacket avcc4 4 == some nalus
    else
      framingRoundtripOk := false
    for nal in nalus do
      let nt := nal.data.getD 0 0 &&& 0x1F
      if nt == 7 then
        let some sps := parseH264SpsFull (ByteSlice.ofByteArray nal) | return none
        if let some sRe := serializeH264SpsFull sps then
          if parseH264SpsFull (ByteSlice.ofByteArray sRe) != some sps then return none
        else return none
        if spsList.all (fun x => x.spsId != sps.spsId) then spsList := spsList.push sps
      else if nt == 8 then
        let activeSps := spsList[0]?
        let some pps := parseH264PpsFull (ByteSlice.ofByteArray nal) activeSps | return none
        let chIdc := match activeSps with | some s => s.chromaFormatIdc | none => 1
        let bdL := match activeSps with | some s => s.bitDepthLumaMinus8 | none => 0
        if let some pRe := serializeH264PpsFull pps chIdc bdL then
          if parseH264PpsFull (ByteSlice.ofByteArray pRe) activeSps != some pps then return none
        else return none
        if ppsList.all (fun x => x.ppsId != pps.ppsId) then ppsList := ppsList.push pps
      else if nt == 1 || nt == 5 then
        vclNalus := vclNalus.push nal
  let some sps0 := spsList[0]? | return none
  let some pps0 := ppsList[0]? | return none
  let mut poc0St : PocType0State := {}
  let mut poc2St : PocType2State := {}
  let mut sliceHeaderRoundtripOk := true
  let mut sliceJsons : Array String := #[]
  for nal in vclNalus do
    let some sh := parseH264SliceHeaderFull (ByteSlice.ofByteArray nal) sps0 pps0 | return none
    if let some shRe := serializeH264SliceHeaderFull sh sps0 pps0 then
      if parseH264SliceHeaderFull (ByteSlice.ofByteArray shRe) sps0 pps0 != some sh then
        sliceHeaderRoundtripOk := false
    else
      sliceHeaderRoundtripOk := false
    let hasMmco5 := sh.mmcoOps.any (fun m => m.opcode == 5)
    let isIdr := sh.nalUnitType == 5
    let mut pocVal : Int := 0
    if sps0.picOrderCntType == 0 then
      let (_, _, p, stNext) := derivePicOrderCntType0 poc0St sps0.log2MaxPicOrderCntLsbMinus4 isIdr sh.nalRefIdc
        hasMmco5 sh.fieldPicFlag sh.bottomFieldFlag pps0.bottomFieldPicOrderInFramePresent sh.picOrderCntLsb sh.deltaPicOrderCntBottom
      if sh.firstMbInSlice == 0 then poc0St := stNext
      pocVal := p
    else if sps0.picOrderCntType == 2 then
      let (_, _, p, stNext) := derivePicOrderCntType2 poc2St sps0.log2MaxFrameNumMinus4 isIdr sh.nalRefIdc hasMmco5 sh.frameNum
      if sh.firstMbInSlice == 0 then poc2St := stNext
      pocVal := p
    if sh.firstMbInSlice == 0 then
      let jA := s!"\{\"nal_type\":{sh.nalUnitType},\"nal_ref_idc\":{sh.nalRefIdc},\"pict_type\":\"{sh.sliceKind.toString}\","
      let jB := s!"\"slice_type\":{sh.sliceType},\"frame_num\":{sh.frameNum},\"poc\":{pocVal},"
      let jC := s!"\"slice_qp_y\":{sh.sliceQpY},\"cabac_init_idc\":{sh.cabacInitIdc},"
      let jD := s!"\"data_bit_offset\":{sh.sliceDataBitOffset}}"
      sliceJsons := sliceJsons.push (jA ++ jB ++ jC ++ jD)
  let slicesStr := String.intercalate "," sliceJsons.toList
  let bdL := sps0.bitDepthLumaMinus8.toNat + 8
  let bdC := sps0.bitDepthChromaMinus8.toNat + 8
  let initQp := pps0.picInitQpMinus26.toInt + 26
  let s0 := s!"\{\"ok\":true,\"profile_idc\":{sps0.profileIdc},\"level_idc\":{sps0.levelIdc},"
  let s0b := s!"\"sps_id\":{sps0.spsId},\"pps_id\":{pps0.ppsId},"
  let s1 := s!"\"chroma_format_idc\":{sps0.chromaFormatIdc},\"bit_depth_luma\":{bdL},\"bit_depth_chroma\":{bdC},"
  let s2 := s!"\"qpprime_bypass\":{sps0.qpprimeYZeroTransformBypass},\"seq_scaling_matrix\":{sps0.seqScalingMatrixPresentFlag},"
  let s2b := s!"\"pic_scaling_matrix\":{pps0.picScalingMatrixPresentFlag},\"weighted_pred\":{pps0.weightedPredFlag},"
  let s2c := s!"\"weighted_bipred_idc\":{pps0.weightedBipredIdc},"
  let s3 := s!"\"width\":{sps0.widthPx},\"height\":{sps0.heightPx},"
  let s3b := s!"\"poc_type\":{sps0.picOrderCntType},\"max_num_ref_frames\":{sps0.maxNumRefFrames},"
  let s4 := s!"\"vui_present\":{sps0.vuiParametersPresentFlag},"
  let s4b := s!"\"num_units_in_tick\":{sps0.vui.numUnitsInTick},\"time_scale\":{sps0.vui.timeScale},"
  let s5 := s!"\"cabac\":{pps0.entropyCodingModeFlag},\"transform_8x8\":{pps0.transform8x8ModeFlag},\"pic_init_qp\":{initQp},"
  let s6 := s!"\"avcc_roundtrip_ok\":{avccRoundtripOk},\"framing_roundtrip_ok\":{framingRoundtripOk},"
  let s6b := s!"\"slice_header_roundtrip_ok\":{sliceHeaderRoundtripOk},\"frames\":[{slicesStr}]}"
  return some (s0 ++ s0b ++ s1 ++ s2 ++ s2b ++ s2c ++ s3 ++ s3b ++ s4 ++ s4b ++ s5 ++ s6 ++ s6b)

/-- Self-test check exercising RBSP/EBSP, `avcC`, full SPS/PPS (`1280x720` real FFmpeg bytes),
    Slice Header, and POC Type 0/2. -/
def runH264SyntaxSelfCheck : Bool :=
  let spsRealOpt := parseH264SpsFull (ByteSlice.ofByteArray (ByteArray.mk realFfmpegH264SpsBytes))
  let ppsRealOpt := parseH264PpsFull (ByteSlice.ofByteArray (ByteArray.mk realFfmpegH264PpsBytes)) spsRealOpt
  let realOk := match spsRealOpt, ppsRealOpt with
    | some sps, some pps =>
      sps.profileIdc == 66 && sps.widthPx == 1280 && sps.heightPx == 720 &&
      (serializeH264SpsFull sps).bind (fun b => parseH264SpsFull (ByteSlice.ofByteArray b)) == some sps &&
      (serializeH264PpsFull pps sps.chromaFormatIdc sps.bitDepthLumaMinus8).bind
        (fun b => parseH264PpsFull (ByteSlice.ofByteArray b) (some sps)) == some pps
    | _, _ => false
  let rawRbsp : List UInt8 := [0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x02, 0x00, 0x00, 0x03, 0x04]
  let ebsp := insertRbspEmulationList rawRbsp
  let rbspOk := stripRbspEmulationList ebsp == rawRbsp && ebsp.length > rawRbsp.length
  let (_, _, pocIdr, st1) := derivePicOrderCntType0 {} 0 true 3 false false false false 0 0
  let (_, _, pocP, st2)   := derivePicOrderCntType0 st1 0 false 2 false false false false 4 0
  let (_, _, pocB, _)     := derivePicOrderCntType0 st2 0 false 0 false false false false 2 0
  realOk && rbspOk && pocIdr == 0 && pocP == 4 && pocB == 2

end LeanAV.H264Syntax
