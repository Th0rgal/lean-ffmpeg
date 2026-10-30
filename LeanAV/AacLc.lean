/-
  LeanAV.AacLc: Standalone ISO/IEC 14496-3 AAC-LC Encoder, Decoder, ADTS & MP4 (`esds`/`mp4a`) Framing
  - Step A: ADTS 7/9-byte header + CRC-16 (`0x8005`), AudioSpecificConfig (`AOT=2`),
    ISO/IEC 14496-3 Tables 4.113–4.128 scale-factor band offsets, and `x^(4/3)` / `x^(3/4)` quantizer.
  - Step B: sine / KBD windows, MDCT-IV / IMDCT + TDAC, rate-controlled quantizer, TNS, M/S.
  - Step C: Huffman codebooks `0..11` + `hcb_sf`, `raw_data_block`, ADTS stream codec.
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.Format
import LeanAV.Audio

namespace LeanAV.AacLc

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream
open LeanAV.Format
open LeanAV.Audio

/-- ISO/IEC 14496-3 Table 1.18 standard sampling frequency table (`0..12`). -/
def aacSampleRateFromIndex (idx : UInt8) : Option UInt32 :=
  match idx.toNat with
  | 0  => some 96000
  | 1  => some 88200
  | 2  => some 64000
  | 3  => some 48000
  | 4  => some 44100
  | 5  => some 32000
  | 6  => some 24000
  | 7  => some 22050
  | 8  => some 16000
  | 9  => some 12000
  | 10 => some 11025
  | 11 => some 8000
  | 12 => some 7350
  | _  => none

/-- Inverse lookup of `samplingFrequencyIndex` (`0..12`) from sample rate in Hz. -/
def aacSampleRateToIndex (sr : UInt32) : Option UInt8 :=
  match sr.toNat with
  | 96000 => some 0
  | 88200 => some 1
  | 64000 => some 2
  | 48000 => some 3
  | 44100 => some 4
  | 32000 => some 5
  | 24000 => some 6
  | 22050 => some 7
  | 16000 => some 8
  | 12000 => some 9
  | 11025 => some 10
  | 8000  => some 11
  | 7350  => some 12
  | _     => none

/-- ISO/IEC 14496-3 §1.6.2.1 AudioSpecificConfig restricted to AAC-LC (`AOT = 2`). -/
structure AacLcAsc where
  audioObjectType        : UInt8 := 2
  samplingFrequencyIndex : UInt8
  channelConfiguration   : UInt8
  frameLengthFlag        : Bool := false
  dependsOnCoreCoder     : Bool := false
  extensionFlag          : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Domain predicate for standalone AAC-LC AudioSpecificConfig (`AOT=2`, `sfi ≤ 12`, `ch ∈ {1,2}`, `1024`-sample frames). -/
def isValidAacLcAsc (asc : AacLcAsc) : Bool :=
  asc.audioObjectType == 2 &&
  asc.samplingFrequencyIndex <= 12 &&
  (asc.channelConfiguration == 1 || asc.channelConfiguration == 2) &&
  !asc.frameLengthFlag &&
  !asc.dependsOnCoreCoder &&
  !asc.extensionFlag

/-- Encode `AacLcAsc` into a 2-byte ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` list. -/
def encodeAacLcAscBytes (asc : AacLcAsc) : List UInt8 :=
  let aot := asc.audioObjectType &&& 0x1F
  let sfi := asc.samplingFrequencyIndex &&& 0x0F
  let ch  := asc.channelConfiguration &&& 0x0F
  let fl  : UInt8 := if asc.frameLengthFlag then 1 else 0
  let dep : UInt8 := if asc.dependsOnCoreCoder then 1 else 0
  let ext : UInt8 := if asc.extensionFlag then 1 else 0
  let b0 : UInt8 := (aot <<< 3) ||| (sfi >>> 1)
  let b1 : UInt8 := ((sfi &&& 0x01) <<< 7) ||| (ch <<< 3) ||| (fl <<< 2) ||| (dep <<< 1) ||| ext
  [b0, b1]

/-- Encode `AacLcAsc` into a 2-byte `ByteArray`. -/
def encodeAacLcAsc (asc : AacLcAsc) : ByteArray :=
  ByteArray.mk (encodeAacLcAscBytes asc).toArray

/-- Decode a 2-byte AAC-LC `AudioSpecificConfig` from `List UInt8` (fails closed outside `isValidAacLcAsc`). -/
def decodeAacLcAscBytes : List UInt8 → Option AacLcAsc
  | b0 :: b1 :: _ =>
    let asc : AacLcAsc := {
      audioObjectType        := (b0 >>> 3) &&& 0x1F
      samplingFrequencyIndex := ((b0 &&& 0x07) <<< 1) ||| ((b1 >>> 7) &&& 0x01)
      channelConfiguration   := (b1 >>> 3) &&& 0x0F
      frameLengthFlag        := ((b1 >>> 2) &&& 0x01) == 1
      dependsOnCoreCoder     := ((b1 >>> 1) &&& 0x01) == 1
      extensionFlag          := (b1 &&& 0x01) == 1
    }
    if isValidAacLcAsc asc then some asc else none
  | _ => none

/-- Decode a 2-byte AAC-LC `AudioSpecificConfig` from `ByteSlice`. -/
def decodeAacLcAsc (s : ByteSlice) : Option AacLcAsc :=
  if s.len < 2 then none
  else decodeAacLcAscBytes [sliceByteD s 0, sliceByteD s 1]

/-- Build an ISO/IEC 14496-14 `esds` full box wrapping an AAC-LC `AudioSpecificConfig`. -/
def buildMp4EsdsBox (asc : AacLcAsc) (avgBitrate maxBitrate : UInt32 := 128000) : ByteArray := Id.run do
  let ascBytes := encodeAacLcAsc asc
  let decSpecInfoLen : UInt8 := ascBytes.size.toUInt8
  let decCfgLen : UInt8 := (13 + 2 + ascBytes.size).toUInt8
  let esDescrLen : UInt8 := (3 + 2 + decCfgLen.toNat + 3).toUInt8
  let mut body := ByteArray.emptyWithCapacity 40
  body := pushU32BE body 0 -- version 0, flags 0
  body := body.push 0x03 -- ES_DescrTag
  body := body.push esDescrLen
  body := pushU16BE body 1 -- ES_ID = 1
  body := body.push 0x00 -- streamDependence/URL/OCR flags = 0
  body := body.push 0x04 -- DecoderConfigDescrTag
  body := body.push decCfgLen
  body := body.push 0x40 -- objectTypeIndication = 0x40 (Audio ISO/IEC 14496-3)
  body := body.push 0x15 -- streamType = 5 (AudioStream << 2 | 1)
  body := body.push 0x00; body := body.push 0x18; body := body.push 0x00 -- bufferSizeDB = 6144
  body := pushU32BE body maxBitrate
  body := pushU32BE body avgBitrate
  body := body.push 0x05 -- DecSpecificInfoTag
  body := body.push decSpecInfoLen
  for i in [:ascBytes.size] do
    body := body.push (ascBytes.get! i)
  body := body.push 0x06 -- SLConfigDescrTag
  body := body.push 0x01
  body := body.push 0x02 -- predefined = 2 (MP4)
  wrapMp4Box 'e' 's' 'd' 's' body

/-- Build an ISO BMFF `mp4a` `AudioSampleEntry` box containing `esds`. -/
def buildMp4aSampleEntryBox (asc : AacLcAsc) (avgBitrate maxBitrate : UInt32 := 128000) : Option ByteArray := do
  if !isValidAacLcAsc asc then none
  let sr ← aacSampleRateFromIndex asc.samplingFrequencyIndex
  let esds := buildMp4EsdsBox asc avgBitrate maxBitrate
  let mut mp4a := ByteArray.emptyWithCapacity (28 + esds.size)
  mp4a := pushZeros mp4a 6 -- reserved
  mp4a := pushU16BE mp4a 1 -- data_reference_index = 1
  mp4a := pushZeros mp4a 8 -- reserved[2]
  mp4a := pushU16BE mp4a asc.channelConfiguration.toUInt16
  mp4a := pushU16BE mp4a 16 -- sampleSize = 16
  mp4a := pushU16BE mp4a 0 -- pre_defined
  mp4a := pushU16BE mp4a 0 -- reserved
  mp4a := pushU32BE mp4a ((sr &&& 0xFFFF) <<< 16)
  for i in [:esds.size] do
    mp4a := mp4a.push (esds.get! i)
  some (wrapMp4Box 'm' 'p' '4' 'a' mp4a)

/-- Extract `AacLcAsc` from an ISO/IEC 14496-14 `esds` box slice by scanning for `DecSpecificInfoTag` (`0x05`). -/
def parseMp4EsdsAsc (s : ByteSlice) : Option AacLcAsc := Id.run do
  if s.len < 16 then return none
  if sliceByteD s 4 != 'e'.toNat.toUInt8 || sliceByteD s 5 != 's'.toNat.toUInt8 ||
     sliceByteD s 6 != 'd'.toNat.toUInt8 || sliceByteD s 7 != 's'.toNat.toUInt8 then
    return none
  let mut idx := 12
  while idx + 3 < s.len do
    let tag := sliceByteD s idx
    idx := idx + 1
    -- Skip expandable length prefix bytes (`0x80` continuation)
    let mut lenVal : Nat := 0
    let mut k := 0
    while k < 4 && idx < s.len do
      let lb := sliceByteD s idx
      idx := idx + 1
      lenVal := (lenVal <<< 7) + (lb &&& 0x7F).toNat
      if (lb &&& 0x80) == 0 then k := 4 else k := k + 1
    if tag == 0x03 then
      idx := idx + 3
    else if tag == 0x04 then
      idx := idx + 13
    else if tag == 0x05 then
      if lenVal >= 2 && idx + 1 < s.len then
        return decodeAacLcAscBytes [sliceByteD s idx, sliceByteD s (idx + 1)]
      else
        return none
    else
      idx := idx + lenVal
  return none

/-- Single-bit step of ISO/IEC 14496-3 ADTS CRC-16 (`x^16 + x^15 + x^2 + 1`, polynomial `0x8005`). -/
@[inline]
def aacAdtsCrc16StepBit (crc : UInt16) (bit : UInt8) : UInt16 :=
  let msb : UInt8 := ((crc >>> 15) &&& 1).toUInt8
  if (msb ^^^ (bit &&& 1)) != 0 then (crc <<< 1) ^^^ 0x8005 else crc <<< 1

/-- Byte update of ADTS CRC-16 (`0x8005`), MSB-first. -/
@[inline]
def aacAdtsCrc16StepByte (crc : UInt16) (b : UInt8) : UInt16 :=
  let c0 := aacAdtsCrc16StepBit crc ((b >>> 7) &&& 1)
  let c1 := aacAdtsCrc16StepBit c0  ((b >>> 6) &&& 1)
  let c2 := aacAdtsCrc16StepBit c1  ((b >>> 5) &&& 1)
  let c3 := aacAdtsCrc16StepBit c2  ((b >>> 4) &&& 1)
  let c4 := aacAdtsCrc16StepBit c3  ((b >>> 3) &&& 1)
  let c5 := aacAdtsCrc16StepBit c4  ((b >>> 2) &&& 1)
  let c6 := aacAdtsCrc16StepBit c5  ((b >>> 1) &&& 1)
  aacAdtsCrc16StepBit c6 (b &&& 1)

/-- Compute ISO/IEC 14496-3 ADTS CRC-16 (`init = 0xFFFF`, `xorOut = 0xFFFF`, poly `0x8005`) over raw payload bytes. -/
def aacAdtsCrc16Bytes (bytes : List UInt8) : UInt16 :=
  (bytes.foldl aacAdtsCrc16StepByte 0xFFFF) ^^^ 0xFFFF

/-- Compute ADTS CRC-16 over a `ByteSlice` (covering up to the first 192 bits / 24 bytes of `raw_data_block` or full slice). -/
def aacAdtsCrc16Slice (s : ByteSlice) : UInt16 := Id.run do
  let mut crc : UInt16 := 0xFFFF
  for i in [:s.len] do
    crc := aacAdtsCrc16StepByte crc (sliceByteD s i)
  return crc ^^^ 0xFFFF

/-- Parsed 7-byte or 9-byte ISO/IEC 14496-3 §1.A.2.2.1 ADTS frame header for AAC-LC. -/
structure AacLcAdtsHeader where
  mpegVersion          : UInt8 := 0    -- 0 = MPEG-4, 1 = MPEG-2
  protectionAbsent     : Bool  := true -- true = 7-byte header, false = 9-byte header + CRC16
  profileObjectType    : UInt8 := 2    -- 2 = AAC-LC (encoded on wire as `profile_ObjectType - 1 = 1`)
  samplingFrequencyIdx : UInt8
  channelConfiguration : UInt8
  frameLength          : UInt16
  bufferFullness       : UInt16 := 0x7FF
  numRawBlocksMinus1   : UInt8 := 0
  crc16                : UInt16 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Header byte length (`7` when `protectionAbsent`, `9` when CRC-16 is present). -/
@[inline]
def AacLcAdtsHeader.headerBytes (h : AacLcAdtsHeader) : Nat :=
  if h.protectionAbsent then 7 else 9

/-- Structural validity predicate for an AAC-LC ADTS frame header. -/
def isValidAacLcAdtsHeader (h : AacLcAdtsHeader) : Bool :=
  (h.mpegVersion == 0 || h.mpegVersion == 1) &&
  h.profileObjectType == 2 &&
  h.samplingFrequencyIdx <= 12 &&
  (h.channelConfiguration == 1 || h.channelConfiguration == 2) &&
  h.frameLength.toNat >= h.headerBytes &&
  h.frameLength.toNat <= 8191 &&
  h.bufferFullness <= 0x07FF &&
  h.numRawBlocksMinus1 == 0

/-- Serialize an `AacLcAdtsHeader` into its 7-byte (no CRC) or 9-byte (with CRC-16) wire representation. -/
def encodeAacLcAdtsHeaderBytes (h : AacLcAdtsHeader) : List UInt8 :=
  let b0 : UInt8 := 0xFF
  let b1 : UInt8 := (0xF0 : UInt8) ||| ((h.mpegVersion &&& 1) <<< 3) ||| (if h.protectionAbsent then 1 else 0)
  let profBits : UInt8 := ((h.profileObjectType - 1) &&& 0x03)
  let sfiBits  : UInt8 := h.samplingFrequencyIdx &&& 0x0F
  let chBits   : UInt8 := h.channelConfiguration &&& 0x07
  let b2 : UInt8 := (profBits <<< 6) ||| (sfiBits <<< 2) ||| (chBits >>> 2)
  let fl : UInt16 := h.frameLength &&& 0x1FFF
  let b3 : UInt8 := ((chBits &&& 0x03) <<< 6) ||| ((fl >>> 11).toUInt8 &&& 0x03)
  let b4 : UInt8 := ((fl >>> 3) &&& 0xFF).toUInt8
  let bf : UInt16 := h.bufferFullness &&& 0x07FF
  let b5 : UInt8 := (((fl &&& 0x07).toUInt8) <<< 5) ||| ((bf >>> 6).toUInt8 &&& 0x1F)
  let b6 : UInt8 := (((bf &&& 0x3F).toUInt8) <<< 2) ||| (h.numRawBlocksMinus1 &&& 0x03)
  if h.protectionAbsent then
    [b0, b1, b2, b3, b4, b5, b6]
  else
    let c0 : UInt8 := ((h.crc16 >>> 8) &&& 0xFF).toUInt8
    let c1 : UInt8 := (h.crc16 &&& 0xFF).toUInt8
    [b0, b1, b2, b3, b4, b5, b6, c0, c1]

/-- Parse a 7-byte or 9-byte `AacLcAdtsHeader` from `ByteSlice` (fails closed on bad syncword, Layer != 0, SSR/Main/LTP, or short length). -/
def decodeAacLcAdtsHeader (s : ByteSlice) : Option AacLcAdtsHeader := do
  if s.len < 7 then none
  let b0 := sliceByteD s 0
  let b1 := sliceByteD s 1
  if b0 != 0xFF || (b1 &&& 0xF0) != 0xF0 || (b1 &&& 0x06) != 0 then none
  let b2 := sliceByteD s 2
  let b3 := sliceByteD s 3
  let b4 := sliceByteD s 4
  let b5 := sliceByteD s 5
  let b6 := sliceByteD s 6
  let protAbs := (b1 &&& 0x01) == 1
  if !protAbs && s.len < 9 then none
  let crcVal : UInt16 :=
    if protAbs then 0
    else ((sliceByteD s 7).toUInt16 <<< 8) ||| (sliceByteD s 8).toUInt16
  let hdr : AacLcAdtsHeader := {
    mpegVersion          := (b1 >>> 3) &&& 0x01
    protectionAbsent     := protAbs
    profileObjectType    := ((b2 >>> 6) &&& 0x03) + 1
    samplingFrequencyIdx := (b2 >>> 2) &&& 0x0F
    channelConfiguration := ((b2 &&& 0x01) <<< 2) ||| ((b3 >>> 6) &&& 0x03)
    frameLength          := (((b3 &&& 0x03).toUInt16) <<< 11) ||| (b4.toUInt16 <<< 3) ||| ((b5 >>> 5).toUInt16 &&& 0x07)
    bufferFullness       := (((b5 &&& 0x1F).toUInt16) <<< 6) ||| ((b6 >>> 2).toUInt16 &&& 0x3F)
    numRawBlocksMinus1   := b6 &&& 0x03
    crc16                := crcVal
  }
  if isValidAacLcAdtsHeader hdr then some hdr else none

/-- Wrap a single `raw_data_block` payload in a 7-byte (`withCrc = false`) or 9-byte (`withCrc = true`) ADTS frame. -/
def muxAdtsFrame (sfi chCfg : UInt8) (rawBlock : ByteArray) (withCrc : Bool := false) : Option ByteArray := do
  let hdrLen := if withCrc then 9 else 7
  let totalLen := hdrLen + rawBlock.size
  if totalLen > 8191 || sfi > 12 || (chCfg != 1 && chCfg != 2) then none
  let crc : UInt16 :=
    if withCrc then aacAdtsCrc16Slice (ByteSlice.ofByteArray rawBlock) else 0
  let hdr : AacLcAdtsHeader := {
    mpegVersion          := 0
    protectionAbsent     := !withCrc
    profileObjectType    := 2
    samplingFrequencyIdx := sfi
    channelConfiguration := chCfg
    frameLength          := totalLen.toUInt16
    bufferFullness       := 0x7FF
    numRawBlocksMinus1   := 0
    crc16                := crc
  }
  let hdrBytes := ByteArray.mk (encodeAacLcAdtsHeaderBytes hdr).toArray
  some (hdrBytes ++ rawBlock)

/-- Demux consecutive ADTS frames from `s : ByteSlice`, failing closed on trailing junk, truncated frames, or mismatched parameters. -/
def demuxAdtsStream (s : ByteSlice) (verifyCrc : Bool := false) : Option (AacLcAdtsHeader × Array ByteSlice) := Id.run do
  if s.len < 7 then return none
  let mut pos : Nat := 0
  let mut firstHdr? : Option AacLcAdtsHeader := none
  let mut frames : Array ByteSlice := #[]
  while pos < s.len do
    let remLen := s.len - pos
    if remLen < 7 then return none
    let sub : ByteSlice := { ba := s.ba, off := s.off + pos, len := remLen }
    let some hdr := decodeAacLcAdtsHeader sub | return none
    let fLen := hdr.frameLength.toNat
    let hLen := hdr.headerBytes
    if fLen < hLen || pos + fLen > s.len then return none
    let payload : ByteSlice := { ba := s.ba, off := s.off + pos + hLen, len := fLen - hLen }
    if verifyCrc && !hdr.protectionAbsent then
      if aacAdtsCrc16Slice payload != hdr.crc16 then return none
    match firstHdr? with
    | none => firstHdr? := some hdr
    | some h0 =>
      if hdr.samplingFrequencyIdx != h0.samplingFrequencyIdx ||
         hdr.channelConfiguration != h0.channelConfiguration ||
         hdr.profileObjectType != h0.profileObjectType then
        return none
    frames := frames.push payload
    pos := pos + fLen
  match firstHdr? with
  | some h0 => if frames.isEmpty then none else some (h0, frames)
  | none    => none

/-! ## ISO/IEC 14496-3 Tables 4.113–4.128 Scale-Factor Band (`swb_offset`) Tables -/

/-- Long-window (`N = 1024`) `swb_offset` table for 96 kHz & 88.2 kHz (`num_swb = 41`, ends at `1024`). -/
def swbOffsetLong96k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88,
    96, 108, 120, 132, 144, 156, 172, 188, 212, 240, 276, 320, 384, 448, 512,
    576, 640, 704, 768, 832, 896, 960, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 64 kHz (`num_swb = 47`, ends at `1024`). -/
def swbOffsetLong64k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88,
    100, 112, 124, 140, 156, 172, 192, 216, 240, 268, 304, 344, 384, 424, 464,
    504, 544, 584, 624, 664, 704, 744, 784, 824, 864, 904, 944, 984, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 48 kHz & 44.1 kHz (`num_swb = 49`, ends at `1024`). -/
def swbOffsetLong48k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 56, 64, 72, 80, 88, 96, 108,
    120, 132, 144, 160, 176, 196, 216, 240, 264, 292, 320, 352, 384, 416, 448,
    480, 512, 544, 576, 608, 640, 672, 704, 736, 768, 800, 832, 864, 896, 928, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 32 kHz (`num_swb = 51`, ends at `1024`). -/
def swbOffsetLong32k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 56, 64, 72, 80, 88, 96, 108,
    120, 132, 144, 160, 176, 196, 216, 240, 264, 292, 320, 352, 384, 416, 448,
    480, 512, 544, 576, 608, 640, 672, 704, 736, 768, 800, 832, 864, 896, 928,
    960, 992, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 24 kHz & 22.05 kHz (`num_swb = 47`, ends at `1024`). -/
def swbOffsetLong24k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 52, 60, 68, 76, 84, 92, 100,
    108, 116, 124, 136, 148, 160, 172, 188, 204, 220, 240, 260, 284, 308, 336,
    364, 396, 432, 468, 508, 552, 600, 652, 704, 768, 832, 896, 960, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 16 kHz, 12 kHz & 11.025 kHz (`num_swb = 43`, ends at `1024`). -/
def swbOffsetLong16k : Array Nat :=
  #[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 100, 112, 124, 136, 148, 160,
    172, 184, 196, 212, 228, 244, 260, 280, 300, 320, 344, 368, 396, 424, 456,
    492, 532, 572, 616, 664, 716, 772, 832, 896, 960, 1024]

/-- Long-window (`N = 1024`) `swb_offset` table for 8 kHz & 7.35 kHz (`num_swb = 40`, ends at `1024`). -/
def swbOffsetLong8k : Array Nat :=
  #[0, 12, 24, 36, 48, 60, 72, 84, 96, 108, 120, 132, 144, 156, 172, 188, 204,
    220, 236, 252, 268, 288, 308, 328, 348, 372, 396, 420, 448, 476, 508, 544,
    580, 620, 664, 712, 764, 820, 880, 944, 1024]

/-- Short-window (`N = 128`) `swb_offset` table for 96 kHz, 88.2 kHz & 64 kHz (`num_swb = 12`, ends at `128`). -/
def swbOffsetShort96k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 32, 40, 48, 64, 92, 128]

/-- Short-window (`N = 128`) `swb_offset` table for 48 kHz, 44.1 kHz & 32 kHz (`num_swb = 14`, ends at `128`). -/
def swbOffsetShort48k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 28, 36, 44, 56, 68, 80, 96, 112, 128]

/-- Short-window (`N = 128`) `swb_offset` table for 24 kHz & 22.05 kHz (`num_swb = 15`, ends at `128`). -/
def swbOffsetShort24k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 36, 44, 52, 64, 76, 92, 108, 128]

/-- Short-window (`N = 128`) `swb_offset` table for 16 kHz, 12 kHz & 11.025 kHz (`num_swb = 15`, ends at `128`). -/
def swbOffsetShort16k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 32, 40, 48, 60, 72, 88, 108, 128]

/-- Short-window (`N = 128`) `swb_offset` table for 8 kHz & 7.35 kHz (`num_swb = 15`, ends at `128`). -/
def swbOffsetShort8k : Array Nat :=
  #[0, 4, 8, 12, 16, 20, 24, 28, 36, 44, 52, 60, 72, 88, 108, 128]

/-- Select the ISO/IEC 14496-3 long-window (`N = 1024`) `swb_offset` table for `samplingFrequencyIndex` (`0..12`). -/
def aacSwbOffsetsLong (sfi : UInt8) : Option (Array Nat) :=
  match sfi.toNat with
  | 0 | 1       => some swbOffsetLong96k
  | 2           => some swbOffsetLong64k
  | 3 | 4       => some swbOffsetLong48k
  | 5           => some swbOffsetLong32k
  | 6 | 7       => some swbOffsetLong24k
  | 8 | 9 | 10  => some swbOffsetLong16k
  | 11 | 12     => some swbOffsetLong8k
  | _           => none

/-- Select the ISO/IEC 14496-3 short-window (`N = 128`) `swb_offset` table for `samplingFrequencyIndex` (`0..12`). -/
def aacSwbOffsetsShort (sfi : UInt8) : Option (Array Nat) :=
  match sfi.toNat with
  | 0 | 1 | 2        => some swbOffsetShort96k
  | 3 | 4 | 5        => some swbOffsetShort48k
  | 6 | 7            => some swbOffsetShort24k
  | 8 | 9 | 10       => some swbOffsetShort16k
  | 11 | 12          => some swbOffsetShort8k
  | _                => none

/-- Check strict monotonicity, multiple-of-4 alignment, start `0`, and exact end `expectedEnd` (`1024` or `128`) of a `swb_offset` table. -/
def isValidSwbOffsetTable (tbl : Array Nat) (expectedEnd : Nat) : Bool := Id.run do
  if tbl.size < 2 then return false
  if tbl.getD 0 9999 != 0 then return false
  if tbl.getD (tbl.size - 1) 0 != expectedEnd then return false
  for i in [:tbl.size - 1] do
    let a := tbl.getD i 0
    let b := tbl.getD (i + 1) 0
    if !(a < b && a % 4 == 0 && b % 4 == 0) then
      return false
  return true

/-! ## ISO/IEC 14496-3 §4.6.2 Inverse Quantizer (`|q|^(4/3) * 2^((sf - 100) / 4)`) & Forward Quantizer -/

/-- Domain check for AAC-LC quantized spectral coefficient (`|q| ≤ 8191`, ISO/IEC 14496-3 §4.6.2). -/
@[inline]
def isValidAacQuantCoeff (q : Int) : Bool :=
  q >= -8191 && q <= 8191

/-- Domain check for AAC-LC scale-factor (`sf ∈ [0, 255]`, ISO/IEC 14496-3 §4.6.2.3). -/
@[inline]
def isValidAacScaleFactor (sf : Nat) : Bool :=
  sf <= 255

/-- Precomputed `|q|^(4/3)` lookup table for `0 ≤ q ≤ 8191`. -/
def aacPow43Table : Array Float := Id.run do
  let mut arr := Array.emptyWithCapacity 8192
  for i in [:8192] do
    let x := Float.ofNat i
    let cbrtX := Float.pow x (1.0 / 3.0)
    arr := arr.push (x * cbrtX)
  return arr

/-- Precomputed `2^((sf - 100) / 4)` gain table for `0 ≤ sf ≤ 255` (plus headroom up to `320`). -/
def aacSfGainTable : Array Float := Id.run do
  let mut arr := Array.emptyWithCapacity 321
  for sf in [:321] do
    let exp := (Float.ofInt ((sf : Int) - 100)) * 0.25
    arr := arr.push (Float.pow 2.0 exp)
  return arr

/-- ISO/IEC 14496-3 §4.6.2 inverse quantization: `sign(q) * |q|^(4/3) * 2^((sf - 100) / 4)`. -/
@[inline]
def aacDequantizeCoeff (q : Int) (sf : Nat) : Float :=
  if q == 0 then 0.0
  else
    let aq := Nat.min 8191 q.natAbs
    let mag := aacPow43Table.getD aq 0.0
    let gain := aacSfGainTable.getD (Nat.min 320 sf) 1.0
    let val := mag * gain
    if q < 0 then -val else val

/-- Forward AAC-LC scalar quantizer (`floor((|x| / gain)^(3/4) + 0.4054)`, clamped to `8191`). -/
@[inline]
def aacQuantizeCoeff (x : Float) (sf : Nat) : Int :=
  if x == 0.0 then 0
  else
    let gain := aacSfGainTable.getD (Nat.min 320 sf) 1.0
    if gain <= 0.0 then 0
    else
      let scaled := (Float.abs x) / gain
      let p34 := Float.pow scaled 0.75
      let qNat := Nat.min 8191 (Float.toUInt64 (p34 + 0.4054)).toNat
      if qNat == 0 then 0
      else if x < 0.0 then -(qNat : Int) else (qNat : Int)

/-! ## ISO/IEC 14496-3 §4.5.2 Windows, MDCT-IV / IMDCT, and TDAC -/

/-- IEEE-754 approximation of π. -/
def aacPi : Float := 3.141592653589793

/-- Sine window `sin(pi / (2N) * (n + 0.5))` of total length `twoN` (`2N ∈ {256, 2048}`). -/
def aacSineWindow (twoN : Nat) : Array Float := Id.run do
  if twoN == 0 || twoN % 2 != 0 then return #[]
  let mut out := Array.emptyWithCapacity twoN
  for i in [:twoN] do
    let w := Float.sin ((aacPi / Float.ofNat twoN) * (Float.ofNat i + 0.5))
    out := out.push w
  return out

/-- Modified Bessel `I_0(x)` series truncated at 24 terms. -/
def aacBesselI0 (x : Float) : Float := Id.run do
  let half := x * 0.5
  let mut term := 1.0
  let mut sum := 1.0
  for k in [1:25] do
    let kf := Float.ofNat k
    term := term * (half * half) / (kf * kf)
    sum := sum + term
  return sum

/-- Kaiser-Bessel derived window (`alpha = 4` long, `alpha = 6` short) of total length `twoN`. -/
def aacKbdWindow (twoN : Nat) (alpha : Float) : Array Float := Id.run do
  let n := twoN / 2
  if twoN == 0 || twoN % 2 != 0 then return #[]
  let i0Den := aacBesselI0 (aacPi * alpha)
  let mut cum := Array.emptyWithCapacity (n + 1)
  let mut s := 0.0
  for i in [:n + 1] do
    let u := (4.0 * Float.ofNat i / Float.ofNat twoN) - 1.0
    let radicand := if u * u >= 1.0 then 0.0 else 1.0 - u * u
    let w := aacBesselI0 (aacPi * alpha * Float.sqrt radicand) / i0Den
    s := s + w
    cum := cum.push s
  let total := cum.getD n 1.0
  let norm := if total <= 0.0 then 1.0 else total
  let mut out := Array.emptyWithCapacity twoN
  for i in [:n] do
    out := out.push (Float.sqrt ((cum.getD i 0.0) / norm))
  for i in [:n] do
    out := out.push (Float.sqrt ((cum.getD (n - 1 - i) 0.0) / norm))
  return out

def aacLongSineWindow : Array Float := aacSineWindow 2048
def aacShortSineWindow : Array Float := aacSineWindow 256
def aacLongKbdWindow : Array Float := aacKbdWindow 2048 4.0
def aacShortKbdWindow : Array Float := aacKbdWindow 256 6.0

/-- In-place radix-2 Cooley-Tukey FFT (`len` power of 2). `inverse = true` applies the conjugate twiddle and `1/len` scale. -/
def aacFftRadix2 (re im : Array Float) (inverse : Bool) : Array Float × Array Float := Id.run do
  let len := re.size
  if len == 0 || len != im.size || len &&& (len - 1) != 0 then return (re, im)
  let mut r := re
  let mut i := im
  let mut j := 0
  for k in [1:len] do
    let mut bit := len >>> 1
    while j >= bit && bit > 0 do
      j := j - bit
      bit := bit >>> 1
    j := j + bit
    if k < j then
      let rk := r.getD k 0.0
      let rj := r.getD j 0.0
      let ik := i.getD k 0.0
      let ij := i.getD j 0.0
      r := r.set! k rj
      r := r.set! j rk
      i := i.set! k ij
      i := i.set! j ik
  let mut step := 2
  while step <= len do
    let half := step / 2
    let ang := (if inverse then 2.0 else -2.0) * aacPi / Float.ofNat step
    let wRe := Float.cos ang
    let wIm := Float.sin ang
    for base in List.range (len / step) do
      let mut curRe := 1.0
      let mut curIm := 0.0
      let off := base * step
      for k in [:half] do
        let t := off + k
        let u := t + half
        let tr := curRe * r.getD u 0.0 - curIm * i.getD u 0.0
        let ti := curRe * i.getD u 0.0 + curIm * r.getD u 0.0
        let ur := r.getD t 0.0
        let ui := i.getD t 0.0
        r := r.set! u (ur - tr)
        i := i.set! u (ui - ti)
        r := r.set! t (ur + tr)
        i := i.set! t (ui + ti)
        let nextRe := curRe * wRe - curIm * wIm
        curIm := curRe * wIm + curIm * wRe
        curRe := nextRe
    step := step * 2
  if inverse then
    let s := 1.0 / Float.ofNat len
    for k in [:len] do
      r := r.set! k (r.getD k 0.0 * s)
      i := i.set! k (i.getD k 0.0 * s)
  return (r, i)

/-- Fold a `2N`-sample block into the `N` inputs of DCT-IV (`N ∈ {128, 1024}`). -/
def aacMdctFold (block : Array Float) : Array Float := Id.run do
  let twoN := block.size
  let n := twoN / 2
  if n != 128 && n != 1024 then return #[]
  let half := n / 2
  let mut u := Array.replicate n 0.0
  for r in [:half] do
    let lo := block.getD (3 * half - 1 - r) 0.0
    let hi := block.getD (3 * half + r) 0.0
    u := u.set! r (-(lo + hi))
  for s in [:half] do
    let lo := block.getD s 0.0
    let hi := block.getD (n - 1 - s) 0.0
    u := u.set! (half + s) (lo - hi)
  return u

/-- Self-inverse unnormalized DCT-IV of length `N ∈ {128, 1024}` via an `N/2`-point forward FFT. -/
def aacDct4 (u : Array Float) : Array Float := Id.run do
  let n := u.size
  if n != 128 && n != 1024 then return #[]
  let m := n / 2
  let mut re := Array.emptyWithCapacity m
  let mut im := Array.emptyWithCapacity m
  for q in [:m] do
    let u0 := u.getD (2 * q) 0.0
    let u1 := u.getD (n - 1 - 2 * q) 0.0
    let ang := aacPi * (Float.ofNat q + 0.125) / Float.ofNat n
    let c := Float.cos ang
    let s := Float.sin ang
    re := re.push (u0 * c + u1 * s)
    im := im.push (u1 * c - u0 * s)
  let (zr, zi) := aacFftRadix2 re im false
  let mut out := Array.replicate n 0.0
  for p in [:m] do
    let ang := aacPi * (Float.ofNat p + 0.125) / Float.ofNat n
    let c := Float.cos ang
    let s := Float.sin ang
    let xr := zr.getD p 0.0
    let xi := zi.getD p 0.0
    out := out.set! (2 * p) (xr * c + xi * s)
    out := out.set! (n - 1 - 2 * p) (-(xi * c - xr * s))
  return out

/-- ISO/IEC 14496-3 MDCT-IV of length `N` over a `2N`-sample block (`N ∈ {128, 1024}`). -/
def aacMdct (block : Array Float) : Array Float :=
  let folded := aacMdctFold block
  if folded.isEmpty then #[] else aacDct4 folded

/-- ISO/IEC 14496-3 IMDCT-IV of length `N` producing `2N` samples, scaled by `2/N`. -/
def aacImdct (coeffs : Array Float) : Array Float := Id.run do
  let n := coeffs.size
  if n != 128 && n != 1024 then return #[]
  let half := n / 2
  let twoN := n * 2
  let d := aacDct4 coeffs
  let scale := 2.0 / Float.ofNat n
  let mut y := Array.replicate twoN 0.0
  for r in [:half] do
    let ur := d.getD r 0.0 * scale
    let us := d.getD (half + r) 0.0 * scale
    y := y.set! r us
    y := y.set! (n - 1 - r) (-us)
    y := y.set! (3 * half - 1 - r) (-ur)
    y := y.set! (3 * half + r) (-ur)
  return y

/-- Apply a `2N` analysis/synthesis window (sine or KBD). -/
def aacApplyWindow (block window : Array Float) : Array Float :=
  if block.size != window.size then #[]
  else block.zipWith (· * ·) window

/-- Overlap-add the second half of `prev` with the first half of `cur` (TDAC). -/
def aacTdacOverlapAdd (prev cur : Array Float) : Array Float := Id.run do
  let n := prev.size / 2
  if cur.size != prev.size || n == 0 then return #[]
  let mut out := Array.emptyWithCapacity n
  for i in [:n] do
    out := out.push ((prev.getD (n + i) 0.0) + (cur.getD i 0.0))
  return out

/-- PCM SNR in dB of `recon` versus `ref` (identical empty arrays yield `120`). -/
def aacPcmSnrDb (ref recon : Array Float) : Float := Id.run do
  if ref.size == 0 || ref.size != recon.size then return 0.0
  let mut sig := 0.0
  let mut err := 0.0
  for i in [:ref.size] do
    let r := ref.getD i 0.0
    let d := r - recon.getD i 0.0
    sig := sig + r * r
    err := err + d * d
  if err <= 1e-20 then return 120.0
  if sig <= 1e-20 then return 0.0
  return 10.0 * Float.log10 (sig / err)

/-- ISO/IEC 14496-3 §4.6.11 four window sequence types (`0..3`). -/
inductive AacWindowSequence where
  | onlyLong   -- 0: ONLY_LONG_SEQUENCE
  | longStart  -- 1: LONG_START_SEQUENCE
  | eightShort -- 2: EIGHT_SHORT_SEQUENCE
  | longStop   -- 3: LONG_STOP_SEQUENCE
  deriving Repr, DecidableEq, Inhabited

def AacWindowSequence.toUInt8 : AacWindowSequence → UInt8
  | .onlyLong   => 0
  | .longStart  => 1
  | .eightShort => 2
  | .longStop   => 3

def AacWindowSequence.ofUInt8? : UInt8 → Option AacWindowSequence
  | 0 => some .onlyLong
  | 1 => some .longStart
  | 2 => some .eightShort
  | 3 => some .longStop
  | _ => none

/-- ISO/IEC 14496-3 allowed state transitions between consecutive `window_sequence` values. -/
def isValidAacWindowTransition (prev cur : AacWindowSequence) : Bool :=
  match prev, cur with
  | .onlyLong, .onlyLong     => true
  | .onlyLong, .longStart    => true
  | .longStart, .eightShort  => true
  | .longStart, .longStop    => true
  | .eightShort, .eightShort => true
  | .eightShort, .longStop   => true
  | .longStop, .onlyLong     => true
  | .longStop, .longStart    => true
  | _, _                     => false

/-- Select rising half-window (`N = 1024` or `N = 128`) for `useKbd` (`false` = sine, `true` = KBD). -/
@[inline]
def aacHalfWindow (isShort useKbd : Bool) : Array Float :=
  let full :=
    if isShort then (if useKbd then aacShortKbdWindow else aacShortSineWindow)
    else (if useKbd then aacLongKbdWindow else aacLongSineWindow)
  full.extract 0 (full.size / 2)

/-- Build the 2048-point composite analysis/synthesis window for `(seq, useKbdCur, useKbdPrev)` (`ONLY_LONG`, `LONG_START`, `LONG_STOP`). -/
def aacBuildCompositeLongWindow (seq : AacWindowSequence) (useKbdCur useKbdPrev : Bool) : Array Float := Id.run do
  let lwPrev := aacHalfWindow false useKbdPrev
  let lwCur  := aacHalfWindow false useKbdCur
  let swPrev := aacHalfWindow true useKbdPrev
  let swCur  := aacHalfWindow true useKbdCur
  let mut w := Array.replicate 2048 0.0
  match seq with
  | .onlyLong =>
    for i in [:1024] do
      w := w.set! i (lwPrev.getD i 0.0)
      w := w.set! (1024 + i) (lwCur.getD (1023 - i) 0.0)
  | .longStart =>
    for i in [:1024] do
      w := w.set! i (lwPrev.getD i 0.0)
    for i in [:448] do
      w := w.set! (1024 + i) 1.0
    for i in [:128] do
      w := w.set! (1472 + i) (swCur.getD (127 - i) 0.0)
  | .longStop =>
    for i in [:128] do
      w := w.set! (448 + i) (swPrev.getD i 0.0)
    for i in [:448] do
      w := w.set! (576 + i) 1.0
    for i in [:1024] do
      w := w.set! (1024 + i) (lwCur.getD (1023 - i) 0.0)
  | .eightShort => pure ()
  return w

/-- Forward filterbank for one 2048-sample channel window (`PCM ∈ [-32768, 32767]`), scaled by `2` to match ISO/IEC 14496-3 MDCT normalization. -/
def aacAnalyzeFrame (pcm2048 : Array Float) (seq : AacWindowSequence) (useKbdCur useKbdPrev : Bool) : Array Float := Id.run do
  if pcm2048.size != 2048 then return #[]
  match seq with
  | .eightShort =>
    let swPrev := aacHalfWindow true useKbdPrev
    let swCur  := aacHalfWindow true useKbdCur
    let mut spec := Array.emptyWithCapacity 1024
    for w in [:8] do
      let base := 448 + w * 128
      let rise := if w == 0 then swPrev else swCur
      let mut blk := Array.emptyWithCapacity 256
      for i in [:128] do
        blk := blk.push (pcm2048.getD (base + i) 0.0 * rise.getD i 0.0)
      for i in [:128] do
        blk := blk.push (pcm2048.getD (base + 128 + i) 0.0 * swCur.getD (127 - i) 0.0)
      let md := aacMdct blk
      for c in md do
        spec := spec.push (2.0 * c)
    return spec
  | _ =>
    let win := aacBuildCompositeLongWindow seq useKbdCur useKbdPrev
    let md := aacMdct (aacApplyWindow pcm2048 win)
    return md.map (fun c => 2.0 * c)

/-- Synthesis filterbank for one 1024-bin channel spectrum (`savedOverlap` has length 1024), returning `(pcm1024, nextSavedOverlap)`. -/
def aacSynthesizeFrame (spec1024 savedOverlap : Array Float) (seq : AacWindowSequence) (useKbdCur useKbdPrev : Bool) : Array Float × Array Float := Id.run do
  if spec1024.size != 1024 || savedOverlap.size != 1024 then
    return (#[], Array.replicate 1024 0.0)
  let halfSpec := spec1024.map (fun c => 0.5 * c)
  match seq with
  | .eightShort =>
    let swPrev := aacHalfWindow true useKbdPrev
    let swCur  := aacHalfWindow true useKbdCur
    let mut y2048 := Array.replicate 2048 0.0
    for w in [:8] do
      let sub := halfSpec.extract (w * 128) ((w + 1) * 128)
      let im := aacImdct sub
      let rise := if w == 0 then swPrev else swCur
      let base := 448 + w * 128
      for i in [:128] do
        let v0 := im.getD i 0.0 * rise.getD i 0.0
        let v1 := im.getD (128 + i) 0.0 * swCur.getD (127 - i) 0.0
        y2048 := y2048.set! (base + i) (y2048.getD (base + i) 0.0 + v0)
        y2048 := y2048.set! (base + 128 + i) (y2048.getD (base + 128 + i) 0.0 + v1)
    let mut pcm := Array.emptyWithCapacity 1024
    for i in [:1024] do
      pcm := pcm.push (savedOverlap.getD i 0.0 + y2048.getD i 0.0)
    return (pcm, y2048.extract 1024 2048)
  | _ =>
    let win := aacBuildCompositeLongWindow seq useKbdCur useKbdPrev
    let y2048 := aacApplyWindow (aacImdct halfSpec) win
    let mut pcm := Array.emptyWithCapacity 1024
    for i in [:1024] do
      pcm := pcm.push (savedOverlap.getD i 0.0 + y2048.getD i 0.0)
    return (pcm, y2048.extract 1024 2048)

/-- Transient detector over a 2048-sample analysis window for switching `ONLY_LONG -> LONG_START -> EIGHT_SHORT -> LONG_STOP`. -/
def aacDetectTransient (pcm2048 : Array Float) : Bool := Id.run do
  if pcm2048.size != 2048 then return false
  let mut energies := Array.emptyWithCapacity 8
  for w in [:8] do
    let base := 448 + w * 128
    let mut e := 1.0
    for i in [:128] do
      let s := pcm2048.getD (base + 64 + i) 0.0
      e := e + s * s
    energies := energies.push e
  for w in [1:8] do
    let prev := energies.getD (w - 1) 1.0
    let cur  := energies.getD w 1.0
    if cur > prev * 10.0 && cur > 1e6 then
      return true
  return false

/-! ## ISO/IEC 14496-3 §4.6.9 Temporal Noise Shaping (TNS) -/

def aacTnsMaxBandsLong : Array Nat :=
  #[31, 31, 34, 40, 42, 51, 46, 46, 42, 42, 42, 39, 39]

def aacTnsMaxBandsShort : Array Nat :=
  #[9, 9, 10, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14]

/-- Maximum allowed TNS filter order in AAC-LC (`12` for long windows, `7` for short windows). -/
@[inline]
def aacTnsMaxOrder (isShort : Bool) : Nat :=
  if isShort then 7 else 12

def aacTnsTmp2Map0_3 : Array Float :=
  #[0.0, -0.43388373, -0.78183150, -0.97492790, 0.98480773, 0.86602539, 0.64278758, 0.34202015]

def aacTnsTmp2Map0_4 : Array Float :=
  #[0.0, -0.20791170, -0.40673664, -0.58778524, -0.74314481, -0.86602539, -0.95105654, -0.99452192,
    0.99573416, 0.96182561, 0.89516330, 0.79801720, 0.67369562, 0.52643216, 0.36124167, 0.18374951]

def aacTnsTmp2Map1_3 : Array Float :=
  #[0.0, -0.43388373, 0.64278758, 0.34202015]

def aacTnsTmp2Map1_4 : Array Float :=
  #[0.0, -0.20791170, -0.40673664, -0.58778524, 0.67369562, 0.52643216, 0.36124167, 0.18374951]

/-- Inverse sine table `tns_tmp2_map[2 * coefCompress + coefRes]` (ISO/IEC 14496-3 §4.6.9.2). -/
def aacTnsLookupParcor (coefCompress coefRes : Bool) (idx : Nat) : Float :=
  let tbl :=
    match coefCompress, coefRes with
    | false, false => aacTnsTmp2Map0_3
    | false, true  => aacTnsTmp2Map0_4
    | true,  false => aacTnsTmp2Map1_3
    | true,  true  => aacTnsTmp2Map1_4
  tbl.getD idx 0.0

/-- Convert reflection/PARCOR coefficients `parcor` (`|k_i| < 1`) into direct-form LPC coefficients `a_1..a_p` via step-up recursion (`tns_decode_coef`). -/
def aacTnsParcorToLpc (parcor : Array Float) : Array Float := Id.run do
  let order := parcor.size
  let mut lpc := Array.replicate order 0.0
  for i in [:order] do
    let r := -(parcor.getD i 0.0)
    let prev := lpc
    lpc := lpc.set! i r
    let half := (i + 1) / 2
    for j in [:half] do
      let f := prev.getD j 0.0
      let b := prev.getD (i - 1 - j) 0.0
      lpc := lpc.set! j (f + r * b)
      lpc := lpc.set! (i - 1 - j) (b + r * f)
  return lpc

/-- Single TNS filter descriptor within one window (`w ∈ 0..numWindows-1`). -/
structure AacTnsFilter where
  length       : Nat
  order        : Nat
  direction    : Bool        -- false = upward (+1), true = downward (-1)
  coefCompress : Bool := false
  coefIndices  : Array Nat   -- raw quantized indices
  parcor       : Array Float -- decoded PARCOR values
  deriving Repr, Inhabited

/-- Channel TNS side-information across `1` (long) or `8` (short) windows. -/
structure AacTnsInfo where
  present   : Bool := false
  coefRes   : Array Bool := #[]                 -- per-window `coef_res` (false = 3-bit, true = 4-bit)
  filters   : Array (Array AacTnsFilter) := #[] -- per-window filter array
  deriving Repr, Inhabited

/-- Apply TNS across a 1024-bin spectrum (`decode = true` applies all-pole AR synthesis; `decode = false` applies MA analysis). -/
def aacApplyTns (coeffs : Array Float) (tns : AacTnsInfo) (sfi : UInt8) (isShort : Bool) (maxSfb : Nat) (decode : Bool) : Array Float := Id.run do
  if !tns.present || coeffs.size != 1024 then return coeffs
  let some swbOffsets := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return coeffs
  let numSwb := swbOffsets.size - 1
  let tnsMax := (if isShort then aacTnsMaxBandsShort else aacTnsMaxBandsLong).getD sfi.toNat 0
  let mmm := Nat.min tnsMax maxSfb
  if mmm == 0 then return coeffs
  let numWin := if isShort then 8 else 1
  let mut out := coeffs
  for w in [:numWin] do
    let winFilts := tns.filters.getD w #[]
    let mut bottom := numSwb
    for filt in winFilts do
      let top := bottom
      bottom := top - Nat.min top filt.length
      let order := Nat.min (aacTnsMaxOrder isShort) filt.order
      if order > 0 && filt.parcor.size >= order then
        let lpc := aacTnsParcorToLpc (filt.parcor.extract 0 order)
        let s0 := swbOffsets.getD (Nat.min bottom mmm) 0
        let e0 := swbOffsets.getD (Nat.min top mmm) 0
        if e0 > s0 then
          let size := e0 - s0
          let winBase := w * 128
          if decode then
            for m in [:size] do
              let pos := winBase + (if filt.direction then e0 - 1 - m else s0 + m)
              let mut acc := out.getD pos 0.0
              let lim := Nat.min m order
              for k in [1:lim + 1] do
                let prevPos := if filt.direction then pos + k else pos - k
                acc := acc - (out.getD prevPos 0.0) * (lpc.getD (k - 1) 0.0)
              out := out.set! pos acc
          else
            let src := out
            for m in [:size] do
              let pos := winBase + (if filt.direction then e0 - 1 - m else s0 + m)
              let mut acc := src.getD pos 0.0
              let lim := Nat.min m order
              for k in [1:lim + 1] do
                let prevPos := if filt.direction then pos + k else pos - k
                acc := acc + (src.getD prevPos 0.0) * (lpc.getD (k - 1) 0.0)
              out := out.set! pos acc
  return out

/-- Schur/Levinson autocorrelation PARCOR estimator + 4-bit TNS analysis search for one channel spectrum. -/
def aacSearchTns (coeffs : Array Float) (sfi : UInt8) (seq : AacWindowSequence) (maxSfb : Nat) : AacTnsInfo × Array Float := Id.run do
  let isShort := seq == .eightShort
  let some swbOffsets := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return ({}, coeffs)
  let numSwb := swbOffsets.size - 1
  let tnsMax := (if isShort then aacTnsMaxBandsShort else aacTnsMaxBandsLong).getD sfi.toNat 0
  let mmm := Nat.min tnsMax maxSfb
  let sfbStart := Nat.min mmm (if isShort then 2 else 8)
  if mmm <= sfbStart || coeffs.size != 1024 then return ({}, coeffs)
  let numWin := if isShort then 8 else 1
  let order := if isShort then 4 else 8
  let mut anyActive := false
  let mut coefResArr := Array.emptyWithCapacity numWin
  let mut filtsPerWin := Array.emptyWithCapacity numWin
  for w in [:numWin] do
    coefResArr := coefResArr.push true
    let cStart := w * 128 + swbOffsets.getD sfbStart 0
    let cEnd   := w * 128 + swbOffsets.getD mmm 0
    let cLen   := cEnd - cStart
    if cLen <= order + 4 then
      filtsPerWin := filtsPerWin.push #[]
    else
      let mut r := Array.replicate (order + 1) 0.0
      for lag in [:order + 1] do
        let mut s := 0.0
        for n in [:cLen - lag] do
          s := s + (coeffs.getD (cStart + n) 0.0) * (coeffs.getD (cStart + n + lag) 0.0)
        r := r.set! lag s
      let r0 := r.getD 0 0.0
      if r0 <= 1e-6 then
        filtsPerWin := filtsPerWin.push #[]
      else
        let mut err := r0
        let mut lpc := Array.replicate order 0.0
        let mut ref := Array.replicate order 0.0
        for i in [:order] do
          let mut num := r.getD (i + 1) 0.0
          for j in [:i] do
            num := num + (lpc.getD j 0.0) * (r.getD (i - j) 0.0)
          let ki := if err <= 1e-12 then 0.0 else -(num / err)
          let kc := if ki > 0.98 then 0.98 else if ki < -0.98 then -0.98 else ki
          ref := ref.set! i (-kc)
          let prev := lpc
          lpc := lpc.set! i kc
          for j in [:i] do
            lpc := lpc.set! j (prev.getD j 0.0 + kc * prev.getD (i - 1 - j) 0.0)
          err := err * (1.0 - kc * kc)
        let predGain := if err <= 1e-12 then 1.0 else r0 / err
        if predGain >= 1.85 then
          let mut idxs := Array.emptyWithCapacity order
          let mut qPar := Array.emptyWithCapacity order
          for i in [:order] do
            let target := ref.getD i 0.0
            let mut bestIdx := 0
            let mut bestDist := 1e9
            for q in [:16] do
              let cand := aacTnsTmp2Map0_4.getD q 0.0
              let d := Float.abs (target - cand)
              if d < bestDist then
                bestDist := d
                bestIdx := q
            idxs := idxs.push bestIdx
            qPar := qPar.push (aacTnsTmp2Map0_4.getD bestIdx 0.0)
          let f : AacTnsFilter := {
            length := numSwb - sfbStart
            order := order
            direction := (seq == .longStop)
            coefCompress := false
            coefIndices := idxs
            parcor := qPar
          }
          let tmpInfo : AacTnsInfo := {
            present := true
            coefRes := Array.replicate numWin true
            filters := (Array.replicate numWin #[]).set! w #[f]
          }
          let candSpec := aacApplyTns coeffs tmpInfo sfi isShort maxSfb false
          let mut ePost := 0.0
          for n in [:cLen] do
            let v := candSpec.getD (cStart + n) 0.0
            ePost := ePost + v * v
          if ePost < r0 * 0.72 then
            anyActive := true
            filtsPerWin := filtsPerWin.push #[f]
          else
            filtsPerWin := filtsPerWin.push #[]
        else
          filtsPerWin := filtsPerWin.push #[]
  if !anyActive then return ({}, coeffs)
  let info : AacTnsInfo := { present := true, coefRes := coefResArr, filters := filtsPerWin }
  return (info, aacApplyTns coeffs info sfi isShort maxSfb false)

/-! ## ISO/IEC 14496-3 §4.6.8 Mid/Side (M/S) Stereo & Intensity Stereo -/

/-- Encoder M/S decision + transform (`M = (L+R)/2`, `S = (L-R)/2`) per `(window_group, sfb)`. Returns `(msMode, msMask, ch0, ch1)`. -/
def aacEncodeMidSide (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat) :
    UInt8 × Array Bool × Array Float × Array Float := Id.run do
  if ch0.size != 1024 || ch1.size != 1024 || maxSfb == 0 then
    return (0, #[], ch0, ch1)
  let mut out0 := ch0
  let mut out1 := ch1
  let mut mask := Array.emptyWithCapacity (groupLens.size * maxSfb)
  let mut activeCount : Nat := 0
  let mut winBase : Nat := 0
  for gLen in groupLens do
    for sfb in [:maxSfb] do
      let s0 := swbOffsets.getD sfb 0
      let e0 := swbOffsets.getD (sfb + 1) s0
      let mut eLR := 0.0
      let mut eMS := 0.0
      for w in [:gLen] do
        let off := (winBase + w) * 128
        for k in [s0:e0] do
          let l := out0.getD (off + k) 0.0
          let r := out1.getD (off + k) 0.0
          let m := 0.5 * (l + r)
          let s := 0.5 * (l - r)
          eLR := eLR + l * l + r * r
          eMS := eMS + m * m + s * s
      let useMs := eLR > 1e-6 && eMS < eLR * 0.85
      mask := mask.push useMs
      if useMs then
        activeCount := activeCount + 1
        for w in [:gLen] do
          let off := (winBase + w) * 128
          for k in [s0:e0] do
            let l := out0.getD (off + k) 0.0
            let r := out1.getD (off + k) 0.0
            out0 := out0.set! (off + k) (0.5 * (l + r))
            out1 := out1.set! (off + k) (0.5 * (l - r))
    winBase := winBase + gLen
  let totalBands := groupLens.size * maxSfb
  let mode : UInt8 :=
    if activeCount == 0 then 0
    else if activeCount == totalBands then 2
    else 1
  return (mode, mask, out0, out1)

/-- Decoder M/S butterfly (`L = M + S`, `R = M - S`) for bands with `msMask[idx] = true` and `bandType < 13`. -/
def aacDecodeMidSide (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt0 bt1 : Array UInt8) : Array Float × Array Float := Id.run do
  if msPresent == 0 || ch0.size != 1024 || ch1.size != 1024 then return (ch0, ch1)
  let mut out0 := ch0
  let mut out1 := ch1
  let mut idx : Nat := 0
  let mut winBase : Nat := 0
  for gLen in groupLens do
    for sfb in [:maxSfb] do
      let active := if msPresent == 2 then true else msMask.getD idx false
      let b0 := bt0.getD idx 0
      let b1 := bt1.getD idx 0
      if active && b0 < 13 && b1 < 13 then
        let s0 := swbOffsets.getD sfb 0
        let e0 := swbOffsets.getD (sfb + 1) s0
        for w in [:gLen] do
          let off := (winBase + w) * 128
          for k in [s0:e0] do
            let m := out0.getD (off + k) 0.0
            let s := out1.getD (off + k) 0.0
            out0 := out0.set! (off + k) (m + s)
            out1 := out1.set! (off + k) (m - s)
      idx := idx + 1
    winBase := winBase + gLen
  return (out0, out1)

/-- Decoder Intensity Stereo reconstruction (`band_type ∈ {14, 15}`, ISO/IEC 14496-3 §4.6.8.2.3). -/
def aacDecodeIntensityStereo (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt1 : Array UInt8) (isScale1 : Array Float) : Array Float := Id.run do
  if ch0.size != 1024 || ch1.size != 1024 then return ch1
  let mut out1 := ch1
  let mut idx : Nat := 0
  let mut winBase : Nat := 0
  for gLen in groupLens do
    for sfb in [:maxSfb] do
      let b1 := bt1.getD idx 0
      if b1 == 14 || b1 == 15 then
        let dirSign : Float := if b1 == 15 then 1.0 else -1.0
        let msFlip : Float :=
          if msPresent != 0 && (if msPresent == 2 then true else msMask.getD idx false) then -1.0 else 1.0
        let scale := dirSign * msFlip * (isScale1.getD idx 0.0)
        let s0 := swbOffsets.getD sfb 0
        let e0 := swbOffsets.getD (sfb + 1) s0
        for w in [:gLen] do
          let off := (winBase + w) * 128
          for k in [s0:e0] do
            out1 := out1.set! (off + k) ((ch0.getD (off + k) 0.0) * scale)
      idx := idx + 1
    winBase := winBase + gLen
  return out1

/-! ## ISO/IEC 14496-3 Tables A.1–A.12 Huffman Codebooks (`hcb_sf` + Spectral `1..11`) -/

def aacSfCodes : Array UInt32 := #[
  0x3ffe8, 0x3ffe6, 0x3ffe7, 0x3ffe5, 0x7fff5, 0x7fff1, 0x7ffed, 0x7fff6,
  0x7ffee, 0x7ffef, 0x7fff0, 0x7fffc, 0x7fffd, 0x7ffff, 0x7fffe, 0x7fff7,
  0x7fff8, 0x7fffb, 0x7fff9, 0x3ffe4, 0x7fffa, 0x3ffe3, 0x1ffef, 0x1fff0,
  0x0fff5, 0x1ffee, 0x0fff2, 0x0fff3, 0x0fff4, 0x0fff1, 0x07ff6, 0x07ff7,
  0x03ff9, 0x03ff5, 0x03ff7, 0x03ff3, 0x03ff6, 0x03ff2, 0x01ff7, 0x01ff5,
  0x00ff9, 0x00ff7, 0x00ff6, 0x007f9, 0x00ff4, 0x007f8, 0x003f9, 0x003f7,
  0x003f5, 0x001f8, 0x001f7, 0x000fa, 0x000f8, 0x000f6, 0x00079, 0x0003a,
  0x00038, 0x0001a, 0x0000b, 0x00004, 0x00000, 0x0000a, 0x0000c, 0x0001b,
  0x00039, 0x0003b, 0x00078, 0x0007a, 0x000f7, 0x000f9, 0x001f6, 0x001f9,
  0x003f4, 0x003f6, 0x003f8, 0x007f5, 0x007f4, 0x007f6, 0x007f7, 0x00ff5,
  0x00ff8, 0x01ff4, 0x01ff6, 0x01ff8, 0x03ff8, 0x03ff4, 0x0fff0, 0x07ff4,
  0x0fff6, 0x07ff5, 0x3ffe2, 0x7ffd9, 0x7ffda, 0x7ffdb, 0x7ffdc, 0x7ffdd,
  0x7ffde, 0x7ffd8, 0x7ffd2, 0x7ffd3, 0x7ffd4, 0x7ffd5, 0x7ffd6, 0x7fff2,
  0x7ffdf, 0x7ffe7, 0x7ffe8, 0x7ffe9, 0x7ffea, 0x7ffeb, 0x7ffe6, 0x7ffe0,
  0x7ffe1, 0x7ffe2, 0x7ffe3, 0x7ffe4, 0x7ffe5, 0x7ffd7, 0x7ffec, 0x7fff4,
  0x7fff3
]

def aacSfBits : Array UInt8 := #[
  18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 18, 19, 18, 17, 17, 16, 17, 16, 16, 16, 16, 15, 15,
  14, 14, 14, 14, 14, 14, 13, 13, 12, 12, 12, 11, 12, 11, 10, 10,
  10,  9,  9,  8,  8,  8,  7,  6,  6,  5,  4,  3,  1,  4,  4,  5,
   6,  6,  7,  7,  8,  8,  9,  9, 10, 10, 10, 11, 11, 11, 11, 12,
  12, 13, 13, 13, 14, 14, 16, 15, 16, 15, 18, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19
]

def aacCodes1 : Array UInt16 := #[
  0x7f8, 0x1f1, 0x7fd, 0x3f5, 0x068, 0x3f0, 0x7f7, 0x1ec,
  0x7f5, 0x3f1, 0x072, 0x3f4, 0x074, 0x011, 0x076, 0x1eb,
  0x06c, 0x3f6, 0x7fc, 0x1e1, 0x7f1, 0x1f0, 0x061, 0x1f6,
  0x7f2, 0x1ea, 0x7fb, 0x1f2, 0x069, 0x1ed, 0x077, 0x017,
  0x06f, 0x1e6, 0x064, 0x1e5, 0x067, 0x015, 0x062, 0x012,
  0x000, 0x014, 0x065, 0x016, 0x06d, 0x1e9, 0x063, 0x1e4,
  0x06b, 0x013, 0x071, 0x1e3, 0x070, 0x1f3, 0x7fe, 0x1e7,
  0x7f3, 0x1ef, 0x060, 0x1ee, 0x7f0, 0x1e2, 0x7fa, 0x3f3,
  0x06a, 0x1e8, 0x075, 0x010, 0x073, 0x1f4, 0x06e, 0x3f7,
  0x7f6, 0x1e0, 0x7f9, 0x3f2, 0x066, 0x1f5, 0x7ff, 0x1f7,
  0x7f4
]

def aacBits1 : Array UInt8 := #[
  11,  9, 11, 10,  7, 10, 11,  9, 11, 10,  7, 10,  7,  5,  7,  9,
   7, 10, 11,  9, 11,  9,  7,  9, 11,  9, 11,  9,  7,  9,  7,  5,
   7,  9,  7,  9,  7,  5,  7,  5,  1,  5,  7,  5,  7,  9,  7,  9,
   7,  5,  7,  9,  7,  9, 11,  9, 11,  9,  7,  9, 11,  9, 11, 10,
   7,  9,  7,  5,  7,  9,  7, 10, 11,  9, 11, 10,  7,  9, 11,  9,
  11
]

def aacCodes2 : Array UInt16 := #[
  0x1f3, 0x06f, 0x1fd, 0x0eb, 0x023, 0x0ea, 0x1f7, 0x0e8,
  0x1fa, 0x0f2, 0x02d, 0x070, 0x020, 0x006, 0x02b, 0x06e,
  0x028, 0x0e9, 0x1f9, 0x066, 0x0f8, 0x0e7, 0x01b, 0x0f1,
  0x1f4, 0x06b, 0x1f5, 0x0ec, 0x02a, 0x06c, 0x02c, 0x00a,
  0x027, 0x067, 0x01a, 0x0f5, 0x024, 0x008, 0x01f, 0x009,
  0x000, 0x007, 0x01d, 0x00b, 0x030, 0x0ef, 0x01c, 0x064,
  0x01e, 0x00c, 0x029, 0x0f3, 0x02f, 0x0f0, 0x1fc, 0x071,
  0x1f2, 0x0f4, 0x021, 0x0e6, 0x0f7, 0x068, 0x1f8, 0x0ee,
  0x022, 0x065, 0x031, 0x002, 0x026, 0x0ed, 0x025, 0x06a,
  0x1fb, 0x072, 0x1fe, 0x069, 0x02e, 0x0f6, 0x1ff, 0x06d,
  0x1f6
]

def aacBits2 : Array UInt8 := #[
  9, 7, 9, 8, 6, 8, 9, 8, 9, 8, 6, 7, 6, 5, 6, 7,
  6, 8, 9, 7, 8, 8, 6, 8, 9, 7, 9, 8, 6, 7, 6, 5,
  6, 7, 6, 8, 6, 5, 6, 5, 3, 5, 6, 5, 6, 8, 6, 7,
  6, 5, 6, 8, 6, 8, 9, 7, 9, 8, 6, 8, 8, 7, 9, 8,
  6, 7, 6, 4, 6, 8, 6, 7, 9, 7, 9, 7, 6, 8, 9, 7,
  9
]

def aacCodes3 : Array UInt16 := #[
  0x0000, 0x0009, 0x00ef, 0x000b, 0x0019, 0x00f0, 0x01eb, 0x01e6,
  0x03f2, 0x000a, 0x0035, 0x01ef, 0x0034, 0x0037, 0x01e9, 0x01ed,
  0x01e7, 0x03f3, 0x01ee, 0x03ed, 0x1ffa, 0x01ec, 0x01f2, 0x07f9,
  0x07f8, 0x03f8, 0x0ff8, 0x0008, 0x0038, 0x03f6, 0x0036, 0x0075,
  0x03f1, 0x03eb, 0x03ec, 0x0ff4, 0x0018, 0x0076, 0x07f4, 0x0039,
  0x0074, 0x03ef, 0x01f3, 0x01f4, 0x07f6, 0x01e8, 0x03ea, 0x1ffc,
  0x00f2, 0x01f1, 0x0ffb, 0x03f5, 0x07f3, 0x0ffc, 0x00ee, 0x03f7,
  0x7ffe, 0x01f0, 0x07f5, 0x7ffd, 0x1ffb, 0x3ffa, 0xffff, 0x00f1,
  0x03f0, 0x3ffc, 0x01ea, 0x03ee, 0x3ffb, 0x0ff6, 0x0ffa, 0x7ffc,
  0x07f2, 0x0ff5, 0xfffe, 0x03f4, 0x07f7, 0x7ffb, 0x0ff7, 0x0ff9,
  0x7ffa
]

def aacBits3 : Array UInt8 := #[
   1,  4,  8,  4,  5,  8,  9,  9, 10,  4,  6,  9,  6,  6,  9,  9,
   9, 10,  9, 10, 13,  9,  9, 11, 11, 10, 12,  4,  6, 10,  6,  7,
  10, 10, 10, 12,  5,  7, 11,  6,  7, 10,  9,  9, 11,  9, 10, 13,
   8,  9, 12, 10, 11, 12,  8, 10, 15,  9, 11, 15, 13, 14, 16,  8,
  10, 14,  9, 10, 14, 12, 12, 15, 11, 12, 16, 10, 11, 15, 12, 12,
  15
]

def aacCodes4 : Array UInt16 := #[
  0x007, 0x016, 0x0f6, 0x018, 0x008, 0x0ef, 0x1ef, 0x0f3,
  0x7f8, 0x019, 0x017, 0x0ed, 0x015, 0x001, 0x0e2, 0x0f0,
  0x070, 0x3f0, 0x1ee, 0x0f1, 0x7fa, 0x0ee, 0x0e4, 0x3f2,
  0x7f6, 0x3ef, 0x7fd, 0x005, 0x014, 0x0f2, 0x009, 0x004,
  0x0e5, 0x0f4, 0x0e8, 0x3f4, 0x006, 0x002, 0x0e7, 0x003,
  0x000, 0x06b, 0x0e3, 0x069, 0x1f3, 0x0eb, 0x0e6, 0x3f6,
  0x06e, 0x06a, 0x1f4, 0x3ec, 0x1f0, 0x3f9, 0x0f5, 0x0ec,
  0x7fb, 0x0ea, 0x06f, 0x3f7, 0x7f9, 0x3f3, 0xfff, 0x0e9,
  0x06d, 0x3f8, 0x06c, 0x068, 0x1f5, 0x3ee, 0x1f2, 0x7f4,
  0x7f7, 0x3f1, 0xffe, 0x3ed, 0x1f1, 0x7f5, 0x7fe, 0x3f5,
  0x7fc
]

def aacBits4 : Array UInt8 := #[
   4,  5,  8,  5,  4,  8,  9,  8, 11,  5,  5,  8,  5,  4,  8,  8,
   7, 10,  9,  8, 11,  8,  8, 10, 11, 10, 11,  4,  5,  8,  4,  4,
   8,  8,  8, 10,  4,  4,  8,  4,  4,  7,  8,  7,  9,  8,  8, 10,
   7,  7,  9, 10,  9, 10,  8,  8, 11,  8,  7, 10, 11, 10, 12,  8,
   7, 10,  7,  7,  9, 10,  9, 11, 11, 10, 12, 10,  9, 11, 11, 10,
  11
]

def aacCodes5 : Array UInt16 := #[
  0x1fff, 0x0ff7, 0x07f4, 0x07e8, 0x03f1, 0x07ee, 0x07f9, 0x0ff8,
  0x1ffd, 0x0ffd, 0x07f1, 0x03e8, 0x01e8, 0x00f0, 0x01ec, 0x03ee,
  0x07f2, 0x0ffa, 0x0ff4, 0x03ef, 0x01f2, 0x00e8, 0x0070, 0x00ec,
  0x01f0, 0x03ea, 0x07f3, 0x07eb, 0x01eb, 0x00ea, 0x001a, 0x0008,
  0x0019, 0x00ee, 0x01ef, 0x07ed, 0x03f0, 0x00f2, 0x0073, 0x000b,
  0x0000, 0x000a, 0x0071, 0x00f3, 0x07e9, 0x07ef, 0x01ee, 0x00ef,
  0x0018, 0x0009, 0x001b, 0x00eb, 0x01e9, 0x07ec, 0x07f6, 0x03eb,
  0x01f3, 0x00ed, 0x0072, 0x00e9, 0x01f1, 0x03ed, 0x07f7, 0x0ff6,
  0x07f0, 0x03e9, 0x01ed, 0x00f1, 0x01ea, 0x03ec, 0x07f8, 0x0ff9,
  0x1ffc, 0x0ffc, 0x0ff5, 0x07ea, 0x03f3, 0x03f2, 0x07f5, 0x0ffb,
  0x1ffe
]

def aacBits5 : Array UInt8 := #[
  13, 12, 11, 11, 10, 11, 11, 12, 13, 12, 11, 10,  9,  8,  9, 10,
  11, 12, 12, 10,  9,  8,  7,  8,  9, 10, 11, 11,  9,  8,  5,  4,
   5,  8,  9, 11, 10,  8,  7,  4,  1,  4,  7,  8, 11, 11,  9,  8,
   5,  4,  5,  8,  9, 11, 11, 10,  9,  8,  7,  8,  9, 10, 11, 12,
  11, 10,  9,  8,  9, 10, 11, 12, 13, 12, 12, 11, 10, 10, 11, 12,
  13
]

def aacCodes6 : Array UInt16 := #[
  0x7fe, 0x3fd, 0x1f1, 0x1eb, 0x1f4, 0x1ea, 0x1f0, 0x3fc,
  0x7fd, 0x3f6, 0x1e5, 0x0ea, 0x06c, 0x071, 0x068, 0x0f0,
  0x1e6, 0x3f7, 0x1f3, 0x0ef, 0x032, 0x027, 0x028, 0x026,
  0x031, 0x0eb, 0x1f7, 0x1e8, 0x06f, 0x02e, 0x008, 0x004,
  0x006, 0x029, 0x06b, 0x1ee, 0x1ef, 0x072, 0x02d, 0x002,
  0x000, 0x003, 0x02f, 0x073, 0x1fa, 0x1e7, 0x06e, 0x02b,
  0x007, 0x001, 0x005, 0x02c, 0x06d, 0x1ec, 0x1f9, 0x0ee,
  0x030, 0x024, 0x02a, 0x025, 0x033, 0x0ec, 0x1f2, 0x3f8,
  0x1e4, 0x0ed, 0x06a, 0x070, 0x069, 0x074, 0x0f1, 0x3fa,
  0x7ff, 0x3f9, 0x1f6, 0x1ed, 0x1f8, 0x1e9, 0x1f5, 0x3fb,
  0x7fc
]

def aacBits6 : Array UInt8 := #[
  11, 10,  9,  9,  9,  9,  9, 10, 11, 10,  9,  8,  7,  7,  7,  8,
   9, 10,  9,  8,  6,  6,  6,  6,  6,  8,  9,  9,  7,  6,  4,  4,
   4,  6,  7,  9,  9,  7,  6,  4,  4,  4,  6,  7,  9,  9,  7,  6,
   4,  4,  4,  6,  7,  9,  9,  8,  6,  6,  6,  6,  6,  8,  9, 10,
   9,  8,  7,  7,  7,  7,  8, 10, 11, 10,  9,  9,  9,  9,  9, 10,
  11
]

def aacCodes7 : Array UInt16 := #[
  0x000, 0x005, 0x037, 0x074, 0x0f2, 0x1eb, 0x3ed, 0x7f7,
  0x004, 0x00c, 0x035, 0x071, 0x0ec, 0x0ee, 0x1ee, 0x1f5,
  0x036, 0x034, 0x072, 0x0ea, 0x0f1, 0x1e9, 0x1f3, 0x3f5,
  0x073, 0x070, 0x0eb, 0x0f0, 0x1f1, 0x1f0, 0x3ec, 0x3fa,
  0x0f3, 0x0ed, 0x1e8, 0x1ef, 0x3ef, 0x3f1, 0x3f9, 0x7fb,
  0x1ed, 0x0ef, 0x1ea, 0x1f2, 0x3f3, 0x3f8, 0x7f9, 0x7fc,
  0x3ee, 0x1ec, 0x1f4, 0x3f4, 0x3f7, 0x7f8, 0xffd, 0xffe,
  0x7f6, 0x3f0, 0x3f2, 0x3f6, 0x7fa, 0x7fd, 0xffc, 0xfff
]

def aacBits7 : Array UInt8 := #[
   1,  3,  6,  7,  8,  9, 10, 11,  3,  4,  6,  7,  8,  8,  9,  9,
   6,  6,  7,  8,  8,  9,  9, 10,  7,  7,  8,  8,  9,  9, 10, 10,
   8,  8,  9,  9, 10, 10, 10, 11,  9,  8,  9,  9, 10, 10, 11, 11,
  10,  9,  9, 10, 10, 11, 12, 12, 11, 10, 10, 10, 11, 11, 12, 12
]

def aacCodes8 : Array UInt16 := #[
  0x00e, 0x005, 0x010, 0x030, 0x06f, 0x0f1, 0x1fa, 0x3fe,
  0x003, 0x000, 0x004, 0x012, 0x02c, 0x06a, 0x075, 0x0f8,
  0x00f, 0x002, 0x006, 0x014, 0x02e, 0x069, 0x072, 0x0f5,
  0x02f, 0x011, 0x013, 0x02a, 0x032, 0x06c, 0x0ec, 0x0fa,
  0x071, 0x02b, 0x02d, 0x031, 0x06d, 0x070, 0x0f2, 0x1f9,
  0x0ef, 0x068, 0x033, 0x06b, 0x06e, 0x0ee, 0x0f9, 0x3fc,
  0x1f8, 0x074, 0x073, 0x0ed, 0x0f0, 0x0f6, 0x1f6, 0x1fd,
  0x3fd, 0x0f3, 0x0f4, 0x0f7, 0x1f7, 0x1fb, 0x1fc, 0x3ff
]

def aacBits8 : Array UInt8 := #[
   5,  4,  5,  6,  7,  8,  9, 10,  4,  3,  4,  5,  6,  7,  7,  8,
   5,  4,  4,  5,  6,  7,  7,  8,  6,  5,  5,  6,  6,  7,  8,  8,
   7,  6,  6,  6,  7,  7,  8,  9,  8,  7,  6,  7,  7,  8,  8, 10,
   9,  7,  7,  8,  8,  8,  9,  9, 10,  8,  8,  8,  9,  9,  9, 10
]

def aacCodes9 : Array UInt16 := #[
  0x0000, 0x0005, 0x0037, 0x00e7, 0x01de, 0x03ce, 0x03d9, 0x07c8,
  0x07cd, 0x0fc8, 0x0fdd, 0x1fe4, 0x1fec, 0x0004, 0x000c, 0x0035,
  0x0072, 0x00ea, 0x00ed, 0x01e2, 0x03d1, 0x03d3, 0x03e0, 0x07d8,
  0x0fcf, 0x0fd5, 0x0036, 0x0034, 0x0071, 0x00e8, 0x00ec, 0x01e1,
  0x03cf, 0x03dd, 0x03db, 0x07d0, 0x0fc7, 0x0fd4, 0x0fe4, 0x00e6,
  0x0070, 0x00e9, 0x01dd, 0x01e3, 0x03d2, 0x03dc, 0x07cc, 0x07ca,
  0x07de, 0x0fd8, 0x0fea, 0x1fdb, 0x01df, 0x00eb, 0x01dc, 0x01e6,
  0x03d5, 0x03de, 0x07cb, 0x07dd, 0x07dc, 0x0fcd, 0x0fe2, 0x0fe7,
  0x1fe1, 0x03d0, 0x01e0, 0x01e4, 0x03d6, 0x07c5, 0x07d1, 0x07db,
  0x0fd2, 0x07e0, 0x0fd9, 0x0feb, 0x1fe3, 0x1fe9, 0x07c4, 0x01e5,
  0x03d7, 0x07c6, 0x07cf, 0x07da, 0x0fcb, 0x0fda, 0x0fe3, 0x0fe9,
  0x1fe6, 0x1ff3, 0x1ff7, 0x07d3, 0x03d8, 0x03e1, 0x07d4, 0x07d9,
  0x0fd3, 0x0fde, 0x1fdd, 0x1fd9, 0x1fe2, 0x1fea, 0x1ff1, 0x1ff6,
  0x07d2, 0x03d4, 0x03da, 0x07c7, 0x07d7, 0x07e2, 0x0fce, 0x0fdb,
  0x1fd8, 0x1fee, 0x3ff0, 0x1ff4, 0x3ff2, 0x07e1, 0x03df, 0x07c9,
  0x07d6, 0x0fca, 0x0fd0, 0x0fe5, 0x0fe6, 0x1feb, 0x1fef, 0x3ff3,
  0x3ff4, 0x3ff5, 0x0fe0, 0x07ce, 0x07d5, 0x0fc6, 0x0fd1, 0x0fe1,
  0x1fe0, 0x1fe8, 0x1ff0, 0x3ff1, 0x3ff8, 0x3ff6, 0x7ffc, 0x0fe8,
  0x07df, 0x0fc9, 0x0fd7, 0x0fdc, 0x1fdc, 0x1fdf, 0x1fed, 0x1ff5,
  0x3ff9, 0x3ffb, 0x7ffd, 0x7ffe, 0x1fe7, 0x0fcc, 0x0fd6, 0x0fdf,
  0x1fde, 0x1fda, 0x1fe5, 0x1ff2, 0x3ffa, 0x3ff7, 0x3ffc, 0x3ffd,
  0x7fff
]

def aacBits9 : Array UInt8 := #[
   1,  3,  6,  8,  9, 10, 10, 11, 11, 12, 12, 13, 13,  3,  4,  6,
   7,  8,  8,  9, 10, 10, 10, 11, 12, 12,  6,  6,  7,  8,  8,  9,
  10, 10, 10, 11, 12, 12, 12,  8,  7,  8,  9,  9, 10, 10, 11, 11,
  11, 12, 12, 13,  9,  8,  9,  9, 10, 10, 11, 11, 11, 12, 12, 12,
  13, 10,  9,  9, 10, 11, 11, 11, 12, 11, 12, 12, 13, 13, 11,  9,
  10, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 11, 10, 10, 11, 11,
  12, 12, 13, 13, 13, 13, 13, 13, 11, 10, 10, 11, 11, 11, 12, 12,
  13, 13, 14, 13, 14, 11, 10, 11, 11, 12, 12, 12, 12, 13, 13, 14,
  14, 14, 12, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 14, 15, 12,
  11, 12, 12, 12, 13, 13, 13, 13, 14, 14, 15, 15, 13, 12, 12, 12,
  13, 13, 13, 13, 14, 14, 14, 14, 15
]

def aacCodes10 : Array UInt16 := #[
  0x022, 0x008, 0x01d, 0x026, 0x05f, 0x0d3, 0x1cf, 0x3d0,
  0x3d7, 0x3ed, 0x7f0, 0x7f6, 0xffd, 0x007, 0x000, 0x001,
  0x009, 0x020, 0x054, 0x060, 0x0d5, 0x0dc, 0x1d4, 0x3cd,
  0x3de, 0x7e7, 0x01c, 0x002, 0x006, 0x00c, 0x01e, 0x028,
  0x05b, 0x0cd, 0x0d9, 0x1ce, 0x1dc, 0x3d9, 0x3f1, 0x025,
  0x00b, 0x00a, 0x00d, 0x024, 0x057, 0x061, 0x0cc, 0x0dd,
  0x1cc, 0x1de, 0x3d3, 0x3e7, 0x05d, 0x021, 0x01f, 0x023,
  0x027, 0x059, 0x064, 0x0d8, 0x0df, 0x1d2, 0x1e2, 0x3dd,
  0x3ee, 0x0d1, 0x055, 0x029, 0x056, 0x058, 0x062, 0x0ce,
  0x0e0, 0x0e2, 0x1da, 0x3d4, 0x3e3, 0x7eb, 0x1c9, 0x05e,
  0x05a, 0x05c, 0x063, 0x0ca, 0x0da, 0x1c7, 0x1ca, 0x1e0,
  0x3db, 0x3e8, 0x7ec, 0x1e3, 0x0d2, 0x0cb, 0x0d0, 0x0d7,
  0x0db, 0x1c6, 0x1d5, 0x1d8, 0x3ca, 0x3da, 0x7ea, 0x7f1,
  0x1e1, 0x0d4, 0x0cf, 0x0d6, 0x0de, 0x0e1, 0x1d0, 0x1d6,
  0x3d1, 0x3d5, 0x3f2, 0x7ee, 0x7fb, 0x3e9, 0x1cd, 0x1c8,
  0x1cb, 0x1d1, 0x1d7, 0x1df, 0x3cf, 0x3e0, 0x3ef, 0x7e6,
  0x7f8, 0xffa, 0x3eb, 0x1dd, 0x1d3, 0x1d9, 0x1db, 0x3d2,
  0x3cc, 0x3dc, 0x3ea, 0x7ed, 0x7f3, 0x7f9, 0xff9, 0x7f2,
  0x3ce, 0x1e4, 0x3cb, 0x3d8, 0x3d6, 0x3e2, 0x3e5, 0x7e8,
  0x7f4, 0x7f5, 0x7f7, 0xffb, 0x7fa, 0x3ec, 0x3df, 0x3e1,
  0x3e4, 0x3e6, 0x3f0, 0x7e9, 0x7ef, 0xff8, 0xffe, 0xffc,
  0xfff
]

def aacBits10 : Array UInt8 := #[
   6,  5,  6,  6,  7,  8,  9, 10, 10, 10, 11, 11, 12,  5,  4,  4,
   5,  6,  7,  7,  8,  8,  9, 10, 10, 11,  6,  4,  5,  5,  6,  6,
   7,  8,  8,  9,  9, 10, 10,  6,  5,  5,  5,  6,  7,  7,  8,  8,
   9,  9, 10, 10,  7,  6,  6,  6,  6,  7,  7,  8,  8,  9,  9, 10,
  10,  8,  7,  6,  7,  7,  7,  8,  8,  8,  9, 10, 10, 11,  9,  7,
   7,  7,  7,  8,  8,  9,  9,  9, 10, 10, 11,  9,  8,  8,  8,  8,
   8,  9,  9,  9, 10, 10, 11, 11,  9,  8,  8,  8,  8,  8,  9,  9,
  10, 10, 10, 11, 11, 10,  9,  9,  9,  9,  9,  9, 10, 10, 10, 11,
  11, 12, 10,  9,  9,  9,  9, 10, 10, 10, 10, 11, 11, 11, 12, 11,
  10,  9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 12, 11, 10, 10, 10,
  10, 10, 10, 11, 11, 12, 12, 12, 12
]

def aacCodes11 : Array UInt16 := #[
  0x000, 0x006, 0x019, 0x03d, 0x09c, 0x0c6, 0x1a7, 0x390,
  0x3c2, 0x3df, 0x7e6, 0x7f3, 0xffb, 0x7ec, 0xffa, 0xffe,
  0x38e, 0x005, 0x001, 0x008, 0x014, 0x037, 0x042, 0x092,
  0x0af, 0x191, 0x1a5, 0x1b5, 0x39e, 0x3c0, 0x3a2, 0x3cd,
  0x7d6, 0x0ae, 0x017, 0x007, 0x009, 0x018, 0x039, 0x040,
  0x08e, 0x0a3, 0x0b8, 0x199, 0x1ac, 0x1c1, 0x3b1, 0x396,
  0x3be, 0x3ca, 0x09d, 0x03c, 0x015, 0x016, 0x01a, 0x03b,
  0x044, 0x091, 0x0a5, 0x0be, 0x196, 0x1ae, 0x1b9, 0x3a1,
  0x391, 0x3a5, 0x3d5, 0x094, 0x09a, 0x036, 0x038, 0x03a,
  0x041, 0x08c, 0x09b, 0x0b0, 0x0c3, 0x19e, 0x1ab, 0x1bc,
  0x39f, 0x38f, 0x3a9, 0x3cf, 0x093, 0x0bf, 0x03e, 0x03f,
  0x043, 0x045, 0x09e, 0x0a7, 0x0b9, 0x194, 0x1a2, 0x1ba,
  0x1c3, 0x3a6, 0x3a7, 0x3bb, 0x3d4, 0x09f, 0x1a0, 0x08f,
  0x08d, 0x090, 0x098, 0x0a6, 0x0b6, 0x0c4, 0x19f, 0x1af,
  0x1bf, 0x399, 0x3bf, 0x3b4, 0x3c9, 0x3e7, 0x0a8, 0x1b6,
  0x0ab, 0x0a4, 0x0aa, 0x0b2, 0x0c2, 0x0c5, 0x198, 0x1a4,
  0x1b8, 0x38c, 0x3a4, 0x3c4, 0x3c6, 0x3dd, 0x3e8, 0x0ad,
  0x3af, 0x192, 0x0bd, 0x0bc, 0x18e, 0x197, 0x19a, 0x1a3,
  0x1b1, 0x38d, 0x398, 0x3b7, 0x3d3, 0x3d1, 0x3db, 0x7dd,
  0x0b4, 0x3de, 0x1a9, 0x19b, 0x19c, 0x1a1, 0x1aa, 0x1ad,
  0x1b3, 0x38b, 0x3b2, 0x3b8, 0x3ce, 0x3e1, 0x3e0, 0x7d2,
  0x7e5, 0x0b7, 0x7e3, 0x1bb, 0x1a8, 0x1a6, 0x1b0, 0x1b2,
  0x1b7, 0x39b, 0x39a, 0x3ba, 0x3b5, 0x3d6, 0x7d7, 0x3e4,
  0x7d8, 0x7ea, 0x0ba, 0x7e8, 0x3a0, 0x1bd, 0x1b4, 0x38a,
  0x1c4, 0x392, 0x3aa, 0x3b0, 0x3bc, 0x3d7, 0x7d4, 0x7dc,
  0x7db, 0x7d5, 0x7f0, 0x0c1, 0x7fb, 0x3c8, 0x3a3, 0x395,
  0x39d, 0x3ac, 0x3ae, 0x3c5, 0x3d8, 0x3e2, 0x3e6, 0x7e4,
  0x7e7, 0x7e0, 0x7e9, 0x7f7, 0x190, 0x7f2, 0x393, 0x1be,
  0x1c0, 0x394, 0x397, 0x3ad, 0x3c3, 0x3c1, 0x3d2, 0x7da,
  0x7d9, 0x7df, 0x7eb, 0x7f4, 0x7fa, 0x195, 0x7f8, 0x3bd,
  0x39c, 0x3ab, 0x3a8, 0x3b3, 0x3b9, 0x3d0, 0x3e3, 0x3e5,
  0x7e2, 0x7de, 0x7ed, 0x7f1, 0x7f9, 0x7fc, 0x193, 0xffd,
  0x3dc, 0x3b6, 0x3c7, 0x3cc, 0x3cb, 0x3d9, 0x3da, 0x7d3,
  0x7e1, 0x7ee, 0x7ef, 0x7f5, 0x7f6, 0xffc, 0xfff, 0x19d,
  0x1c2, 0x0b5, 0x0a1, 0x096, 0x097, 0x095, 0x099, 0x0a0,
  0x0a2, 0x0ac, 0x0a9, 0x0b1, 0x0b3, 0x0bb, 0x0c0, 0x18f,
  0x004
]

def aacBits11 : Array UInt8 := #[
   4,  5,  6,  7,  8,  8,  9, 10, 10, 10, 11, 11, 12, 11, 12, 12,
  10,  5,  4,  5,  6,  7,  7,  8,  8,  9,  9,  9, 10, 10, 10, 10,
  11,  8,  6,  5,  5,  6,  7,  7,  8,  8,  8,  9,  9,  9, 10, 10,
  10, 10,  8,  7,  6,  6,  6,  7,  7,  8,  8,  8,  9,  9,  9, 10,
  10, 10, 10,  8,  8,  7,  7,  7,  7,  8,  8,  8,  8,  9,  9,  9,
  10, 10, 10, 10,  8,  8,  7,  7,  7,  7,  8,  8,  8,  9,  9,  9,
   9, 10, 10, 10, 10,  8,  9,  8,  8,  8,  8,  8,  8,  8,  9,  9,
   9, 10, 10, 10, 10, 10,  8,  9,  8,  8,  8,  8,  8,  8,  9,  9,
   9, 10, 10, 10, 10, 10, 10,  8, 10,  9,  8,  8,  9,  9,  9,  9,
   9, 10, 10, 10, 10, 10, 10, 11,  8, 10,  9,  9,  9,  9,  9,  9,
   9, 10, 10, 10, 10, 10, 10, 11, 11,  8, 11,  9,  9,  9,  9,  9,
   9, 10, 10, 10, 10, 10, 11, 10, 11, 11,  8, 11, 10,  9,  9, 10,
   9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11,  8, 11, 10, 10, 10,
  10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11,  9, 11, 10,  9,
   9, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11,  9, 11, 10,
  10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11,  9, 12,
  10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12,  9,
   9,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  9,
   5
]

def aacCbCodes (book : Nat) : Array UInt16 :=
  match book with
  | 1 => aacCodes1 | 2 => aacCodes2 | 3 => aacCodes3 | 4 => aacCodes4
  | 5 => aacCodes5 | 6 => aacCodes6 | 7 => aacCodes7 | 8 => aacCodes8
  | 9 => aacCodes9 | 10 => aacCodes10 | 11 => aacCodes11 | _ => #[]

def aacCbBits (book : Nat) : Array UInt8 :=
  match book with
  | 1 => aacBits1 | 2 => aacBits2 | 3 => aacBits3 | 4 => aacBits4
  | 5 => aacBits5 | 6 => aacBits6 | 7 => aacBits7 | 8 => aacBits8
  | 9 => aacBits9 | 10 => aacBits10 | 11 => aacBits11 | _ => #[]

def aacCbSize (book : Nat) : Nat :=
  match book with
  | 1 | 2 | 3 | 4 | 5 | 6 => 81
  | 7 | 8 => 64
  | 9 | 10 => 169
  | 11 => 289
  | _ => 0

def aacCbDim (book : Nat) : Nat :=
  match book with
  | 1 | 2 | 3 | 4 => 4
  | 5 | 6 | 7 | 8 | 9 | 10 | 11 => 2
  | _ => 0

def aacCbSigned (book : Nat) : Bool :=
  match book with
  | 1 | 2 | 5 | 6 => true
  | _ => false

def aacCbOff (book : Nat) : Nat :=
  match book with
  | 1 | 2 => 1
  | 5 | 6 => 4
  | _ => 0

def aacCbMaxAbs (book : Nat) : Nat :=
  match book with
  | 1 | 2 => 1
  | 3 | 4 => 2
  | 5 | 6 => 4
  | 7 | 8 => 7
  | 9 | 10 => 12
  | 11 => 16
  | _ => 0

def aacCbIndex (book : Nat) (vals : Array Int) : Option Nat :=
  let dim := aacCbDim book
  if dim == 0 || vals.size != dim then none
  else
    let signed := aacCbSigned book
    let maxA := aacCbMaxAbs book
    let off := aacCbOff book
    let base := if signed then 2 * maxA + 1 else maxA + 1
    Id.run do
      let mut idx : Nat := 0
      for i in [:dim] do
        let v := vals.getD i 0
        if signed then
          if v < -(maxA : Int) || v > (maxA : Int) then return none
          let d := (v + (off : Int)).toNat
          idx := idx * base + d
        else
          let a := if book == 11 then Nat.min 16 v.natAbs else v.natAbs
          if a > maxA then return none
          idx := idx * base + a
      return some idx

def aacCbUnpack (book : Nat) (idx : Nat) : Array Int :=
  let dim := aacCbDim book
  let signed := aacCbSigned book
  let maxA := aacCbMaxAbs book
  let off := aacCbOff book
  let base := if signed then 2 * maxA + 1 else maxA + 1
  if dim == 0 || base == 0 then #[]
  else Id.run do
    let mut rem := idx
    let mut out := Array.replicate dim (0 : Int)
    for k in [:dim] do
      let i := dim - 1 - k
      let d := rem % base
      rem := rem / base
      let v : Int := if signed then (d : Int) - (off : Int) else (d : Int)
      out := out.set! i v
    return out

def aacHuffWrite (w : BitWriter) (codes : Array UInt32) (bits : Array UInt8) (idx : Nat) : Option BitWriter :=
  if h : idx < codes.size ∧ idx < bits.size then
    let n := (bits[idx]).toNat
    if n == 0 || n > 32 then none
    else some (w.writeBitsMSB (codes[idx]).toUInt64 n)
  else none

def aacHuffRead (r : BitReader) (codes : Array UInt32) (bits : Array UInt8) (maxBits : Nat) : Option (Nat × BitReader) :=
  Id.run do
    let mut acc : UInt64 := 0
    let mut cur := r
    let lim := Nat.min maxBits 32
    for n in [1:lim + 1] do
      let some (bit, cur') := cur.readBit | return none
      cur := cur'
      acc := (acc <<< 1) ||| bit.toUInt64
      let mut found : Option Nat := none
      for i in [:codes.size] do
        if (bits.getD i 0).toNat == n && (codes.getD i 0).toUInt64 == acc then
          found := some i
          break
      match found with
      | some i => return some (i, cur)
      | none => pure ()
    return none

def aacWriteSfDelta (w : BitWriter) (diff : Int) : Option BitWriter :=
  let idx := diff + 60
  if idx < 0 || idx > 120 then none
  else aacHuffWrite w aacSfCodes aacSfBits idx.toNat

/-- Build a flat binary trie over `(codes, bits)` where node `p` holds `[left, right, sym1Based]`. -/
def aacBuildVlcTrie (codes : Array UInt32) (bits : Array UInt8) : Array Int := Id.run do
  let mut trie : Array Int := #[-1, -1, 0]
  for i in [:codes.size] do
    let len := (bits.getD i 0).toNat
    if len > 0 && len <= 32 then
      let code := codes.getD i 0
      let mut node : Nat := 0
      for s in [:len] do
        let shift := len - 1 - s
        let bit := ((code >>> shift.toUInt32) &&& 1).toNat
        let child := trie.getD (node + bit) (-1)
        if child >= 0 then
          node := child.toNat
        else
          let nextNode := trie.size
          trie := trie ++ #[-1, -1, 0]
          trie := trie.set! (node + bit) (nextNode : Int)
          node := nextNode
      trie := trie.set! (node + 2) ((i + 1) : Int)
  return trie

def aacSfTrie : Array Int := aacBuildVlcTrie aacSfCodes aacSfBits

def aacSpectralTries : Array (Array Int) := Id.run do
  let mut out := Array.emptyWithCapacity 12
  out := out.push #[]
  for b in [1:12] do
    out := out.push (aacBuildVlcTrie ((aacCbCodes b).map (·.toUInt32)) (aacCbBits b))
  return out

def aacTrieRead (r : BitReader) (trie : Array Int) (maxSteps : Nat := 24) : Option (Nat × BitReader) := Id.run do
  if trie.isEmpty then return none
  let mut node : Nat := 0
  let mut cur := r
  for _ in [:maxSteps] do
    let some (bit, cur') := cur.readBit | return none
    cur := cur'
    let child := trie.getD (node + (bit &&& 1).toNat) (-1)
    if child < 0 then return none
    node := child.toNat
    let sym := trie.getD (node + 2) 0
    if sym > 0 then
      return some ((sym - 1).toNat, cur)
  return none

/-- Write an ISO/IEC 14496-3 Book 11 escape sequence (`N` ones, `0`, `(N+4)`-bit suffix) for `16 ≤ mag ≤ 8191`. -/
def aacWriteEscape (w : BitWriter) (mag : Nat) : Option BitWriter := Id.run do
  if mag < 16 || mag > 8191 then return none
  let mut n : Nat := 0
  while (1 <<< (n + 5)) <= mag && n < 9 do
    n := n + 1
  if n > 8 then return none
  let mut cur := w
  for _ in [:n] do
    cur := cur.writeBit 1
  cur := cur.writeBit 0
  let suffixBits := n + 4
  let suffix := mag - (1 <<< suffixBits)
  return some (cur.writeBitsMSB suffix.toUInt64 suffixBits)

/-- Read an ISO/IEC 14496-3 Book 11 escape sequence (`N ≤ 8`, total `< 22` bits, value `≤ 8191`). -/
def aacReadEscape (r : BitReader) : Option (Nat × BitReader) := Id.run do
  let mut cur := r
  let mut n : Nat := 0
  let mut terminated := false
  for _ in [:10] do
    let some (bit, cur') := cur.readBit | return none
    cur := cur'
    if bit == 0 then
      terminated := true
      break
    n := n + 1
  if !terminated || n > 8 then return none
  let suffixBits := n + 4
  let some (suf, cur') := cur.readBitsMSB suffixBits | return none
  let val := (1 <<< suffixBits) + suf.toNat
  if val > 8191 then return none
  return some (val, cur')

def aacReadSfDelta (r : BitReader) : Option (Int × BitReader) :=
  match aacTrieRead r aacSfTrie 20 with
  | some (idx, r') => some ((idx : Int) - 60, r')
  | none => none

/-- Encode one spectral tuple (`dim = 4` for books `1..4`, `dim = 2` for books `5..11`). -/
def aacEncodeTuple (w : BitWriter) (book : Nat) (tuple : Array Int) : Option BitWriter := Id.run do
  let some idx := aacCbIndex book tuple | return none
  let codes := (aacCbCodes book).map (·.toUInt32)
  let bits  := aacCbBits book
  let some cur0 := aacHuffWrite w codes bits idx | return none
  let mut cur := cur0
  if !aacCbSigned book then
    for v in tuple do
      if v != 0 then
        cur := cur.writeBit (if v < 0 then 1 else 0)
  if book == 11 then
    for v in tuple do
      let a := v.natAbs
      if a >= 16 then
        let some cur' := aacWriteEscape cur a | return none
        cur := cur'
  return some cur

/-- Decode one spectral tuple (`dim = 4` for books `1..4`, `dim = 2` for books `5..11`). -/
def aacDecodeTuple (r : BitReader) (book : Nat) : Option (Array Int × BitReader) := Id.run do
  let trie := aacSpectralTries.getD book #[]
  let some (idx, cur0) := aacTrieRead r trie 20 | return none
  let mut cur := cur0
  let raw := aacCbUnpack book idx
  if aacCbSigned book then
    return some (raw, cur)
  let dim := raw.size
  let mut signs := Array.replicate dim false
  for i in [:dim] do
    if raw.getD i 0 != 0 then
      let some (b, cur') := cur.readBit | return none
      cur := cur'
      signs := signs.set! i (b == 1)
  let mut out := Array.emptyWithCapacity dim
  for i in [:dim] do
    let a0 := (raw.getD i 0).natAbs
    let mut mag := a0
    if book == 11 && a0 == 16 then
      let some (esc, cur') := aacReadEscape cur | return none
      cur := cur'
      mag := esc
    let v : Int := if signs.getD i false then -(mag : Int) else (mag : Int)
    out := out.push v
  return some (out, cur)

/-- Bit cost of encoding quantized band slice `qSlice` with codebook `book` (`0..11`). -/
def aacBandBookBits (book : Nat) (qSlice : Array Int) : Option Nat := Id.run do
  if book == 0 then
    for v in qSlice do
      if v != 0 then return none
    return some 0
  let dim := aacCbDim book
  if dim == 0 || qSlice.size % dim != 0 then return none
  let bitsTbl := aacCbBits book
  let signed := aacCbSigned book
  let mut total : Nat := 0
  let nTuples := qSlice.size / dim
  for t in [:nTuples] do
    let sub := qSlice.extract (t * dim) ((t + 1) * dim)
    let some idx := aacCbIndex book sub | return none
    let cwBits := (bitsTbl.getD idx 0).toNat
    if cwBits == 0 then return none
    total := total + cwBits
    if !signed then
      for v in sub do
        if v != 0 then total := total + 1
    if book == 11 then
      for v in sub do
        let a := v.natAbs
        if a > 8191 then return none
        if a >= 16 then
          let mut n : Nat := 0
          while (1 <<< (n + 5)) <= a && n < 9 do
            n := n + 1
          total := total + (2 * n + 5)
  return some total

/-- Choose the minimum-bit Huffman codebook (`0..11`) for a quantized band `qSlice`. -/
def aacSelectBestBook (qSlice : Array Int) : UInt8 × Nat := Id.run do
  if let some _ := aacBandBookBits 0 qSlice then
    return (0, 0)
  let mut bestBook : UInt8 := 11
  let mut bestBits : Nat := 1000000000
  for b in [1:12] do
    if let some c := aacBandBookBits b qSlice then
      if c < bestBits then
        bestBits := c
        bestBook := b.toUInt8
  return (bestBook, bestBits)

/-! ## ISO/IEC 14496-3 §4.4.2 Channel Stream Bitstream (`section_data`, TNS, ICS, `raw_data_block`) -/

/-- One contiguous run of scalefactor bands sharing a single codebook (`section_data`). -/
structure AacSection where
  book   : UInt8
  length : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One channel's spectral payload before framing. -/
structure AacChannelPayload where
  globalGain : Nat
  maxSfb     : Nat
  sections   : Array AacSection
  sf         : Array Nat
  isScale    : Array Float := #[]
  pnsGain    : Array Float := #[]
  q          : Array Int
  tns        : AacTnsInfo
  deriving Repr, Inhabited

/-- A decoded AAC-LC frame (`1` or `2` channels of `1024` inverse-quantized bins each). -/
structure AacLcFrame where
  sfi      : UInt8
  seq      : AacWindowSequence
  useKbd   : Bool
  seqCh1   : AacWindowSequence := .onlyLong
  kbdCh1   : Bool := false
  groupLen : Array Nat
  maxSfb   : Nat
  msMode   : UInt8 := 0
  msMask   : Array Bool := #[]
  ch       : Array (Array Float)
  deriving Repr, Inhabited

/-- Collapse consecutive identical codebooks into `section_data` runs. -/
def aacBuildSections (books : Array UInt8) : Array AacSection := Id.run do
  let mut out : Array AacSection := #[]
  let mut i : Nat := 0
  while i < books.size do
    let b := books.getD i 0
    let mut len : Nat := 1
    while i + len < books.size && books.getD (i + len) 0 == b do
      len := len + 1
    out := out.push { book := b, length := len }
    i := i + len
  return out

/-- Expand `section_data` runs back into one codebook per scalefactor band. -/
def aacExpandSections (sections : Array AacSection) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for s in sections do
    for _ in [:s.length] do
      out := out.push s.book
  return out

/-- Write `section_data` (table 4.46) per window group: 4-bit book, then `3`- or `5`-bit length increments bounded by `maxSfb`. -/
def aacWriteSections (w : BitWriter) (books : Array UInt8) (isShort : Bool) (numGroups maxSfb : Nat) : Option BitWriter := Id.run do
  if books.size != numGroups * maxSfb then return none
  let bits := if isShort then 3 else 5
  let esc := (1 <<< bits) - 1
  let mut cur := w
  for g in [:numGroups] do
    let gBooks := books.extract (g * maxSfb) ((g + 1) * maxSfb)
    let gSecs := aacBuildSections gBooks
    let mut covered : Nat := 0
    for s in gSecs do
      if s.book == 12 || s.book > 15 || s.length == 0 then return none
      cur := cur.writeBitsMSB s.book.toUInt64 4
      let mut rem := s.length
      while rem >= esc do
        cur := cur.writeBitsMSB esc.toUInt64 bits
        rem := rem - esc
      cur := cur.writeBitsMSB rem.toUInt64 bits
      covered := covered + s.length
    if covered != maxSfb then return none
  return some cur

/-- Read `section_data` (table 4.46) per window group, rejecting book `12` and runs past `maxSfb`. -/
def aacReadSections (r : BitReader) (isShort : Bool) (numGroups maxSfb : Nat) : Option (Array AacSection × BitReader) := Id.run do
  let bits := if isShort then 3 else 5
  let esc := (1 <<< bits) - 1
  let mut cur := r
  let mut out : Array AacSection := #[]
  for _ in [:numGroups] do
    let mut covered : Nat := 0
    let mut guard : Nat := 0
    while covered < maxSfb && guard < 128 do
      guard := guard + 1
      let some (book, c1) := cur.readBitsMSB 4 | return none
      cur := c1
      if book.toNat == 12 then return none
      let mut len : Nat := 0
      let mut more := true
      while more do
        let some (incr, c2) := cur.readBitsMSB bits | return none
        cur := c2
        len := len + incr.toNat
        if covered + len > maxSfb then return none
        more := incr.toNat == esc
      if len > 0 then
        out := out.push { book := book.toUInt8, length := len }
      covered := covered + len
    if covered != maxSfb then return none
  return some (out, cur)

/-- Write the per-band scalefactor deltas of one channel (table 4.47) for LC codebooks `0..11`. -/
def aacWriteScaleFactors (w : BitWriter) (books : Array UInt8) (sf : Array Nat) (globalGain : Nat) : Option BitWriter := Id.run do
  let mut cur := w
  let mut prev : Int := globalGain
  for idx in [:books.size] do
    let b := books.getD idx 0
    if b != 0 then
      if b > 11 then return none
      let v := sf.getD idx globalGain
      if v > 255 then return none
      let some cur' := aacWriteSfDelta cur ((v : Int) - prev) | return none
      cur := cur'
      prev := v
  return some cur

/-- Read the per-band scalefactor/noise/IS deltas of one channel (table 4.47), returning `(sf, isScale, pnsGain, nextReader)`. -/
def aacReadScaleFactors (r : BitReader) (sections : Array AacSection) (globalGain : Nat) :
    Option (Array Nat × Array Float × Array Float × BitReader) := Id.run do
  let mut cur := r
  let mut offSf  : Int := globalGain
  let mut offPns : Int := (globalGain : Int) - 90
  let mut offIs  : Int := 0
  let mut noiseFlag : Bool := true
  let mut sfOut  : Array Nat := #[]
  let mut isOut  : Array Float := #[]
  let mut pnsOut : Array Float := #[]
  for s in sections do
    for _ in [:s.length] do
      if s.book == 0 then
        sfOut := sfOut.push 0
        isOut := isOut.push 0.0
        pnsOut := pnsOut.push 0.0
      else if s.book == 14 || s.book == 15 then
        let some (d, c') := aacReadSfDelta cur | return none
        cur := c'
        offIs := offIs + d
        let clipped : Int := if offIs < -155 then -155 else if offIs > 100 then 100 else offIs
        let scale := Float.pow 2.0 ((Float.ofInt (-clipped)) * 0.25)
        sfOut := sfOut.push 0
        isOut := isOut.push scale
        pnsOut := pnsOut.push 0.0
      else if s.book == 13 then
        if noiseFlag then
          noiseFlag := false
          let some (raw, c') := cur.readBitsMSB 9 | return none
          cur := c'
          offPns := offPns + (raw.toNat : Int) - 256
        else
          let some (d, c') := aacReadSfDelta cur | return none
          cur := c'
          offPns := offPns + d
        let clipped : Int := if offPns < -100 then -100 else if offPns > 155 then 155 else offPns
        let gain := Float.pow 2.0 ((Float.ofInt clipped) * 0.25)
        sfOut := sfOut.push 0
        isOut := isOut.push 0.0
        pnsOut := pnsOut.push gain
      else
        let some (d, c') := aacReadSfDelta cur | return none
        cur := c'
        offSf := offSf + d
        if offSf < 0 || offSf > 255 then return none
        sfOut := sfOut.push offSf.toNat
        isOut := isOut.push 0.0
        pnsOut := pnsOut.push 0.0
  return some (sfOut, isOut, pnsOut, cur)

/-- Write `tns_data` (table 4.48) for one channel. -/
def aacWriteTns (w : BitWriter) (tns : AacTnsInfo) (isShort : Bool) : Option BitWriter := Id.run do
  let mut cur := w
  cur := cur.writeBit (if tns.present then 1 else 0)
  if !tns.present then return some cur
  let nFiltBits := if isShort then 1 else 2
  let lenBits := if isShort then 4 else 6
  let ordBits := if isShort then 3 else 5
  let nWin := if isShort then 8 else 1
  let maxOrd := aacTnsMaxOrder isShort
  for win in [:nWin] do
    let filts := tns.filters.getD win #[]
    if filts.size >= (1 <<< nFiltBits) then return none
    cur := cur.writeBitsMSB filts.size.toUInt64 nFiltBits
    if filts.size > 0 then
      cur := cur.writeBit (if tns.coefRes.getD win false then 1 else 0)
      for f in filts do
        if f.order > maxOrd then return none
        cur := cur.writeBitsMSB f.length.toUInt64 lenBits
        cur := cur.writeBitsMSB f.order.toUInt64 ordBits
        if f.order > 0 then
          cur := cur.writeBit (if f.direction then 1 else 0)
          cur := cur.writeBit (if f.coefCompress then 1 else 0)
          let coefBits := (if tns.coefRes.getD win false then 4 else 3) - (if f.coefCompress then 1 else 0)
          for i in [:f.order] do
            cur := cur.writeBitsMSB (f.coefIndices.getD i 0).toUInt64 coefBits
  return some cur

/-- Read `tns_data` (table 4.48) for one channel. -/
def aacReadTns (r : BitReader) (isShort : Bool) : Option (AacTnsInfo × BitReader) := Id.run do
  let some (present, c0) := r.readBit | return none
  if present == 0 then return some ({}, c0)
  let mut cur := c0
  let nFiltBits := if isShort then 1 else 2
  let lenBits := if isShort then 4 else 6
  let ordBits := if isShort then 3 else 5
  let nWin := if isShort then 8 else 1
  let maxOrd := aacTnsMaxOrder isShort
  let mut coefRes : Array Bool := #[]
  let mut filts : Array (Array AacTnsFilter) := #[]
  for _ in [:nWin] do
    let some (nFilt, c1) := cur.readBitsMSB nFiltBits | return none
    cur := c1
    if nFilt.toNat == 0 then
      coefRes := coefRes.push false
      filts := filts.push #[]
    else
      let some (cr, c2) := cur.readBit | return none
      cur := c2
      coefRes := coefRes.push (cr == 1)
      let mut win : Array AacTnsFilter := #[]
      for _ in [:nFilt.toNat] do
        let some (len, c3) := cur.readBitsMSB lenBits | return none
        cur := c3
        let some (ord, c4) := cur.readBitsMSB ordBits | return none
        cur := c4
        if ord.toNat > maxOrd then return none
        if ord.toNat == 0 then
          win := win.push { length := len.toNat, order := 0, direction := false, coefIndices := #[], parcor := #[] }
        else
          let some (dir, c5) := cur.readBit | return none
          cur := c5
          let some (comp, c6) := cur.readBit | return none
          cur := c6
          let coefBits := (if cr == 1 then 4 else 3) - (if comp == 1 then 1 else 0)
          let mut idxs : Array Nat := #[]
          let mut par : Array Float := #[]
          for _ in [:ord.toNat] do
            let some (idx, c7) := cur.readBitsMSB coefBits | return none
            cur := c7
            idxs := idxs.push idx.toNat
            par := par.push (aacTnsLookupParcor (comp == 1) (cr == 1) idx.toNat)
          win := win.push {
            length := len.toNat, order := ord.toNat, direction := dir == 1,
            coefCompress := comp == 1, coefIndices := idxs, parcor := par }
      filts := filts.push win
  return some ({ present := true, coefRes := coefRes, filters := filts }, cur)

/-- Write the 7 `scale_factor_grouping` bits for an `EIGHT_SHORT_SEQUENCE` (`1` = continue group, `0` = new group). -/
def aacWriteShortGrouping (w : BitWriter) (groupLen : Array Nat) : Option BitWriter := Id.run do
  let mut total : Nat := 0
  for g in groupLen do
    if g == 0 then return none
    total := total + g
  if total != 8 then return none
  let mut cur := w
  let mut first := true
  for g in groupLen do
    for step in [:g] do
      if first then first := false
      else if step > 0 then cur := cur.writeBit 1
      else cur := cur.writeBit 0
  return some cur

/-- Write one window group's quantized spectrum, replicating the group codebook across each window. -/
def aacWriteGroupSpectrum (w : BitWriter) (q : Array Int) (swb : Array Nat) (books : Array UInt8)
    (winBase gLen : Nat) : Option BitWriter := Id.run do
  let mut cur := w
  for sfb in [:books.size] do
    let book := (books.getD sfb 0).toNat
    if book != 0 && book <= 11 then
      let s0 := swb.getD sfb 0
      let e0 := swb.getD (sfb + 1) s0
      let dim := aacCbDim book
      if dim == 0 || (e0 - s0) % dim != 0 then return none
      for win in [:gLen] do
        let off := (winBase + win) * 128
        let mut k := s0
        while k < e0 do
          let mut tup : Array Int := #[]
          for d in [:dim] do
            tup := tup.push (q.getD (off + k + d) 0)
          let some cur' := aacEncodeTuple cur book tup | return none
          cur := cur'
          k := k + dim
  return some cur

/-- Read one window group's quantized spectrum. -/
def aacReadGroupSpectrum (r : BitReader) (swb : Array Nat) (books : Array UInt8) (winBase gLen : Nat)
    (acc : Array Int) : Option (Array Int × BitReader) := Id.run do
  let mut cur := r
  let mut out := acc
  for sfb in [:books.size] do
    let book := (books.getD sfb 0).toNat
    let s0 := swb.getD sfb 0
    let e0 := swb.getD (sfb + 1) s0
    if book == 0 || book > 11 then
      pure ()
    else
      let dim := aacCbDim book
      if dim == 0 || (e0 - s0) % dim != 0 then return none
      for win in [:gLen] do
        let off := (winBase + win) * 128
        let mut k := s0
        while k < e0 do
          let some (tup, c') := aacDecodeTuple cur book | return none
          cur := c'
          for d in [:dim] do
            out := out.set! (off + k + d) (tup.getD d 0)
          k := k + dim
  return some (out, cur)

/-- Write one `individual_channel_stream` (table 4.44), LC profile: no prediction, no pulses, no gain control. -/
def aacWriteIcs (w : BitWriter) (p : AacChannelPayload) (seq : AacWindowSequence) (useKbd : Bool)
    (groupLen swb : Array Nat) (commonWindow : Bool) : Option BitWriter := Id.run do
  if p.globalGain > 255 then return none
  let mut cur := w.writeBitsMSB p.globalGain.toUInt64 8
  let isShort := seq == .eightShort
  if !commonWindow then
    cur := cur.writeBit 0
    cur := cur.writeBitsMSB seq.toUInt8.toUInt64 2
    cur := cur.writeBit (if useKbd then 1 else 0)
    if isShort then
      cur := cur.writeBitsMSB p.maxSfb.toUInt64 4
      let some cGrp := aacWriteShortGrouping cur groupLen | return none
      cur := cGrp
    else
      cur := cur.writeBitsMSB p.maxSfb.toUInt64 6
      cur := cur.writeBit 0
  let books := aacExpandSections p.sections
  let numBands := groupLen.size * p.maxSfb
  if books.size != numBands then return none
  let some cSec := aacWriteSections cur books isShort groupLen.size p.maxSfb | return none
  cur := cSec
  let some cSf := aacWriteScaleFactors cur books p.sf p.globalGain | return none
  cur := cSf
  cur := cur.writeBit 0
  let some cTns := aacWriteTns cur p.tns isShort | return none
  cur := cTns
  cur := cur.writeBit 0
  let mut base : Nat := 0
  for gi in [:groupLen.size] do
    let gLen := groupLen.getD gi 1
    let gBooks := books.extract (gi * p.maxSfb) ((gi + 1) * p.maxSfb)
    let some cur' := aacWriteGroupSpectrum cur p.q swb gBooks base gLen | return none
    cur := cur'
    base := base + gLen
  return some cur

/-- Read one `individual_channel_stream` (table 4.44). -/
def aacReadIcs (r : BitReader) (sfi : UInt8) (commonWindow : Bool) (seq0 : AacWindowSequence)
    (kbd0 : Bool) (groups0 : Array Nat) (maxSfb0 : Nat) :
    Option (AacChannelPayload × AacWindowSequence × Bool × Array Nat × BitReader) := Id.run do
  let some (gg, c0) := r.readBitsMSB 8 | return none
  let mut cur := c0
  let mut seq := seq0
  let mut kbd := kbd0
  let mut groups := groups0
  let mut maxSfb := maxSfb0
  if !commonWindow then
    let some (res, c1) := cur.readBit | return none
    if res != 0 then return none
    cur := c1
    let some (sq, c2) := cur.readBitsMSB 2 | return none
    cur := c2
    let some (kb, c3) := cur.readBit | return none
    cur := c3
    seq := match sq.toNat with | 1 => .longStart | 2 => .eightShort | 3 => .longStop | _ => .onlyLong
    kbd := kb == 1
    if sq.toNat == 2 then
      let some (ms, c4) := cur.readBitsMSB 4 | return none
      cur := c4
      maxSfb := ms.toNat
      let mut gl : Array Nat := #[1]
      let mut openIdx : Nat := 0
      for _ in [:7] do
        let some (b, c5) := cur.readBit | return none
        cur := c5
        if b == 1 then
          gl := gl.set! openIdx ((gl.getD openIdx 1) + 1)
        else
          gl := gl.push 1
          openIdx := openIdx + 1
      groups := gl
    else
      let some (ms, c4) := cur.readBitsMSB 6 | return none
      cur := c4
      maxSfb := ms.toNat
      let some (pred, c5) := cur.readBit | return none
      if pred != 0 then return none
      cur := c5
      groups := #[1]
  let isShort := seq == .eightShort
  let some swbFull := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return none
  if maxSfb > swbFull.size - 1 then return none
  let swb := swbFull.extract 0 (maxSfb + 1)
  let some (sections, c6) := aacReadSections cur isShort groups.size maxSfb | return none
  cur := c6
  let some (sf, isScale, pnsGain, c7) := aacReadScaleFactors cur sections gg.toNat | return none
  cur := c7
  let some (pulse, c8) := cur.readBit | return none
  if pulse != 0 then return none
  cur := c8
  let some (tns, c9) := aacReadTns cur isShort | return none
  cur := c9
  let some (gain, c10) := cur.readBit | return none
  if gain != 0 then return none
  cur := c10
  let books := aacExpandSections sections
  let mut q : Array Int := Array.replicate 1024 0
  let mut base : Nat := 0
  for gi in [:groups.size] do
    let gLen := groups.getD gi 1
    let gBooks := books.extract (gi * maxSfb) ((gi + 1) * maxSfb)
    let some (q', c11) := aacReadGroupSpectrum cur swb gBooks base gLen q | return none
    q := q'
    cur := c11
    base := base + gLen
  let payload : AacChannelPayload := {
    globalGain := gg.toNat, maxSfb := maxSfb, sections := sections,
    sf := sf, isScale := isScale, pnsGain := pnsGain, q := q, tns := tns }
  return some (payload, seq, kbd, groups, cur)

/-- Inverse-quantize one channel (including deterministic LCG PNS for `book = 13`), without TNS. -/
def aacDequantizeChannel (p : AacChannelPayload) (swb : Array Nat)
    (groupLen : Array Nat) (rng0 : UInt32 := 0x1F2E3D4C) : Array Float × UInt32 := Id.run do
  let books := aacExpandSections p.sections
  let mut spec : Array Float := Array.replicate 1024 0.0
  let mut rng : UInt32 := rng0
  let mut idx : Nat := 0
  let mut base : Nat := 0
  for gLen in groupLen do
    for sfb in [:p.maxSfb] do
      let book := books.getD idx 0
      let sfv := p.sf.getD idx 0
      let s0 := swb.getD sfb 0
      let e0 := swb.getD (sfb + 1) s0
      if book != 0 && book <= 11 then
        for win in [:gLen] do
          let off := (base + win) * 128
          for k in [s0:e0] do
            spec := spec.set! (off + k) (aacDequantizeCoeff (p.q.getD (off + k) 0) sfv)
      else if book == 13 && e0 > s0 then
        let gain := p.pnsGain.getD idx 0.0
        for win in [:gLen] do
          let off := (base + win) * 128
          let mut ener : Float := 0.0
          let mut noiseVals : Array Float := Array.emptyWithCapacity (e0 - s0)
          for _ in [s0:e0] do
            rng := rng * 1664525 + 1013904223
            let s32 : Int32 := rng.toInt32
            let vf := Float.ofInt s32.toInt
            ener := ener + vf * vf
            noiseVals := noiseVals.push vf
          let scale := if ener <= 1e-20 then 0.0 else gain / Float.sqrt ener
          for j in [:e0 - s0] do
            spec := spec.set! (off + s0 + j) ((noiseVals.getD j 0.0) * scale)
      idx := idx + 1
    base := base + gLen
  return (spec, rng)

/-- Inverse-quantize one channel and undo its TNS analysis filter. -/
def aacReconstructChannel (p : AacChannelPayload) (sfi : UInt8) (seq : AacWindowSequence) (swb : Array Nat)
    (groupLen : Array Nat) : Array Float :=
  let (spec, _) := aacDequantizeChannel p swb groupLen
  aacApplyTns spec p.tns sfi (seq == .eightShort) p.maxSfb true

/-- Write one `raw_data_block`: a single SCE (mono) or CPE (stereo) followed by `END`. -/
def aacWriteRawDataBlock (seq : AacWindowSequence) (useKbd : Bool) (groupLen swb : Array Nat)
    (msMode : UInt8) (msMask : Array Bool) (chs : Array AacChannelPayload) : Option ByteArray := Id.run do
  if chs.isEmpty || chs.size > 2 then return none
  let mut w := BitWriter.empty
  if chs.size == 1 then
    w := w.writeBitsMSB 0 3
    w := w.writeBitsMSB 0 4
    let some w' := aacWriteIcs w (chs.getD 0 default) seq useKbd groupLen swb false | return none
    w := w'
  else
    w := w.writeBitsMSB 1 3
    w := w.writeBitsMSB 0 4
    w := w.writeBit 1
    w := w.writeBit 0
    w := w.writeBitsMSB seq.toUInt8.toUInt64 2
    w := w.writeBit (if useKbd then 1 else 0)
    let isShort := seq == .eightShort
    let maxSfb := (chs.getD 0 default).maxSfb
    if isShort then
      w := w.writeBitsMSB maxSfb.toUInt64 4
      let some wGrp := aacWriteShortGrouping w groupLen | return none
      w := wGrp
    else
      w := w.writeBitsMSB maxSfb.toUInt64 6
      w := w.writeBit 0
    if msMode > 2 then return none
    w := w.writeBitsMSB msMode.toUInt64 2
    if msMode == 1 then
      if msMask.size != groupLen.size * maxSfb then return none
      for b in msMask do
        w := w.writeBit (if b then 1 else 0)
    for ch in chs do
      let some w' := aacWriteIcs w ch seq useKbd groupLen swb true | return none
      w := w'
  w := w.writeBitsMSB 7 3
  w := w.alignToByte
  return some w.toByteArray

/-- Skip a `data_stream_element` (`TYPE_DSE = 4`, ISO/IEC 14496-3 table 4.10), failing closed on truncated payload. -/
def aacSkipDse (r : BitReader) : Option BitReader := do
  let (byteAlign, r1) ← r.readBit
  let (cnt0, r2) ← r1.readBitsMSB 8
  let mut cnt := cnt0.toNat
  let mut cur := r2
  if cnt == 255 then
    let (esc, r3) ← cur.readBitsMSB 8
    cnt := cnt + esc.toNat
    cur := r3
  if byteAlign == 1 then
    let rem := cur.bitOffset % 8
    if rem != 0 then
      let pad := 8 - rem
      if cur.bitsLeft < pad then none
      cur := { cur with bitOffset := cur.bitOffset + pad }
  let skipBits := 8 * cnt
  if cur.bitsLeft < skipBits then none
  else some { cur with bitOffset := cur.bitOffset + skipBits }

/-- Skip a `fill_element` (`TYPE_FIL = 6`, ISO/IEC 14496-3 table 4.11), failing closed on truncated payload. -/
def aacSkipFil (r : BitReader) (elemId : Nat) : Option BitReader := do
  let mut cnt := elemId
  let mut cur := r
  if cnt == 15 then
    let (esc, r1) ← cur.readBitsMSB 8
    if esc.toNat == 0 then none
    cnt := cnt + esc.toNat - 1
    cur := r1
  let skipBits := 8 * cnt
  if cur.bitsLeft < skipBits then none
  else some { cur with bitOffset := cur.bitOffset + skipBits }

/-- Read one `raw_data_block`, accepting a single SCE or CPE plus optional DSE/FIL elements and rejecting invalid syntax. -/
def aacReadRawDataBlock (bytes : ByteArray) (sfi : UInt8) (rng0 : UInt32 := 0x1F2E3D4C) :
    Option (AacLcFrame × UInt32) := Id.run do
  let mut r := BitReader.ofSlice (ByteSlice.ofByteArray bytes)
  let mut decoded? : Option AacLcFrame := none
  let mut rng : UInt32 := rng0
  let mut guard : Nat := 0
  while guard < 64 do
    guard := guard + 1
    let some (tag, r1) := r.readBitsMSB 3 | return none
    r := r1
    if tag.toNat == 7 then
      return decoded?.map (fun f => (f, rng))
    let some (id, r2) := r.readBitsMSB 4 | return none
    r := r2
    if tag.toNat == 4 then
      let some r' := aacSkipDse r | return none
      r := r'
    else if tag.toNat == 6 then
      let some r' := aacSkipFil r id.toNat | return none
      r := r'
    else if tag.toNat == 0 then
      if decoded?.isSome || id.toNat != 0 then return none
      let some (p, seq, kbd, groups, r3) := aacReadIcs r sfi false .onlyLong false #[1] 0 | return none
      r := r3
      let some swbFull := (if seq == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return none
      let swb := swbFull.extract 0 (p.maxSfb + 1)
      let (deq, rng1) := aacDequantizeChannel p swb groups rng
      rng := rng1
      let spec := aacApplyTns deq p.tns sfi (seq == .eightShort) p.maxSfb true
      decoded? := some {
        sfi := sfi, seq := seq, useKbd := kbd, seqCh1 := seq, kbdCh1 := kbd,
        groupLen := groups, maxSfb := p.maxSfb, ch := #[spec] }
    else if tag.toNat == 1 then
      if decoded?.isSome || id.toNat != 0 then return none
      let some (cw, r3) := r.readBit | return none
      r := r3
      if cw == 1 then
        let some (res, r4) := r.readBit | return none
        if res != 0 then return none
        r := r4
        let some (sq, r5) := r.readBitsMSB 2 | return none
        r := r5
        let some (kb, r6) := r.readBit | return none
        r := r6
        let seq := match sq.toNat with | 1 => AacWindowSequence.longStart | 2 => .eightShort | 3 => .longStop | _ => .onlyLong
        let mut groups : Array Nat := #[1]
        let mut maxSfb : Nat := 0
        if sq.toNat == 2 then
          let some (ms, r7) := r.readBitsMSB 4 | return none
          r := r7
          maxSfb := ms.toNat
          let mut openIdx : Nat := 0
          for _ in [:7] do
            let some (b, r8) := r.readBit | return none
            r := r8
            if b == 1 then groups := groups.set! openIdx ((groups.getD openIdx 1) + 1)
            else
              groups := groups.push 1
              openIdx := openIdx + 1
        else
          let some (ms, r7) := r.readBitsMSB 6 | return none
          r := r7
          maxSfb := ms.toNat
          let some (pred, r8) := r.readBit | return none
          if pred != 0 then return none
          r := r8
        let some (msMode, r9) := r.readBitsMSB 2 | return none
        if msMode.toNat == 3 then return none
        r := r9
        let mut mask : Array Bool := #[]
        if msMode.toNat == 1 then
          for _ in [:groups.size * maxSfb] do
            let some (b, r10) := r.readBit | return none
            r := r10
            mask := mask.push (b == 1)
        let some swbFull := (if seq == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return none
        if maxSfb > swbFull.size - 1 then return none
        let swb := swbFull.extract 0 (maxSfb + 1)
        let some (p0, _, _, _, r11) := aacReadIcs r sfi true seq (kb == 1) groups maxSfb | return none
        r := r11
        let some (p1, _, _, _, r12) := aacReadIcs r sfi true seq (kb == 1) groups maxSfb | return none
        r := r12
        let (deq0, rng1) := aacDequantizeChannel p0 swb groups rng
        let (deq1, rng2) := aacDequantizeChannel p1 swb groups rng1
        rng := rng2
        let bt0 := aacExpandSections p0.sections
        let bt1 := aacExpandSections p1.sections
        let (ms0, ms1) := aacDecodeMidSide deq0 deq1 swb groups maxSfb msMode.toUInt8 mask bt0 bt1
        let is1 := aacDecodeIntensityStereo ms0 ms1 swb groups maxSfb msMode.toUInt8 mask bt1 p1.isScale
        let ch0 := aacApplyTns ms0 p0.tns sfi (seq == .eightShort) p0.maxSfb true
        let ch1 := aacApplyTns is1 p1.tns sfi (seq == .eightShort) p1.maxSfb true
        decoded? := some {
          sfi := sfi, seq := seq, useKbd := kb == 1, seqCh1 := seq, kbdCh1 := kb == 1,
          groupLen := groups, maxSfb := maxSfb, msMode := msMode.toUInt8, msMask := mask, ch := #[ch0, ch1] }
      else
        let some (p0, seq0, kbd0, groups0, r4) := aacReadIcs r sfi false .onlyLong false #[1] 0 | return none
        r := r4
        let some (p1, seq1, kbd1, groups1, r5) := aacReadIcs r sfi false .onlyLong false #[1] 0 | return none
        r := r5
        let some swbFull0 := (if seq0 == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return none
        let some swbFull1 := (if seq1 == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return none
        let swb0 := swbFull0.extract 0 (p0.maxSfb + 1)
        let swb1 := swbFull1.extract 0 (p1.maxSfb + 1)
        let (deq0, rng1) := aacDequantizeChannel p0 swb0 groups0 rng
        let (deq1, rng2) := aacDequantizeChannel p1 swb1 groups1 rng1
        rng := rng2
        let bt1 := aacExpandSections p1.sections
        let is1 :=
          if seq0 == seq1 && groups0 == groups1 then
            aacDecodeIntensityStereo deq0 deq1 swb1 groups1 p1.maxSfb 0 #[] bt1 p1.isScale
          else deq1
        let ch0 := aacApplyTns deq0 p0.tns sfi (seq0 == .eightShort) p0.maxSfb true
        let ch1 := aacApplyTns is1 p1.tns sfi (seq1 == .eightShort) p1.maxSfb true
        decoded? := some {
          sfi := sfi, seq := seq0, useKbd := kbd0, seqCh1 := seq1, kbdCh1 := kbd1,
          groupLen := groups0, maxSfb := Nat.max p0.maxSfb p1.maxSfb, ch := #[ch0, ch1] }
    else
      return none
  return none

/-- Encode one frame of PCM (`2048` samples per channel) and mux it as a single ADTS frame. -/
def aacEncodeAdtsFrame (pcm : Array (Array Float)) (sfi : UInt8) (bitrate : Nat)
    (useKbd : Bool := false) (useKbdPrev : Bool := false)
    (seq : AacWindowSequence := .onlyLong) : Option ByteArray := do
  let nch := pcm.size
  if nch != 1 && nch != 2 then none
  let some sr := aacSampleRateFromIndex sfi | none
  let isShort := seq == .eightShort
  let some swbFull := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | none
  let groups : Array Nat := if isShort then #[2, 2, 2, 2] else #[1]
  let budget := Nat.max 384 ((bitrate * 1024) / sr.toNat)
  let mut chans : Array AacChannelPayload := #[]
  let mut spectra : Array (Array Float) := #[]
  let mut maxSfb : Nat := 0
  for ch in [:nch] do
    let samples := pcm.getD ch #[]
    if samples.size < 2048 then none
    let analyzed := aacAnalyzeFrame (samples.extract 0 2048) seq useKbd useKbdPrev
    let mut peak : Nat := 0
    for sfb in [:swbFull.size - 1] do
      let s0 := swbFull.getD sfb 0
      let e0 := swbFull.getD (sfb + 1) s0
      let mut e := 0.0
      if isShort then
        for w in [:8] do
          for k in [s0:e0] do
            let v := analyzed.getD (w * 128 + k) 0.0
            e := e + v * v
      else
        for k in [s0:e0] do
          let v := analyzed.getD k 0.0
          e := e + v * v
      if e > 1e-4 then peak := sfb + 1
    maxSfb := Nat.max maxSfb peak
    spectra := spectra.push analyzed
  if maxSfb == 0 then maxSfb := 1
  let swb := swbFull.extract 0 (maxSfb + 1)
  let mut tnsList : Array AacTnsInfo := #[]
  let mut tnsSpecs : Array (Array Float) := #[]
  for ch in [:nch] do
    let (ti, tf) := aacSearchTns (spectra.getD ch #[]) sfi seq maxSfb
    tnsList := tnsList.push ti
    tnsSpecs := tnsSpecs.push tf
  let mut shaped : Array (Array Float) := tnsSpecs
  let mut msMode : UInt8 := 0
  let mut msMask : Array Bool := #[]
  if nch == 2 then
    let sameTns := !((tnsList.getD 0 {}).present || (tnsList.getD 1 {}).present)
    if sameTns then
      let (mode, mask, a0, a1) := aacEncodeMidSide (tnsSpecs.getD 0 #[]) (tnsSpecs.getD 1 #[]) swb groups maxSfb
      msMode := mode
      msMask := mask
      shaped := #[a0, a1]
  let numBands := groups.size * maxSfb
  for ch in [:nch] do
    let filtered := shaped.getD ch #[]
    let tns := tnsList.getD ch {}
    let share := Nat.max 128 (budget / nch)
    let mut minBase : Nat := 72
    let mut maxBase : Nat := 72
    for k in [:1024] do
      let a := Float.abs (filtered.getD k 0.0)
      if a > 1.0 then
        let need := Float.log2 a * 4.0 - 69.0
        if need > 0.0 then
          let needNat := (Float.toUInt64 need).toNat + 101
          if needNat > maxBase then maxBase := Nat.min 218 needNat
    if maxBase > 96 then minBase := maxBase - 24
    let mut bestQ : Array Int := Array.replicate 1024 0
    let mut bestSf : Array Nat := Array.replicate numBands minBase
    for step in [:64] do
      let sf0 : Nat := Nat.min 236 (minBase + step * 2)
      let mut q : Array Int := Array.replicate 1024 0
      let mut sfArr : Array Nat := Array.replicate numBands sf0
      let mut bits : Nat := 0
      let mut winBase : Nat := 0
      for gi in [:groups.size] do
        let gLen := groups.getD gi 1
        for sfb in [:maxSfb] do
          let bIdx := gi * maxSfb + sfb
          let s0 := swb.getD sfb 0
          let e0 := swb.getD (sfb + 1) s0
          let mut bMin : Nat := 72
          for w in [:gLen] do
            let off := (winBase + w) * 128
            for k in [s0:e0] do
              let a := Float.abs (filtered.getD (off + k) 0.0)
              if a > 1.0 then
                let need := Float.log2 a * 4.0 - 69.0
                if need > 0.0 then
                  let needNat := (Float.toUInt64 need).toNat + 101
                  if needNat > bMin then bMin := Nat.min 218 needNat
          let mut sfbSf : Nat := Nat.max bMin sf0
          let mut slice : Array Int := Array.emptyWithCapacity (gLen * (e0 - s0))
          for _ in [:6] do
            slice := Array.emptyWithCapacity (gLen * (e0 - s0))
            let mut clipped := false
            for w in [:gLen] do
              let off := (winBase + w) * 128
              for k in [s0:e0] do
                let c := aacQuantizeCoeff (filtered.getD (off + k) 0.0) sfbSf
                if c.natAbs >= 8191 then clipped := true
                slice := slice.push c
            if !clipped || sfbSf >= 236 then break
            sfbSf := sfbSf + 1
          let bCost := (aacSelectBestBook slice).2
          sfArr := sfArr.set! bIdx sfbSf
          for w in [:gLen] do
            let off := (winBase + w) * 128
            for j in [:e0 - s0] do
              q := q.set! (off + s0 + j) (slice.getD (w * (e0 - s0) + j) 0)
          bits := bits + bCost
        winBase := winBase + gLen
      bestQ := q
      bestSf := sfArr
      if bits + 48 <= share then break
    let mut books : Array UInt8 := Array.emptyWithCapacity numBands
    let mut winBase2 : Nat := 0
    for gi in [:groups.size] do
      let gLen := groups.getD gi 1
      for sfb in [:maxSfb] do
        let s0 := swb.getD sfb 0
        let e0 := swb.getD (sfb + 1) s0
        let mut slice : Array Int := Array.emptyWithCapacity (gLen * (e0 - s0))
        for w in [:gLen] do
          let off := (winBase2 + w) * 128
          for k in [s0:e0] do
            slice := slice.push (bestQ.getD (off + k) 0)
        books := books.push (aacSelectBestBook slice).1
      winBase2 := winBase2 + gLen
    let mut prevActive : Nat := 0
    let mut havePrev := false
    for bIdx in [:numBands] do
      if books.getD bIdx 0 != 0 then
        let cur := bestSf.getD bIdx 140
        if !havePrev then
          prevActive := cur
          havePrev := true
        else
          let clamped :=
            if cur > prevActive + 60 then prevActive + 60
            else if cur + 60 < prevActive then prevActive - 60
            else cur
          bestSf := bestSf.set! bIdx clamped
          prevActive := clamped
    let mut firstGain : Nat := bestSf.getD 0 140
    for bIdx in [:numBands] do
      if books.getD bIdx 0 != 0 then
        firstGain := bestSf.getD bIdx 140
        break
    let mut grpSecs : Array AacSection := #[]
    for gi in [:groups.size] do
      let gBooks := books.extract (gi * maxSfb) ((gi + 1) * maxSfb)
      for s in aacBuildSections gBooks do
        grpSecs := grpSecs.push s
    chans := chans.push {
      globalGain := firstGain, maxSfb := maxSfb, sections := grpSecs,
      sf := bestSf, q := bestQ, tns := tns }
  let raw ← aacWriteRawDataBlock seq useKbd groups swb msMode msMask chans
  muxAdtsFrame sfi nch.toUInt8 raw

/-- Decode one ADTS frame into inverse-quantized TNS spectra (`1024` bins per channel). -/
def aacDecodeAdtsFrame (frame : ByteArray) : Option (AacLcAdtsHeader × AacLcFrame) := do
  let hdr ← decodeAacLcAdtsHeader (ByteSlice.ofByteArray frame)
  let payload := frame.extract hdr.headerBytes frame.size
  let (decoded, _) ← aacReadRawDataBlock payload hdr.samplingFrequencyIdx
  if decoded.ch.size != hdr.channelConfiguration.toNat then none
  some (hdr, decoded)

/-- Clamp a floating-point PCM sample in `[-32768, 32767]` to signed 16-bit `Int32`. -/
@[inline]
def aacClampFloatToI16 (x : Float) : Int32 :=
  if x >= 32767.0 then 32767
  else if x <= -32768.0 then -32768
  else if x >= 0.0 then (Float.toUInt64 (x + 0.5)).toUInt32.toInt32
  else -((Float.toUInt64 ((-x) + 0.5)).toUInt32.toInt32)

/-- Encode `1` or `2` channels of signed `Int32` PCM (`bps`-bit) into a standalone ADTS AAC-LC stream.
    Prepends `1024` zero-padded priming samples and appends one trailing flush window (`aacenc` convention). -/
def aacEncodeAdtsStream (channelsData : Array (Array Int32)) (sampleRate : UInt32) (bps : Nat := 16)
    (bitrate : Nat := 128000) (useKbd : Bool := true) : Option ByteArray := Id.run do
  let nch := channelsData.size
  if nch != 1 && nch != 2 then return none
  if bps < 4 || bps > 32 then return none
  let some sfi := aacSampleRateToIndex sampleRate | return none
  let nSamples := (channelsData.getD 0 #[]).size
  if nSamples == 0 then return none
  for ch in [:nch] do
    if (channelsData.getD ch #[]).size != nSamples then return none
  let scale : Float :=
    if bps == 16 then 1.0
    else if bps > 16 then 1.0 / Float.ofNat (1 <<< (bps - 16))
    else Float.ofNat (1 <<< (16 - bps))
  let numFrames := (nSamples + 1023) / 1024 + 1
  let totalPadded := (numFrames + 1) * 1024
  let mut padded : Array (Array Float) := Array.emptyWithCapacity nch
  for ch in [:nch] do
    let src := channelsData.getD ch #[]
    let mut buf := Array.replicate totalPadded 0.0
    for i in [:nSamples] do
      let v := Float.ofInt (src.getD i 0).toInt * scale
      buf := buf.set! (1024 + i) v
    padded := padded.push buf
  let mut lookaheadTrans : Array Bool := Array.replicate (numFrames + 1) false
  for f in [:numFrames] do
    let off := f * 1024
    let mut hit := false
    for ch in [:nch] do
      let pcmCh := padded.getD ch #[]
      let mut subE : Array Float := Array.emptyWithCapacity 8
      for w in [:8] do
        let base := off + 448 + w * 128
        let mut e := 1.0
        for i in [:128] do
          let s := pcmCh.getD (base + i) 0.0
          e := e + s * s
        subE := subE.push e
      for w in [1:8] do
        let prev := subE.getD (w - 1) 1.0
        let cur  := subE.getD w 1.0
        if cur > prev * 12.0 && cur > 1e7 then
          hit := true
    lookaheadTrans := lookaheadTrans.set! f hit
  let mut seqs : Array AacWindowSequence := Array.replicate numFrames .onlyLong
  let mut prevSeq : AacWindowSequence := .onlyLong
  for f in [:numFrames] do
    let curTrans := lookaheadTrans.getD f false
    let nextTrans := lookaheadTrans.getD (f + 1) false
    let curSeq : AacWindowSequence :=
      match prevSeq with
      | .onlyLong   => if nextTrans then .longStart else .onlyLong
      | .longStart  => if curTrans || nextTrans then .eightShort else .longStop
      | .eightShort => if nextTrans then .eightShort else .longStop
      | .longStop   => if nextTrans then .longStart else .onlyLong
    seqs := seqs.set! f curSeq
    prevSeq := curSeq
  let mut out := ByteArray.emptyWithCapacity (numFrames * 384)
  for f in [:numFrames] do
    let off := f * 1024
    let mut winChans : Array (Array Float) := Array.emptyWithCapacity nch
    for ch in [:nch] do
      winChans := winChans.push ((padded.getD ch #[]).extract off (off + 2048))
    let curSeq := seqs.getD f .onlyLong
    let some frameBytes := aacEncodeAdtsFrame winChans sfi bitrate useKbd useKbd curSeq | return none
    out := out ++ frameBytes
  return some out

/-- Decode a standalone ADTS AAC-LC stream into `(channelsData, sampleRate, 16)` signed 16-bit PCM. -/
def aacDecodeAdtsStream (s : ByteSlice) (verifyCrc : Bool := false) :
    Option (Array (Array Int32) × UInt32 × Nat) := Id.run do
  let some (hdr, payloads) := demuxAdtsStream s verifyCrc | return none
  let some sr := aacSampleRateFromIndex hdr.samplingFrequencyIdx | return none
  let nch := hdr.channelConfiguration.toNat
  if nch != 1 && nch != 2 then return none
  let mut saved : Array (Array Float) := Array.replicate nch (Array.replicate 1024 0.0)
  let mut prevKbd : Array Bool := Array.replicate nch false
  let mut prevSeq : Array AacWindowSequence := Array.replicate nch .onlyLong
  let mut outChans : Array (Array Int32) := Array.replicate nch (Array.emptyWithCapacity (payloads.size * 1024))
  let mut rng : UInt32 := 0x1F2E3D4C
  let mut firstFrame := true
  for pSlice in payloads do
    let raw := pSlice.ba.extract pSlice.off (pSlice.off + pSlice.len)
    let some (frm, rngNext) := aacReadRawDataBlock raw hdr.samplingFrequencyIdx rng | return none
    rng := rngNext
    if frm.ch.size != nch then return none
    for ch in [:nch] do
      let curSeq := if ch == 0 then frm.seq else frm.seqCh1
      let curKbd := if ch == 0 then frm.useKbd else frm.kbdCh1
      if !firstFrame && !isValidAacWindowTransition (prevSeq.getD ch .onlyLong) curSeq then
        return none
      let kbdPrev := if firstFrame then curKbd else prevKbd.getD ch curKbd
      let (pcmF, nextSaved) := aacSynthesizeFrame (frm.ch.getD ch #[]) (saved.getD ch #[]) curSeq curKbd kbdPrev
      if pcmF.size != 1024 then return none
      saved := saved.set! ch nextSaved
      prevKbd := prevKbd.set! ch curKbd
      prevSeq := prevSeq.set! ch curSeq
      let mut dst := outChans.getD ch #[]
      for i in [:1024] do
        dst := dst.push (aacClampFloatToI16 (pcmF.getD i 0.0))
      outChans := outChans.set! ch dst
    firstFrame := false
  return some (outChans, sr, 16)

end LeanAV.AacLc







