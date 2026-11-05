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
def aacAdtsCrc16SliceGo (s : ByteSlice) (crc : UInt16) : Nat → Nat → UInt16
  | _, 0 => crc ^^^ 0xFFFF
  | i, rem + 1 => aacAdtsCrc16SliceGo s (aacAdtsCrc16StepByte crc (sliceByteD s i)) (i + 1) rem

def aacAdtsCrc16Slice (s : ByteSlice) : UInt16 :=
  aacAdtsCrc16SliceGo s 0xFFFF 0 s.len

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
def demuxAdtsStreamGo (s : ByteSlice) (verifyCrc : Bool) (pos : Nat)
    (firstHdr? : Option AacLcAdtsHeader) (frames : List ByteSlice) :
    Nat → Option (AacLcAdtsHeader × Array ByteSlice)
  | 0 => none
  | fuel + 1 =>
    if pos >= s.len then
      match firstHdr? with
      | some h0 => if frames.isEmpty then none else some (h0, frames.reverse.toArray)
      | none => none
    else
      let remLen := s.len - pos
      if remLen < 7 then none
      else
        let sub : ByteSlice := { ba := s.ba, off := s.off + pos, len := remLen }
        match decodeAacLcAdtsHeader sub with
        | none => none
        | some hdr =>
          let fLen := hdr.frameLength.toNat
          let hLen := hdr.headerBytes
          if fLen < hLen || pos + fLen > s.len then none
          else
            let payload : ByteSlice := { ba := s.ba, off := s.off + pos + hLen, len := fLen - hLen }
            if verifyCrc && !hdr.protectionAbsent && aacAdtsCrc16Slice payload != hdr.crc16 then none
            else
              match firstHdr? with
              | none => demuxAdtsStreamGo s verifyCrc (pos + fLen) (some hdr) (payload :: frames) fuel
              | some h0 =>
                if hdr.samplingFrequencyIdx != h0.samplingFrequencyIdx ||
                   hdr.channelConfiguration != h0.channelConfiguration ||
                   hdr.profileObjectType != h0.profileObjectType then none
                else demuxAdtsStreamGo s verifyCrc (pos + fLen) firstHdr? (payload :: frames) fuel

def demuxAdtsStream (s : ByteSlice) (verifyCrc : Bool := false) : Option (AacLcAdtsHeader × Array ByteSlice) :=
  if s.len < 7 then none
  else demuxAdtsStreamGo s verifyCrc 0 none [] (s.len + 2)

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
    let mag := if aq == 1 then 1.0 else aacPow43Table.getD aq 0.0
    let gain := if sf == 100 then 1.0 else aacSfGainTable.getD (Nat.min 320 sf) 1.0
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
def aacMdctFold (block : Array Float) : Array Float :=
  let n := block.size / 2
  if n != 128 && n != 1024 then #[]
  else
    let half := n / 2
    Array.ofFn (fun (idx : Fin n) =>
      let i := idx.val
      if i < half then
        -(block.getD (3 * half - 1 - i) 0.0 + block.getD (3 * half + i) 0.0)
      else
        let s := i - half
        block.getD s 0.0 - block.getD (n - 1 - s) 0.0)

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
def aacImdct (coeffs : Array Float) : Array Float :=
  let n := coeffs.size
  if n != 128 && n != 1024 then #[]
  else
    let d := aacDct4 coeffs
    let half := n / 2
    let scale := 2.0 / Float.ofNat n
    Array.ofFn (fun (idx : Fin (n * 2)) =>
      let i := idx.val
      if i < half then d.getD (half + i) 0.0 * scale
      else if i < n then -(d.getD (half + (n - 1 - i)) 0.0 * scale)
      else if i < 3 * half then -(d.getD (3 * half - 1 - i) 0.0 * scale)
      else -(d.getD (i - 3 * half) 0.0 * scale))

/-- Apply a `2N` analysis/synthesis window (sine or KBD). -/
def aacApplyWindow (block window : Array Float) : Array Float :=
  if block.size != window.size then #[]
  else block.zipWith (· * ·) window

/-- Overlap-add the second half of `prev` with the first half of `cur` (TDAC). -/
def aacTdacOverlapAdd (prev cur : Array Float) : Array Float :=
  let n := prev.size / 2
  if cur.size != prev.size || n == 0 then #[]
  else Array.ofFn (fun (idx : Fin n) => prev.getD (n + idx.val) 0.0 + cur.getD idx.val 0.0)

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
def aacBuildCompositeLongWindow (seq : AacWindowSequence) (useKbdCur useKbdPrev : Bool) : Array Float :=
  let lwPrev := aacHalfWindow false useKbdPrev
  let lwCur  := aacHalfWindow false useKbdCur
  let swPrev := aacHalfWindow true useKbdPrev
  let swCur  := aacHalfWindow true useKbdCur
  Array.ofFn (fun (idx : Fin 2048) =>
    let i := idx.val
    match seq with
    | .onlyLong =>
      if i < 1024 then lwPrev.getD i 0.0 else lwCur.getD (2047 - i) 0.0
    | .longStart =>
      if i < 1024 then lwPrev.getD i 0.0
      else if i < 1472 then 1.0
      else if i < 1600 then swCur.getD (1599 - i) 0.0
      else 0.0
    | .longStop =>
      if i < 448 then 0.0
      else if i < 576 then swPrev.getD (i - 448) 0.0
      else if i < 1024 then 1.0
      else lwCur.getD (2047 - i) 0.0
    | .eightShort => 0.0)

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
def aacEightShortAddBins (y im rise swCur : Array Float) (base : Nat) : Nat → Array Float
  | 0 => y
  | k + 1 =>
    let v0 := im.getD k 0.0 * rise.getD k 0.0
    let v1 := im.getD (128 + k) 0.0 * swCur.getD (127 - k) 0.0
    let y1 := y.set! (base + k) (y.getD (base + k) 0.0 + v0)
    let y2 := y1.set! (base + 128 + k) (y1.getD (base + 128 + k) 0.0 + v1)
    aacEightShortAddBins y2 im rise swCur base k

def aacEightShortSynthesizeWins (y halfSpec swPrev swCur : Array Float) : Nat → Nat → Array Float
  | _, 0 => y
  | w, rem + 1 =>
    let sub := halfSpec.extract (w * 128) ((w + 1) * 128)
    let im := aacImdct sub
    let rise := if w == 0 then swPrev else swCur
    let base := 448 + w * 128
    let y' := aacEightShortAddBins y im rise swCur base 128
    aacEightShortSynthesizeWins y' halfSpec swPrev swCur (w + 1) rem

def aacSynthesizeFrame (spec1024 savedOverlap : Array Float) (seq : AacWindowSequence) (useKbdCur useKbdPrev : Bool) : Array Float × Array Float :=
  if spec1024.size != 1024 || savedOverlap.size != 1024 then
    (#[], Array.replicate 1024 0.0)
  else
    let halfSpec := spec1024.map (fun c => 0.5 * c)
    let y2048 : Array Float :=
      match seq with
      | .eightShort =>
        let swPrev := aacHalfWindow true useKbdPrev
        let swCur  := aacHalfWindow true useKbdCur
        aacEightShortSynthesizeWins (Array.replicate 2048 0.0) halfSpec swPrev swCur 0 8
      | _ =>
        let win := aacBuildCompositeLongWindow seq useKbdCur useKbdPrev
        aacApplyWindow (aacImdct halfSpec) win
    let pcm := Array.ofFn (fun (idx : Fin 1024) => savedOverlap.getD idx.val 0.0 + y2048.getD idx.val 0.0)
    let nextSaved := Array.ofFn (fun (idx : Fin 1024) => y2048.getD (1024 + idx.val) 0.0)
    (pcm, nextSaved)

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
def aacTnsStepUpJ (prev lpc : Array Float) (i : Nat) (r : Float) : Nat → Nat → Array Float
  | _, 0 => lpc
  | j, rem + 1 =>
    let f := prev.getD j 0.0
    let b := prev.getD (i - 1 - j) 0.0
    let lpc1 := lpc.set! j (f + r * b)
    let lpc2 := lpc1.set! (i - 1 - j) (b + r * f)
    aacTnsStepUpJ prev lpc2 i r (j + 1) rem

def aacTnsParcorToLpcGo (parcor lpc : Array Float) : Nat → Nat → Array Float
  | _, 0 => lpc
  | i, rem + 1 =>
    let r := -(parcor.getD i 0.0)
    let lpc1 := lpc.set! i r
    let lpc2 := aacTnsStepUpJ lpc lpc1 i r 0 ((i + 1) / 2)
    aacTnsParcorToLpcGo parcor lpc2 (i + 1) rem

def aacTnsParcorToLpc (parcor : Array Float) : Array Float :=
  let order := parcor.size
  aacTnsParcorToLpcGo parcor (Array.replicate order 0.0) 0 order

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

/-- Clipped TNS band count `min(tns_max_bands, max_sfb)` (`0` when unsupported). -/
@[inline]
def aacTnsMaxBandCount (sfi : UInt8) (isShort : Bool) (maxSfb : Nat) : Nat :=
  let tnsMax := (if isShort then aacTnsMaxBandsShort else aacTnsMaxBandsLong).getD sfi.toNat 0
  Nat.min tnsMax maxSfb

/-- Clip a TNS filter's `length` to `tns_max_bands` (`sfiMaxBands`) on the encoder side. -/
@[inline]
def aacClipTnsFilterLength (filtLen sfiMaxBands maxSfb : Nat) : Nat :=
  Nat.min (Nat.min sfiMaxBands maxSfb) filtLen

/-- Apply TNS across a 1024-bin spectrum (`decode = true` applies all-pole AR synthesis; `decode = false` applies MA analysis). -/
def aacTnsTapSum (src : Array Float) (lpc : Array Float) (decode dir : Bool) (pos : Nat) : Nat → Float → Float
  | 0, acc => acc
  | k + 1, acc =>
    let tap := k + 1
    let prevPos := if dir then pos + tap else pos - tap
    let term := (src.getD prevPos 0.0) * (lpc.getD k 0.0)
    aacTnsTapSum src lpc decode dir pos k (if decode then acc - term else acc + term)

def aacTnsFilterBins (src out : Array Float) (lpc : Array Float) (decode dir : Bool)
    (winBase s0 e0 size order : Nat) : Nat → Array Float
  | 0 => out
  | rem + 1 =>
    let m := size - 1 - rem
    let pos := winBase + (if dir then e0 - 1 - m else s0 + m)
    let baseSrc := if decode then out else src
    let acc := aacTnsTapSum baseSrc lpc decode dir pos (Nat.min m order) (baseSrc.getD pos 0.0)
    let out' := out.set! pos acc
    aacTnsFilterBins src out' lpc decode dir winBase s0 e0 size order rem

def aacApplyTnsWindow (out : Array Float) (swbOffsets : Array Nat) (mmm w : Nat)
    (isShort decode : Bool) : Nat → List AacTnsFilter → Array Float
  | _, [] => out
  | top, filt :: rest =>
    let bottom := top - Nat.min top filt.length
    let order := Nat.min (aacTnsMaxOrder isShort) filt.order
    let out' :=
      if order > 0 && filt.parcor.size >= order then
        let lpc := aacTnsParcorToLpc (filt.parcor.extract 0 order)
        let s0 := swbOffsets.getD (Nat.min bottom mmm) 0
        let e0 := swbOffsets.getD (Nat.min top mmm) 0
        if e0 > s0 then
          let size := e0 - s0
          aacTnsFilterBins out out lpc decode filt.direction (w * 128) s0 e0 size order size
        else out
      else out
    aacApplyTnsWindow out' swbOffsets mmm w isShort decode bottom rest

def aacApplyTnsWindows (out : Array Float) (tns : AacTnsInfo) (swbOffsets : Array Nat)
    (numSwb mmm : Nat) (isShort decode : Bool) : Nat → Nat → Array Float
  | _, 0 => out
  | w, rem + 1 =>
    let winFilts := (tns.filters.getD w #[]).toList
    let out' := aacApplyTnsWindow out swbOffsets mmm w isShort decode numSwb winFilts
    aacApplyTnsWindows out' tns swbOffsets numSwb mmm isShort decode (w + 1) rem

def aacApplyTns (coeffs : Array Float) (tns : AacTnsInfo) (sfi : UInt8) (isShort : Bool) (maxSfb : Nat) (decode : Bool) : Array Float :=
  if !tns.present || coeffs.size != 1024 then coeffs
  else
    match (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) with
    | none => coeffs
    | some swbOffsets =>
      let numSwb := swbOffsets.size - 1
      let tnsMax := (if isShort then aacTnsMaxBandsShort else aacTnsMaxBandsLong).getD sfi.toNat 0
      let mmm := Nat.min tnsMax maxSfb
      if mmm == 0 then coeffs
      else aacApplyTnsWindows coeffs tns swbOffsets numSwb mmm isShort decode 0 (if isShort then 8 else 1)

/-- Schur/Levinson autocorrelation PARCOR estimator + 4-bit TNS analysis search for one channel spectrum. -/
def aacSearchTns (coeffs : Array Float) (sfi : UInt8) (seq : AacWindowSequence) (maxSfb : Nat) : AacTnsInfo × Array Float := Id.run do
  let isShort := seq == .eightShort
  let some swbOffsets := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | return ({}, coeffs)
  let numSwb := swbOffsets.size - 1
  let tnsMax := (if isShort then aacTnsMaxBandsShort else aacTnsMaxBandsLong).getD sfi.toNat 0
  let mmm := Nat.min tnsMax maxSfb
  let sfbStart := Nat.max (numSwb - tnsMax) (Nat.min mmm (if isShort then 2 else 8))
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
        if predGain >= 6.0 then
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
          let maxFiltBits := if isShort then 15 else 63
          let rawFiltLen := Nat.min maxFiltBits (Nat.min numSwb (numSwb - sfbStart))
          let fLen := aacClipTnsFilterLength rawFiltLen tnsMax mmm
          let f : AacTnsFilter := {
            length := fLen
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
          if ePost < r0 * 0.25 then
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

def aacMsBandEnergyBins (out0 out1 : Array Float) (off : Nat) :
    Nat → Nat → Float × Float × Float × Float → Float × Float × Float × Float
  | _, 0, acc => acc
  | k, rem + 1, (eL, eR, eM, eS) =>
    let l := out0.getD (off + k) 0.0
    let r := out1.getD (off + k) 0.0
    let m := 0.5 * (l + r)
    let s := 0.5 * (l - r)
    aacMsBandEnergyBins out0 out1 off (k + 1) rem (eL + l * l, eR + r * r, eM + m * m, eS + s * s)

def aacMsBandEnergyWins (out0 out1 : Array Float) (winBase s0 e0 : Nat) :
    Nat → Nat → Float × Float × Float × Float → Float × Float × Float × Float
  | _, 0, acc => acc
  | w, rem + 1, acc =>
    let acc' := aacMsBandEnergyBins out0 out1 ((winBase + w) * 128) s0 (e0 - s0) acc
    aacMsBandEnergyWins out0 out1 winBase s0 e0 (w + 1) rem acc'

def aacMsTransformBins (encode : Bool) (out0 out1 : Array Float) (off : Nat) :
    Nat → Nat → Array Float × Array Float
  | _, 0 => (out0, out1)
  | k, rem + 1 =>
    let a := out0.getD (off + k) 0.0
    let b := out1.getD (off + k) 0.0
    let v0 := if encode then 0.5 * (a + b) else a + b
    let v1 := if encode then 0.5 * (a - b) else a - b
    aacMsTransformBins encode (out0.set! (off + k) v0) (out1.set! (off + k) v1) off (k + 1) rem

def aacMsTransformWins (encode : Bool) (out0 out1 : Array Float) (winBase s0 e0 : Nat) :
    Nat → Nat → Array Float × Array Float
  | _, 0 => (out0, out1)
  | w, rem + 1 =>
    let (o0, o1) := aacMsTransformBins encode out0 out1 ((winBase + w) * 128) s0 (e0 - s0)
    aacMsTransformWins encode o0 o1 winBase s0 e0 (w + 1) rem

def aacEncodeMsBands (out0 out1 : Array Float) (swbOffsets : Array Nat) (winBase gLen : Nat)
    (mask : List Bool) (activeCount : Nat) : Nat → Nat → List Bool × Nat × Array Float × Array Float
  | _, 0 => (mask, activeCount, out0, out1)
  | sfb, rem + 1 =>
    let s0 := swbOffsets.getD sfb 0
    let e0 := swbOffsets.getD (sfb + 1) s0
    let (eL, eR, eM, eS) := aacMsBandEnergyWins out0 out1 winBase s0 e0 0 gLen (0.0, 0.0, 0.0, 0.0)
    let eLR := eL + eR
    let minLR := if eL < eR then eL else eR
    let minMS := if eM < eS then eM else eS
    let useMs := eLR > 1e-6 && minLR > 0.0 && minMS * 2.5 < minLR
    let (o0, o1, ac') :=
      if useMs then
        let (t0, t1) := aacMsTransformWins true out0 out1 winBase s0 e0 0 gLen
        (t0, t1, activeCount + 1)
      else (out0, out1, activeCount)
    aacEncodeMsBands o0 o1 swbOffsets winBase gLen (useMs :: mask) ac' (sfb + 1) rem

def aacEncodeMsGroups (out0 out1 : Array Float) (swbOffsets : Array Nat) (maxSfb winBase : Nat)
    (mask : List Bool) (activeCount : Nat) : List Nat → List Bool × Nat × Array Float × Array Float
  | [] => (mask.reverse, activeCount, out0, out1)
  | gLen :: rest =>
    let (mask', ac', o0, o1) := aacEncodeMsBands out0 out1 swbOffsets winBase gLen mask activeCount 0 maxSfb
    aacEncodeMsGroups o0 o1 swbOffsets maxSfb (winBase + gLen) mask' ac' rest

/-- Encoder M/S decision + transform (`M = (L+R)/2`, `S = (L-R)/2`) per `(window_group, sfb)`. Returns `(msMode, msMask, ch0, ch1)`. -/
def aacEncodeMidSide (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat) :
    UInt8 × Array Bool × Array Float × Array Float :=
  if ch0.size != 1024 || ch1.size != 1024 || maxSfb == 0 then (0, #[], ch0, ch1)
  else
    let (maskL, activeCount, out0, out1) := aacEncodeMsGroups ch0 ch1 swbOffsets maxSfb 0 [] 0 groupLens.toList
    let totalBands := groupLens.size * maxSfb
    let mode : UInt8 :=
      if activeCount == 0 then 0
      else if activeCount == totalBands then 2
      else 1
    (mode, maskL.toArray, out0, out1)

def aacDecodeMsBands (out0 out1 : Array Float) (swbOffsets : Array Nat) (winBase gLen : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt0 bt1 : Array UInt8) :
    Nat → Nat → Nat → Array Float × Array Float × Nat
  | _, 0, idx => (out0, out1, idx)
  | sfb, rem + 1, idx =>
    let active := if msPresent == 2 then true else msMask.getD idx false
    let b0 := bt0.getD idx 0
    let b1 := bt1.getD idx 0
    let (o0, o1) :=
      if active && b0 < 13 && b1 < 13 then
        let s0 := swbOffsets.getD sfb 0
        let e0 := swbOffsets.getD (sfb + 1) s0
        aacMsTransformWins false out0 out1 winBase s0 e0 0 gLen
      else (out0, out1)
    aacDecodeMsBands o0 o1 swbOffsets winBase gLen msPresent msMask bt0 bt1 (sfb + 1) rem (idx + 1)

def aacDecodeMsGroups (out0 out1 : Array Float) (swbOffsets : Array Nat) (maxSfb winBase idx : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt0 bt1 : Array UInt8) : List Nat → Array Float × Array Float
  | [] => (out0, out1)
  | gLen :: rest =>
    let (o0, o1, idx') := aacDecodeMsBands out0 out1 swbOffsets winBase gLen msPresent msMask bt0 bt1 0 maxSfb idx
    aacDecodeMsGroups o0 o1 swbOffsets maxSfb (winBase + gLen) idx' msPresent msMask bt0 bt1 rest

/-- Decoder M/S butterfly (`L = M + S`, `R = M - S`) for bands with `msMask[idx] = true` and `bandType < 13`. -/
def aacDecodeMidSide (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt0 bt1 : Array UInt8) : Array Float × Array Float :=
  if msPresent == 0 || ch0.size != 1024 || ch1.size != 1024 then (ch0, ch1)
  else aacDecodeMsGroups ch0 ch1 swbOffsets maxSfb 0 0 msPresent msMask bt0 bt1 groupLens.toList

def aacIsBandBins (ch0 out1 : Array Float) (scale : Float) (off : Nat) : Nat → Nat → Array Float
  | _, 0 => out1
  | k, rem + 1 =>
    let out1' := out1.set! (off + k) ((ch0.getD (off + k) 0.0) * scale)
    aacIsBandBins ch0 out1' scale off (k + 1) rem

def aacIsBandWins (ch0 out1 : Array Float) (scale : Float) (winBase s0 e0 : Nat) : Nat → Nat → Array Float
  | _, 0 => out1
  | w, rem + 1 =>
    let o1 := aacIsBandBins ch0 out1 scale ((winBase + w) * 128) s0 (e0 - s0)
    aacIsBandWins ch0 o1 scale winBase s0 e0 (w + 1) rem

def aacDecodeIsBands (ch0 out1 : Array Float) (swbOffsets : Array Nat) (winBase gLen : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt1 : Array UInt8) (isScale1 : Array Float) :
    Nat → Nat → Nat → Array Float × Nat
  | _, 0, idx => (out1, idx)
  | sfb, rem + 1, idx =>
    let b1 := bt1.getD idx 0
    let o1 :=
      if b1 == 14 || b1 == 15 then
        let dirSign : Float := if b1 == 15 then 1.0 else -1.0
        let msFlip : Float :=
          if msPresent != 0 && (if msPresent == 2 then true else msMask.getD idx false) then -1.0 else 1.0
        let scale := dirSign * msFlip * (isScale1.getD idx 0.0)
        let s0 := swbOffsets.getD sfb 0
        let e0 := swbOffsets.getD (sfb + 1) s0
        aacIsBandWins ch0 out1 scale winBase s0 e0 0 gLen
      else out1
    aacDecodeIsBands ch0 o1 swbOffsets winBase gLen msPresent msMask bt1 isScale1 (sfb + 1) rem (idx + 1)

def aacDecodeIsGroups (ch0 out1 : Array Float) (swbOffsets : Array Nat) (maxSfb winBase idx : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt1 : Array UInt8) (isScale1 : Array Float) :
    List Nat → Array Float
  | [] => out1
  | gLen :: rest =>
    let (o1, idx') := aacDecodeIsBands ch0 out1 swbOffsets winBase gLen msPresent msMask bt1 isScale1 0 maxSfb idx
    aacDecodeIsGroups ch0 o1 swbOffsets maxSfb (winBase + gLen) idx' msPresent msMask bt1 isScale1 rest

/-- Decoder Intensity Stereo reconstruction (`band_type ∈ {14, 15}`, ISO/IEC 14496-3 §4.6.8.2.3). -/
def aacDecodeIntensityStereo (ch0 ch1 : Array Float) (swbOffsets groupLens : Array Nat) (maxSfb : Nat)
    (msPresent : UInt8) (msMask : Array Bool) (bt1 : Array UInt8) (isScale1 : Array Float) : Array Float :=
  if ch0.size != 1024 || ch1.size != 1024 then ch1
  else aacDecodeIsGroups ch0 ch1 swbOffsets maxSfb 0 0 msPresent msMask bt1 isScale1 groupLens.toList

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

def aacCbIndexGo (book : Nat) (signed : Bool) (maxA off base : Nat) (acc : Nat) : List Int → Option Nat
  | [] => some acc
  | v :: rest =>
    if signed then
      if v < -(maxA : Int) || v > (maxA : Int) then none
      else
        let d := (v + (off : Int)).toNat
        aacCbIndexGo book signed maxA off base (acc * base + d) rest
    else
      let a := if book == 11 then Nat.min 16 v.natAbs else v.natAbs
      if a > maxA then none
      else aacCbIndexGo book signed maxA off base (acc * base + a) rest

def aacCbIndex (book : Nat) (vals : Array Int) : Option Nat :=
  let dim := aacCbDim book
  if dim == 0 || vals.size != dim then none
  else
    let signed := aacCbSigned book
    let maxA := aacCbMaxAbs book
    let off := aacCbOff book
    let base := if signed then 2 * maxA + 1 else maxA + 1
    aacCbIndexGo book signed maxA off base 0 vals.toList

def aacCbUnpackGo (signed : Bool) (off base : Nat) : Nat → Nat → List Int → List Int
  | 0, _, acc => acc
  | k + 1, rem, acc =>
    let d := rem % base
    let v : Int := if signed then (d : Int) - (off : Int) else (d : Int)
    aacCbUnpackGo signed off base k (rem / base) (v :: acc)

def aacCbUnpack (book : Nat) (idx : Nat) : Array Int :=
  let dim := aacCbDim book
  let signed := aacCbSigned book
  let maxA := aacCbMaxAbs book
  let off := aacCbOff book
  let base := if signed then 2 * maxA + 1 else maxA + 1
  if dim == 0 || base == 0 then #[]
  else (aacCbUnpackGo signed off base dim idx []).toArray

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

def aacHuffWrite16 (w : BitWriter) (codes : Array UInt16) (bits : Array UInt8) (idx : Nat) : Option BitWriter :=
  if h : idx < codes.size ∧ idx < bits.size then
    let n := (bits[idx]).toNat
    if n == 0 || n > 32 then none
    else some (w.writeBitsMSB (codes[idx]).toUInt64 n)
  else none

def aacWriteSfDelta (w : BitWriter) (diff : Int) : Option BitWriter :=
  let idx := diff + 60
  if idx < 0 || idx > 120 then none
  else aacHuffWrite w aacSfCodes aacSfBits idx.toNat

/-- Algebraic binary VLC trie over `(codes, bits)` for kernel-reducible prefix decoding. -/
inductive AacVlcTrie where
  | empty : AacVlcTrie
  | leaf (sym : Nat) : AacVlcTrie
  | branch (left right : AacVlcTrie) : AacVlcTrie
  deriving Repr, Inhabited

def AacVlcTrie.insert (t : AacVlcTrie) (code : UInt32) (sym : Nat) : Nat → AacVlcTrie
  | 0 => AacVlcTrie.leaf sym
  | rem + 1 =>
    let bit := ((code >>> rem.toUInt32) &&& 1) == 1
    let (l, r) :=
      match t with
      | .branch l r => (l, r)
      | _ => (.empty, .empty)
    if bit then .branch l (AacVlcTrie.insert r code sym rem)
    else .branch (AacVlcTrie.insert l code sym rem) r

def AacVlcTrie.buildGo (t : AacVlcTrie) (idx : Nat) : List UInt32 → List UInt8 → AacVlcTrie
  | c :: cs, b :: bs =>
    let len := b.toNat
    let t' := if len > 0 && len <= 32 then t.insert c idx len else t
    AacVlcTrie.buildGo t' (idx + 1) cs bs
  | _, _ => t

def AacVlcTrie.build16Go (t : AacVlcTrie) (idx : Nat) : List UInt16 → List UInt8 → AacVlcTrie
  | c :: cs, b :: bs =>
    let len := b.toNat
    let t' := if len > 0 && len <= 32 then t.insert c.toUInt32 idx len else t
    AacVlcTrie.build16Go t' (idx + 1) cs bs
  | _, _ => t

def aacBuildVlcTrie (codes : Array UInt32) (bits : Array UInt8) : AacVlcTrie :=
  AacVlcTrie.buildGo .empty 0 codes.toList bits.toList

def aacBuildVlcTrie16 (codes : Array UInt16) (bits : Array UInt8) : AacVlcTrie :=
  AacVlcTrie.build16Go .empty 0 codes.toList bits.toList

def aacSfTrie : AacVlcTrie := aacBuildVlcTrie aacSfCodes aacSfBits

def aacSpectralTrie (book : Nat) : AacVlcTrie :=
  match book with
  | 1 => aacBuildVlcTrie16 aacCodes1 aacBits1
  | 2 => aacBuildVlcTrie16 aacCodes2 aacBits2
  | 3 => aacBuildVlcTrie16 aacCodes3 aacBits3
  | 4 => aacBuildVlcTrie16 aacCodes4 aacBits4
  | 5 => aacBuildVlcTrie16 aacCodes5 aacBits5
  | 6 => aacBuildVlcTrie16 aacCodes6 aacBits6
  | 7 => aacBuildVlcTrie16 aacCodes7 aacBits7
  | 8 => aacBuildVlcTrie16 aacCodes8 aacBits8
  | 9 => aacBuildVlcTrie16 aacCodes9 aacBits9
  | 10 => aacBuildVlcTrie16 aacCodes10 aacBits10
  | 11 => aacBuildVlcTrie16 aacCodes11 aacBits11
  | _ => .empty

def aacTrieRead : BitReader → AacVlcTrie → Nat → Option (Nat × BitReader)
  | _, .empty, _ => none
  | r, .leaf sym, _ => some (sym, r)
  | _, .branch _ _, 0 => none
  | r, .branch l rt, steps + 1 =>
    match r.readBit with
    | none => none
    | some (bit, r') =>
      let child := if (bit &&& 1) == 1 then rt else l
      match child with
      | .leaf sym => some (sym, r')
      | .empty => none
      | .branch _ _ => aacTrieRead r' child steps

def aacEscapeFindN : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | fuel + 1, n, mag =>
    if (1 <<< (n + 5)) <= mag && n < 9 then aacEscapeFindN fuel (n + 1) mag
    else n

def aacWriteOnes (w : BitWriter) : Nat → BitWriter
  | 0 => w
  | k + 1 => aacWriteOnes (w.writeBit 1) k

/-- Write an ISO/IEC 14496-3 Book 11 escape sequence (`N` ones, `0`, `(N+4)`-bit suffix) for `16 ≤ mag ≤ 8191`. -/
def aacWriteEscape (w : BitWriter) (mag : Nat) : Option BitWriter :=
  if mag < 16 || !decide (mag ≤ 8191) then none
  else
    let n := aacEscapeFindN 9 0 mag
    if n > 8 then none
    else
      let cur := (aacWriteOnes w n).writeBit 0
      let suffixBits := n + 4
      let suffix := mag - (1 <<< suffixBits)
      some (cur.writeBitsMSB suffix.toUInt64 suffixBits)

def aacReadEscapePrefix (r : BitReader) : Nat → Nat → Option (Nat × BitReader)
  | 0, _ => none
  | fuel + 1, n =>
    match r.readBit with
    | none => none
    | some (bit, r') =>
      if bit == 0 then some (n, r')
      else aacReadEscapePrefix r' fuel (n + 1)

/-- Read an ISO/IEC 14496-3 Book 11 escape sequence (`N ≤ 8`, total `< 22` bits, value `≤ 8191`). -/
def aacReadEscape (r : BitReader) : Option (Nat × BitReader) :=
  match aacReadEscapePrefix r 10 0 with
  | none => none
  | some (n, cur) =>
    if n > 8 then none
    else
      let suffixBits := n + 4
      match cur.readBitsMSB suffixBits with
      | none => none
      | some (suf, cur') =>
        let val := (1 <<< suffixBits) + suf.toNat
        if !decide (val ≤ 8191) then none
        else some (val, cur')

def aacReadSfDelta (r : BitReader) : Option (Int × BitReader) :=
  match aacTrieRead r aacSfTrie 20 with
  | some (idx, r') => some ((idx : Int) - 60, r')
  | none => none

def aacWriteTupleSigns (w : BitWriter) : List Int → BitWriter
  | [] => w
  | v :: rest =>
    let w' := if v != 0 then w.writeBit (if v < 0 then 1 else 0) else w
    aacWriteTupleSigns w' rest

def aacWriteTupleEscapes (w : BitWriter) : List Int → Option BitWriter
  | [] => some w
  | v :: rest =>
    let a := v.natAbs
    if a >= 16 then
      match aacWriteEscape w a with
      | none => none
      | some w' => aacWriteTupleEscapes w' rest
    else aacWriteTupleEscapes w rest

/-- Encode one spectral tuple (`dim = 4` for books `1..4`, `dim = 2` for books `5..11`). -/
def aacEncodeTuple (w : BitWriter) (book : Nat) (tuple : Array Int) : Option BitWriter :=
  match aacCbIndex book tuple with
  | none => none
  | some idx =>
    match aacHuffWrite16 w (aacCbCodes book) (aacCbBits book) idx with
    | none => none
    | some cur0 =>
      let cur1 := if !aacCbSigned book then aacWriteTupleSigns cur0 tuple.toList else cur0
      if book == 11 then aacWriteTupleEscapes cur1 tuple.toList else some cur1

def aacReadTupleSigns (r : BitReader) : List Int → List Bool → Option (List Bool × BitReader)
  | [], acc => some (acc.reverse, r)
  | v :: rest, acc =>
    if v != 0 then
      match r.readBit with
      | none => none
      | some (b, r') => aacReadTupleSigns r' rest ((b == 1) :: acc)
    else aacReadTupleSigns r rest (false :: acc)

def aacDecodeTupleEscapes (r : BitReader) (isBook11 : Bool) : List Int → List Bool → List Int → Option (Array Int × BitReader)
  | [], _, acc => some (acc.reverse.toArray, r)
  | v :: vRest, s :: sRest, acc =>
    let a0 := v.natAbs
    if isBook11 && a0 == 16 then
      match aacReadEscape r with
      | none => none
      | some (esc, r') =>
        let outV : Int := if s then -(esc : Int) else (esc : Int)
        aacDecodeTupleEscapes r' isBook11 vRest sRest (outV :: acc)
    else
      let outV : Int := if s then -(a0 : Int) else (a0 : Int)
      aacDecodeTupleEscapes r isBook11 vRest sRest (outV :: acc)
  | _, [], _ => none

/-- Decode one spectral tuple (`dim = 4` for books `1..4`, `dim = 2` for books `5..11`). -/
def aacDecodeTuple (r : BitReader) (book : Nat) : Option (Array Int × BitReader) :=
  let trie := aacSpectralTrie book
  match aacTrieRead r trie 20 with
  | none => none
  | some (idx, cur0) =>
    let raw := aacCbUnpack book idx
    if aacCbSigned book then some (raw, cur0)
    else
      let rawL := raw.toList
      match aacReadTupleSigns cur0 rawL [] with
      | none => none
      | some (signs, cur1) => aacDecodeTupleEscapes cur1 (book == 11) rawL signs []

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

/-- Decoded `pulse_data` payload (ISO/IEC 14496-3 table 4.49 / §4.6.3.3):
    up to `4` escape pulses on a long-window spectrum starting at `pulseStartSfb`. -/
structure AacPulseData where
  present   : Bool := false
  startSfb  : Nat := 0
  offsets   : Array Nat := #[]
  amps      : Array Nat := #[]
  deriving Repr, DecidableEq, Inhabited

/-- Check whether `book` is a legal non-reserved AAC-LC section codebook (`book ≠ 12 ∧ book ≤ 15`). -/
@[inline]
def isValidAacSectionBook (book : UInt8) : Bool :=
  book != 12 && book <= 15

/-- One channel's spectral payload before framing. -/
structure AacChannelPayload where
  globalGain : Nat
  maxSfb     : Nat
  sections   : Array AacSection
  sf         : Array Nat
  isScale    : Array Float := #[]
  pnsGain    : Array Float := #[]
  pulse      : AacPulseData := {}
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
def aacBuildSectionsGo (cur : UInt8) (len : Nat) (acc : List AacSection) : List UInt8 → Array AacSection
  | [] => ({ book := cur, length := len } :: acc).reverse.toArray
  | b :: bs =>
    if b == cur then aacBuildSectionsGo cur (len + 1) acc bs
    else aacBuildSectionsGo b 1 ({ book := cur, length := len } :: acc) bs

def aacBuildSections (books : Array UInt8) : Array AacSection :=
  match books.toList with
  | [] => #[]
  | b :: bs => aacBuildSectionsGo b 1 [] bs

/-- Expand `section_data` runs back into one codebook per scalefactor band. -/
def aacExpandSections (sections : Array AacSection) : Array UInt8 :=
  (sections.toList.flatMap (fun s => List.replicate s.length s.book)).toArray

/-- Write `section_data` (table 4.46) per window group: 4-bit book, then `3`- or `5`-bit length increments bounded by `maxSfb`. -/
def aacWriteSecLenEsc (w : BitWriter) (esc bits : Nat) : Nat → Nat → BitWriter
  | 0, rem => w.writeBitsMSB rem.toUInt64 bits
  | fuel + 1, rem =>
    if rem >= esc then
      aacWriteSecLenEsc (w.writeBitsMSB esc.toUInt64 bits) esc bits fuel (rem - esc)
    else
      w.writeBitsMSB rem.toUInt64 bits

def aacWriteSectionList (w : BitWriter) (esc bits : Nat) (covered : Nat) : List AacSection → Option (BitWriter × Nat)
  | [] => some (w, covered)
  | s :: rest =>
    if s.book == 12 || s.book > 15 || s.length == 0 then none
    else
      let w1 := w.writeBitsMSB s.book.toUInt64 4
      let w2 := aacWriteSecLenEsc w1 esc bits s.length s.length
      aacWriteSectionList w2 esc bits (covered + s.length) rest

def aacWriteSectionGroups (w : BitWriter) (books : Array UInt8) (esc bits maxSfb : Nat) : Nat → Nat → Option BitWriter
  | _, 0 => some w
  | g, rem + 1 =>
    let gBooks := books.extract (g * maxSfb) ((g + 1) * maxSfb)
    let gSecs := aacBuildSections gBooks
    match aacWriteSectionList w esc bits 0 gSecs.toList with
    | none => none
    | some (w', covered) =>
      if covered != maxSfb then none
      else aacWriteSectionGroups w' books esc bits maxSfb (g + 1) rem

def aacWriteSections (w : BitWriter) (books : Array UInt8) (isShort : Bool) (numGroups maxSfb : Nat) : Option BitWriter :=
  if books.size != numGroups * maxSfb then none
  else
    let bits := if isShort then 3 else 5
    let esc := (1 <<< bits) - 1
    aacWriteSectionGroups w books esc bits maxSfb 0 numGroups

/-- Read `section_data` (table 4.46) per window group, rejecting reserved book `12` and runs past `maxSfb`. -/
def aacReadSecLenEsc (r : BitReader) (esc bits covered maxSfb len : Nat) : Nat → Option (Nat × BitReader)
  | 0 => none
  | fuel + 1 =>
    match r.readBitsMSB bits with
    | none => none
    | some (incr, c2) =>
      let len' := len + incr.toNat
      if covered + len' > maxSfb then none
      else if incr.toNat == esc then aacReadSecLenEsc c2 esc bits covered maxSfb len' fuel
      else some (len', c2)

def aacReadSectionGroup (r : BitReader) (esc bits maxSfb covered : Nat) (acc : List AacSection) :
    Nat → Option (List AacSection × BitReader)
  | 0 => if covered == maxSfb then some (acc, r) else none
  | guard + 1 =>
    if covered >= maxSfb then
      if covered == maxSfb then some (acc, r) else none
    else
      match r.readBitsMSB 4 with
      | none => none
      | some (book, c1) =>
        if !isValidAacSectionBook book.toUInt8 then none
        else
          match aacReadSecLenEsc c1 esc bits covered maxSfb 0 (maxSfb + 4) with
          | none => none
          | some (len, c2) =>
            let acc' := if len > 0 then { book := book.toUInt8, length := len } :: acc else acc
            aacReadSectionGroup c2 esc bits maxSfb (covered + len) acc' guard

def aacReadSectionGroups (r : BitReader) (esc bits maxSfb : Nat) (acc : List AacSection) :
    Nat → Option (Array AacSection × BitReader)
  | 0 => some (acc.reverse.toArray, r)
  | rem + 1 =>
    match aacReadSectionGroup r esc bits maxSfb 0 acc 128 with
    | none => none
    | some (acc', r') => aacReadSectionGroups r' esc bits maxSfb acc' rem

def aacReadSections (r : BitReader) (isShort : Bool) (numGroups maxSfb : Nat) : Option (Array AacSection × BitReader) :=
  let bits := if isShort then 3 else 5
  let esc := (1 <<< bits) - 1
  aacReadSectionGroups r esc bits maxSfb [] numGroups

/-- Write the per-band scalefactor deltas of one channel (table 4.47) for LC codebooks `0..11`. -/
def aacWriteSfLoop (cur : BitWriter) (books : Array UInt8) (sf : Array Nat) (globalGain : Nat) (prev : Int) :
    Nat → Nat → Option BitWriter
  | _, 0 => some cur
  | idx, rem + 1 =>
    let b := books.getD idx 0
    if b != 0 then
      if b > 11 then none
      else
        let v := sf.getD idx globalGain
        if !decide (v ≤ 255) then none
        else
          match aacWriteSfDelta cur ((v : Int) - prev) with
          | none => none
          | some cur' => aacWriteSfLoop cur' books sf globalGain (v : Int) (idx + 1) rem
    else
      aacWriteSfLoop cur books sf globalGain prev (idx + 1) rem

def aacWriteScaleFactors (w : BitWriter) (books : Array UInt8) (sf : Array Nat) (globalGain : Nat) : Option BitWriter :=
  aacWriteSfLoop w books sf globalGain (globalGain : Int) 0 books.size

/-- Read the per-band scalefactor/noise/IS deltas of one channel (table 4.47), returning `(sf, isScale, pnsGain, nextReader)`. -/
def aacReadSfSecSteps (cur : BitReader) (book : UInt8) (offSf offPns offIs : Int) (noiseFlag : Bool)
    (sfOut : List Nat) (isOut pnsOut : List Float) :
    Nat → Option (BitReader × Int × Int × Int × Bool × List Nat × List Float × List Float)
  | 0 => some (cur, offSf, offPns, offIs, noiseFlag, sfOut, isOut, pnsOut)
  | rem + 1 =>
    if book == 0 then
      aacReadSfSecSteps cur book offSf offPns offIs noiseFlag (0 :: sfOut) (0.0 :: isOut) (0.0 :: pnsOut) rem
    else if book == 14 || book == 15 then
      match aacReadSfDelta cur with
      | none => none
      | some (d, c') =>
        let offIs' := offIs + d
        let clipped : Int := if decide (offIs' < -155) then -155 else if decide (offIs' > 100) then 100 else offIs'
        let scale := if clipped == 0 then 1.0 else Float.pow 2.0 ((Float.ofInt (-clipped)) * 0.25)
        aacReadSfSecSteps c' book offSf offPns offIs' noiseFlag (0 :: sfOut) (scale :: isOut) (0.0 :: pnsOut) rem
    else if book == 13 then
      let step? : Option (BitReader × Int × Bool) :=
        if noiseFlag then
          match cur.readBitsMSB 9 with
          | none => none
          | some (raw, c') => some (c', offPns + (raw.toNat : Int) - 256, false)
        else
          match aacReadSfDelta cur with
          | none => none
          | some (d, c') => some (c', offPns + d, false)
      match step? with
      | none => none
      | some (c', offPns', nf') =>
        let clipped : Int := if decide (offPns' < -100) then -100 else if decide (offPns' > 155) then 155 else offPns'
        let gain := if clipped == 0 then 1.0 else Float.pow 2.0 ((Float.ofInt clipped) * 0.25)
        aacReadSfSecSteps c' book offSf offPns' offIs nf' (0 :: sfOut) (0.0 :: isOut) (gain :: pnsOut) rem
    else
      match aacReadSfDelta cur with
      | none => none
      | some (d, c') =>
        let offSf' := offSf + d
        if decide (offSf' < 0) || decide (offSf' > 255) then none
        else aacReadSfSecSteps c' book offSf' offPns offIs noiseFlag (offSf'.toNat :: sfOut) (0.0 :: isOut) (0.0 :: pnsOut) rem

def aacReadSfSecs (cur : BitReader) (offSf offPns offIs : Int) (noiseFlag : Bool)
    (sfOut : List Nat) (isOut pnsOut : List Float) :
    List AacSection → Option (Array Nat × Array Float × Array Float × BitReader)
  | [] => some (sfOut.reverse.toArray, isOut.reverse.toArray, pnsOut.reverse.toArray, cur)
  | s :: rest =>
    match aacReadSfSecSteps cur s.book offSf offPns offIs noiseFlag sfOut isOut pnsOut s.length with
    | none => none
    | some (c', offSf', offPns', offIs', nf', sf', is', pns') =>
      aacReadSfSecs c' offSf' offPns' offIs' nf' sf' is' pns' rest

def aacReadScaleFactors (r : BitReader) (sections : Array AacSection) (globalGain : Nat) :
    Option (Array Nat × Array Float × Array Float × BitReader) :=
  aacReadSfSecs r (globalGain : Int) ((globalGain : Int) - 90) 0 true [] [] [] sections.toList

/-- Write `tns_data` (table 4.48) for one channel. -/
def aacWriteTnsCoefs (cur : BitWriter) (idxs : Array Nat) (coefBits : Nat) : Nat → Nat → BitWriter
  | _, 0 => cur
  | i, rem + 1 =>
    aacWriteTnsCoefs (cur.writeBitsMSB (idxs.getD i 0).toUInt64 coefBits) idxs coefBits (i + 1) rem

def aacWriteTnsFilts (cur : BitWriter) (cr : Bool) (lenBits ordBits maxOrd : Nat) : List AacTnsFilter → Option BitWriter
  | [] => some cur
  | f :: rest =>
    if f.order > maxOrd then none
    else
      let c1 := (cur.writeBitsMSB f.length.toUInt64 lenBits).writeBitsMSB f.order.toUInt64 ordBits
      let c2 :=
        if f.order > 0 then
          let c1a := (c1.writeBit (if f.direction then 1 else 0)).writeBit (if f.coefCompress then 1 else 0)
          let coefBits := (if cr then 4 else 3) - (if f.coefCompress then 1 else 0)
          aacWriteTnsCoefs c1a f.coefIndices coefBits 0 f.order
        else c1
      aacWriteTnsFilts c2 cr lenBits ordBits maxOrd rest

def aacWriteTnsWins (cur : BitWriter) (tns : AacTnsInfo) (nFiltBits lenBits ordBits maxOrd : Nat) : Nat → Nat → Option BitWriter
  | _, 0 => some cur
  | win, rem + 1 =>
    let filts := tns.filters.getD win #[]
    if filts.size >= (1 <<< nFiltBits) then none
    else
      let c1 := cur.writeBitsMSB filts.size.toUInt64 nFiltBits
      if filts.size > 0 then
        let cr := tns.coefRes.getD win false
        let c2 := c1.writeBit (if cr then 1 else 0)
        match aacWriteTnsFilts c2 cr lenBits ordBits maxOrd filts.toList with
        | none => none
        | some c3 => aacWriteTnsWins c3 tns nFiltBits lenBits ordBits maxOrd (win + 1) rem
      else
        aacWriteTnsWins c1 tns nFiltBits lenBits ordBits maxOrd (win + 1) rem

def aacWriteTns (w : BitWriter) (tns : AacTnsInfo) (isShort : Bool) : Option BitWriter :=
  let c0 := w.writeBit (if tns.present then 1 else 0)
  if !tns.present then some c0
  else
    let nFiltBits := if isShort then 1 else 2
    let lenBits := if isShort then 4 else 6
    let ordBits := if isShort then 3 else 5
    let nWin := if isShort then 8 else 1
    let maxOrd := aacTnsMaxOrder isShort
    aacWriteTnsWins c0 tns nFiltBits lenBits ordBits maxOrd 0 nWin

/-- Read `tns_data` (table 4.48) for one channel. -/
def aacReadTnsCoefs (cur : BitReader) (comp cr : Bool) (coefBits : Nat) (idxs : List Nat) (par : List Float) :
    Nat → Option (Array Nat × Array Float × BitReader)
  | 0 => some (idxs.reverse.toArray, par.reverse.toArray, cur)
  | rem + 1 =>
    match cur.readBitsMSB coefBits with
    | none => none
    | some (idx, c') =>
      let v := aacTnsLookupParcor comp cr idx.toNat
      aacReadTnsCoefs c' comp cr coefBits (idx.toNat :: idxs) (v :: par) rem

def aacReadTnsFilts (cur : BitReader) (cr : Bool) (lenBits ordBits maxOrd : Nat) (acc : List AacTnsFilter) :
    Nat → Option (Array AacTnsFilter × BitReader)
  | 0 => some (acc.reverse.toArray, cur)
  | rem + 1 =>
    match cur.readBitsMSB lenBits with
    | none => none
    | some (len, c3) =>
      match c3.readBitsMSB ordBits with
      | none => none
      | some (ord, c4) =>
        if ord.toNat > maxOrd then none
        else if ord.toNat == 0 then
          let f : AacTnsFilter := { length := len.toNat, order := 0, direction := false, coefIndices := #[], parcor := #[] }
          aacReadTnsFilts c4 cr lenBits ordBits maxOrd (f :: acc) rem
        else
          match c4.readBit with
          | none => none
          | some (dir, c5) =>
            match c5.readBit with
            | none => none
            | some (comp, c6) =>
              let coefBits := (if cr then 4 else 3) - (if comp == 1 then 1 else 0)
              match aacReadTnsCoefs c6 (comp == 1) cr coefBits [] [] ord.toNat with
              | none => none
              | some (idxs, par, c7) =>
                let f : AacTnsFilter := {
                  length := len.toNat, order := ord.toNat, direction := dir == 1,
                  coefCompress := comp == 1, coefIndices := idxs, parcor := par }
                aacReadTnsFilts c7 cr lenBits ordBits maxOrd (f :: acc) rem

def aacReadTnsWins (cur : BitReader) (nFiltBits lenBits ordBits maxOrd : Nat)
    (coefRes : List Bool) (filts : List (Array AacTnsFilter)) :
    Nat → Option (AacTnsInfo × BitReader)
  | 0 => some ({ present := true, coefRes := coefRes.reverse.toArray, filters := filts.reverse.toArray }, cur)
  | rem + 1 =>
    match cur.readBitsMSB nFiltBits with
    | none => none
    | some (nFilt, c1) =>
      if nFilt.toNat == 0 then
        aacReadTnsWins c1 nFiltBits lenBits ordBits maxOrd (false :: coefRes) (#[] :: filts) rem
      else
        match c1.readBit with
        | none => none
        | some (cr, c2) =>
          match aacReadTnsFilts c2 (cr == 1) lenBits ordBits maxOrd [] nFilt.toNat with
          | none => none
          | some (win, c3) =>
            aacReadTnsWins c3 nFiltBits lenBits ordBits maxOrd ((cr == 1) :: coefRes) (win :: filts) rem

def aacReadTns (r : BitReader) (isShort : Bool) : Option (AacTnsInfo × BitReader) :=
  match r.readBit with
  | none => none
  | some (present, c0) =>
    if present == 0 then some ({}, c0)
    else
      let nFiltBits := if isShort then 1 else 2
      let lenBits := if isShort then 4 else 6
      let ordBits := if isShort then 3 else 5
      let nWin := if isShort then 8 else 1
      let maxOrd := aacTnsMaxOrder isShort
      aacReadTnsWins c0 nFiltBits lenBits ordBits maxOrd [] [] nWin

/-- Write the 7 `scale_factor_grouping` bits for an `EIGHT_SHORT_SEQUENCE` (`1` = continue group, `0` = new group). -/
def aacWriteShortGrpSteps : BitWriter → Bool → Nat → Nat → BitWriter × Bool
  | cur, first, _, 0 => (cur, first)
  | cur, first, step, rem + 1 =>
    if first then aacWriteShortGrpSteps cur false (step + 1) rem
    else
      let cur' := if step > 0 then cur.writeBit 1 else cur.writeBit 0
      aacWriteShortGrpSteps cur' false (step + 1) rem

def aacWriteShortGrpList (cur : BitWriter) (first : Bool) (total : Nat) : List Nat → Option BitWriter
  | [] => if total == 8 then some cur else none
  | g :: rest =>
    if g == 0 then none
    else
      let (cur', first') := aacWriteShortGrpSteps cur first 0 g
      aacWriteShortGrpList cur' first' (total + g) rest

def aacWriteShortGrouping (w : BitWriter) (groupLen : Array Nat) : Option BitWriter :=
  aacWriteShortGrpList w true 0 groupLen.toList

/-- Write one window group's quantized spectrum, replicating the group codebook across each window. -/
def aacExtractTuple (q : Array Int) (base : Nat) (acc : List Int) : Nat → Nat → Array Int
  | _, 0 => acc.reverse.toArray
  | d, rem + 1 => aacExtractTuple q base (q.getD (base + d) 0 :: acc) (d + 1) rem

def aacWriteBandTuples (cur : BitWriter) (q : Array Int) (book dim off : Nat) : Nat → Nat → Option BitWriter
  | _, 0 => some cur
  | k, rem + 1 =>
    let tup := aacExtractTuple q (off + k) [] 0 dim
    match aacEncodeTuple cur book tup with
    | none => none
    | some cur' => aacWriteBandTuples cur' q book dim off (k + dim) rem

def aacWriteBandWins (cur : BitWriter) (q : Array Int) (book dim s0 nTup winBase : Nat) : Nat → Nat → Option BitWriter
  | _, 0 => some cur
  | win, rem + 1 =>
    match aacWriteBandTuples cur q book dim ((winBase + win) * 128) s0 nTup with
    | none => none
    | some cur' => aacWriteBandWins cur' q book dim s0 nTup winBase (win + 1) rem

def aacWriteGroupSfbs (cur : BitWriter) (q : Array Int) (swb : Array Nat) (books : Array UInt8)
    (winBase gLen : Nat) : Nat → Nat → Option BitWriter
  | _, 0 => some cur
  | sfb, rem + 1 =>
    let book := (books.getD sfb 0).toNat
    if book != 0 && book <= 11 then
      let s0 := swb.getD sfb 0
      let e0 := swb.getD (sfb + 1) s0
      let dim := aacCbDim book
      if dim == 0 || (e0 - s0) % dim != 0 then none
      else
        match aacWriteBandWins cur q book dim s0 ((e0 - s0) / dim) winBase 0 gLen with
        | none => none
        | some cur' => aacWriteGroupSfbs cur' q swb books winBase gLen (sfb + 1) rem
    else
      aacWriteGroupSfbs cur q swb books winBase gLen (sfb + 1) rem

def aacWriteGroupSpectrum (w : BitWriter) (q : Array Int) (swb : Array Nat) (books : Array UInt8)
    (winBase gLen : Nat) : Option BitWriter :=
  aacWriteGroupSfbs w q swb books winBase gLen 0 books.size

/-- Read one window group's quantized spectrum. -/
def aacScatterTuple (out : Array Int) (tup : Array Int) (base : Nat) : Nat → Nat → Array Int
  | _, 0 => out
  | d, rem + 1 => aacScatterTuple (out.set! (base + d) (tup.getD d 0)) tup base (d + 1) rem

def aacReadBandTuples (cur : BitReader) (out : Array Int) (book dim off : Nat) : Nat → Nat → Option (Array Int × BitReader)
  | _, 0 => some (out, cur)
  | k, rem + 1 =>
    match aacDecodeTuple cur book with
    | none => none
    | some (tup, c') =>
      let out' := aacScatterTuple out tup (off + k) 0 dim
      aacReadBandTuples c' out' book dim off (k + dim) rem

def aacReadBandWins (cur : BitReader) (out : Array Int) (book dim s0 nTup winBase : Nat) :
    Nat → Nat → Option (Array Int × BitReader)
  | _, 0 => some (out, cur)
  | win, rem + 1 =>
    match aacReadBandTuples cur out book dim ((winBase + win) * 128) s0 nTup with
    | none => none
    | some (out', c') => aacReadBandWins c' out' book dim s0 nTup winBase (win + 1) rem

def aacReadGroupSfbs (cur : BitReader) (out : Array Int) (swb : Array Nat) (books : Array UInt8)
    (winBase gLen : Nat) : Nat → Nat → Option (Array Int × BitReader)
  | _, 0 => some (out, cur)
  | sfb, rem + 1 =>
    let book := (books.getD sfb 0).toNat
    if book == 0 || book > 11 then
      aacReadGroupSfbs cur out swb books winBase gLen (sfb + 1) rem
    else
      let s0 := swb.getD sfb 0
      let e0 := swb.getD (sfb + 1) s0
      let dim := aacCbDim book
      if dim == 0 || (e0 - s0) % dim != 0 then none
      else
        match aacReadBandWins cur out book dim s0 ((e0 - s0) / dim) winBase 0 gLen with
        | none => none
        | some (out', c') => aacReadGroupSfbs c' out' swb books winBase gLen (sfb + 1) rem

def aacReadGroupSpectrum (r : BitReader) (swb : Array Nat) (books : Array UInt8) (winBase gLen : Nat)
    (acc : Array Int) : Option (Array Int × BitReader) :=
  aacReadGroupSfbs r acc swb books winBase gLen 0 books.size

def aacWritePulsePairs (w : BitWriter) : List Nat → List Nat → Option BitWriter
  | [], [] => some w
  | off :: offs, amp :: amps =>
    if off > 31 || amp > 15 then none
    else
      let w1 := w.writeBitsMSB off.toUInt64 5
      let w2 := w1.writeBitsMSB amp.toUInt64 4
      aacWritePulsePairs w2 offs amps
  | _, _ => none

/-- Write `pulse_data` (ISO/IEC 14496-3 table 4.49) for one channel; rejects pulses on `EIGHT_SHORT_SEQUENCE`. -/
def aacWritePulseData (w : BitWriter) (pulse : AacPulseData) (isShort : Bool) (numSwb : Nat) : Option BitWriter :=
  if !pulse.present then some (w.writeBit 0)
  else if isShort || pulse.offsets.isEmpty || pulse.offsets.size > 4 ||
          pulse.offsets.size != pulse.amps.size || pulse.startSfb >= numSwb || pulse.startSfb > 63 then none
  else
    let w1 := (w.writeBit 1).writeBitsMSB (pulse.offsets.size - 1).toUInt64 2
    let w2 := w1.writeBitsMSB pulse.startSfb.toUInt64 6
    aacWritePulsePairs w2 pulse.offsets.toList pulse.amps.toList

def aacReadPulsePairs : BitReader → Nat → List Nat → List Nat →
    Nat → Option (Array Nat × Array Nat × BitReader)
  | r, _, offs, amps, 0 => some (offs.reverse.toArray, amps.reverse.toArray, r)
  | r, pos, offs, amps, k + 1 =>
    match r.readBitsMSB 5 with
    | none => none
    | some (off, r1) =>
      match r1.readBitsMSB 4 with
      | none => none
      | some (amp, r2) =>
        let pos' := pos + off.toNat
        if !decide (pos' < 1024) then none
        else aacReadPulsePairs r2 pos' (off.toNat :: offs) (amp.toNat :: amps) k

/-- Read `pulse_data` (ISO/IEC 14496-3 table 4.49), failing closed on `EIGHT_SHORT_SEQUENCE`,
    `pulse_start_sfb ≥ numSwb`, or pulse positions `≥ 1024`. -/
def aacReadPulseData (r : BitReader) (isShort : Bool) (swbFull : Array Nat) : Option (AacPulseData × BitReader) :=
  match r.readBit with
  | none => none
  | some (present, c0) =>
    if present == 0 then some ({}, c0)
    else if isShort then none
    else
      let numSwb := swbFull.size - 1
      match c0.readBitsMSB 2 with
      | none => none
      | some (npMinus1, c1) =>
        match c1.readBitsMSB 6 with
        | none => none
        | some (startSfb64, c2) =>
          let startSfb := startSfb64.toNat
          if startSfb >= numSwb then none
          else
            let count := npMinus1.toNat + 1
            let pos0 := swbFull.getD startSfb 1024
            match aacReadPulsePairs c2 pos0 [] [] count with
            | none => none
            | some (offs, amps, cur) =>
              some ({ present := true, startSfb := startSfb, offsets := offs, amps := amps }, cur)

def aacAdvancePulseSfb (swbFull : Array Nat) (pos : Nat) : Nat → Nat → Nat
  | 0, sfb => sfb
  | fuel + 1, sfb =>
    if sfb + 1 < swbFull.size && swbFull.getD (sfb + 1) 1024 <= pos then
      aacAdvancePulseSfb swbFull pos fuel (sfb + 1)
    else sfb

def aacApplyPulsePairs (out : Array Int) (swbFull : Array Nat) (books : Array UInt8) (maxSfb : Nat)
    (pos sfb : Nat) : List Nat → List Nat → Option (Array Int)
  | [], [] => some out
  | off :: offs, ampNat :: amps =>
    let pos' := pos + off
    if !decide (pos' < 1024) then none
    else
      let sfb' := aacAdvancePulseSfb swbFull pos' swbFull.size sfb
      let book := if sfb' < maxSfb then (books.getD sfb' 0).toNat else 0
      let out' :=
        if book >= 1 && book <= 11 then
          let cur := out.getD pos' 0
          let amp : Int := (ampNat : Int)
          let updated := if cur > 0 then cur + amp else cur - amp
          out.set! pos' updated
        else out
      aacApplyPulsePairs out' swbFull books maxSfb pos' sfb' offs amps
  | _, _ => none

/-- Apply decoded `pulse_data` to quantized long-window coefficients `q` (ISO/IEC 14496-3 §4.6.3.3).
    Fails closed if any pulse lands past `1023`; pulses in `1..11` spectral bands add `+amp` when
    `q > 0` and `-amp` when `q ≤ 0` (`0` becomes `-amp`), while pulses in
    zero (`0`), PNS (`13`), IS (`14..15`), or above-`maxSfb` bands leave `q` at `0`. -/
def aacApplyPulses (q : Array Int) (pulse : AacPulseData) (swbFull : Array Nat)
    (books : Array UInt8) (maxSfb : Nat) : Option (Array Int) :=
  if !pulse.present then some q
  else
    let numSwb := swbFull.size - 1
    if q.size != 1024 || pulse.offsets.isEmpty || pulse.offsets.size > 4 ||
        pulse.offsets.size != pulse.amps.size || pulse.startSfb >= numSwb then none
    else
      let pos0 := swbFull.getD pulse.startSfb 1024
      aacApplyPulsePairs q swbFull books maxSfb pos0 pulse.startSfb pulse.offsets.toList pulse.amps.toList

/-- Write one `individual_channel_stream` (table 4.44), LC profile: no prediction, optional `pulse_data`, no gain control. -/
def aacWriteIcsGroups (cur : BitWriter) (q : Array Int) (swb : Array Nat) (books : Array UInt8)
    (maxSfb gi base : Nat) : List Nat → Option BitWriter
  | [] => some cur
  | gLen :: rest =>
    let gBooks := books.extract (gi * maxSfb) ((gi + 1) * maxSfb)
    match aacWriteGroupSpectrum cur q swb gBooks base gLen with
    | none => none
    | some cur' => aacWriteIcsGroups cur' q swb books maxSfb (gi + 1) (base + gLen) rest

def aacWriteIcs (w : BitWriter) (p : AacChannelPayload) (seq : AacWindowSequence) (useKbd : Bool)
    (groupLen swb : Array Nat) (commonWindow : Bool) (numSwb : Nat := 0) : Option BitWriter :=
  if !decide (p.globalGain ≤ 255) then none
  else
    let c0 := w.writeBitsMSB p.globalGain.toUInt64 8
    let isShort := seq == .eightShort
    let hdr? : Option BitWriter :=
      if !commonWindow then
        let c1 := ((c0.writeBit 0).writeBitsMSB seq.toUInt8.toUInt64 2).writeBit (if useKbd then 1 else 0)
        if isShort then
          aacWriteShortGrouping (c1.writeBitsMSB p.maxSfb.toUInt64 4) groupLen
        else
          some ((c1.writeBitsMSB p.maxSfb.toUInt64 6).writeBit 0)
      else some c0
    match hdr? with
    | none => none
    | some cur =>
      let books := aacExpandSections p.sections
      if books.size != groupLen.size * p.maxSfb then none
      else
        match aacWriteSections cur books isShort groupLen.size p.maxSfb with
        | none => none
        | some cSec =>
          match aacWriteScaleFactors cSec books p.sf p.globalGain with
          | none => none
          | some cSf =>
            let effNumSwb := if numSwb > 0 then numSwb else swb.size - 1
            match aacWritePulseData cSf p.pulse isShort effNumSwb with
            | none => none
            | some cPulse =>
              match aacWriteTns cPulse p.tns isShort with
              | none => none
              | some cTns =>
                aacWriteIcsGroups (cTns.writeBit 0) p.q swb books p.maxSfb 0 0 groupLen.toList

/-- Read one `individual_channel_stream` (table 4.44). -/
def aacReadShortGrouping (cur : BitReader) (curLen : Nat) (acc : List Nat) : Nat → Option (Array Nat × BitReader)
  | 0 => some ((curLen :: acc).reverse.toArray, cur)
  | rem + 1 =>
    match cur.readBit with
    | none => none
    | some (b, c') =>
      if b == 1 then aacReadShortGrouping c' (curLen + 1) acc rem
      else aacReadShortGrouping c' 1 (curLen :: acc) rem

def aacReadIcsInfo (cur : BitReader) : Option (AacWindowSequence × Bool × Array Nat × Nat × BitReader) :=
  match cur.readBit with
  | none => none
  | some (res, c1) =>
    if res != 0 then none
    else
      match c1.readBitsMSB 2 with
      | none => none
      | some (sq, c2) =>
        match c2.readBit with
        | none => none
        | some (kb, c3) =>
          let seq := match sq.toNat with | 1 => AacWindowSequence.longStart | 2 => .eightShort | 3 => .longStop | _ => .onlyLong
          if sq.toNat == 2 then
            match c3.readBitsMSB 4 with
            | none => none
            | some (ms, c4) =>
              match aacReadShortGrouping c4 1 [] 7 with
              | none => none
              | some (groups, c5) => some (seq, kb == 1, groups, ms.toNat, c5)
          else
            match c3.readBitsMSB 6 with
            | none => none
            | some (ms, c4) =>
              match c4.readBit with
              | none => none
              | some (pred, c5) =>
                if pred != 0 then none
                else some (seq, kb == 1, #[1], ms.toNat, c5)

def aacReadIcsGroups (cur : BitReader) (q : Array Int) (swb : Array Nat) (books : Array UInt8)
    (maxSfb gi base : Nat) : List Nat → Option (Array Int × BitReader)
  | [] => some (q, cur)
  | gLen :: rest =>
    let gBooks := books.extract (gi * maxSfb) ((gi + 1) * maxSfb)
    match aacReadGroupSpectrum cur swb gBooks base gLen q with
    | none => none
    | some (q', c') => aacReadIcsGroups c' q' swb books maxSfb (gi + 1) (base + gLen) rest

def aacReadIcs (r : BitReader) (sfi : UInt8) (commonWindow : Bool) (seq0 : AacWindowSequence)
    (kbd0 : Bool) (groups0 : Array Nat) (maxSfb0 : Nat) :
    Option (AacChannelPayload × AacWindowSequence × Bool × Array Nat × BitReader) :=
  match r.readBitsMSB 8 with
  | none => none
  | some (gg, c0) =>
    let info? :=
      if !commonWindow then aacReadIcsInfo c0
      else some (seq0, kbd0, groups0, maxSfb0, c0)
    match info? with
    | none => none
    | some (seq, kbd, groups, maxSfb, c5) =>
      let isShort := seq == .eightShort
      match (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) with
      | none => none
      | some swbFull =>
        if maxSfb > swbFull.size - 1 then none
        else
          let swb := swbFull.extract 0 (maxSfb + 1)
          match aacReadSections c5 isShort groups.size maxSfb with
          | none => none
          | some (sections, c6) =>
            match aacReadScaleFactors c6 sections gg.toNat with
            | none => none
            | some (sf, isScale, pnsGain, c7) =>
              match aacReadPulseData c7 isShort swbFull with
              | none => none
              | some (pulse, c8) =>
                match aacReadTns c8 isShort with
                | none => none
                | some (tns, c9) =>
                  match c9.readBit with
                  | none => none
                  | some (gain, c10) =>
                    if gain != 0 then none
                    else
                      let books := aacExpandSections sections
                      match aacReadIcsGroups c10 (Array.replicate 1024 0) swb books maxSfb 0 0 groups.toList with
                      | none => none
                      | some (q, c11) =>
                        match aacApplyPulses q pulse swbFull books maxSfb with
                        | none => none
                        | some qPulsed =>
                          let payload : AacChannelPayload := {
                            globalGain := gg.toNat, maxSfb := maxSfb, sections := sections,
                            sf := sf, isScale := isScale, pnsGain := pnsGain, pulse := pulse, q := qPulsed, tns := tns }
                          some (payload, seq, kbd, groups, c11)

/-- Canonical per-frame initial LCG seed for deterministic PNS (`book = 13`) synthesis.
    Resetting to `aacPnsFrameInitSeed` at the start of every `raw_data_block` guarantees that
    isolated single-frame decode (`aacDecodeAdtsFrame`) and in-stream decode (`aacDecodeAdtsStream`)
    produce identical inverse-quantized spectra and PCM on the deterministic PNS subset. -/
def aacPnsFrameInitSeed : UInt32 := 0x1F2E3D4C

/-- Advance the 32-bit LCG used for PNS (`book = 13`) by one step. -/
@[inline]
def aacPnsNextRng (rng : UInt32) : UInt32 :=
  rng * 1664525 + 1013904223

/-- Inverse-quantize one channel (including deterministic LCG PNS for `book = 13`), without TNS. -/
def aacDequantizeSpectralBins (spec : Array Float) (q : Array Int) (sfv off s0 : Nat) : Nat → Array Float
  | 0 => spec
  | k + 1 =>
    let idx := off + s0 + k
    let v := aacDequantizeCoeff (q.getD idx 0) sfv
    aacDequantizeSpectralBins (spec.set! idx v) q sfv off s0 k

def aacDequantizeSpectralWins (spec : Array Float) (q : Array Int) (sfv base s0 len : Nat) : Nat → Nat → Array Float
  | _, 0 => spec
  | win, rem + 1 =>
    let spec' := aacDequantizeSpectralBins spec q sfv ((base + win) * 128) s0 len
    aacDequantizeSpectralWins spec' q sfv base s0 len (win + 1) rem

def aacPnsGenNoiseBins (rng : UInt32) (ener : Float) (acc : List Float) : Nat → UInt32 × Float × Array Float
  | 0 => (rng, ener, acc.reverse.toArray)
  | k + 1 =>
    let rng' := aacPnsNextRng rng
    let s32 : Int32 := rng'.toInt32
    let vf := Float.ofInt s32.toInt
    aacPnsGenNoiseBins rng' (ener + vf * vf) (vf :: acc) k

def aacPnsScaleBins (spec noiseVals : Array Float) (scale : Float) (off s0 : Nat) : Nat → Array Float
  | 0 => spec
  | j + 1 =>
    let spec' := spec.set! (off + s0 + j) ((noiseVals.getD j 0.0) * scale)
    aacPnsScaleBins spec' noiseVals scale off s0 j

def aacPnsDequantWins (spec : Array Float) (rng : UInt32) (gain : Float) (base s0 len : Nat) :
    Nat → Nat → Array Float × UInt32
  | _, 0 => (spec, rng)
  | win, rem + 1 =>
    let off := (base + win) * 128
    let (rng', ener, noiseVals) := aacPnsGenNoiseBins rng 0.0 [] len
    let scale := if ener <= 1e-20 then 0.0 else gain / Float.sqrt ener
    let spec' := aacPnsScaleBins spec noiseVals scale off s0 len
    aacPnsDequantWins spec' rng' gain base s0 len (win + 1) rem

def aacDequantizeBands (spec : Array Float) (rng : UInt32) (p : AacChannelPayload)
    (books : Array UInt8) (swb : Array Nat) (base gLen : Nat) : Nat → Nat → Nat → Array Float × UInt32 × Nat
  | _, idx, 0 => (spec, rng, idx)
  | sfb, idx, rem + 1 =>
    let book := books.getD idx 0
    let sfv := p.sf.getD idx 0
    let s0 := swb.getD sfb 0
    let e0 := swb.getD (sfb + 1) s0
    let (spec', rng') :=
      if book != 0 && book <= 11 then
        (aacDequantizeSpectralWins spec p.q sfv base s0 (e0 - s0) 0 gLen, rng)
      else if book == 13 && e0 > s0 then
        aacPnsDequantWins spec rng (p.pnsGain.getD idx 0.0) base s0 (e0 - s0) 0 gLen
      else (spec, rng)
    aacDequantizeBands spec' rng' p books swb base gLen (sfb + 1) (idx + 1) rem

def aacDequantizeGroups (spec : Array Float) (rng : UInt32) (p : AacChannelPayload)
    (books : Array UInt8) (swb : Array Nat) (base idx : Nat) : List Nat → Array Float × UInt32
  | [] => (spec, rng)
  | gLen :: gs =>
    let (spec', rng', idx') := aacDequantizeBands spec rng p books swb base gLen 0 idx p.maxSfb
    aacDequantizeGroups spec' rng' p books swb (base + gLen) idx' gs

def aacDequantizeChannel (p : AacChannelPayload) (swb : Array Nat)
    (groupLen : Array Nat) (rng0 : UInt32 := aacPnsFrameInitSeed) : Array Float × UInt32 :=
  let books := aacExpandSections p.sections
  aacDequantizeGroups (Array.replicate 1024 0.0) rng0 p books swb 0 0 groupLen.toList

/-- Inverse-quantize one channel and undo its TNS analysis filter. -/
def aacReconstructChannel (p : AacChannelPayload) (sfi : UInt8) (seq : AacWindowSequence) (swb : Array Nat)
    (groupLen : Array Nat) : Array Float :=
  let (spec, _) := aacDequantizeChannel p swb groupLen
  aacApplyTns spec p.tns sfi (seq == .eightShort) p.maxSfb true

/-- Write one `raw_data_block`: a single SCE (mono) or CPE (stereo) followed by `END`. -/
def aacWriteMsBits (w : BitWriter) : List Bool → BitWriter
  | [] => w
  | b :: bs => aacWriteMsBits (w.writeBit (if b then 1 else 0)) bs

def aacWriteCpeChs (w : BitWriter) (seq : AacWindowSequence) (useKbd : Bool) (groupLen swb : Array Nat) :
    List AacChannelPayload → Option BitWriter
  | [] => some w
  | ch :: rest =>
    match aacWriteIcs w ch seq useKbd groupLen swb true with
    | none => none
    | some w' => aacWriteCpeChs w' seq useKbd groupLen swb rest

def aacWriteRawDataBlock (seq : AacWindowSequence) (useKbd : Bool) (groupLen swb : Array Nat)
    (msMode : UInt8) (msMask : Array Bool) (chs : Array AacChannelPayload) : Option ByteArray :=
  if chs.isEmpty || chs.size > 2 then none
  else
    let body? : Option BitWriter :=
      if chs.size == 1 then
        let w0 := (BitWriter.empty.writeBitsMSB 0 3).writeBitsMSB 0 4
        aacWriteIcs w0 (chs.getD 0 default) seq useKbd groupLen swb false
      else if msMode > 2 then none
      else
        let w0 := ((((BitWriter.empty.writeBitsMSB 1 3).writeBitsMSB 0 4).writeBit 1).writeBit 0)
        let w1 := (w0.writeBitsMSB seq.toUInt8.toUInt64 2).writeBit (if useKbd then 1 else 0)
        let isShort := seq == .eightShort
        let maxSfb := (chs.getD 0 default).maxSfb
        let hdr? :=
          if isShort then aacWriteShortGrouping (w1.writeBitsMSB maxSfb.toUInt64 4) groupLen
          else some ((w1.writeBitsMSB maxSfb.toUInt64 6).writeBit 0)
        match hdr? with
        | none => none
        | some w2 =>
          let w3 := w2.writeBitsMSB msMode.toUInt64 2
          let w4? :=
            if msMode == 1 then
              if msMask.size != groupLen.size * maxSfb then none
              else some (aacWriteMsBits w3 msMask.toList)
            else some w3
          match w4? with
          | none => none
          | some w4 => aacWriteCpeChs w4 seq useKbd groupLen swb chs.toList
    match body? with
    | none => none
    | some w => some (w.writeBitsMSB 7 3).alignToByte.toByteArray

/-- Skip a `data_stream_element` (`TYPE_DSE = 4`, ISO/IEC 14496-3 table 4.10), failing closed on truncated payload. -/
def aacSkipDse (r : BitReader) : Option BitReader :=
  match r.readBit with
  | none => none
  | some (byteAlign, r1) =>
    match r1.readBitsMSB 8 with
    | none => none
    | some (cnt0, r2) =>
      let step (cnt : Nat) (cur : BitReader) : Option BitReader :=
        let aligned? : Option BitReader :=
          if byteAlign == 1 then
            let rem := cur.bitOffset % 8
            if rem != 0 then
              let pad := 8 - rem
              if cur.bitsLeft < pad then none
              else some { cur with bitOffset := cur.bitOffset + pad }
            else some cur
          else some cur
        match aligned? with
        | none => none
        | some cur' =>
          let skipBits := 8 * cnt
          if cur'.bitsLeft < skipBits then none
          else some { cur' with bitOffset := cur'.bitOffset + skipBits }
      if cnt0.toNat == 255 then
        match r2.readBitsMSB 8 with
        | none => none
        | some (esc, r3) => step (cnt0.toNat + esc.toNat) r3
      else step cnt0.toNat r2

/-- Skip a `fill_element` (`TYPE_FIL = 6`, ISO/IEC 14496-3 table 4.11), failing closed on truncated payload. -/
def aacSkipFil (r : BitReader) (elemId : Nat) : Option BitReader :=
  let cnt? : Option (Nat × BitReader) :=
    if elemId == 15 then
      match r.readBitsMSB 8 with
      | none => none
      | some (esc, r1) =>
        if esc.toNat == 0 then none
        else some (elemId + esc.toNat - 1, r1)
    else some (elemId, r)
  match cnt? with
  | none => none
  | some (cnt, cur) =>
    let skipBits := 8 * cnt
    if cur.bitsLeft < skipBits then none
    else some { cur with bitOffset := cur.bitOffset + skipBits }

def aacReadMsBits (cur : BitReader) (acc : List Bool) : Nat → Option (Array Bool × BitReader)
  | 0 => some (acc.reverse.toArray, cur)
  | rem + 1 =>
    match cur.readBit with
    | none => none
    | some (b, c') => aacReadMsBits c' ((b == 1) :: acc) rem

def aacReadCpeElem (r : BitReader) (sfi : UInt8) (rng : UInt32) : Option (AacLcFrame × UInt32 × BitReader) :=
  match r.readBit with
  | none => none
  | some (cw, r3) =>
    if cw == 1 then
      match aacReadIcsInfo r3 with
      | none => none
      | some (seq, useKbd, groups, maxSfb, r8) =>
        match r8.readBitsMSB 2 with
        | none => none
        | some (msMode, r9) =>
          if msMode.toNat == 3 then none
          else
            let mask? :=
              if msMode.toNat == 1 then aacReadMsBits r9 [] (groups.size * maxSfb)
              else some (#[], r9)
            match mask? with
            | none => none
            | some (mask, r10) =>
              match (if seq == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) with
              | none => none
              | some swbFull =>
                if maxSfb > swbFull.size - 1 then none
                else
                  let swb := swbFull.extract 0 (maxSfb + 1)
                  match aacReadIcs r10 sfi true seq useKbd groups maxSfb with
                  | none => none
                  | some (p0, _, _, _, r11) =>
                    match aacReadIcs r11 sfi true seq useKbd groups maxSfb with
                    | none => none
                    | some (p1, _, _, _, r12) =>
                      let (deq0, rng1) := aacDequantizeChannel p0 swb groups rng
                      let (deq1, rng2) := aacDequantizeChannel p1 swb groups rng1
                      let bt0 := aacExpandSections p0.sections
                      let bt1 := aacExpandSections p1.sections
                      let (ms0, ms1) := aacDecodeMidSide deq0 deq1 swb groups maxSfb msMode.toUInt8 mask bt0 bt1
                      let is1 := aacDecodeIntensityStereo ms0 ms1 swb groups maxSfb msMode.toUInt8 mask bt1 p1.isScale
                      let ch0 := aacApplyTns ms0 p0.tns sfi (seq == .eightShort) p0.maxSfb true
                      let ch1 := aacApplyTns is1 p1.tns sfi (seq == .eightShort) p1.maxSfb true
                      let frm : AacLcFrame := {
                        sfi := sfi, seq := seq, useKbd := useKbd, seqCh1 := seq, kbdCh1 := useKbd,
                        groupLen := groups, maxSfb := maxSfb, msMode := msMode.toUInt8, msMask := mask, ch := #[ch0, ch1] }
                      some (frm, rng2, r12)
    else
      match aacReadIcs r3 sfi false .onlyLong false #[1] 0 with
      | none => none
      | some (p0, seq0, kbd0, groups0, r4) =>
        match aacReadIcs r4 sfi false .onlyLong false #[1] 0 with
        | none => none
        | some (p1, seq1, kbd1, groups1, r5) =>
          match (if seq0 == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi),
                (if seq1 == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) with
          | some swbFull0, some swbFull1 =>
            let swb0 := swbFull0.extract 0 (p0.maxSfb + 1)
            let swb1 := swbFull1.extract 0 (p1.maxSfb + 1)
            let (deq0, rng1) := aacDequantizeChannel p0 swb0 groups0 rng
            let (deq1, rng2) := aacDequantizeChannel p1 swb1 groups1 rng1
            let bt1 := aacExpandSections p1.sections
            let is1 :=
              if seq0 == seq1 && groups0 == groups1 then
                aacDecodeIntensityStereo deq0 deq1 swb1 groups1 p1.maxSfb 0 #[] bt1 p1.isScale
              else deq1
            let ch0 := aacApplyTns deq0 p0.tns sfi (seq0 == .eightShort) p0.maxSfb true
            let ch1 := aacApplyTns is1 p1.tns sfi (seq1 == .eightShort) p1.maxSfb true
            let frm : AacLcFrame := {
              sfi := sfi, seq := seq0, useKbd := kbd0, seqCh1 := seq1, kbdCh1 := kbd1,
              groupLen := groups0, maxSfb := Nat.max p0.maxSfb p1.maxSfb, ch := #[ch0, ch1] }
            some (frm, rng2, r5)
          | _, _ => none

def aacReadRawElems : BitReader → UInt8 → Option AacLcFrame → UInt32 →
    Nat → Option (AacLcFrame × UInt32)
  | _, _, _, _, 0 => none
  | r, sfi, decoded?, rng, guard + 1 =>
    match r.readBitsMSB 3 with
    | none => none
    | some (tag, r1) =>
      if tag.toNat == 7 then decoded?.map (fun f => (f, rng))
      else
        match r1.readBitsMSB 4 with
        | none => none
        | some (id, r2) =>
          if tag.toNat == 4 then
            match aacSkipDse r2 with
            | none => none
            | some r' => aacReadRawElems r' sfi decoded? rng guard
          else if tag.toNat == 6 then
            match aacSkipFil r2 id.toNat with
            | none => none
            | some r' => aacReadRawElems r' sfi decoded? rng guard
          else if tag.toNat == 0 then
            if decoded?.isSome || id.toNat != 0 then none
            else
              match aacReadIcs r2 sfi false .onlyLong false #[1] 0 with
              | none => none
              | some (p, seq, kbd, groups, r3) =>
                match (if seq == .eightShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) with
                | none => none
                | some swbFull =>
                  let swb := swbFull.extract 0 (p.maxSfb + 1)
                  let (deq, rng1) := aacDequantizeChannel p swb groups rng
                  let spec := aacApplyTns deq p.tns sfi (seq == .eightShort) p.maxSfb true
                  let frm : AacLcFrame := {
                    sfi := sfi, seq := seq, useKbd := kbd, seqCh1 := seq, kbdCh1 := kbd,
                    groupLen := groups, maxSfb := p.maxSfb, ch := #[spec] }
                  aacReadRawElems r3 sfi (some frm) rng1 guard
          else if tag.toNat == 1 then
            if decoded?.isSome || id.toNat != 0 then none
            else
              match aacReadCpeElem r2 sfi rng with
              | none => none
              | some (frm, rng2, r') => aacReadRawElems r' sfi (some frm) rng2 guard
          else none

/-- Read one `raw_data_block`, accepting a single SCE or CPE plus optional DSE/FIL elements and rejecting invalid syntax.
    Starts PNS synthesis from `rng0` (defaulting to the per-frame deterministic seed `aacPnsFrameInitSeed`). -/
def aacReadRawDataBlock (bytes : ByteArray) (sfi : UInt8) (rng0 : UInt32 := aacPnsFrameInitSeed) :
    Option (AacLcFrame × UInt32) :=
  aacReadRawElems (BitReader.ofSlice (ByteSlice.ofByteArray bytes)) sfi none rng0 64

/-- Exact bit cost of encoding `section_data` + `scale_factor_data` + `tns_data` + fixed ICS overhead for one channel. -/
def aacEstimateChannelSideBits (books : Array UInt8) (sf : Array Nat) (tns : AacTnsInfo)
    (isShort : Bool) (numGroups maxSfb : Nat) : Nat := Id.run do
  let secBits := if isShort then 3 else 5
  let secEsc := (1 <<< secBits) - 1
  let mut bits : Nat := 18
  for g in [:numGroups] do
    let gSecs := aacBuildSections (books.extract (g * maxSfb) ((g + 1) * maxSfb))
    for s in gSecs do
      bits := bits + 4 + ((s.length / secEsc) + 1) * secBits
  let mut prev : Nat := 0
  let mut havePrev := false
  for i in [:books.size] do
    if books.getD i 0 != 0 then
      let cur := sf.getD i 100
      if !havePrev then
        prev := cur
        havePrev := true
      else
        let d : Int := (cur : Int) - (prev : Int)
        let idx := (if d < -60 then -60 else if d > 60 then 60 else d) + 60
        bits := bits + (aacSfBits.getD idx.toNat 19).toNat
        prev := cur
  if tns.present then
    let nWin := if isShort then 8 else 1
    let nFiltBits := if isShort then 1 else 2
    let lenBits := if isShort then 4 else 6
    let ordBits := if isShort then 3 else 5
    for w in [:nWin] do
      let fs := tns.filters.getD w #[]
      bits := bits + nFiltBits
      if fs.size > 0 then
        bits := bits + 1
        for f in fs do
          bits := bits + lenBits + ordBits
          if f.order > 0 then
            let cb := (if tns.coefRes.getD w false then 4 else 3) - (if f.coefCompress then 1 else 0)
            bits := bits + 2 + f.order * cb
  return bits

/-- Quantize one `(group, sfb)` band at `sf0` (bumping only if `|q| ≥ 8191` clips), returning `(sfbSf, book, specBits, dist, slice)`.
    `weight` scales the MSE distortion (`2.0` on active M/S bands so `L = M + S`, `R = M - S` matches L/R MSE). -/
def aacQuantizeBandAtSf (filtered : Array Float) (winBase gLen s0 e0 sfInit : Nat)
    (weight : Float := 1.0) : Nat × UInt8 × Nat × Float × Array Int := Id.run do
  let mut sfbSf := sfInit
  let mut slice : Array Int := Array.emptyWithCapacity (gLen * (e0 - s0))
  for _ in [:8] do
    slice := Array.emptyWithCapacity (gLen * (e0 - s0))
    let mut clipped := false
    for w in [:gLen] do
      let off := (winBase + w) * 128
      for k in [s0:e0] do
        let c := aacQuantizeCoeff (filtered.getD (off + k) 0.0) sfbSf
        if c.natAbs >= 8191 then clipped := true
        slice := slice.push c
    if !clipped || sfbSf >= 248 then break
    sfbSf := sfbSf + 1
  let (book, specBits) := aacSelectBestBook slice
  let mut dist : Float := 0.0
  for w in [:gLen] do
    let off := (winBase + w) * 128
    for j in [:e0 - s0] do
      let orig := filtered.getD (off + s0 + j) 0.0
      let qv := if book == 0 then 0 else slice.getD (w * (e0 - s0) + j) 0
      let recV := aacDequantizeCoeff qv sfbSf
      let diff := orig - recV
      dist := dist + diff * diff
  return (sfbSf, book, specBits, dist * weight, slice)

/-- Minimum non-clipping scalefactor (`|q| ≤ 8191`) across every bin in `(winBase..winBase+gLen, s0..e0)`. -/
def aacBandMinNonClipSf (filtered : Array Float) (winBase gLen s0 e0 : Nat) : Nat := Id.run do
  let mut bMin : Nat := 16
  for w in [:gLen] do
    let off := (winBase + w) * 128
    for k in [s0:e0] do
      let a := Float.abs (filtered.getD (off + k) 0.0)
      if a > 1.0 then
        let need := Float.log2 a * 4.0 - 69.0
        if need > 0.0 then
          let needNat := (Float.toUInt64 need).toNat + 101
          if needNat > bMin then bMin := Nat.min 232 needNat
  return bMin

/-- Coarse-to-fine best-SNR scalefactor search for one channel within `share` bits:
    sweeps base scalefactors from `16` up to `244` to minimize spectral MSE within budget. -/
def aacSearchCoarseChannel (filtered : Array Float) (tns : AacTnsInfo)
    (swb groups bandMin : Array Nat) (maxSfb share : Nat) (isShort : Bool)
    (bandWeights : Array Float := #[]) :
    Array Int × Array Nat × Array UInt8 × Array Float × Bool × Nat := Id.run do
  let numBands := groups.size * maxSfb
  let mut minBase : Nat := 16
  for bm in bandMin do
    if bm > minBase + 48 then minBase := bm - 48
  let mut bestQ : Array Int := Array.replicate 1024 0
  let mut bestSf : Array Nat := Array.replicate numBands 140
  let mut bestBooks : Array UInt8 := Array.replicate numBands 0
  let mut bestDist : Array Float := Array.replicate numBands 0.0
  let mut bestTotalDist : Float := 1e38
  let mut bestBits : Nat := 1000000000
  let mut foundFeasible := false
  for step in [:115] do
    let sf0 : Nat := Nat.min 244 (minBase + step * 2)
    let mut q : Array Int := Array.replicate 1024 0
    let mut sfArr : Array Nat := Array.replicate numBands sf0
    let mut books : Array UInt8 := Array.emptyWithCapacity numBands
    let mut dists : Array Float := Array.emptyWithCapacity numBands
    let mut specBits : Nat := 0
    let mut totDist : Float := 0.0
    let mut wb : Nat := 0
    for gi in [:groups.size] do
      let gLen := groups.getD gi 1
      for sfb in [:maxSfb] do
        let bIdx := gi * maxSfb + sfb
        let s0 := swb.getD sfb 0
        let e0 := swb.getD (sfb + 1) s0
        let wgt := bandWeights.getD bIdx 1.0
        let (sfbSf, book, bCost, dist, slice) :=
          aacQuantizeBandAtSf filtered wb gLen s0 e0 (Nat.max (bandMin.getD bIdx 16) sf0) wgt
        sfArr := sfArr.set! bIdx sfbSf; books := books.push book; dists := dists.push dist
        specBits := specBits + bCost; totDist := totDist + dist
        for w in [:gLen] do
          let off := (wb + w) * 128
          for j in [:e0 - s0] do
            q := q.set! (off + s0 + j) (if book == 0 then 0 else slice.getD (w * (e0 - s0) + j) 0)
      wb := wb + gLen
    let totalBits := specBits + aacEstimateChannelSideBits books sfArr tns isShort groups.size maxSfb
    let feasible := totalBits <= share
    if (feasible && (!foundFeasible || totDist < bestTotalDist)) || (!foundFeasible && totalBits < bestBits) then
      bestQ := q; bestSf := sfArr; bestBooks := books; bestDist := dists
      bestTotalDist := totDist; bestBits := totalBits
      if feasible then foundFeasible := true
  return (bestQ, bestSf, bestBooks, bestDist, foundFeasible, bestBits)

/-- Check whether every consecutive pair of active (`book ≠ 0`) bands satisfies `|Δsf| ≤ 60`. -/
def aacValidActiveSfDeltas (books : Array UInt8) (sf : Array Nat) : Bool := Id.run do
  let mut prev : Nat := 0
  let mut havePrev := false
  for i in [:books.size] do
    if books.getD i 0 != 0 then
      let cur := sf.getD i 140
      if havePrev && (cur > prev + 60 || prev > cur + 60) then
        return false
      prev := cur
      havePrev := true
  return true

/-- Greedily lower individual band scalefactors (`sf - 1`) to maximize SNR within `share` bits and `|Δsf| ≤ 60`. -/
def aacRefineBestSnrChannel (filtered : Array Float) (tns : AacTnsInfo)
    (swb groups bandMin : Array Nat) (maxSfb share : Nat) (isShort : Bool)
    (bandWeights : Array Float := #[]) : AacChannelPayload := Id.run do
  let (q0, sf0, books0, dist0, feasible0, bits0) :=
    aacSearchCoarseChannel filtered tns swb groups bandMin maxSfb share isShort bandWeights
  let mut bestQ := q0
  let mut bestSf := sf0
  let mut bestBooks := books0
  let mut bestDist := dist0
  if feasible0 then
    let mut curSpecBits : Nat := bits0 - aacEstimateChannelSideBits bestBooks bestSf tns isShort groups.size maxSfb
    for _ in [:256] do
      let mut pickIdx : Option Nat := none
      let mut pickGain : Float := 0.0
      let mut pickCand : Nat × UInt8 × Nat × Float × Array Int := (0, 0, 0, 0.0, #[])
      let mut pickWb : Nat := 0
      let mut pickOldB : Nat := 0
      let mut wb : Nat := 0
      for gi in [:groups.size] do
        let gLen := groups.getD gi 1
        for sfb in [:maxSfb] do
          let bIdx := gi * maxSfb + sfb
          let curSf := bestSf.getD bIdx 140
          let curD := bestDist.getD bIdx 0.0
          if curSf > Nat.max 8 (bandMin.getD bIdx 16) && curD > pickGain then
            let s0 := swb.getD sfb 0
            let e0 := swb.getD (sfb + 1) s0
            let wgt := bandWeights.getD bIdx 1.0
            let (cSf, cBook, cBits, cDist, cSlice) := aacQuantizeBandAtSf filtered wb gLen s0 e0 (curSf - 1) wgt
            if cSf < curSf && curD - cDist > pickGain then
              let trialBooks := bestBooks.set! bIdx cBook
              let trialSf := bestSf.set! bIdx cSf
              if aacValidActiveSfDeltas trialBooks trialSf then
                let mut oldSl : Array Int := #[]
                for w in [:gLen] do
                  for k in [s0:e0] do oldSl := oldSl.push (bestQ.getD ((wb + w) * 128 + k) 0)
                let oldB := (aacSelectBestBook oldSl).2
                let newTot := (curSpecBits - oldB + cBits) + aacEstimateChannelSideBits trialBooks trialSf tns isShort groups.size maxSfb
                if newTot <= share then
                  pickIdx := some bIdx; pickGain := curD - cDist
                  pickCand := (cSf, cBook, cBits, cDist, cSlice); pickWb := wb; pickOldB := oldB
        wb := wb + gLen
      let some bIdx := pickIdx | break
      let (pSf, pBook, pBits, pDist, pSlice) := pickCand
      let gi := bIdx / maxSfb
      let sfb := bIdx % maxSfb
      let gLen := groups.getD gi 1
      let s0 := swb.getD sfb 0
      let e0 := swb.getD (sfb + 1) s0
      curSpecBits := curSpecBits - pickOldB + pBits
      bestSf := bestSf.set! bIdx pSf
      bestBooks := bestBooks.set! bIdx pBook
      bestDist := bestDist.set! bIdx pDist
      for w in [:gLen] do
        let off := (pickWb + w) * 128
        for j in [:e0 - s0] do
          bestQ := bestQ.set! (off + s0 + j) (if pBook == 0 then 0 else pSlice.getD (w * (e0 - s0) + j) 0)
  return { globalGain := 140, maxSfb := maxSfb, sections := #[], sf := bestSf, q := bestQ, tns := tns }

/-- Encode one frame of PCM (`2048` samples per channel) and mux it as a single ADTS frame. -/
def aacEncodeAdtsFrame (pcm : Array (Array Float)) (sfi : UInt8) (bitrate : Nat)
    (useKbd : Bool := false) (useKbdPrev : Bool := false)
    (seq : AacWindowSequence := .onlyLong) (extraBits : Nat := 0) : Option ByteArray := do
  let nch := pcm.size
  if nch != 1 && nch != 2 then none
  let some sr := aacSampleRateFromIndex sfi | none
  let isShort := seq == .eightShort
  let some swbFull := (if isShort then aacSwbOffsetsShort sfi else aacSwbOffsetsLong sfi) | none
  let groups : Array Nat := if isShort then #[2, 2, 2, 2] else #[1]
  let baseBudget := Nat.max 384 ((bitrate * 1024) / sr.toNat)
  let budget := Nat.min (6144 * nch - 72) (baseBudget + extraBits)
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
    let (mode, mask, a0, a1) := aacEncodeMidSide (tnsSpecs.getD 0 #[]) (tnsSpecs.getD 1 #[]) swb groups maxSfb
    msMode := mode
    msMask := mask
    shaped := #[a0, a1]
  let numBands := groups.size * maxSfb
  let mut bandWeights : Array Float := Array.emptyWithCapacity numBands
  for bIdx in [:numBands] do
    let isMs := msMode == 2 || (msMode == 1 && msMask.getD bIdx false)
    bandWeights := bandWeights.push (if isMs then 2.0 else 1.0)
  let mut chEnergies : Array Float := Array.emptyWithCapacity nch
  let mut totEnergy : Float := 0.0
  for ch in [:nch] do
    let sp := shaped.getD ch #[]
    let mut e : Float := 0.0
    let mut wbE : Nat := 0
    for gi in [:groups.size] do
      let gLen := groups.getD gi 1
      for sfb in [:maxSfb] do
        let bIdx := gi * maxSfb + sfb
        let wgt := bandWeights.getD bIdx 1.0
        let s0 := swb.getD sfb 0
        let e0 := swb.getD (sfb + 1) s0
        for w in [:gLen] do
          let off := (wbE + w) * 128
          for k in [s0:e0] do
            let v := sp.getD (off + k) 0.0
            e := e + wgt * v * v
      wbE := wbE + gLen
    chEnergies := chEnergies.push e
    totEnergy := totEnergy + e
  let mut frameHdrBits : Nat := if nch == 1 then 7 else if isShort then 27 else 23
  if nch == 2 && msMode == 1 then frameHdrBits := frameHdrBits + numBands
  let usableBudget := if budget > frameHdrBits + 8 then budget - frameHdrBits - 8 else budget / 2
  let mut remBudget : Nat := usableBudget
  for ch in [:nch] do
    let filtered := shaped.getD ch #[]
    let tns := tnsList.getD ch {}
    let share : Nat :=
      if ch + 1 == nch then Nat.max 64 remBudget
      else if totEnergy <= 1e-9 then Nat.max 64 (usableBudget / nch)
      else
        let e0 := chEnergies.getD 0 0.0
        let e1 := chEnergies.getD 1 0.0
        let ratio := Float.log2 ((1.0 + e0) / (1.0 + e1))
        let rawFrac := 0.5 + 0.04 * ratio
        let clampedFrac := if rawFrac < 0.15 then 0.15 else if rawFrac > 0.85 then 0.85 else rawFrac
        Nat.max 64 (Float.toUInt64 (Float.ofNat usableBudget * clampedFrac)).toNat
    let mut bandMin : Array Nat := Array.emptyWithCapacity numBands
    let mut wb0 : Nat := 0
    for gi in [:groups.size] do
      let gLen := groups.getD gi 1
      for sfb in [:maxSfb] do
        bandMin := bandMin.push (aacBandMinNonClipSf filtered wb0 gLen (swb.getD sfb 0) (swb.getD (sfb + 1) 0))
      wb0 := wb0 + gLen
    let searched := aacRefineBestSnrChannel filtered tns swb groups bandMin maxSfb share isShort bandWeights
    let mut bestQ := searched.q
    let mut bestSf := searched.sf
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
    let mut winBase3 : Nat := 0
    for gi in [:groups.size] do
      let gLen := groups.getD gi 1
      for sfb in [:maxSfb] do
        let bIdx := gi * maxSfb + sfb
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
            if clamped != cur then
              let s0 := swb.getD sfb 0
              let e0 := swb.getD (sfb + 1) s0
              let (sfbSf', book', _, _, slice') := aacQuantizeBandAtSf filtered winBase3 gLen s0 e0 clamped
              bestSf := bestSf.set! bIdx sfbSf'
              books := books.set! bIdx book'
              for w in [:gLen] do
                let off := (winBase3 + w) * 128
                for j in [:e0 - s0] do
                  bestQ := bestQ.set! (off + s0 + j) (if book' == 0 then 0 else slice'.getD (w * (e0 - s0) + j) 0)
              prevActive := sfbSf'
            else
              prevActive := cur
      winBase3 := winBase3 + gLen
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
    let chPay : AacChannelPayload := {
      globalGain := firstGain, maxSfb := maxSfb, sections := grpSecs,
      sf := bestSf, q := bestQ, tns := tns }
    if ch + 1 < nch then
      if let some wCh := aacWriteIcs BitWriter.empty chPay seq useKbd groups swb (nch == 2) then
        let used := wCh.totalBitsWritten
        remBudget := if remBudget > used then remBudget - used else 0
      else
        remBudget := if remBudget > share then remBudget - share else 0
    chans := chans.push chPay
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
        if (cur > prev * 12.0 && cur > 1e7) || (prev > cur * 12.0 && prev > 1e7) then
          hit := true
    if off + 448 <= 1024 && 1024 < off + 1472 then
      for ch in [:nch] do
        let s0 := (padded.getD ch #[]).getD 1024 0.0
        let s1 := (padded.getD ch #[]).getD 1025 0.0
        if s0 * s0 + s1 * s1 > 1e5 then hit := true
    if off + 448 < 1024 + nSamples && 1024 + nSamples <= off + 1472 then
      for ch in [:nch] do
        let sLast := (padded.getD ch #[]).getD (1024 + nSamples - 1) 0.0
        if sLast * sLast > 1e5 then hit := true
    lookaheadTrans := lookaheadTrans.set! f hit
  let mut seqs : Array AacWindowSequence := Array.replicate numFrames .onlyLong
  let mut prevSeq : AacWindowSequence :=
    if lookaheadTrans.getD 0 false then .longStart else .onlyLong
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
  let baseFrameBits := Nat.max 384 ((bitrate * 1024) / sampleRate.toNat)
  let maxReservoir := 6144 * nch - baseFrameBits
  let mut reservoir : Nat := Nat.min maxReservoir ((baseFrameBits * 3) / 2)
  let mut out := ByteArray.emptyWithCapacity (numFrames * 384)
  for f in [:numFrames] do
    let off := f * 1024
    let mut winChans : Array (Array Float) := Array.emptyWithCapacity nch
    for ch in [:nch] do
      winChans := winChans.push ((padded.getD ch #[]).extract off (off + 2048))
    let curSeq := seqs.getD f .onlyLong
    let extra : Nat :=
      if curSeq == .eightShort then reservoir
      else if curSeq == .longStart || curSeq == .longStop then reservoir / 2
      else reservoir / 8
    let some frameBytes := aacEncodeAdtsFrame winChans sfi bitrate useKbd useKbd curSeq extra | return none
    let usedPayloadBits := if frameBytes.size > 7 then (frameBytes.size - 7) * 8 else 0
    let poolAfter := baseFrameBits + reservoir
    reservoir := Nat.min maxReservoir (if poolAfter > usedPayloadBits then poolAfter - usedPayloadBits else 0)
    out := out ++ frameBytes
  return some out

/-- Synthesize one decoded `AacLcFrame` (`1` or `2` channels) into signed 16-bit PCM plus updated overlap-add state. -/
def aacSynthesizeDecodedChans (frm : AacLcFrame) (firstFrame : Bool)
    (saved : Array (Array Float)) (prevKbd : Array Bool) (prevSeq : Array AacWindowSequence)
    (framePcm : List (Array Int32)) :
    Nat → Nat → Option (Array (Array Int32) × Array (Array Float) × Array Bool × Array AacWindowSequence)
  | _, 0 => some (framePcm.reverse.toArray, saved, prevKbd, prevSeq)
  | ch, rem + 1 =>
    let curSeq := if ch == 0 then frm.seq else frm.seqCh1
    let curKbd := if ch == 0 then frm.useKbd else frm.kbdCh1
    if !firstFrame && !isValidAacWindowTransition (prevSeq.getD ch .onlyLong) curSeq then none
    else
      let kbdPrev := if firstFrame then curKbd else prevKbd.getD ch curKbd
      let (pcmF, nextSaved) := aacSynthesizeFrame (frm.ch.getD ch #[]) (saved.getD ch #[]) curSeq curKbd kbdPrev
      if pcmF.size != 1024 then none
      else
        let saved' := saved.set! ch nextSaved
        let prevKbd' := prevKbd.set! ch curKbd
        let prevSeq' := prevSeq.set! ch curSeq
        let dst := Array.ofFn (fun (idx : Fin 1024) => aacClampFloatToI16 (pcmF.getD idx.val 0.0))
        aacSynthesizeDecodedChans frm firstFrame saved' prevKbd' prevSeq' (dst :: framePcm) (ch + 1) rem

def aacSynthesizeDecodedFrame (frm : AacLcFrame) (nch : Nat) (firstFrame : Bool)
    (saved : Array (Array Float)) (prevKbd : Array Bool) (prevSeq : Array AacWindowSequence) :
    Option (Array (Array Int32) × Array (Array Float) × Array Bool × Array AacWindowSequence) :=
  if frm.ch.size != nch then none
  else aacSynthesizeDecodedChans frm firstFrame saved prevKbd prevSeq [] 0 nch

def aacAppendFramePcm (nch : Nat) (outChans framePcm : Array (Array Int32)) : Array (Array Int32) :=
  Array.ofFn (fun (ch : Fin nch) => (outChans.getD ch.val #[]) ++ (framePcm.getD ch.val #[]))

def aacDecodeAdtsPayloads (sfi : UInt8) (nch : Nat) (firstFrame : Bool)
    (saved : Array (Array Float)) (prevKbd : Array Bool) (prevSeq : Array AacWindowSequence)
    (outChans : Array (Array Int32)) : List ByteSlice → Option (Array (Array Int32))
  | [] => some outChans
  | pSlice :: rest =>
    let raw := pSlice.ba.extract pSlice.off (pSlice.off + pSlice.len)
    match aacReadRawDataBlock raw sfi aacPnsFrameInitSeed with
    | none => none
    | some (frm, _) =>
      match aacSynthesizeDecodedFrame frm nch firstFrame saved prevKbd prevSeq with
      | none => none
      | some (framePcm, saved', prevKbd', prevSeq') =>
        let out' := aacAppendFramePcm nch outChans framePcm
        aacDecodeAdtsPayloads sfi nch false saved' prevKbd' prevSeq' out' rest

/-- Decode a standalone ADTS AAC-LC stream into `(channelsData, sampleRate, 16)` signed 16-bit PCM.
    Every frame resets PNS synthesis to `aacPnsFrameInitSeed`, matching `aacDecodeAdtsFrame` frame-for-frame. -/
def aacDecodeAdtsStream (s : ByteSlice) (verifyCrc : Bool := false) :
    Option (Array (Array Int32) × UInt32 × Nat) :=
  match demuxAdtsStream s verifyCrc with
  | none => none
  | some (hdr, payloads) =>
    match aacSampleRateFromIndex hdr.samplingFrequencyIdx with
    | none => none
    | some sr =>
      let nch := hdr.channelConfiguration.toNat
      if nch != 1 && nch != 2 then none
      else
        let saved := Array.replicate nch (Array.replicate 1024 0.0)
        let prevKbd := Array.replicate nch false
        let prevSeq := Array.replicate nch .onlyLong
        let outChans := Array.replicate nch #[]
        match aacDecodeAdtsPayloads hdr.samplingFrequencyIdx nch true saved prevKbd prevSeq outChans payloads.toList with
        | none => none
        | some pcm => some (pcm, sr, 16)

end LeanAV.AacLc







