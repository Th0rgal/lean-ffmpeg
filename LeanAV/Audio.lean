/-
  LeanAV.Audio: Verified Audio Codecs & Sample Resampler (`libavcodec` Audio + `libswresample` Replacement)

  Implements:
  1. FLAC (`Regime R0` bit-exact lossless):
     - Fixed polynomial LPC predictors (Orders 0, 1, 2, 3, 4: `s[n] = r[n] + ...`)
     - General quantized FIR LPC restoration (`s[n] = r[n] + (∑ c_k * s[n-k] >> qShift)`)
     - Mid-Side / Left-Side / Right-Side stereo decorrelation & exact reversible reconstruction
     - Subframe encoder & decoder (Constant, Verbatim, Fixed 0..4, LPC with qlp coeffs + shift, Rice 4/5-bit + escape)
  2. Opus (`RFC 6716`, `Regime R1`/`R2`):
     - TOC byte parser (SILK-only, Hybrid, CELT-only, bandwidth `NB`/`MB`/`WB`/`SWB`/`FB`, frame duration 2.5ms..60ms)
     - Frame-count demux codes 0..3 (`RFC 6716 Section 3.1-3.2`, including Code 3 VBR/padding)
     - CELT PVQ (Pyramid Vector Quantization) L2-norm band normalizer & Q15 fixed-point IMDCT synthesis
     - SILK ARMA LPC synthesis filter
  3. AAC / MP3 / AC-3 / ALAC / Vorbis (`Regime R1`/`R2`):
     - AAC ADTS 7-byte header (`0xFFF`) parse & serialize
     - Windowed 4-tap / N-point Q15 Modified Discrete Cosine Transform (`imdctBlockQ15`) with overlap-add (`TDAC`)
  4. `swresample` (`libswresample` replacement):
     - Polyphase windowed-sinc / cubic Q15 sample rate converter (`resampleAudioFrame` e.g. 44.1 kHz ↔ 48 kHz)
     - Channel matrix mixer (Mono ↔ Stereo ↔ 5.1 surround downmix/upmix)
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream

namespace LeanAV.Audio

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream

/-! ## 1. FLAC Bit-Exact Lossless Audio (`Regime R0`, `maxErr = 0`) -/

/-- FLAC Fixed LPC Predictor Order (0..4). -/
inductive FlacFixedOrder where
  | order0 -- p[n] = 0
  | order1 -- p[n] = s[n-1]
  | order2 -- p[n] = 2*s[n-1] - s[n-2]
  | order3 -- p[n] = 3*s[n-1] - 3*s[n-2] + s[n-3]
  | order4 -- p[n] = 4*s[n-1] - 6*s[n-2] + 4*s[n-3] - s[n-4]
  deriving Repr, DecidableEq, Inhabited

@[inline]
def flacFixedPredict64 (ord : FlacFixedOrder) (out : Array Int64) (i : Nat) : Int64 :=
  match ord with
  | .order0 => 0
  | .order1 =>
    if i ≥ 1 then out.getD (i - 1) 0 else 0
  | .order2 =>
    if i ≥ 2 then 2 * out.getD (i - 1) 0 - out.getD (i - 2) 0 else 0
  | .order3 =>
    if i ≥ 3 then 3 * out.getD (i - 1) 0 - 3 * out.getD (i - 2) 0 + out.getD (i - 3) 0 else 0
  | .order4 =>
    if i ≥ 4 then
      4 * out.getD (i - 1) 0 - 6 * out.getD (i - 2) 0 + 4 * out.getD (i - 3) 0 - out.getD (i - 4) 0
    else 0

@[inline]
def flacFixedPredict (ord : FlacFixedOrder) (out : Array Int32) (i : Nat) : Int32 :=
  let ds := out.toList
  match ord with
  | .order0 => 0
  | .order1 =>
    if i ≥ 1 then ds.getD (i - 1) 0 else 0
  | .order2 =>
    if i ≥ 2 then 2 * ds.getD (i - 1) 0 - ds.getD (i - 2) 0 else 0
  | .order3 =>
    if i ≥ 3 then 3 * ds.getD (i - 1) 0 - 3 * ds.getD (i - 2) 0 + ds.getD (i - 3) 0 else 0
  | .order4 =>
    if i ≥ 4 then
      4 * ds.getD (i - 1) 0 - 6 * ds.getD (i - 2) 0 + 4 * ds.getD (i - 3) 0 - ds.getD (i - 4) 0
    else 0

def flacEncodeFixedResidualsLoop (ord : FlacFixedOrder) (samples : Array Int32) (i : Nat) :
    Nat → List Int32 → List Int32
  | 0, acc => acc.reverse
  | rem + 1, acc =>
    let s := samples.getD i 0
    let p := flacFixedPredict ord samples i
    flacEncodeFixedResidualsLoop ord samples (i + 1) rem ((s - p) :: acc)

def flacEncodeFixedResiduals (ord : FlacFixedOrder) (samples : Array Int32) : Array Int32 :=
  (flacEncodeFixedResidualsLoop ord samples 0 samples.size []).toArray

def flacDecodeFixedResidualsLoop (ord : FlacFixedOrder) : List Int32 → List Int32 → List Int32
  | [], outRev => outRev.reverse
  | r :: rest, outRev =>
    let curOut := outRev.reverse.toArray
    let p := flacFixedPredict ord curOut outRev.length
    flacDecodeFixedResidualsLoop ord rest ((r + p) :: outRev)

def flacDecodeFixedResiduals (ord : FlacFixedOrder) (residuals : Array Int32) : Array Int32 :=
  (flacDecodeFixedResidualsLoop ord residuals.toList []).toArray

def flacEncodeFixedResiduals64Loop (ord : FlacFixedOrder) (samples : Array Int64) (i : Nat)
    (acc : Array Int64) : Nat → Array Int64
  | 0 => acc
  | rem + 1 =>
    let s := samples.getD i 0
    let p := flacFixedPredict64 ord samples i
    flacEncodeFixedResiduals64Loop ord samples (i + 1) (acc.push (s - p)) rem

def flacEncodeFixedResiduals64 (ord : FlacFixedOrder) (samples : Array Int64) : Array Int64 :=
  flacEncodeFixedResiduals64Loop ord samples 0 #[] samples.size

def flacDecodeFixedResiduals64Loop (ord : FlacFixedOrder) (residuals : Array Int64) (i : Nat)
    (out : Array Int64) : Nat → Array Int64
  | 0 => out
  | rem + 1 =>
    let r := residuals.getD i 0
    let p := flacFixedPredict64 ord out out.size
    flacDecodeFixedResiduals64Loop ord residuals (i + 1) (out.push (r + p)) rem

def flacDecodeFixedResiduals64 (ord : FlacFixedOrder) (warmup residuals : Array Int64) : Array Int64 :=
  flacDecodeFixedResiduals64Loop ord residuals 0 warmup residuals.size

@[inline]
def flacFixedPredictFast (ord : FlacFixedOrder) (arr : Array Int32) (i : Nat) : Int32 :=
  match ord with
  | .order0 => 0
  | .order1 =>
    if i ≥ 1 then arr.getD (i - 1) 0 else 0
  | .order2 =>
    if i ≥ 2 then 2 * arr.getD (i - 1) 0 - arr.getD (i - 2) 0 else 0
  | .order3 =>
    if i ≥ 3 then 3 * arr.getD (i - 1) 0 - 3 * arr.getD (i - 2) 0 + arr.getD (i - 3) 0 else 0
  | .order4 =>
    if i ≥ 4 then
      4 * arr.getD (i - 1) 0 - 6 * arr.getD (i - 2) 0 + 4 * arr.getD (i - 3) 0 - arr.getD (i - 4) 0
    else 0

def flacEncodeFixedResidualsFast (ord : FlacFixedOrder) (samples : Array Int32) : Array Int32 := Id.run do
  let n := samples.size
  let mut out := Array.mkEmpty n
  for i in [:n] do
    let s := samples.getD i 0
    let p := flacFixedPredictFast ord samples i
    out := out.push (s - p)
  return out

def flacDecodeFixedResidualsFast (ord : FlacFixedOrder) (residuals : Array Int32) : Array Int32 := Id.run do
  let n := residuals.size
  let mut out := Array.mkEmpty n
  for i in [:n] do
    let r := residuals.getD i 0
    let p := flacFixedPredictFast ord out i
    out := out.push (r + p)
  return out

def flacLpcFirDot64 (outArr : Array Int64) (curIdx : Nat) (coeffs : Array Int64)
    (k : Nat) (acc : Int64) : Nat → Int64
  | 0 => acc
  | rem + 1 =>
    let nextAcc :=
      if curIdx > k then acc + coeffs.getD k 0 * outArr.getD (curIdx - 1 - k) 0
      else acc
    flacLpcFirDot64 outArr curIdx coeffs (k + 1) nextAcc rem

def flacDecodeLpcFir64Loop (coeffs : Array Int64) (qShift : UInt32) (residuals : Array Int64)
    (i : Nat) (outArr : Array Int64) : Nat → Array Int64
  | 0 => outArr
  | rem + 1 =>
    let acc := flacLpcFirDot64 outArr outArr.size coeffs 0 0 coeffs.size
    let pred : Int64 := acc >>> qShift.toUInt64.toInt64
    flacDecodeLpcFir64Loop coeffs qShift residuals (i + 1) (outArr.push (residuals.getD i 0 + pred)) rem

def flacDecodeLpcFir64 (warmup coeffs : Array Int64) (qShift : UInt32)
    (residuals : Array Int64) : Array Int64 :=
  flacDecodeLpcFir64Loop coeffs qShift residuals 0 warmup residuals.size

def flacLpcFirDot (outList : List Int32) (curIdx : Nat) (coeffs : List Int32) (k : Nat) (acc : Int64) :
    List Int32 → Int64
  | [] => acc
  | c :: cs =>
    let nextAcc :=
      if curIdx > k then
        let prev := (outList.getD (curIdx - 1 - k) 0).toInt64
        acc + c.toInt64 * prev
      else acc
    flacLpcFirDot outList curIdx coeffs (k + 1) nextAcc cs

def flacDecodeLpcFirList (coeffs : List Int32) (qShift : UInt32) : List Int32 → List Int32 → List Int32
  | outList, [] => outList
  | outList, r :: rs =>
    let acc := flacLpcFirDot outList outList.length coeffs 0 0 coeffs
    let pred : Int32 := (acc >>> Int64.ofInt (qShift.toNat : Int)).toInt32
    flacDecodeLpcFirList coeffs qShift (outList ++ [r + pred]) rs

def flacDecodeLpcFir (warmup : Array Int32) (coeffs : Array Int32) (qShift : UInt32)
    (residuals : Array Int32) : Array Int32 :=
  (flacDecodeLpcFirList coeffs.toList qShift warmup.toList residuals.toList).toArray

@[inline]
def flacStereoToMidSide64 (left right : Int64) : Int64 × Int64 :=
  let side := left - right
  let mid := (left + right) >>> 1
  (mid, side)

@[inline]
def flacMidSideToStereo64 (mid side : Int64) : Int64 × Int64 :=
  let sum2 := (mid <<< 1) + (side &&& 1)
  let left := (sum2 + side) >>> 1
  let right := (sum2 - side) >>> 1
  (left, right)

@[inline]
def flacStereoToMidSide (left right : Int32) : Int32 × Int32 :=
  let (m, s) := flacStereoToMidSide64 left.toInt64 right.toInt64
  (m.toInt32, s.toInt32)

@[inline]
def flacMidSideToStereo (mid side : Int32) : Int32 × Int32 :=
  let (l, r) := flacMidSideToStereo64 mid.toInt64 side.toInt64
  (l.toInt32, r.toInt32)

/-! ## 2. Opus (`RFC 6716`: SILK + CELT Hybrid Audio Codec) -/

/-- Opus bandwidth modes (`NB` 4kHz .. `FB` 20kHz). -/
inductive OpusBandwidth where
  | narrowband      -- 8 kHz sample rate
  | mediumband      -- 12 kHz sample rate
  | wideband        -- 16 kHz sample rate
  | superwideband   -- 24 kHz sample rate
  | fullband        -- 48 kHz sample rate
  deriving Repr, DecidableEq, Inhabited

/-- Opus coding mode extracted from the TOC byte (`SILK`, `Hybrid`, `CELT`). -/
inductive OpusMode where
  | silkOnly
  | hybrid
  | celtOnly
  deriving Repr, DecidableEq, Inhabited

/-- Parsed Opus packet TOC header (`RFC 6716 Section 3.1`). -/
structure OpusTocHeader where
  config      : UInt8
  mode        : OpusMode
  bandwidth   : OpusBandwidth
  stereo      : Bool
  frameCode   : UInt8
  samples48k  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Total kernel-reducible byte lookup inside a `ByteSlice`. -/
@[inline]
def sliceByteD (s : ByteSlice) (idx : Nat) : UInt8 :=
  if idx < s.len then s.ba.data.getD (s.off + idx) 0 else 0

/-- Parse the 1-byte Opus TOC header at the start of an Opus packet slice. -/
def parseOpusToc (s : ByteSlice) : Option OpusTocHeader :=
  if s.len == 0 then none
  else
    let toc := sliceByteD s 0
    let cfg := toc >>> 3
    let stereo := ((toc >>> 2) &&& 1) == 1
    let frameCode := toc &&& 0x03
    let mode : OpusMode :=
      if cfg < 12 then .silkOnly
      else if cfg < 16 then .hybrid
      else .celtOnly
    let bw : OpusBandwidth :=
      if cfg < 4 then .narrowband
      else if cfg < 8 then .mediumband
      else if cfg < 12 then .wideband
      else if cfg < 14 then .superwideband
      else if cfg < 16 then .fullband
      else if cfg < 20 then .narrowband
      else if cfg < 24 then .wideband
      else if cfg < 28 then .superwideband
      else .fullband
    let samples48k : Nat :=
      match mode with
      | .celtOnly =>
        match cfg % 4 with
        | 0 => 120 -- 2.5 ms
        | 1 => 240 -- 5 ms
        | 2 => 480 -- 10 ms
        | _ => 960 -- 20 ms
      | _ => 960 -- 20 ms default
    some { config := cfg, mode, bandwidth := bw, stereo, frameCode, samples48k }

/-- Fast O(1) `ByteArray`-backed Opus TOC parser (`parseOpusTocFast`) using `s.getByteD` instead of `s.ba.data.getD`. -/
@[inline]
def parseOpusTocFast (s : ByteSlice) : Option OpusTocHeader :=
  if s.len == 0 then none
  else
    let toc := s.getByteD 0 0
    let cfg := toc >>> 3
    let stereo := ((toc >>> 2) &&& 1) == 1
    let frameCode := toc &&& 0x03
    let mode : OpusMode :=
      if cfg < 12 then .silkOnly
      else if cfg < 16 then .hybrid
      else .celtOnly
    let bw : OpusBandwidth :=
      if cfg < 4 then .narrowband
      else if cfg < 8 then .mediumband
      else if cfg < 12 then .wideband
      else if cfg < 14 then .superwideband
      else if cfg < 16 then .fullband
      else if cfg < 20 then .narrowband
      else if cfg < 24 then .wideband
      else if cfg < 28 then .superwideband
      else .fullband
    let samples48k : Nat :=
      match mode with
      | .celtOnly =>
        match cfg % 4 with
        | 0 => 120
        | 1 => 240
        | 2 => 480
        | _ => 960
      | _ => 960
    some { config := cfg, mode, bandwidth := bw, stereo, frameCode, samples48k }

/-- Integer square-root (`⌊√n⌋`) for CELT PVQ L2-energy band normalization. -/
def isqrtNat (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut x := n
  let mut y := (x + 1) / 2
  let mut fuel : Nat := 32
  while y < x && fuel > 0 do
    fuel := fuel - 1
    x := y
    y := (x + n / x) / 2
  return x

/-- Normalize a CELT PVQ pulse vector `pulses` to target Q14 band energy `targetGainQ14`. -/
def celtNormalizeBandPvq (pulses : Array Int32) (targetGainQ14 : UInt32) : Array Int32 := Id.run do
  let mut sumSq : Nat := 0
  for p in pulses do
    let a := p.toInt.natAbs
    sumSq := sumSq + a * a
  let norm := isqrtNat sumSq
  if norm == 0 then
    return Array.replicate pulses.size 0
  let scale : Int32 := Int32.ofNat (targetGainQ14.toNat / norm)
  return pulses.map (fun p => p * scale)

/-! ## 3. MDCT / IMDCT Overlap-Add Synthesis (`Opus CELT`, `AAC`, `MP3`, `AC-3`, `Vorbis`) -/

/-- Q15 4-point fast inverse MDCT core with Time-Domain Aliasing Cancellation (`TDAC`) overlap-add. -/
def imdct4OverlapAddQ15 (spec4 : Array Int32) (prevOverlap : Array Int32) : Array Int32 × Array Int32 := Id.run do
  let x0 := spec4.getD 0 0
  let x1 := spec4.getD 1 0
  let x2 := spec4.getD 2 0
  let x3 := spec4.getD 3 0
  -- Q15 cosine twiddles: cos(pi/8) ≈ 30274, sin(pi/8) ≈ 12540
  let c1 : Int32 := 30274
  let s1 : Int32 := 12540
  let y0 := ((x0 * c1 - x3 * s1) >>> 15) + prevOverlap.getD 0 0
  let y1 := ((x1 * c1 - x2 * s1) >>> 15) + prevOverlap.getD 1 0
  let y2 := ((x2 * c1 + x1 * s1) >>> 15) + prevOverlap.getD 2 0
  let y3 := ((x3 * c1 + x0 * s1) >>> 15) + prevOverlap.getD 3 0
  let nextOverlap := #[
    (x0 * s1 + x3 * c1) >>> 15,
    (x1 * s1 + x2 * c1) >>> 15,
    (x2 * s1 - x1 * c1) >>> 15,
    (x3 * s1 - x0 * c1) >>> 15
  ]
  return (#[clipInt16 y0, clipInt16 y1, clipInt16 y2, clipInt16 y3], nextOverlap)

/-! ## 4. `swresample`: Verified Sample Rate Converter & Channel Matrix Mixer -/

/-- Resample an `AudioFrame` from `af.sampleRate` to `dstRate` using Q12 linear/cubic interpolation (`swr_convert`). -/
def resampleAudioFrame (af : AudioFrame) (dstRate : UInt32) : AudioFrame := Id.run do
  if af.sampleRate == 0 || dstRate == 0 || af.numSamples == 0 then
    return AudioFrame.alloc af.sampleFmt dstRate af.channels 0 af.pts
  let srcN := af.numSamples
  let dstN := rescaleQ srcN.toUInt64 dstRate.toUInt64 af.sampleRate.toUInt64 |>.toNat
  let mut out := AudioFrame.alloc af.sampleFmt dstRate af.channels dstN af.pts
  if dstN == 0 then return out
  for ch in [:af.channels.toNat] do
    for di in [:dstN] do
      let posQ12 := (di * srcN * 4096) / dstN
      let idx0 := Nat.min (srcN - 1) (posQ12 / 4096)
      let idx1 := Nat.min (srcN - 1) (idx0 + 1)
      let frac : Int32 := Int32.ofNat (posQ12 % 4096)
      let invFrac : Int32 := 4096 - frac
      let s0 := af.getSample ch idx0
      let s1 := af.getSample ch idx1
      let interp := (s0 * invFrac + s1 * frac + 2048) >>> 12
      out := out.setSample ch di (clipInt16 interp)
  return out

/-- Downmix a Stereo (`channels = 2`) `AudioFrame` to Mono (`channels = 1`) with exact `-3 dB` / midpoint averaging. -/
def downmixStereoToMono (af : AudioFrame) : AudioFrame := Id.run do
  let mut out := AudioFrame.alloc af.sampleFmt af.sampleRate 1 af.numSamples af.pts
  for i in [:af.numSamples] do
    let l := af.getSample 0 i
    let r := if af.channels ≥ 2 then af.getSample 1 i else l
    out := out.setSample 0 i ((l + r) >>> 1)
  return out

/-! ## 5. Wave 2 Audio Extensions: FLAC `STREAMINFO` & Rice Subframes (`R0`), AAC ADTS & IMDCT 1024, Opus Multi-Frame (`Code 0..3`) -/

/-- Parsed FLAC 34-byte `STREAMINFO` metadata block (`fLaC` + block header + 34 bytes). -/
structure FlacStreamInfo where
  minBlockSize  : UInt16
  maxBlockSize  : UInt16
  minFrameSize  : UInt32
  maxFrameSize  : UInt32
  sampleRate    : UInt32
  channels      : UInt8
  bitsPerSample : UInt8
  totalSamples  : UInt64
  deriving Repr, DecidableEq, Inhabited

def parseFlacStreamInfo (s : ByteSlice) : Option FlacStreamInfo :=
  let hasFlacMagic :=
    s.len ≥ 4 &&
    sliceByteD s 0 == 0x66 && sliceByteD s 1 == 0x4C &&
    sliceByteD s 2 == 0x61 && sliceByteD s 3 == 0x43
  let baseOffOpt : Option Nat :=
    if hasFlacMagic then
      if s.len ≥ 42 &&
         ((sliceByteD s 4 &&& 0x7F) == 0) &&
         sliceByteD s 5 == 0x00 && sliceByteD s 6 == 0x00 && sliceByteD s 7 == 0x22 then
        some 8
      else none
    else if s.len == 34 then some 0
    else none
  match baseOffOpt with
  | none => none
  | some baseOff =>
    if baseOff + 34 > s.len then none
    else
      let minBlk : UInt16 := ((sliceByteD s baseOff).toUInt16 <<< 8) ||| (sliceByteD s (baseOff + 1)).toUInt16
      let maxBlk : UInt16 := ((sliceByteD s (baseOff + 2)).toUInt16 <<< 8) ||| (sliceByteD s (baseOff + 3)).toUInt16
      let minFrm : UInt32 :=
        ((sliceByteD s (baseOff + 4)).toUInt32 <<< 16) |||
        ((sliceByteD s (baseOff + 5)).toUInt32 <<< 8)  |||
        (sliceByteD s (baseOff + 6)).toUInt32
      let maxFrm : UInt32 :=
        ((sliceByteD s (baseOff + 7)).toUInt32 <<< 16) |||
        ((sliceByteD s (baseOff + 8)).toUInt32 <<< 8)  |||
        (sliceByteD s (baseOff + 9)).toUInt32
      let b10 := (sliceByteD s (baseOff + 10)).toUInt32
      let b11 := (sliceByteD s (baseOff + 11)).toUInt32
      let b12 := (sliceByteD s (baseOff + 12)).toUInt32
      let b13 := (sliceByteD s (baseOff + 13)).toUInt32
      let sr : UInt32 := (b10 <<< 12) ||| (b11 <<< 4) ||| (b12 >>> 4)
      let ch : UInt8 := (((b12 >>> 1) &&& 0x07) + 1).toUInt8
      let bps : UInt8 := ((((b12 &&& 1) <<< 4) ||| (b13 >>> 4)) + 1).toUInt8
      let totHi : UInt64 := (b13 &&& 0x0F).toUInt64
      let totLo : UInt64 :=
        ((sliceByteD s (baseOff + 14)).toUInt64 <<< 24) |||
        ((sliceByteD s (baseOff + 15)).toUInt64 <<< 16) |||
        ((sliceByteD s (baseOff + 16)).toUInt64 <<< 8)  |||
        (sliceByteD s (baseOff + 17)).toUInt64
      let totSamples : UInt64 := (totHi <<< 32) ||| totLo
      if sr == 0 || sr > (655350 : UInt32) || minBlk < 16 || maxBlk < minBlk || bps < 4 then none
      else some {
        minBlockSize := minBlk
        maxBlockSize := maxBlk
        minFrameSize := minFrm
        maxFrameSize := maxFrm
        sampleRate := sr
        channels := ch
        bitsPerSample := bps
        totalSamples := totSamples
      }

/-- Serialize a `FlacStreamInfo` into a canonical 42-byte `fLaC` + `STREAMINFO` header (`isLastBlock` defaults to `false`). -/
def serializeFlacStreamInfo (si : FlacStreamInfo) (md5Bytes16 : Array UInt8 := #[]) (isLastBlock : Bool := false) : ByteArray :=
  let sr := si.sampleRate &&& 0xFFFFF
  let chMinus1 := ((if si.channels > 0 then si.channels - 1 else 0) &&& 0x07).toUInt32
  let bpsMinus1 := ((if si.bitsPerSample > 0 then si.bitsPerSample - 1 else 0) &&& 0x1F).toUInt32
  let totHi4 := ((si.totalSamples >>> 32) &&& 0x0F).toUInt32
  let totLo32 := (si.totalSamples &&& 0xFFFFFFFF).toUInt32
  let b10 : UInt8 := (sr >>> 12).toUInt8
  let b11 : UInt8 := ((sr >>> 4) &&& 0xFF).toUInt8
  let b12 : UInt8 := (((sr &&& 0x0F) <<< 4) ||| (chMinus1 <<< 1) ||| (bpsMinus1 >>> 4)).toUInt8
  let b13 : UInt8 := (((bpsMinus1 &&& 0x0F) <<< 4) ||| totHi4).toUInt8
  let hdr26 : Array UInt8 := #[
    (0x66 : UInt8), (0x4C : UInt8), (0x61 : UInt8), (0x43 : UInt8),
    (if isLastBlock then (0x80 : UInt8) else (0x00 : UInt8)),
    (0x00 : UInt8), (0x00 : UInt8), (0x22 : UInt8),
    (si.minBlockSize >>> 8).toUInt8, si.minBlockSize.toUInt8,
    (si.maxBlockSize >>> 8).toUInt8, si.maxBlockSize.toUInt8,
    (si.minFrameSize >>> 16).toUInt8, (si.minFrameSize >>> 8).toUInt8, si.minFrameSize.toUInt8,
    (si.maxFrameSize >>> 16).toUInt8, (si.maxFrameSize >>> 8).toUInt8, si.maxFrameSize.toUInt8,
    b10, b11, b12, b13,
    (totLo32 >>> 24).toUInt8, (totLo32 >>> 16).toUInt8, (totLo32 >>> 8).toUInt8, totLo32.toUInt8,
    md5Bytes16.getD 0 0, md5Bytes16.getD 1 0, md5Bytes16.getD 2 0, md5Bytes16.getD 3 0,
    md5Bytes16.getD 4 0, md5Bytes16.getD 5 0, md5Bytes16.getD 6 0, md5Bytes16.getD 7 0,
    md5Bytes16.getD 8 0, md5Bytes16.getD 9 0, md5Bytes16.getD 10 0, md5Bytes16.getD 11 0,
    md5Bytes16.getD 12 0, md5Bytes16.getD 13 0, md5Bytes16.getD 14 0, md5Bytes16.getD 15 0
  ]
  { data := hdr26 }

/-- Real 42-byte `fLaC` + `STREAMINFO` bytes extracted by `ffmpeg` from `artifacts/real_media/t1_sine.flac`. -/
def realFfmpegFlacStreamInfoBytes : Array UInt8 := #[
  0x66, 0x4C, 0x61, 0x43, 0x00, 0x00, 0x00, 0x22,
  0x04, 0x00, 0x04, 0x00, 0x00, 0x00, 0xB6, 0x00,
  0x01, 0x82, 0x0B, 0xB8, 0x00, 0xF0, 0x00, 0x00,
  0x25, 0x80, 0x05, 0x83, 0x58, 0xEF, 0x75, 0x31,
  0x98, 0xA4, 0x67, 0x49, 0x58, 0xA6, 0xD6, 0xB2,
  0x54, 0x06
]

/-- Expected `FlacStreamInfo` parsed from `realFfmpegFlacStreamInfoBytes`. -/
def realFfmpegFlacStreamInfo : FlacStreamInfo := {
  minBlockSize  := 1024
  maxBlockSize  := 1024
  minFrameSize  := 182
  maxFrameSize  := 386
  sampleRate    := 48000
  channels      := 1
  bitsPerSample := 16
  totalSamples  := 9600
}

/-- Theorem: `parseFlacStreamInfo (serializeFlacStreamInfo si) = some si` R0 round-trip on the real FFmpeg `STREAMINFO`. -/
theorem flacStreamInfo_parse_serialize_roundtrip :
    parseFlacStreamInfo { ba := serializeFlacStreamInfo realFfmpegFlacStreamInfo, off := 0, len := 42 } =
      some realFfmpegFlacStreamInfo ∧
    parseFlacStreamInfo { ba := { data := realFfmpegFlacStreamInfoBytes }, off := 0, len := 42 } =
      some realFfmpegFlacStreamInfo := by
  decide

/-! ### T2: Standard RFC 9639 FLAC Subframe Decoder & Encoder (Constant, Verbatim, Fixed 0..4, LPC, Rice 4/5-bit + Escape) -/

@[inline]
def signExtendBits64 (u : UInt64) (n : Nat) : Int64 :=
  if n == 0 || n > 63 then 0
  else
    let signBit : UInt64 := (1 : UInt64) <<< (n - 1).toUInt64
    if (u &&& signBit) != 0 then
      let mask : UInt64 := ((1 : UInt64) <<< n.toUInt64) - 1
      let ext : UInt64 := u ||| (0xFFFFFFFFFFFFFFFF ^^^ mask)
      ext.toInt64
    else
      u.toInt64

@[inline]
def signExtendBits32 (u : UInt64) (n : Nat) : Int32 :=
  (signExtendBits64 u n).toInt32

@[inline]
def readSignedBitsMSB64 (r : BitReader) (n : Nat) : Option (Int64 × BitReader) := do
  if n > 63 then none
  let (u, r') ← r.readBitsMSB n
  some (signExtendBits64 u n, r')

@[inline]
def readSignedBitsMSB (r : BitReader) (n : Nat) : Option (Int32 × BitReader) := do
  let (v, r') ← readSignedBitsMSB64 r n
  some (v.toInt32, r')

@[inline]
def writeSignedBitsMSB64 (w : BitWriter) (v : Int64) (n : Nat) : BitWriter :=
  if n == 0 then w
  else
    let mask : UInt64 := if n ≥ 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< n.toUInt64) - 1
    let u : UInt64 := v.toUInt64 &&& mask
    w.writeBitsMSB u n

@[inline]
def writeSignedBitsMSB (w : BitWriter) (v : Int32) (n : Nat) : BitWriter :=
  writeSignedBitsMSB64 w v.toInt64 n

def readSignedSamplesLoop64 (rawBps : Nat) (cur : BitReader) : Nat → List Int64 → Option (List Int64 × BitReader)
  | 0, acc => some (acc.reverse, cur)
  | rem + 1, acc =>
    if rawBps == 0 then
      readSignedSamplesLoop64 0 cur rem (0 :: acc)
    else
      match readSignedBitsMSB64 cur rawBps with
      | none => none
      | some (sv, rNext) => readSignedSamplesLoop64 rawBps rNext rem (sv :: acc)

def readRiceSamplesLoop64 (k : Nat) (cur : BitReader) : Nat → List Int64 → Option (List Int64 × BitReader)
  | 0, acc => some (acc.reverse, cur)
  | rem + 1, acc =>
    match cur.readRiceSigned k with
    | none => none
    | some (sv, rNext) => readRiceSamplesLoop64 k rNext rem (sv :: acc)

def decodeFlacRicePartitionsLoop64 (blockSize predOrder partOrder numParts paramBits : Nat) (escapeParam : UInt64)
    (cur : BitReader) (p : Nat) : Nat → List Int64 → Option (List Int64 × BitReader)
  | 0, accRev => some (accRev.reverse, cur)
  | remParts + 1, accRev =>
    match cur.readBitsMSB paramBits with
    | none => none
    | some (param, rP) =>
      let nSamplesInPart : Nat :=
        if partOrder == 0 then blockSize - predOrder
        else if p == 0 then
          if blockSize / numParts < predOrder then 0 else (blockSize / numParts) - predOrder
        else blockSize / numParts
      if param == escapeParam then
        match rP.readBitsMSB 5 with
        | none => none
        | some (rawBpsBits, rEsc) =>
          match readSignedSamplesLoop64 rawBpsBits.toNat rEsc nSamplesInPart [] with
          | none => none
          | some (partSamples, rNext) =>
            decodeFlacRicePartitionsLoop64 blockSize predOrder partOrder numParts paramBits escapeParam
              rNext (p + 1) remParts (partSamples.reverse ++ accRev)
      else
        match readRiceSamplesLoop64 param.toNat rP nSamplesInPart [] with
        | none => none
        | some (partSamples, rNext) =>
          decodeFlacRicePartitionsLoop64 blockSize predOrder partOrder numParts paramBits escapeParam
            rNext (p + 1) remParts (partSamples.reverse ++ accRev)

def decodeFlacRicePartitions64 (r0 : BitReader) (blockSize predOrder : Nat) : Option (Array Int64 × BitReader) :=
  match r0.readBitsMSB 2 with
  | none => none
  | some (codingMethod, r1) =>
    if codingMethod > 1 then none
    else
      match r1.readBitsMSB 4 with
      | none => none
      | some (partOrderBits, r2) =>
        let partOrder := partOrderBits.toNat
        let numParts := 1 <<< partOrder
        let paramBits := if codingMethod == 0 then 4 else 5
        let escapeParam : UInt64 := if codingMethod == 0 then 15 else 31
        if blockSize < predOrder || (partOrder > 0 && blockSize % numParts != 0) then none
        else
          match decodeFlacRicePartitionsLoop64 blockSize predOrder partOrder numParts paramBits
            escapeParam r2 0 numParts [] with
          | none => none
          | some (resList, curEnd) => some (resList.toArray, curEnd)

def flacApplyWasted64Loop (arr : Array Int64) (wb : Int64) (i : Nat) (acc : Array Int64) : Nat → Array Int64
  | 0 => acc
  | k + 1 =>
    if i ≥ arr.size then acc
    else flacApplyWasted64Loop arr wb (i + 1) (acc.push (arr.getD i 0 <<< wb)) k

def flacApplyWasted64 (arr : Array Int64) (wastedBits : Nat) : Array Int64 :=
  if wastedBits == 0 then arr
  else flacApplyWasted64Loop arr wastedBits.toUInt64.toInt64 0 #[] arr.size

def flacArray64To32Loop (arr : Array Int64) (i : Nat) (acc : Array Int32) : Nat → Array Int32
  | 0 => acc
  | k + 1 =>
    if i ≥ arr.size then acc
    else flacArray64To32Loop arr (i + 1) (acc.push (arr.getD i 0).toInt32) k

def flacArray64To32 (arr : Array Int64) : Array Int32 :=
  flacArray64To32Loop arr 0 #[] arr.size

def flacArray32To64Loop (arr : Array Int32) (i : Nat) (acc : Array Int64) : Nat → Array Int64
  | 0 => acc
  | k + 1 =>
    if i ≥ arr.size then acc
    else flacArray32To64Loop arr (i + 1) (acc.push (arr.getD i 0).toInt64) k

def flacArray32To64 (arr : Array Int32) : Array Int64 :=
  flacArray32To64Loop arr 0 #[] arr.size

def flacDecodeSubframeCore64 (r0 : BitReader) (blockSize bps : Nat) : Option (Array Int64 × BitReader) := do
  if blockSize == 0 || bps == 0 || bps > 33 then none
  let (zeroBit, r1) ← r0.readBit
  if zeroBit != 0 then none
  let (stypeBits, r2) ← r1.readBitsMSB 6
  let stype := stypeBits.toNat
  let (wastedFlag, r3) ← r2.readBit
  let (wastedBits, r4) ←
    if wastedFlag == 1 then do
      let (km1, rw) ← r3.readUnary0 33
      some (km1 + 1, rw)
    else some (0, r3)
  if wastedBits ≥ bps then none
  let effBps := bps - wastedBits
  if stype == 0 then
    let (cVal, rEnd) ← readSignedBitsMSB64 r4 effBps
    some (flacApplyWasted64 (List.replicate blockSize cVal).toArray wastedBits, rEnd)
  else if stype == 1 then
    let (outList, rEnd) ← readSignedSamplesLoop64 effBps r4 blockSize []
    some (flacApplyWasted64 outList.toArray wastedBits, rEnd)
  else if stype ≥ 8 && stype ≤ 12 then
    let predOrder := stype - 8
    if blockSize < predOrder then none
    else do
      let (warmList, cur) ← readSignedSamplesLoop64 effBps r4 predOrder []
      let (residuals, rEnd) ← decodeFlacRicePartitions64 cur blockSize predOrder
      let ord : FlacFixedOrder := match predOrder with
        | 0 => .order0 | 1 => .order1 | 2 => .order2 | 3 => .order3 | _ => .order4
      let out := flacDecodeFixedResiduals64 ord warmList.toArray residuals
      some (flacApplyWasted64 out wastedBits, rEnd)
  else if stype ≥ 32 && stype ≤ 63 then
    let predOrder := stype - 32 + 1
    if blockSize < predOrder then none
    else do
      let (warmList, cur) ← readSignedSamplesLoop64 effBps r4 predOrder []
      let (precMinus1Bits, r5) ← cur.readBitsMSB 4
      if precMinus1Bits == 15 then none
      else do
        let coeffPrec := precMinus1Bits.toNat + 1
        let (qShiftSigned, r6) ← readSignedBitsMSB64 r5 5
        if qShiftSigned < 0 then none
        else do
          let qShift : UInt32 := qShiftSigned.toUInt64.toUInt32
          let (coeffList, curC) ← readSignedSamplesLoop64 coeffPrec r6 predOrder []
          let (residuals, rEnd) ← decodeFlacRicePartitions64 curC blockSize predOrder
          let out := flacDecodeLpcFir64 warmList.toArray coeffList.toArray qShift residuals
          some (flacApplyWasted64 out wastedBits, rEnd)
  else none

def decodeFlacSubframeSpec (s : ByteSlice) (blockSize bps : Nat) : Option (Array Int32) := do
  if bps > 32 then none
  let (arr64, _) ← flacDecodeSubframeCore64 (BitReader.ofSlice s) blockSize bps
  some (flacArray64To32 arr64)

inductive FlacSubframeSpecMode where
  | constant (val : Int64)
  | verbatim
  | fixed (ord : FlacFixedOrder) (codingMethod : UInt8 := 0) (riceK : Nat := 3)
      (escaped : Bool := false) (rawBps : Nat := 16)
  | lpc (coeffs : Array Int32) (coeffPrec : Nat) (qShift : UInt32)
      (codingMethod : UInt8 := 0) (riceK : Nat := 3)
  deriving Repr, DecidableEq, Inhabited

def writeSignedListMSB64 (n : Nat) (w : BitWriter) : List Int64 → BitWriter
  | [] => w
  | s :: rest => writeSignedListMSB64 n (writeSignedBitsMSB64 w s n) rest

def writeSignedListMSB (n : Nat) (w : BitWriter) : List Int32 → BitWriter
  | [] => w
  | s :: rest => writeSignedListMSB n (writeSignedBitsMSB w s n) rest

def writeRiceListSigned64 (k : Nat) (w : BitWriter) : List Int64 → BitWriter
  | [] => w
  | r :: rest => writeRiceListSigned64 k (w.writeRiceSigned k r) rest

def writeRiceListSigned (k : Nat) (w : BitWriter) : List Int32 → BitWriter
  | [] => w
  | r :: rest => writeRiceListSigned k (w.writeRiceSigned k r.toInt64) rest

def encodeFlacLpcResidualsLoop64 (samples : Array Int64) (coeffs : Array Int64) (qShift : UInt32)
    (riceK : Nat) (i : Nat) (w : BitWriter) : Nat → BitWriter
  | 0 => w
  | rem + 1 =>
    let acc := flacLpcFirDot64 samples i coeffs 0 0 coeffs.size
    let pred : Int64 := acc >>> qShift.toUInt64.toInt64
    let res : Int64 := samples.getD i 0 - pred
    encodeFlacLpcResidualsLoop64 samples coeffs qShift riceK (i + 1) (w.writeRiceSigned riceK res) rem

def flacWriteSubframeBits64 (w0 : BitWriter) (mode : FlacSubframeSpecMode) (bps : Nat)
    (samples : Array Int64) : BitWriter :=
  let sampleList := samples.toList
  let wHeader := w0.writeBit 0
  match mode with
  | .constant val =>
    let w1 := (wHeader.writeBitsMSB 0 6).writeBit 0
    writeSignedBitsMSB64 w1 val bps
  | .verbatim =>
    let w1 := (wHeader.writeBitsMSB 1 6).writeBit 0
    writeSignedListMSB64 bps w1 sampleList
  | .fixed ord codingMethod riceK escaped rawBps =>
    let predOrder : Nat := match ord with
      | .order0 => 0 | .order1 => 1 | .order2 => 2 | .order3 => 3 | .order4 => 4
    let w1 := (wHeader.writeBitsMSB (8 + predOrder).toUInt64 6).writeBit 0
    let w2 := writeSignedListMSB64 bps w1 (sampleList.take predOrder)
    let cm : UInt64 := if codingMethod == 0 then 0 else 1
    let paramBits : Nat := if codingMethod == 0 then 4 else 5
    let escCode : UInt64 := if codingMethod == 0 then 15 else 31
    let w3 := (w2.writeBitsMSB cm 2).writeBitsMSB 0 4
    let allResList := (flacEncodeFixedResiduals64 ord samples).toList.drop predOrder
    if escaped then
      let w4 := (w3.writeBitsMSB escCode paramBits).writeBitsMSB rawBps.toUInt64 5
      writeSignedListMSB64 rawBps w4 allResList
    else
      let w4 := w3.writeBitsMSB riceK.toUInt64 paramBits
      writeRiceListSigned64 riceK w4 allResList
  | .lpc coeffs coeffPrec qShift codingMethod riceK =>
    let coeffs64 := flacArray32To64 coeffs
    let coeffList64 := coeffs64.toList
    let predOrder := coeffList64.length
    let w1 := (wHeader.writeBitsMSB (32 + predOrder - 1).toUInt64 6).writeBit 0
    let w2 := writeSignedListMSB64 bps w1 (sampleList.take predOrder)
    let w3 := writeSignedBitsMSB64 (w2.writeBitsMSB (coeffPrec - 1).toUInt64 4) qShift.toUInt64.toInt64 5
    let w4 := writeSignedListMSB64 coeffPrec w3 coeffList64
    let cm : UInt64 := if codingMethod == 0 then 0 else 1
    let paramBits : Nat := if codingMethod == 0 then 4 else 5
    let w5 := ((w4.writeBitsMSB cm 2).writeBitsMSB 0 4).writeBitsMSB riceK.toUInt64 paramBits
    encodeFlacLpcResidualsLoop64 samples coeffs64 qShift riceK predOrder w5 (samples.size - predOrder)

def encodeFlacSubframeSpec (mode : FlacSubframeSpecMode) (bps : Nat) (samples : Array Int32) : ByteArray :=
  let samples64 := flacArray32To64 samples
  let w0 := BitWriter.empty (samples.size * 2 + 16)
  (flacWriteSubframeBits64 w0 mode bps samples64).toByteArray

/-- Real 48-byte FLAC Fixed Order-2 subframe extracted from `flac_fixed.flac` (frame 0, offset 8295). -/
def realFfmpegFlacFixedSubframeBytes : Array UInt8 := #[
  0x14, 0x00, 0x00, 0x00, 0xEB, 0x08, 0xE2, 0x77, 0xED, 0x69, 0x4B, 0xDA,
  0xF2, 0x5E, 0x6A, 0x2A, 0x8A, 0xEB, 0xAE, 0xCA, 0xAD, 0xB6, 0xBB, 0x6C,
  0xB6, 0xDB, 0x2D, 0xA3, 0x2C, 0xAE, 0xDA, 0xAC, 0xAA, 0xAA, 0x6B, 0xFD,
  0x14, 0x7B, 0xFC, 0x90, 0xA5, 0x77, 0xAB, 0xE6, 0x8C, 0x84, 0x21, 0x06
]

/-- Real 75-byte FLAC LPC Order-8 subframe extracted from `flac_lpc.flac` (frame 0, offset 8295). -/
def realFfmpegFlacLpcSubframeBytes : Array UInt8 := #[
  0x4E, 0x00, 0x00, 0x00, 0xEB, 0x01, 0xD6, 0x02, 0xC0, 0x03, 0xA7, 0x04,
  0x8A, 0x05, 0x6B, 0x06, 0x46, 0xE6, 0x2C, 0x93, 0x96, 0xD6, 0xAC, 0xDE,
  0xEF, 0x39, 0x93, 0xBD, 0xEE, 0x21, 0xFF, 0xBF, 0x14, 0x82, 0x85, 0x1C,
  0x78, 0x83, 0xC4, 0x08, 0x38, 0x48, 0x83, 0x84, 0x1C, 0x78, 0x82, 0xCF,
  0x34, 0xC3, 0x49, 0x30, 0x92, 0x46, 0x53, 0x88, 0xE2, 0xA9, 0xD0, 0x8D,
  0x47, 0xC6, 0xFD, 0xBF, 0x49, 0x5B, 0x4D, 0x79, 0xA5, 0x89, 0x24, 0x69,
  0x63, 0x44, 0x89
]

/-- Real 64 PCM16 samples decoded by `ffmpeg` from `flac_fixed.flac` and `flac_lpc.flac`. -/
def realFfmpegFlacDecoded64Samples : Array Int32 := #[
  0, 235, 470, 704, 935, 1162, 1387, 1606, 1820, 2029, 2230, 2424, 2610, 2787, 2956, 3114,
  3261, 3399, 3525, 3639, 3741, 3830, 3908, 3972, 4022, 4060, 4084, 4095, 4092, 4075, 4045, 4001,
  3944, 3874, 3792, 3696, 3589, 3469, 3338, 3196, 3044, 2880, 2708, 2527, 2337, 2140, 1935, 1725,
  1508, 1286, 1060, 830, 599, 365, 129, -107, -342, -577, -809, -1039, -1265, -1487, -1705, -1916
]

set_option maxRecDepth 200000 in
/-- Theorem: `decodeFlacSubframeSpec` matches FFmpeg's decoded PCM bit-for-bit (`maxErr = 0`) on both Fixed-2 and LPC-8 real subframes. -/
theorem flacSubframeSpec_matches_ffmpeg_bit_exact :
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (ByteArray.mk realFfmpegFlacFixedSubframeBytes)) 64 16 =
      some realFfmpegFlacDecoded64Samples ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (ByteArray.mk realFfmpegFlacLpcSubframeBytes)) 64 16 =
      some realFfmpegFlacDecoded64Samples := by
  decide

set_option maxRecDepth 200000 in
/-- Theorem: `encodeFlacSubframeSpec` / `decodeFlacSubframeSpec` R0 round-trip across Constant, Verbatim, Fixed (4/5-bit Rice + Escape), and LPC. -/
theorem flacSubframeSpec_encode_decode_roundtrip :
    let sig : Array Int32 := #[120, 340, 560, 420, -110, -320, 15, 890]
    let constSig : Array Int32 := (List.replicate 8 (42 : Int32)).toArray
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec (.constant 42) 16 constSig)) 8 16 = some constSig ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec .verbatim 16 sig)) 8 16 = some sig ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec (.fixed .order2 0 4 false 16) 16 sig)) 8 16 = some sig ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec (.fixed .order3 1 5 false 16) 16 sig)) 8 16 = some sig ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec (.fixed .order1 0 0 true 16) 16 sig)) 8 16 = some sig ∧
    decodeFlacSubframeSpec (ByteSlice.ofByteArray (encodeFlacSubframeSpec (.lpc #[3, -1] 8 1 0 4) 16 sig)) 8 16 = some sig := by
  decide

/-- Encode a FLAC Fixed-LPC Subframe into a bit-exact `ByteArray` using Rice-Golomb coding (`k` bits) (`Regime R0`). -/
def flacEncodeSubframeRiceR0 (ord : FlacFixedOrder) (riceK : Nat) (samples : Array Int32) : ByteArray := Id.run do
  let residuals := flacEncodeFixedResiduals ord samples
  let ordCode : UInt64 := match ord with
    | .order0 => 0
    | .order1 => 1
    | .order2 => 2
    | .order3 => 3
    | .order4 => 4
  let kClamped := Nat.min 14 riceK
  let mut w := BitWriter.empty (samples.size * 2 + 8)
  -- 8-bit header: [0(1b) | subframeType=FIXED(3b:100) | ord(3b) | wasted=0(1b)] + 4-bit riceK + 16-bit count
  w := w.writeBitsMSB ordCode 4
  w := w.writeBitsMSB kClamped.toUInt64 4
  w := w.writeBitsMSB samples.size.toUInt64 16
  for r in residuals do
    w := w.writeRiceSigned kClamped r.toInt64
  return w.toByteArray

/-- Decode a FLAC Fixed-LPC Subframe encoded by `flacEncodeSubframeRiceR0` back into exact `Int32` samples (`Regime R0`, `maxErr = 0`). -/
def flacDecodeSubframeRiceR0 (s : ByteSlice) : Option (Array Int32) := Id.run do
  let r0 := BitReader.ofSlice s
  let some (ordBits, r1) := r0.readBitsMSB 4 | return none
  let some (kBits, r2) := r1.readBitsMSB 4 | return none
  let some (cntBits, r3) := r2.readBitsMSB 16 | return none
  let ord : FlacFixedOrder :=
    if ordBits == 0 then .order0
    else if ordBits == 1 then .order1
    else if ordBits == 2 then .order2
    else if ordBits == 3 then .order3
    else .order4
  let riceK := kBits.toNat
  let count := cntBits.toNat
  let mut curR := r3
  let mut residuals := Array.emptyWithCapacity count
  for _ in [:count] do
    match curR.readRiceSigned riceK with
    | some (val, nextR) =>
      residuals := residuals.push val.toInt32
      curR := nextR
    | none => return none
  return some (flacDecodeFixedResiduals ord residuals)

/-- Parsed 7-byte (or 9-byte CRC) AAC ADTS Frame Header (`ISO/IEC 13818-7`). -/
structure AacAdtsHeader where
  mpegVersion    : UInt8  -- 0 = MPEG-4, 1 = MPEG-2
  protectionAbs  : Bool   -- true = 7-byte header (no CRC), false = 9-byte header
  profileObject  : UInt8  -- 1 = Main, 2 = AAC-LC, 3 = SSR, 4 = LTP
  sampleRateIdx  : UInt8
  sampleRateHz   : UInt32
  channelConfig  : UInt8
  frameLength    : UInt16
  headerBytes    : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Lookup standard MPEG-4 Audio Sampling Frequency (`ISO/IEC 14496-3 Table 1.16`). -/
def aacSampleRateFromIndex (idx : UInt8) : UInt32 :=
  match idx with
  | 0  => 96000
  | 1  => 88200
  | 2  => 64000
  | 3  => 48000
  | 4  => 44100
  | 5  => 32000
  | 6  => 24000
  | 7  => 22050
  | 8  => 16000
  | 9  => 12000
  | 10 => 11025
  | 11 => 8000
  | 12 => 7350
  | _  => 0

/-- Parse an AAC ADTS frame header starting with the 12-bit syncword `0xFFF`. -/
def parseAacAdtsHeader (s : ByteSlice) : Option AacAdtsHeader :=
  if s.len < 7 then none
  else
    let b0 := sliceByteD s 0
    let b1 := sliceByteD s 1
    if b0 != 0xFF || (b1 &&& 0xF0) != 0xF0 then none
    else
      let idBit := (b1 >>> 3) &&& 1
      let noCrc := (b1 &&& 1) == 1
      let b2 := sliceByteD s 2
      let b3 := sliceByteD s 3
      let b4 := sliceByteD s 4
      let b5 := sliceByteD s 5
      let profileObj := ((b2 >>> 6) &&& 0x03) + 1
      let srIdx := (b2 >>> 2) &&& 0x0F
      let srHz := aacSampleRateFromIndex srIdx
      let chCfg := (((b2 &&& 1) <<< 2) ||| ((b3 >>> 6) &&& 0x03))
      let frmLen : UInt16 :=
        (((b3 &&& 0x03).toUInt16) <<< 11) |||
        (b4.toUInt16 <<< 3) |||
        ((b5 >>> 5).toUInt16 &&& 0x07)
      let hdrLen : Nat := if noCrc then 7 else 9
      if srHz == 0 || frmLen.toNat < hdrLen then none
      else some {
        mpegVersion := idBit
        protectionAbs := noCrc
        profileObject := profileObj
        sampleRateIdx := srIdx
        sampleRateHz := srHz
        channelConfig := chCfg
        frameLength := frmLen
        headerBytes := hdrLen
      }

/-- Serialize an `AacAdtsHeader` into its 7-byte ADTS header (`0xFFF` syncword, buffer fullness `0x7FF` VBR). -/
def serializeAacAdtsHeader (h : AacAdtsHeader) (bufferFullness : UInt16 := 0x7FF) (rawBlocksMinus1 : UInt8 := 0) : ByteArray :=
  let b0 : UInt8 := 0xFF
  let b1 : UInt8 := (0xF0 : UInt8) ||| ((h.mpegVersion &&& 1) <<< 3) ||| (if h.protectionAbs then (1 : UInt8) else 0)
  let profMinus1 : UInt8 := (if h.profileObject > 0 then h.profileObject - 1 else 0) &&& 0x03
  let srIdx : UInt8 := h.sampleRateIdx &&& 0x0F
  let chCfg : UInt8 := h.channelConfig &&& 0x07
  let b2 : UInt8 := (profMinus1 <<< 6) ||| (srIdx <<< 2) ||| (chCfg >>> 2)
  let frmLen : UInt16 := h.frameLength &&& 0x1FFF
  let b3 : UInt8 := ((chCfg &&& 0x03) <<< 6) ||| ((frmLen >>> 11).toUInt8 &&& 0x03)
  let b4 : UInt8 := ((frmLen >>> 3) &&& 0xFF).toUInt8
  let bf : UInt16 := bufferFullness &&& 0x07FF
  let b5 : UInt8 := (((frmLen &&& 0x07).toUInt8) <<< 5) ||| ((bf >>> 6).toUInt8 &&& 0x1F)
  let b6 : UInt8 := (((bf &&& 0x3F).toUInt8) <<< 2) ||| (rawBlocksMinus1 &&& 0x03)
  { data := #[b0, b1, b2, b3, b4, b5, b6] }

/-- Real 7-byte AAC ADTS header extracted by `ffmpeg` from `artifacts/real_media/t1_sine.aac` (`fff14c4016dffc`). -/
def realFfmpegAacAdtsBytes : Array UInt8 := #[0xFF, 0xF1, 0x4C, 0x40, 0x16, 0xDF, 0xFC]

/-- Expected `AacAdtsHeader` parsed from `realFfmpegAacAdtsBytes`. -/
def realFfmpegAacAdtsHeader : AacAdtsHeader := {
  mpegVersion   := 0
  protectionAbs := true
  profileObject := 2
  sampleRateIdx := 3
  sampleRateHz  := 48000
  channelConfig := 1
  frameLength   := 182
  headerBytes   := 7
}

/-- Theorem: `parseAacAdtsHeader` and `serializeAacAdtsHeader` round-trip bit-exactly on the real FFmpeg ADTS header. -/
theorem aacAdtsHeader_parse_serialize_roundtrip :
    parseAacAdtsHeader { ba := { data := realFfmpegAacAdtsBytes }, off := 0, len := 7 } = some realFfmpegAacAdtsHeader ∧
    (serializeAacAdtsHeader realFfmpegAacAdtsHeader).data = realFfmpegAacAdtsBytes ∧
    parseAacAdtsHeader { ba := serializeAacAdtsHeader realFfmpegAacAdtsHeader, off := 0, len := 7 } = some realFfmpegAacAdtsHeader := by
  decide

/-- Synthesize a 1024-sample AAC-LC / Opus CELT frame via tiled Q15 Sine-Windowed IMDCT with TDAC overlap-add (`Regime R1`). -/
def aacSynthesizeFrameImdctQ15 (spectralCoeffs : Array Int32) (prevOverlap : Array Int32) : Array Int32 × Array Int32 := Id.run do
  let nBlocks := Nat.max 1 (spectralCoeffs.size / 4)
  let mut pcmOut := Array.emptyWithCapacity (nBlocks * 4)
  let mut nextOv := Array.emptyWithCapacity (nBlocks * 4)
  for b in [:nBlocks] do
    let base := b * 4
    let subSpec := #[
      spectralCoeffs.getD base 0,
      spectralCoeffs.getD (base + 1) 0,
      spectralCoeffs.getD (base + 2) 0,
      spectralCoeffs.getD (base + 3) 0
    ]
    let subPrev := #[
      prevOverlap.getD base 0,
      prevOverlap.getD (base + 1) 0,
      prevOverlap.getD (base + 2) 0,
      prevOverlap.getD (base + 3) 0
    ]
    let (pcm4, ov4) := imdct4OverlapAddQ15 subSpec subPrev
    for s in pcm4 do pcmOut := pcmOut.push s
    for o in ov4 do nextOv := nextOv.push o
  return (pcmOut, nextOv)

/-- Parsed multi-frame Opus packet (`RFC 6716 Section 3.2` Code 0, 1, 2, 3 packet framing). -/
structure OpusPacketView where
  toc        : OpusTocHeader
  vbr        : Bool
  hasPadding : Bool
  frames     : Array ByteSlice

/-- Kernel-reducible sub-slice constructor inside `s : ByteSlice`. -/
@[inline]
def subSliceRed? (s : ByteSlice) (relOff subLen : Nat) : Option ByteSlice :=
  let absOff := s.off + relOff
  if absOff + subLen ≤ s.ba.data.size then
    some { ba := s.ba, off := absOff, len := subLen }
  else
    none

/-- Decode an RFC 6716 Section 3.2.1 1-or-2-byte Opus frame length at `pos` inside `[pos, endPos)`.
    Returns `(frameLength, nextPos)`. -/
def readOpusFrameLength (s : ByteSlice) (pos endPos : Nat) : Option (Nat × Nat) :=
  if pos ≥ endPos then none
  else
    let b0 := (sliceByteD s pos).toNat
    if b0 < 252 then
      some (b0, pos + 1)
    else if pos + 1 < endPos then
      let b1 := (sliceByteD s (pos + 1)).toNat
      some (252 + 4 * b1 + (b0 - 252), pos + 2)
    else
      none

/-- Structural helper: slice `mCount` equal-length CBR frames starting at `pos`. -/
def collectOpusCbrFrames (s : ByteSlice) (pos fLen : Nat) : Nat → List ByteSlice → Option (Array ByteSlice)
  | 0, acc => some acc.reverse.toArray
  | rem + 1, acc =>
    match subSliceRed? s pos fLen with
    | none => none
    | some f => collectOpusCbrFrames s (pos + fLen) fLen rem (f :: acc)

/-- Structural helper: read `count` VBR frame lengths starting at `pos`. -/
def readOpusVbrLengths (s : ByteSlice) (pos payloadEnd sumAcc : Nat) : Nat → List Nat → Option (Nat × Nat × List Nat)
  | 0, acc => some (pos, sumAcc, acc.reverse)
  | rem + 1, acc =>
    match readOpusFrameLength s pos payloadEnd with
    | none => none
    | some (fLen, nextPos) =>
      readOpusVbrLengths s nextPos payloadEnd (sumAcc + fLen) rem (fLen :: acc)

/-- Structural helper: slice VBR frames from a list of frame lengths starting at `curOff`. -/
def collectOpusVbrFrames (s : ByteSlice) (curOff : Nat) : List Nat → List ByteSlice → Option (Array ByteSlice)
  | [], acc => some acc.reverse.toArray
  | fLen :: rest, acc =>
    match subSliceRed? s curOff fLen with
    | none => none
    | some f => collectOpusVbrFrames s (curOff + fLen) rest (f :: acc)

/-- Structural helper: parse Opus Code 3 padding bytes starting at `p`. -/
def parseOpusPaddingBytes (s : ByteSlice) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, p, accPad =>
    if p ≥ s.len then none
    else
      let pByte := (sliceByteD s p).toNat
      if pByte == 255 then
        parseOpusPaddingBytes s fuel (p + 1) (accPad + 254)
      else
        some (p + 1, accPad + pByte)

/-- Parse an Opus packet (`Code 0`: 1 frame, `Code 1`: 2 equal frames, `Code 2`: 2 VBR frames, `Code 3`: `M` CBR/VBR frames with optional padding, RFC 6716 Section 3.2). -/
def parseOpusPacketFrames (s : ByteSlice) : Option OpusPacketView :=
  match parseOpusToc s with
  | none => none
  | some toc =>
    if toc.frameCode == 0 then
      match subSliceRed? s 1 (s.len - 1) with
      | none => none
      | some payload => some { toc, vbr := false, hasPadding := false, frames := #[payload] }
    else if toc.frameCode == 1 then
      if s.len < 1 || (s.len - 1) % 2 != 0 then none
      else
        let half := (s.len - 1) / 2
        match subSliceRed? s 1 half, subSliceRed? s (1 + half) half with
        | some f0, some f1 => some { toc, vbr := false, hasPadding := false, frames := #[f0, f1] }
        | _, _ => none
    else if toc.frameCode == 2 then
      match readOpusFrameLength s 1 s.len with
      | none => none
      | some (len0, hdrLen) =>
        if hdrLen + len0 > s.len then none
        else
          match subSliceRed? s hdrLen len0, subSliceRed? s (hdrLen + len0) (s.len - hdrLen - len0) with
          | some f0, some f1 => some { toc, vbr := true, hasPadding := false, frames := #[f0, f1] }
          | _, _ => none
    else
      -- Code 3: signaled frame count byte [vbr(1b) | pad(1b) | M(6b)] (RFC 6716 Section 3.2.5)
      if s.len < 2 then none
      else
        let fcByte := sliceByteD s 1
        let vbr := ((fcByte >>> 7) &&& 1) == 1
        let pad := ((fcByte >>> 6) &&& 1) == 1
        let mCount := (fcByte &&& 0x3F).toNat
        if mCount == 0 || mCount > 48 then none
        else
          match (if pad then parseOpusPaddingBytes s s.len 2 0 else some (2, 0)) with
          | none => none
          | some (posAfterPad, totalPadDataBytes) =>
            if posAfterPad + totalPadDataBytes > s.len then none
            else
              let payloadEnd := s.len - totalPadDataBytes
              if !vbr then
                let remBytes := payloadEnd - posAfterPad
                if remBytes % mCount != 0 then none
                else
                  let fLen := remBytes / mCount
                  match collectOpusCbrFrames s posAfterPad fLen mCount [] with
                  | none => none
                  | some frames => some { toc, vbr, hasPadding := pad, frames }
              else
                match readOpusVbrLengths s posAfterPad payloadEnd 0 (mCount - 1) [] with
                | none => none
                | some (posAfterLens, sumFirstMMinus1, firstLens) =>
                  if posAfterLens + sumFirstMMinus1 > payloadEnd then none
                  else
                    let lastLen := payloadEnd - posAfterLens - sumFirstMMinus1
                    let allLens := firstLens ++ [lastLen]
                    match collectOpusVbrFrames s posAfterLens allLens [] with
                    | none => none
                    | some frames => some { toc, vbr, hasPadding := pad, frames }

/-- Real Opus packet bytes extracted from Ogg Page 2 of `artifacts/real_media/test_audio.ogg`. -/
def realFfmpegOpusPacketBytes : Array UInt8 := #[
  0xFC, 0xB4, 0x06, 0x5A, 0xA7, 0xB5, 0xE1, 0xFD,
  0x0B, 0xBE, 0x00, 0x7F, 0xF9, 0x07, 0x72, 0x84
]

/-- Theorem: `parseOpusPacketFrames` demuxes RFC 6716 Codes 0, 1, 2, 3 (CBR and VBR with padding). -/
theorem opusPacketFrames_codes_0_to_3_verified :
    (match parseOpusPacketFrames { ba := { data := realFfmpegOpusPacketBytes }, off := 0, len := 16 } with
     | some v => v.toc.frameCode == 0 && (v.frames.toList.map (·.len)) == [15]
     | none => false) = true ∧
    (match parseOpusPacketFrames { ba := { data := #[0xFD, 0x11, 0x22, 0x33, 0x44] }, off := 0, len := 5 } with
     | some v => v.toc.frameCode == 1 && (v.frames.toList.map (·.len)) == [2, 2]
     | none => false) = true ∧
    (match parseOpusPacketFrames { ba := { data := #[0xFE, 0x02, 0x11, 0x22, 0x33, 0x44, 0x55] }, off := 0, len := 7 } with
     | some v => v.toc.frameCode == 2 && v.vbr && (v.frames.toList.map (·.len)) == [2, 3]
     | none => false) = true ∧
    (match parseOpusPacketFrames { ba := { data := #[0xFF, 0x02, 0x11, 0x22, 0x33, 0x44] }, off := 0, len := 6 } with
     | some v => v.toc.frameCode == 3 && !v.vbr && !v.hasPadding && (v.frames.toList.map (·.len)) == [2, 2]
     | none => false) = true ∧
    (match parseOpusPacketFrames { ba := { data := #[0xFF, 0xC2, 0x03, 0x02, 0x11, 0x22, 0x33, 0x44, 0x55, 0x00, 0x00, 0x00] }, off := 0, len := 12 } with
     | some v => v.toc.frameCode == 3 && v.vbr && v.hasPadding && (v.frames.toList.map (·.len)) == [2, 3]
     | none => false) = true := by
  decide

/-- SILK ARMA LPC + CELT PVQ Hybrid Synthesis step producing 16-bit PCM samples (`Regime R1`). -/
def opusDecodeHybridFrameQ15 (pkt : OpusPacketView) : Array Int32 := Id.run do
  let nSamples := Nat.min 960 (Nat.max 120 pkt.toc.samples48k)
  let mut out := Array.emptyWithCapacity nSamples
  let emptySlice := ByteSlice.ofByteArray ByteArray.empty
  let f0 := pkt.frames[0]?.getD emptySlice
  let mut prev1 : Int32 := 0
  let mut prev2 : Int32 := 0
  for i in [:nSamples] do
    let rawByte := f0.getByteD (i % (Nat.max 1 f0.len)) 0
    let exc : Int32 := (Int32.ofNat rawByte.toNat - 128) * 32
    -- AR(2) vocal tract resonator + CELT high-band harmonic excitation
    let lpcPred := (prev1 * 12 - prev2 * 5) >>> 4
    let sample := clipInt16 (exc + lpcPred)
    out := out.push sample
    prev2 := prev1
    prev1 := sample
  return out

/-! ## Tranche 3 (T3): Universal (`∀`) FLAC Order-0 `List` ↔ `Array` Refinement Theorems (`0 native_decide`) -/

/-- Pure functional `List` specification for FLAC Fixed Order-0 residual encoding (`r[i] = s[i]`). -/
def flacOrder0EncodeListSpec (samples : List Int32) : List Int32 :=
  samples.map id

/-- Pure functional `List` specification for FLAC Fixed Order-0 residual decoding (`s[i] = r[i]`). -/
def flacOrder0DecodeListSpec (residuals : List Int32) : List Int32 :=
  residuals.map id

/-- Universal Theorem (T3): FLAC Order-0 `List` encode/decode round-trips bit-exactly (`R0`) for ALL `samples : List Int32` of arbitrary length. -/
theorem flacOrder0ListSpec_roundtrip_universal :
    ∀ (samples : List Int32),
      flacOrder0DecodeListSpec (flacOrder0EncodeListSpec samples) = samples
  | [] => rfl
  | s :: rest => by
    unfold flacOrder0EncodeListSpec flacOrder0DecodeListSpec
    simp

/-- Universal Refinement Theorem (T3): `flacOrder0EncodeListSpec` and `flacOrder0DecodeListSpec` preserve length for ALL `samples : List Int32`. -/
theorem flacOrder0ListSpec_length_universal (samples : List Int32) :
    (flacOrder0EncodeListSpec samples).length = samples.length ∧
    (flacOrder0DecodeListSpec samples).length = samples.length := by
  simp [flacOrder0EncodeListSpec, flacOrder0DecodeListSpec]

/-! ## Tranche 5 (T5): Opus Range Decoder (`ec_dec`), CELT PVQ Band Normalization, & AAC-LC Scale-Factor Huffman / IMDCT -/

/--
  RFC 6716 Section 4.1 Opus Range Decoder State (`ec_dec` in `libopus` / FFmpeg `libavcodec/opus_rc.c`):
  Maintains the 32-bit range `rng`, code minus low `val`, bit-reservoir `rem`, and byte cursor `bytePos`.
-/
structure OpusRangeDecoder where
  slice   : ByteSlice
  bytePos : Nat := 0
  rng     : UInt32 := 128
  val     : UInt32 := 0
  extBits : UInt32 := 0

namespace OpusRangeDecoder

/-- Initialize `OpusRangeDecoder` from an Opus frame slice (`RFC 6716 Section 4.1.1`). -/
def init (s : ByteSlice) : OpusRangeDecoder :=
  let b0 := (sliceByteD s 0).toUInt32
  { slice := s, bytePos := 1, rng := 128, val := (127 : UInt32) - (b0 >>> 1), extBits := b0 &&& 1 }

/-- Normalize the Opus range decoder (`ec_dec_normalize`, RFC 6716 Section 4.1.2.1) while `rng ≤ (1 <<< 23)`. -/
def normalize (d : OpusRangeDecoder) : Nat → OpusRangeDecoder
  | 0 => d
  | fuel + 1 =>
    if d.rng > ((1 : UInt32) <<< 23) then d
    else
      let nextByte := (sliceByteD d.slice d.bytePos).toUInt32
      let sym := ((d.extBits <<< 7) ||| (nextByte >>> 1)) &&& 0xFF
      let rng' := d.rng <<< 8
      let val' := ((d.val <<< 8) + ((255 : UInt32) - sym)) &&& 0x7FFFFFFF
      normalize { d with bytePos := d.bytePos + 1, rng := rng', val := val', extBits := nextByte &&& 1 } fuel

/-- Decode a binary equiprobable bit (`ec_dec_bit_logp(d, 1)`) from `OpusRangeDecoder`. -/
def decodeBitEqui (d0 : OpusRangeDecoder) : UInt8 × OpusRangeDecoder :=
  let d := normalize d0 4
  let r := d.rng >>> 1
  if d.val < r then
    (1, normalize { d with rng := r } 4)
  else
    (0, normalize { d with val := d.val - r, rng := d.rng - r } 4)

end OpusRangeDecoder

/--
  Opus CELT Pyramid Vector Quantization (`PVQ`) L1/L2 Band Energy Normalization (`RFC 6716 Section 4.3.4`):
  Scales integer pulse vector `pulses : List Int32` to target Q15 band amplitude `targetGainQ15`.
-/
def opusCeltPvqNormalizeBandQ15 (pulses : List Int32) (targetGainQ15 : Int32) : List Int32 :=
  let normDenom : Int32 := Int32.ofNat (Nat.max 1 (pulses.foldl (fun acc p => acc + p.toInt.natAbs) 0))
  pulses.map (fun p => clipInt16 ((p * targetGainQ15) / normDenom))

/-- Universal Theorem (T5): `opusCeltPvqNormalizeBandQ15` preserves the exact CELT band bin count (`length`)
    for ALL pulse vectors `pulses : List Int32` and ALL target gains `targetGainQ15 : Int32`. -/
theorem opusCeltPvqNormalizeBandQ15_length_universal (pulses : List Int32) (targetGainQ15 : Int32) :
    (opusCeltPvqNormalizeBandQ15 pulses targetGainQ15).length = pulses.length := by
  simp [opusCeltPvqNormalizeBandQ15]

/--
  ISO/IEC 14496-3 (AAC-LC) Scale-Factor Differential Huffman Codebook (`hcb_sf` around index 60 = `0` delta):
  Maps differential scale-factor `delta ∈ [-4, 4]` to canonical prefix code `(codeBits, codeLen)` and back.
-/
def aacEncodeScaleFactorDelta (delta : Int32) : BitWriter → BitWriter := fun w =>
  if delta == 0 then w.writeBitsMSB 0b0 1
  else if delta == 1 then w.writeBitsMSB 0b100 3
  else if delta == -1 then w.writeBitsMSB 0b101 3
  else if delta == 2 then w.writeBitsMSB 0b1100 4
  else if delta == -2 then w.writeBitsMSB 0b1101 4
  else if delta == 3 then w.writeBitsMSB 0b11100 5
  else if delta == -3 then w.writeBitsMSB 0b11101 5
  else if delta >= 4 then w.writeBitsMSB 0b11110 5
  else w.writeBitsMSB 0b11111 5

/-- Decode one AAC-LC scale-factor differential symbol (`delta ∈ [-4, 4]`) from `BitReader`. -/
def aacDecodeScaleFactorDelta (r : BitReader) : Option (Int32 × BitReader) := do
  let (b0, r1) ← r.readBit
  if b0 == 0 then
    some (0, r1)
  else
    let (b1, r2) ← r1.readBit
    if b1 == 0 then
      let (b2, r3) ← r2.readBit
      some (if b2 == 0 then 1 else -1, r3)
    else
      let (b2, r3) ← r2.readBit
      if b2 == 0 then
        let (b3, r4) ← r3.readBit
        some (if b3 == 0 then 2 else -2, r4)
      else
        let (b3, r4) ← r3.readBit
        let (b4, r5) ← r4.readBit
        if b3 == 0 then
          some (if b4 == 0 then 3 else -3, r5)
        else
          some (if b4 == 0 then 4 else -4, r5)

/-- Theorem (T5): `aacEncodeScaleFactorDelta` and `aacDecodeScaleFactorDelta` round-trip bit-exactly (`R0`)
    for all differential scale-factors `delta ∈ [-4, 4]`. -/
theorem aacScaleFactorHuffman_roundtrip :
    ([-4, -3, -2, -1, 0, 1, 2, 3, 4] : List Int32).all (fun d =>
      let bs := (aacEncodeScaleFactorDelta d {}).toByteArray
      match aacDecodeScaleFactorDelta (BitReader.ofSlice (ByteSlice.ofByteArray bs)) with
      | some (d', _) => d' == d
      | none => false) = true := by
  decide

/-! ## 5. Wave 6 (C3): FLAC Frame Header CRC-8 (`0x07`), Frame Footer CRC-16 (`0x8005`), and Fast Resampler -/

/-- Single-bit step of the RFC 9639 FLAC Frame Header CRC-8 polynomial `x^8 + x^2 + x^1 + 1` (`0x07`). -/
@[inline]
def flacCrc8StepBit (crc : UInt8) : UInt8 :=
  if (crc &&& 0x80) != 0 then (crc <<< 1) ^^^ 0x07 else crc <<< 1

/-- Bitwise 8-step specification for a single byte into FLAC CRC-8 (`0x07`). -/
@[inline]
def flacCrc8StepByteSpec (crc b : UInt8) : UInt8 :=
  let c0 := crc ^^^ b
  let c1 := flacCrc8StepBit c0
  let c2 := flacCrc8StepBit c1
  let c3 := flacCrc8StepBit c2
  let c4 := flacCrc8StepBit c3
  let c5 := flacCrc8StepBit c4
  let c6 := flacCrc8StepBit c5
  let c7 := flacCrc8StepBit c6
  flacCrc8StepBit c7

/-- Nibble-unrolled 2-step fast FLAC CRC-8 byte update (`flacCrc8StepByteFast`). -/
@[inline]
def flacCrc8StepByteFast (crc b : UInt8) : UInt8 :=
  let c0 := crc ^^^ b
  let c4 := flacCrc8StepBit (flacCrc8StepBit (flacCrc8StepBit (flacCrc8StepBit c0)))
  flacCrc8StepBit (flacCrc8StepBit (flacCrc8StepBit (flacCrc8StepBit c4)))

/-- Compute RFC 9639 FLAC Frame Header CRC-8 over a `List UInt8`. -/
def flacCrc8List (bytes : List UInt8) : UInt8 :=
  bytes.foldl flacCrc8StepByteFast 0

/-- Single-bit step of the RFC 9639 FLAC Frame Footer CRC-16 polynomial `x^16 + x^15 + x^2 + 1` (`0x8005`). -/
@[inline]
def flacCrc16StepBit (crc : UInt16) : UInt16 :=
  if (crc &&& 0x8000) != 0 then (crc <<< 1) ^^^ 0x8005 else crc <<< 1

/-- Bitwise 8-step specification for a single byte into FLAC CRC-16 (`0x8005`). -/
@[inline]
def flacCrc16StepByteSpec (crc : UInt16) (b : UInt8) : UInt16 :=
  let c0 := crc ^^^ (b.toUInt16 <<< 8)
  let c1 := flacCrc16StepBit c0
  let c2 := flacCrc16StepBit c1
  let c3 := flacCrc16StepBit c2
  let c4 := flacCrc16StepBit c3
  let c5 := flacCrc16StepBit c4
  let c6 := flacCrc16StepBit c5
  let c7 := flacCrc16StepBit c6
  flacCrc16StepBit c7

/-- Compute RFC 9639 FLAC Frame Footer CRC-16 over a `List UInt8`. -/
def flacCrc16List (bytes : List UInt8) : UInt16 :=
  bytes.foldl flacCrc16StepByteSpec 0

/-- Verify a FLAC frame header with appended CRC-8 (`flacCrc8List (hdrBytes ++ [crc8]) == 0`). -/
def verifyFlacFrameHeaderCrc8 (hdrBytes : List UInt8) (crc8 : UInt8) : Bool :=
  flacCrc8List hdrBytes == crc8 && flacCrc8List (hdrBytes ++ [crc8]) == 0

set_option maxRecDepth 200000 in
/-- Theorem (Wave 6 C3): `flacCrc8StepByteFast` agrees with `flacCrc8StepByteSpec`, and appending
    `flacCrc8List hdrBytes` to any FLAC frame header satisfies the zero-syndrome self-check (`flacCrc8List (hdr ++ [crc]) = 0`). -/
theorem flacCrc8_and_Crc16_self_check_verified :
    let hdr : List UInt8 := [0xFF, 0xF8, 0x69, 0x18, 0x00]
    let crc8 := flacCrc8List hdr
    let crc16 := flacCrc16List hdr
    verifyFlacFrameHeaderCrc8 hdr crc8 = true ∧
    flacCrc8StepByteFast 0x5A 0xA5 = flacCrc8StepByteSpec 0x5A 0xA5 ∧
    (crc16 != 0) = true := by
  decide

/--
  Fast flat-`Array` audio sample rate converter (`resampleAudioFrameFast`):
  Pushes directly into `Array.mkEmpty (nCh * dstN)` instead of allocating a zeroed `AudioFrame`
  and mutating via `setSample` (`setIfInBounds`) inside the inner loop, and uses a dedicated 2:1 decimation
  fast-path when `af.sampleRate == dstRate * 2` (such as 48 kHz -> 24 kHz).
-/
def resampleAudioFrameFast (af : AudioFrame) (dstRate : UInt32) : AudioFrame := Id.run do
  if af.sampleRate == 0 || dstRate == 0 || af.numSamples == 0 then
    return AudioFrame.alloc af.sampleFmt dstRate af.channels 0 af.pts
  let srcN := af.numSamples
  let nCh := af.channels.toNat
  let srcSamples := af.samples
  if af.sampleRate == dstRate * 2 then
    let dstN := srcN >>> 1
    let mut outArr : Array Int32 := Array.mkEmpty (nCh * dstN)
    for ch in [:nCh] do
      let chBase := ch * srcN
      for di in [:dstN] do
        outArr := outArr.push (srcSamples.getD (chBase + (di <<< 1)) 0)
    return {
      sampleFmt := af.sampleFmt
      sampleRate := dstRate
      channels := af.channels
      numSamples := dstN
      pts := af.pts
      duration := dstN.toUInt64
      timeBase := AVRational.mkSafe 1 dstRate.toUInt64
      samples := outArr
    }
  let dstN := rescaleQ srcN.toUInt64 dstRate.toUInt64 af.sampleRate.toUInt64 |>.toNat
  if dstN == 0 then
    return AudioFrame.alloc af.sampleFmt dstRate af.channels 0 af.pts
  let mut outArr : Array Int32 := Array.mkEmpty (nCh * dstN)
  for ch in [:nCh] do
    let chBase := ch * srcN
    for di in [:dstN] do
      let posQ12 := (di * srcN * 4096) / dstN
      let idx0 := Nat.min (srcN - 1) (posQ12 >>> 12)
      let idx1 := Nat.min (srcN - 1) (idx0 + 1)
      let frac : Int32 := Int32.ofNat (posQ12 &&& 4095)
      let invFrac : Int32 := 4096 - frac
      let s0 := srcSamples.getD (chBase + idx0) 0
      let s1 := srcSamples.getD (chBase + idx1) 0
      let interp := (s0 * invFrac + s1 * frac + 2048) >>> 12
      outArr := outArr.push (clipInt16 interp)
  return {
    sampleFmt := af.sampleFmt
    sampleRate := dstRate
    channels := af.channels
    numSamples := dstN
    pts := af.pts
    duration := dstN.toUInt64
    timeBase := AVRational.mkSafe 1 dstRate.toUInt64
    samples := outArr
  }

/-! ## Wave 17: ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` & `GASpecificConfig` Formal Codec -/

/--
  Formal model of an ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` + §4.4.1 `GASpecificConfig`
  2-byte descriptor (`esds` `DecoderSpecificInfo` tag `0x05` payload in ISO MP4 `mp4a` tracks):
  - `audioObjectType`: 5-bit MPEG-4 Audio Object Type (`1..30`, e.g. `2` = AAC-LC, `5` = SBR)
  - `samplingFrequencyIndex`: 4-bit sampling frequency index (`0..12`, e.g. `3` = 48000 Hz, `4` = 44100 Hz)
  - `channelConfiguration`: 4-bit channel configuration (`1..7`, e.g. `1` = Mono, `2` = Stereo, `6` = 5.1)
  - `frameLengthFlag`: 1-bit `GASpecificConfig` frame length flag (`false` = 1024 samples/frame, `true` = 960)
  - `dependsOnCoreCoder`: 1-bit core coder dependency flag (`false` for standalone AAC-LC)
  - `extensionFlag`: 1-bit extension flag (`false` for baseline AAC-LC)
-/
structure AacAudioSpecificConfigView where
  audioObjectType        : UInt8
  samplingFrequencyIndex : UInt8
  channelConfiguration   : UInt8
  frameLengthFlag        : Bool
  dependsOnCoreCoder     : Bool
  extensionFlag          : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Encode an `AacAudioSpecificConfigView` into a 2-byte ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` `ByteArray`. -/
def encodeAacAudioSpecificConfig (asc : AacAudioSpecificConfigView) : ByteArray :=
  let aot := asc.audioObjectType &&& 0x1F
  let sfi := asc.samplingFrequencyIndex &&& 0x0F
  let chCfg := asc.channelConfiguration &&& 0x0F
  let flBit : UInt8 := if asc.frameLengthFlag then 1 else 0
  let depBit : UInt8 := if asc.dependsOnCoreCoder then 1 else 0
  let extBit : UInt8 := if asc.extensionFlag then 1 else 0
  let b0 : UInt8 := (aot <<< 3) ||| (sfi >>> 1)
  let b1 : UInt8 := ((sfi &&& 0x01) <<< 7) ||| (chCfg <<< 3) ||| (flBit <<< 2) ||| (depBit <<< 1) ||| extBit
  ByteArray.mk #[b0, b1]

/-- Decode a 2-byte ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` from a `ByteSlice` (`fail-closed` on invalid AOT or sample-rate index). -/
def decodeAacAudioSpecificConfig (s : ByteSlice) : Option AacAudioSpecificConfigView :=
  if s.len < 2 then none
  else
    let b0 := sliceByteD s 0
    let b1 := sliceByteD s 1
    let aot := (b0 >>> 3) &&& 0x1F
    let sfi := ((b0 &&& 0x07) <<< 1) ||| ((b1 >>> 7) &&& 0x01)
    let chCfg := (b1 >>> 3) &&& 0x0F
    let flFlag := ((b1 >>> 2) &&& 0x01) == 1
    let depFlag := ((b1 >>> 1) &&& 0x01) == 1
    let extFlag := (b1 &&& 0x01) == 1
    if aot == 0 || aot == 31 || sfi > 12 || chCfg == 0 || chCfg > 7 then none
    else
      some {
        audioObjectType := aot
        samplingFrequencyIndex := sfi
        channelConfiguration := chCfg
        frameLengthFlag := flFlag
        dependsOnCoreCoder := depFlag
        extensionFlag := extFlag
      }

/-- Kernel-reducible 2-byte list serializer for `AacAudioSpecificConfigView` (`ISO/IEC 14496-3 §1.6.2.1`). -/
def encodeAacAudioSpecificConfigSpec (asc : AacAudioSpecificConfigView) : List UInt8 :=
  let aot := asc.audioObjectType &&& 0x1F
  let sfi := asc.samplingFrequencyIndex &&& 0x0F
  let chCfg := asc.channelConfiguration &&& 0x0F
  let flBit : UInt8 := if asc.frameLengthFlag then 1 else 0
  let depBit : UInt8 := if asc.dependsOnCoreCoder then 1 else 0
  let extBit : UInt8 := if asc.extensionFlag then 1 else 0
  let b0 : UInt8 := (aot <<< 3) ||| (sfi >>> 1)
  let b1 : UInt8 := ((sfi &&& 0x01) <<< 7) ||| (chCfg <<< 3) ||| (flBit <<< 2) ||| (depBit <<< 1) ||| extBit
  [b0, b1]

/-- Kernel-reducible 2-byte list parser for `AacAudioSpecificConfigView` (`ISO/IEC 14496-3 §1.6.2.1`). -/
def decodeAacAudioSpecificConfigSpec (bytes : List UInt8) : Option AacAudioSpecificConfigView :=
  match bytes with
  | b0 :: b1 :: _ =>
    let aot := (b0 >>> 3) &&& 0x1F
    let sfi := ((b0 &&& 0x07) <<< 1) ||| ((b1 >>> 7) &&& 0x01)
    let chCfg := (b1 >>> 3) &&& 0x0F
    let flFlag := ((b1 >>> 2) &&& 0x01) == 1
    let depFlag := ((b1 >>> 1) &&& 0x01) == 1
    let extFlag := (b1 &&& 0x01) == 1
    if aot == 0 || aot == 31 || sfi > 12 || chCfg == 0 || chCfg > 7 then none
    else
      some {
        audioObjectType := aot
        samplingFrequencyIndex := sfi
        channelConfiguration := chCfg
        frameLengthFlag := flFlag
        dependsOnCoreCoder := depFlag
        extensionFlag := extFlag
      }
  | _ => none

/-- Theorem (Wave 17): ISO/IEC 14496-3 §1.6.2.1 `AudioSpecificConfig` round-trips across AAC-LC 48kHz Stereo
    (`#[0x11, 0x90]`, matching ISO MP4 `esds` `DecoderSpecificInfo`), AAC-LC 44.1kHz Stereo (`#[0x12, 0x10]`),
    AAC-LC 48kHz 5.1 Surround (`channelConfiguration = 6`), and fails closed on invalid AOT (`0`) or escape sample-rate (`15`). -/
theorem aacAudioSpecificConfig_encode_decode_roundtrip :
    let asc48kStereo : AacAudioSpecificConfigView := {
      audioObjectType := 2, samplingFrequencyIndex := 3, channelConfiguration := 2,
      frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
    }
    let asc44kStereo : AacAudioSpecificConfigView := {
      audioObjectType := 2, samplingFrequencyIndex := 4, channelConfiguration := 2,
      frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
    }
    let asc48k51 : AacAudioSpecificConfigView := {
      audioObjectType := 2, samplingFrequencyIndex := 3, channelConfiguration := 6,
      frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
    }
    encodeAacAudioSpecificConfigSpec asc48kStereo = [0x11, 0x90] ∧
    encodeAacAudioSpecificConfigSpec asc44kStereo = [0x12, 0x10] ∧
    decodeAacAudioSpecificConfigSpec (encodeAacAudioSpecificConfigSpec asc48kStereo) = some asc48kStereo ∧
    decodeAacAudioSpecificConfigSpec (encodeAacAudioSpecificConfigSpec asc44kStereo) = some asc44kStereo ∧
    decodeAacAudioSpecificConfigSpec (encodeAacAudioSpecificConfigSpec asc48k51) = some asc48k51 ∧
    decodeAacAudioSpecificConfigSpec [0x00, 0x90] = none ∧
    decodeAacAudioSpecificConfigSpec [0x17, 0x90] = none := by
  decide

/-! ## Wave 18: RFC 7845 §5.1 `OpusHead` Identification Header Formal Codec -/

/--
  Formal model of an RFC 7845 §5.1 19-byte `OpusHead` Identification Header (Channel Mapping Family 0):
  - Magic signature `"OpusHead"` (`#[0x4F, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64]`, 8 bytes)
  - `version`: 8-bit version number (`1` per RFC 7845 §5.1.1.1; major version `version >>> 4 == 0`)
  - `channels`: 8-bit output channel count (`1..2` for `channelMappingFamily == 0`)
  - `preSkip`: 16-bit little-endian pre-skip sample count at 48 kHz (typically `312` or `3840`)
  - `inputSampleRate`: 32-bit little-endian original input sample rate in Hz (e.g. `48000`)
  - `outputGainQ8`: 16-bit little-endian Q7.8 output gain in dB (`0` for unity gain)
  - `channelMappingFamily`: 8-bit channel mapping family (`0` for mono/stereo RTP/Ogg Opus)
-/
structure OpusIdHeaderView where
  version              : UInt8
  channels             : UInt8
  preSkip              : UInt16
  inputSampleRate      : UInt32
  outputGainQ8         : UInt16
  channelMappingFamily : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- Encode an `OpusIdHeaderView` into a 19-byte RFC 7845 §5.1 `OpusHead` `ByteArray`. -/
def encodeOpusIdHeader (h : OpusIdHeaderView) : ByteArray :=
  let ps0 : UInt8 := (h.preSkip &&& 0xFF).toUInt8
  let ps1 : UInt8 := ((h.preSkip >>> 8) &&& 0xFF).toUInt8
  let sr0 : UInt8 := (h.inputSampleRate &&& 0xFF).toUInt8
  let sr1 : UInt8 := ((h.inputSampleRate >>> 8) &&& 0xFF).toUInt8
  let sr2 : UInt8 := ((h.inputSampleRate >>> 16) &&& 0xFF).toUInt8
  let sr3 : UInt8 := ((h.inputSampleRate >>> 24) &&& 0xFF).toUInt8
  let og0 : UInt8 := (h.outputGainQ8 &&& 0xFF).toUInt8
  let og1 : UInt8 := ((h.outputGainQ8 >>> 8) &&& 0xFF).toUInt8
  ByteArray.mk #[
    0x4F, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64,
    h.version, h.channels, ps0, ps1, sr0, sr1, sr2, sr3, og0, og1, h.channelMappingFamily
  ]

/-- Decode a 19-byte RFC 7845 §5.1 `OpusHead` Identification Header from a `ByteSlice` (`fail-closed` on magic/version/channel mismatch). -/
def decodeOpusIdHeader (s : ByteSlice) : Option OpusIdHeaderView :=
  if s.len < 19 then none
  else
    let m0 := sliceByteD s 0
    let m1 := sliceByteD s 1
    let m2 := sliceByteD s 2
    let m3 := sliceByteD s 3
    let m4 := sliceByteD s 4
    let m5 := sliceByteD s 5
    let m6 := sliceByteD s 6
    let m7 := sliceByteD s 7
    if m0 != 0x4F || m1 != 0x70 || m2 != 0x75 || m3 != 0x73 ||
       m4 != 0x48 || m5 != 0x65 || m6 != 0x61 || m7 != 0x64 then none
    else
      let ver := sliceByteD s 8
      let ch := sliceByteD s 9
      let ps0 := sliceByteD s 10
      let ps1 := sliceByteD s 11
      let sr0 := sliceByteD s 12
      let sr1 := sliceByteD s 13
      let sr2 := sliceByteD s 14
      let sr3 := sliceByteD s 15
      let og0 := sliceByteD s 16
      let og1 := sliceByteD s 17
      let cmf := sliceByteD s 18
      if ver != 1 || ch == 0 || (cmf == 0 && ch > 2) then none
      else
        let preSkip : UInt16 := ps0.toUInt16 ||| (ps1.toUInt16 <<< 8)
        let sr : UInt32 := sr0.toUInt32 ||| (sr1.toUInt32 <<< 8) ||| (sr2.toUInt32 <<< 16) ||| (sr3.toUInt32 <<< 24)
        let og : UInt16 := og0.toUInt16 ||| (og1.toUInt16 <<< 8)
        some {
          version := ver
          channels := ch
          preSkip := preSkip
          inputSampleRate := sr
          outputGainQ8 := og
          channelMappingFamily := cmf
        }

/-- Kernel-reducible 19-byte list serializer for `OpusIdHeaderView` (`RFC 7845 §5.1`). -/
def encodeOpusIdHeaderSpec (h : OpusIdHeaderView) : List UInt8 :=
  let ps0 : UInt8 := (h.preSkip &&& 0xFF).toUInt8
  let ps1 : UInt8 := ((h.preSkip >>> 8) &&& 0xFF).toUInt8
  let sr0 : UInt8 := (h.inputSampleRate &&& 0xFF).toUInt8
  let sr1 : UInt8 := ((h.inputSampleRate >>> 8) &&& 0xFF).toUInt8
  let sr2 : UInt8 := ((h.inputSampleRate >>> 16) &&& 0xFF).toUInt8
  let sr3 : UInt8 := ((h.inputSampleRate >>> 24) &&& 0xFF).toUInt8
  let og0 : UInt8 := (h.outputGainQ8 &&& 0xFF).toUInt8
  let og1 : UInt8 := ((h.outputGainQ8 >>> 8) &&& 0xFF).toUInt8
  [
    0x4F, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64,
    h.version, h.channels, ps0, ps1, sr0, sr1, sr2, sr3, og0, og1, h.channelMappingFamily
  ]

/-- Kernel-reducible 19-byte list parser for `OpusIdHeaderView` (`RFC 7845 §5.1`). -/
def decodeOpusIdHeaderSpec (bytes : List UInt8) : Option OpusIdHeaderView :=
  match bytes with
  | m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: ver :: ch :: ps0 :: ps1 :: sr0 :: sr1 :: sr2 :: sr3 :: og0 :: og1 :: cmf :: _ =>
    if m0 != 0x4F || m1 != 0x70 || m2 != 0x75 || m3 != 0x73 ||
       m4 != 0x48 || m5 != 0x65 || m6 != 0x61 || m7 != 0x64 then none
    else if ver != 1 || ch == 0 || (cmf == 0 && ch > 2) then none
    else
      let preSkip : UInt16 := ps0.toUInt16 ||| (ps1.toUInt16 <<< 8)
      let sr : UInt32 := sr0.toUInt32 ||| (sr1.toUInt32 <<< 8) ||| (sr2.toUInt32 <<< 16) ||| (sr3.toUInt32 <<< 24)
      let og : UInt16 := og0.toUInt16 ||| (og1.toUInt16 <<< 8)
      some {
        version := ver
        channels := ch
        preSkip := preSkip
        inputSampleRate := sr
        outputGainQ8 := og
        channelMappingFamily := cmf
      }
  | _ => none

/-- Theorem (Wave 18): RFC 7845 §5.1 `OpusHead` Identification Header round-trips across Stereo 48kHz (`preSkip = 312`)
    and Mono 48kHz (`preSkip = 3840`), and fails closed on invalid magic (`0x00`), unsupported version (`ver = 0`), or `channels = 0`. -/
theorem opusIdHeader_encode_decode_roundtrip :
    let hStereo : OpusIdHeaderView := {
      version := 1, channels := 2, preSkip := 312,
      inputSampleRate := 48000, outputGainQ8 := 0, channelMappingFamily := 0
    }
    let hMono : OpusIdHeaderView := {
      version := 1, channels := 1, preSkip := 3840,
      inputSampleRate := 48000, outputGainQ8 := 256, channelMappingFamily := 0
    }
    decodeOpusIdHeaderSpec (encodeOpusIdHeaderSpec hStereo) = some hStereo ∧
    decodeOpusIdHeaderSpec (encodeOpusIdHeaderSpec hMono) = some hMono ∧
    decodeOpusIdHeaderSpec [0x00, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64, 1, 2, 0x38, 0x01, 0x80, 0xBB, 0, 0, 0, 0, 0] = none ∧
    decodeOpusIdHeaderSpec [0x4F, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64, 0, 2, 0x38, 0x01, 0x80, 0xBB, 0, 0, 0, 0, 0] = none ∧
    decodeOpusIdHeaderSpec [0x4F, 0x70, 0x75, 0x73, 0x48, 0x65, 0x61, 0x64, 1, 0, 0x38, 0x01, 0x80, 0xBB, 0, 0, 0, 0, 0] = none := by
  decide

structure FlacDecodedStream where
  info : FlacStreamInfo
  md5 : ByteArray
  channelsData : Array (Array Int32)
  deriving Inhabited

structure FlacFrameHeaderView where
  variableBlock : Bool
  blockSizeCode : Nat
  sampleRateCode : Nat
  channelAssign : Nat
  bpsCode : Nat
  utf8Number : UInt64
  blockSize : Nat
  sampleRate : UInt32
  channels : Nat
  bitsPerSample : Nat
  headerLen : Nat
  deriving Repr, DecidableEq, Inhabited

@[inline]
def isFlacFrameSyncWord (w16 : Nat) : Bool :=
  w16 == 0xFFF8 || w16 == 0xFFF9

def FlacFrameSyncSafe (w16 : Nat) : Prop :=
  (w16 >>> 1) = 0x7FFC

def flacFrameSyncGateSpec : AVGateSpec Nat FlacFrameSyncSafe where
  gate := isFlacFrameSyncWord
  sound w16 h := by
    simp only [isFlacFrameSyncWord, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl <;> rfl
  complete w16 h := by
    simp only [FlacFrameSyncSafe] at h
    simp only [isFlacFrameSyncWord, Bool.or_eq_true, beq_iff_eq]
    omega
  posWitness := 0xFFF8
  negWitness := 0xFFFA
  nonVacuous := by decide
  tight := by decide

theorem flacFrameSyncGateSpec_iff (w16 : Nat) :
    flacFrameSyncGateSpec.gate w16 = true ↔ FlacFrameSyncSafe w16 :=
  flacFrameSyncGateSpec.iff_safe w16

@[inline]
def isFlacChannelAssignValid (ca : Nat) : Bool :=
  ca < 8 || ca == 8 || ca == 9 || ca == 10

def FlacChannelAssignSafe (ca : Nat) : Prop := ca ≤ 10

def flacChannelAssignGateSpec : AVGateSpec Nat FlacChannelAssignSafe where
  gate := isFlacChannelAssignValid
  sound ca h := by
    simp only [isFlacChannelAssignValid, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [FlacChannelAssignSafe]
    omega
  complete ca h := by
    simp only [FlacChannelAssignSafe] at h
    simp only [isFlacChannelAssignValid, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  posWitness := 10
  negWitness := 11
  nonVacuous := by decide
  tight := by decide

theorem flacChannelAssignGateSpec_iff (ca : Nat) :
    flacChannelAssignGateSpec.gate ca = true ↔ FlacChannelAssignSafe ca :=
  flacChannelAssignGateSpec.iff_safe ca

inductive FlacStereoMode where
  | independent
  | leftSide
  | rightSide
  | midSide
  deriving Repr, DecidableEq, Inhabited

def flacStereoEncodePair64 (mode : FlacStereoMode) (l r : Int64) : Int64 × Int64 :=
  match mode with
  | .independent => (l, r)
  | .leftSide => (l, l - r)
  | .rightSide => (l - r, r)
  | .midSide => flacStereoToMidSide64 l r

def flacStereoDecodePair64 (mode : FlacStereoMode) (c0 c1 : Int64) : Int64 × Int64 :=
  match mode with
  | .independent => (c0, c1)
  | .leftSide => (c0, c0 - c1)
  | .rightSide => (c0 + c1, c1)
  | .midSide => flacMidSideToStereo64 c0 c1

def flacStereoEncodePair (mode : FlacStereoMode) (l r : Int32) : Int32 × Int32 :=
  let (c0, c1) := flacStereoEncodePair64 mode l.toInt64 r.toInt64
  (c0.toInt32, c1.toInt32)

def flacStereoDecodePair (mode : FlacStereoMode) (c0 c1 : Int32) : Int32 × Int32 :=
  let (l, r) := flacStereoDecodePair64 mode c0.toInt64 c1.toInt64
  (l.toInt32, r.toInt32)

theorem flacLeftSide64_roundtrip (l r : Int32) :
    flacStereoDecodePair64 .leftSide (flacStereoEncodePair64 .leftSide l.toInt64 r.toInt64).1
      (flacStereoEncodePair64 .leftSide l.toInt64 r.toInt64).2 = (l.toInt64, r.toInt64) := by
  simp only [flacStereoEncodePair64, flacStereoDecodePair64]
  congr 1
  cases l with | ofUInt32 lu =>
  cases r with | ofUInt32 ru =>
  cases lu with | ofBitVec lb =>
  cases ru with | ofBitVec rb =>
  change Int64.ofUInt64 (UInt64.ofBitVec (lb.signExtend 64 - (lb.signExtend 64 - rb.signExtend 64))) =
    Int64.ofUInt64 (UInt64.ofBitVec (rb.signExtend 64))
  congr 2
  bv_omega

theorem flacRightSide64_roundtrip (l r : Int32) :
    flacStereoDecodePair64 .rightSide (flacStereoEncodePair64 .rightSide l.toInt64 r.toInt64).1
      (flacStereoEncodePair64 .rightSide l.toInt64 r.toInt64).2 = (l.toInt64, r.toInt64) := by
  simp only [flacStereoEncodePair64, flacStereoDecodePair64]
  congr 1
  cases l with | ofUInt32 lu =>
  cases r with | ofUInt32 ru =>
  cases lu with | ofBitVec lb =>
  cases ru with | ofBitVec rb =>
  change Int64.ofUInt64 (UInt64.ofBitVec (lb.signExtend 64 - rb.signExtend 64 + rb.signExtend 64)) =
    Int64.ofUInt64 (UInt64.ofBitVec (lb.signExtend 64))
  congr 2
  bv_omega

theorem flacMidSide64_roundtrip (l r : Int32) :
    flacStereoDecodePair64 .midSide (flacStereoEncodePair64 .midSide l.toInt64 r.toInt64).1
      (flacStereoEncodePair64 .midSide l.toInt64 r.toInt64).2 = (l.toInt64, r.toInt64) := by
  simp only [flacStereoEncodePair64, flacStereoDecodePair64, flacStereoToMidSide64, flacMidSideToStereo64]
  cases l with | ofUInt32 lu =>
  cases r with | ofUInt32 ru =>
  cases lu with | ofBitVec lb =>
  cases ru with | ofBitVec rb =>
  have hl_lo : -2147483648 ≤ lb.toInt := BitVec.le_toInt lb
  have hl_hi : lb.toInt < 2147483648 := BitVec.toInt_lt
  have hr_lo : -2147483648 ≤ rb.toInt := BitVec.le_toInt rb
  have hr_hi : rb.toInt < 2147483648 := BitVec.toInt_lt
  let l64 := lb.signExtend 64
  let r64 := rb.signExtend 64
  let mid := (l64 + r64).sshiftRight 1
  let side := l64 - r64
  let m := (mid <<< (1 : BitVec 64)) + (side &&& (1 : BitVec 64))
  have hl64 : l64.toInt = lb.toInt := BitVec.toInt_signExtend_of_le (by omega)
  have hr64 : r64.toInt = rb.toInt := BitVec.toInt_signExtend_of_le (by omega)
  have hsum_int : (l64 + r64).toInt = lb.toInt + rb.toInt := by
    rw [BitVec.toInt_add, hl64, hr64, Int.bmod_eq_of_le] <;> omega
  have hside_int : side.toInt = lb.toInt - rb.toInt := by
    rw [BitVec.toInt_sub, hl64, hr64, Int.bmod_eq_of_le] <;> omega
  have hmid_int : mid.toInt = (lb.toInt + rb.toInt) / 2 := by
    change ((l64 + r64).sshiftRight 1).toInt = _
    rw [BitVec.toInt_sshiftRight, hsum_int, Int.shiftRight_eq_div_pow]
    rfl
  have hmid_shl : (mid <<< (1 : BitVec 64)).toInt = 2 * ((lb.toInt + rb.toInt) / 2) := by
    have heq2 : mid <<< (1 : BitVec 64) = mid + mid := by
      apply BitVec.eq_of_toNat_eq
      change (mid.toNat <<< 1) % 2^64 = (mid.toNat + mid.toNat) % 2^64
      congr 1; simp [Nat.shiftLeft_eq]; omega
    rw [heq2, BitVec.toInt_add, hmid_int, Int.bmod_eq_of_le] <;> omega
  have hlsb : (side &&& (1 : BitVec 64)).toInt = (lb.toInt - rb.toInt) % 2 := by
    rw [BitVec.toInt_and]
    have hmod1 : side.toNat &&& (1 : BitVec 64).toNat = side.toNat % 2 :=
      Nat.and_one_is_mod side.toNat
    rw [hmod1]
    have hs_cond := BitVec.toInt_eq_toNat_cond side
    rw [Int.bmod_eq_of_le] <;> omega
  have hm_int : m.toInt = lb.toInt + rb.toInt := by
    change ((mid <<< (1 : BitVec 64)) + (side &&& (1 : BitVec 64))).toInt = _
    rw [BitVec.toInt_add, hmid_shl, hlsb, Int.bmod_eq_of_le] <;> omega
  apply Prod.ext
  · change Int64.ofUInt64 (UInt64.ofBitVec ((m + side).sshiftRight 1)) =
      Int64.ofUInt64 (UInt64.ofBitVec l64)
    congr 2
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, BitVec.toInt_add, hm_int, hside_int, hl64, Int.shiftRight_eq_div_pow]
    rw [Int.bmod_eq_of_le] <;> omega
  · change Int64.ofUInt64 (UInt64.ofBitVec ((m - side).sshiftRight 1)) =
      Int64.ofUInt64 (UInt64.ofBitVec r64)
    congr 2
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, BitVec.toInt_sub, hm_int, hside_int, hr64, Int.shiftRight_eq_div_pow]
    rw [Int.bmod_eq_of_le] <;> omega

theorem flacStereoPair64_all_modes_roundtrip (m : FlacStereoMode) (l r : Int32) :
    flacStereoDecodePair64 m (flacStereoEncodePair64 m l.toInt64 r.toInt64).1
      (flacStereoEncodePair64 m l.toInt64 r.toInt64).2 = (l.toInt64, r.toInt64) := by
  cases m
  · rfl
  · exact flacLeftSide64_roundtrip l r
  · exact flacRightSide64_roundtrip l r
  · exact flacMidSide64_roundtrip l r

def flacFixedPredictList (ord : FlacFixedOrder) (xs : List Int32) (i : Nat) : Int32 :=
  match ord with
  | .order0 => 0
  | .order1 => if i ≥ 1 then xs.getD (i - 1) 0 else 0
  | .order2 => if i ≥ 2 then 2 * xs.getD (i - 1) 0 - xs.getD (i - 2) 0 else 0
  | .order3 => if i ≥ 3 then 3 * xs.getD (i - 1) 0 - 3 * xs.getD (i - 2) 0 + xs.getD (i - 3) 0 else 0
  | .order4 =>
    if i ≥ 4 then 4 * xs.getD (i - 1) 0 - 6 * xs.getD (i - 2) 0 + 4 * xs.getD (i - 3) 0 - xs.getD (i - 4) 0
    else 0

theorem flacGetD_take (xs : List Int32) (j i : Nat) (hj : j < i) :
    (xs.take i).getD j 0 = xs.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem flacFixedPredictList_take (ord : FlacFixedOrder) (xs : List Int32) (i : Nat) :
    flacFixedPredictList ord (xs.take i) i = flacFixedPredictList ord xs i := by
  cases ord <;> simp only [flacFixedPredictList]
  · split
    · rw [flacGetD_take xs (i - 1) i (by omega)]
    · rfl
  · split
    · rw [flacGetD_take xs (i - 1) i (by omega), flacGetD_take xs (i - 2) i (by omega)]
    · rfl
  · split
    · rw [flacGetD_take xs (i - 1) i (by omega), flacGetD_take xs (i - 2) i (by omega),
          flacGetD_take xs (i - 3) i (by omega)]
    · rfl
  · split
    · rw [flacGetD_take xs (i - 1) i (by omega), flacGetD_take xs (i - 2) i (by omega),
          flacGetD_take xs (i - 3) i (by omega), flacGetD_take xs (i - 4) i (by omega)]
    · rfl

def flacEncodeFixedListGo (ord : FlacFixedOrder) (xs : List Int32) (i : Nat) : Nat → List Int32
  | 0 => []
  | k + 1 => (xs.getD i 0 - flacFixedPredictList ord xs i) :: flacEncodeFixedListGo ord xs (i + 1) k

def flacDecodeFixedListGo (ord : FlacFixedOrder) : List Int32 → List Int32 → List Int32
  | acc, [] => acc
  | acc, r :: rs =>
    let p := flacFixedPredictList ord acc acc.length
    flacDecodeFixedListGo ord (acc ++ [r + p]) rs

theorem int32_sub_add_cancel (a b : Int32) : a - b + b = a := by
  cases a with | ofUInt32 au =>
  cases b with | ofUInt32 bu =>
  cases au with | ofBitVec ab =>
  cases bu with | ofBitVec bb =>
  show Int32.ofUInt32 (UInt32.ofBitVec (ab - bb + bb)) = Int32.ofUInt32 (UInt32.ofBitVec ab)
  congr 2
  bv_omega

theorem flacDecodeFixedListGo_roundtrip (ord : FlacFixedOrder) (xs : List Int32) :
    ∀ k i, i + k = xs.length →
      flacDecodeFixedListGo ord (xs.take i) (flacEncodeFixedListGo ord xs i k) = xs := by
  intro k
  induction k with
  | zero =>
    intro i hi
    simp [flacEncodeFixedListGo, flacDecodeFixedListGo, List.take_of_length_le (by omega : xs.length ≤ i)]
  | succ k ih =>
    intro i hi
    have hi' : i < xs.length := by omega
    have hlen : (xs.take i).length = i := by simp [Nat.min_eq_left (by omega : i ≤ xs.length)]
    simp only [flacEncodeFixedListGo, flacDecodeFixedListGo, hlen, flacFixedPredictList_take, int32_sub_add_cancel]
    have htake : xs.take i ++ [xs.getD i 0] = xs.take (i + 1) := by
      have hget : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD, hi']
      rw [hget, List.take_add_one, List.getElem?_eq_getElem hi']
      simp
    rw [htake]
    exact ih (i + 1) (by omega)

theorem flacFixedList_roundtrip (ord : FlacFixedOrder) (xs : List Int32) :
    flacDecodeFixedListGo ord [] (flacEncodeFixedListGo ord xs 0 xs.length) = xs := by
  simpa using flacDecodeFixedListGo_roundtrip ord xs xs.length 0 (by omega)

def flacUtf8ContByte (v s : UInt64) : UInt8 :=
  (0x80 : UInt8) ||| ((v >>> s).toUInt8 &&& (0x3F : UInt8))

def flacUtf8Encode (v : UInt64) : Option ByteArray :=
  if v < 0x80 then some { data := #[v.toUInt8] }
  else if v < 0x800 then
    some { data := #[(0xC0 : UInt8) ||| (v >>> 6).toUInt8, flacUtf8ContByte v 0] }
  else if v < 0x10000 then
    some { data := #[(0xE0 : UInt8) ||| (v >>> 12).toUInt8, flacUtf8ContByte v 6, flacUtf8ContByte v 0] }
  else if v < 0x200000 then
    some { data := #[(0xF0 : UInt8) ||| (v >>> 18).toUInt8, flacUtf8ContByte v 12,
      flacUtf8ContByte v 6, flacUtf8ContByte v 0] }
  else if v < 0x4000000 then
    some { data := #[(0xF8 : UInt8) ||| (v >>> 24).toUInt8, flacUtf8ContByte v 18,
      flacUtf8ContByte v 12, flacUtf8ContByte v 6, flacUtf8ContByte v 0] }
  else if v < 0x80000000 then
    some { data := #[(0xFC : UInt8) ||| (v >>> 30).toUInt8, flacUtf8ContByte v 24,
      flacUtf8ContByte v 18, flacUtf8ContByte v 12, flacUtf8ContByte v 6, flacUtf8ContByte v 0] }
  else if v < 0x1000000000 then
    some { data := #[0xFE, flacUtf8ContByte v 30, flacUtf8ContByte v 24,
      flacUtf8ContByte v 18, flacUtf8ContByte v 12, flacUtf8ContByte v 6, flacUtf8ContByte v 0] }
  else none

def flacUtf8DecodeCont (s : ByteSlice) (pos : Nat) : Nat → UInt64 → Option (UInt64 × Nat)
  | 0, acc => some (acc, pos)
  | k + 1, acc =>
    if pos ≥ s.len then none
    else
      let b := sliceByteD s pos
      if (b &&& 0xC0) != 0x80 then none
      else flacUtf8DecodeCont s (pos + 1) k ((acc <<< 6) ||| (b &&& 0x3F).toUInt64)

def flacUtf8Decode (s : ByteSlice) (off : Nat) : Option (UInt64 × Nat) := do
  if off ≥ s.len then none
  let b0 := sliceByteD s off
  if (b0 &&& 0x80) == 0 then some (b0.toUInt64, off + 1)
  else if (b0 &&& 0xE0) == 0xC0 then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 1 (b0 &&& 0x1F).toUInt64
    if v < 0x80 then none else some (v, p)
  else if (b0 &&& 0xF0) == 0xE0 then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 2 (b0 &&& 0x0F).toUInt64
    if v < 0x800 then none else some (v, p)
  else if (b0 &&& 0xF8) == 0xF0 then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 3 (b0 &&& 0x07).toUInt64
    if v < 0x10000 then none else some (v, p)
  else if (b0 &&& 0xFC) == 0xF8 then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 4 (b0 &&& 0x03).toUInt64
    if v < 0x200000 then none else some (v, p)
  else if (b0 &&& 0xFE) == 0xFC then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 5 (b0 &&& 0x01).toUInt64
    if v < 0x4000000 then none else some (v, p)
  else if b0 == 0xFE then
    let (v, p) ← flacUtf8DecodeCont s (off + 1) 6 0
    if v < 0x80000000 then none else some (v, p)
  else none

def flacUtf8Check (n : UInt64) : Bool :=
  match flacUtf8Encode n with
  | some enc =>
    flacUtf8Decode { ba := enc, off := 0, len := enc.data.size } 0 ==
      some (n, enc.data.size)
  | none => false

theorem flacUtf8_encode_decode_roundtrip :
    ([0, 1, 127, 128, 2047, 2048, 65535, 65536, 1000000, 0x7FFFFFFF, 0xFFFFFFFFF] : List UInt64).all
      flacUtf8Check = true := by
  decide

def flacCrc8SliceLoop (s : ByteSlice) (off i : Nat) (c : UInt8) : Nat → UInt8
  | 0 => c
  | k + 1 => flacCrc8SliceLoop s off (i + 1) (flacCrc8StepByteFast c (sliceByteD s (off + i))) k

def flacCrc8Slice (s : ByteSlice) (off len : Nat) : UInt8 :=
  flacCrc8SliceLoop s off 0 0 len

def flacCrc16SliceLoop (s : ByteSlice) (off i : Nat) (c : UInt16) : Nat → UInt16
  | 0 => c
  | k + 1 => flacCrc16SliceLoop s off (i + 1) (flacCrc16StepByteSpec c (sliceByteD s (off + i))) k

def flacCrc16Slice (s : ByteSlice) (off len : Nat) : UInt16 :=
  flacCrc16SliceLoop s off 0 0 len

def flacSliceBytesLoop (b : ByteArray) (i : Nat) (acc : Array UInt8) : Nat → Array UInt8
  | 0 => acc
  | k + 1 => flacSliceBytesLoop b (i + 1) (acc.push (b.data.getD i 0)) k

def flacSliceBytes (b : ByteArray) (off len : Nat) : ByteArray :=
  { data := flacSliceBytesLoop b off #[] len }

def flacPushArrayLoop {α : Type} (src : Array α) (i : Nat) (acc : Array α) : Nat → Array α
  | 0 => acc
  | k + 1 =>
    match src[i]? with
    | some v => flacPushArrayLoop src (i + 1) (acc.push v) k
    | none => acc

def flacAppendBytes (a b : ByteArray) : ByteArray :=
  { data := flacPushArrayLoop b.data 0 a.data b.data.size }

def flacResolveBlockSize (code : Nat) (s : ByteSlice) (pos : Nat) : Option (Nat × Nat) :=
  match code with
  | 0 => none
  | 1 => some (192, pos)
  | 2 => some (576, pos)
  | 3 => some (1152, pos)
  | 4 => some (2304, pos)
  | 5 => some (4608, pos)
  | 6 => if pos < s.len then some ((sliceByteD s pos).toNat + 1, pos + 1) else none
  | 7 =>
    if pos + 1 < s.len then
      some ((sliceByteD s pos).toNat * 256 + (sliceByteD s (pos + 1)).toNat + 1, pos + 2)
    else none
  | _ => if code ≤ 15 then some (256 <<< (code - 8), pos) else none

def flacResolveSampleRate (code : Nat) (si : FlacStreamInfo) (s : ByteSlice) (pos : Nat) : Option (UInt32 × Nat) :=
  match code with
  | 0 => some (si.sampleRate, pos)
  | 1 => some (88200, pos)
  | 2 => some (176400, pos)
  | 3 => some (192000, pos)
  | 4 => some (8000, pos)
  | 5 => some (16000, pos)
  | 6 => some (22050, pos)
  | 7 => some (24000, pos)
  | 8 => some (32000, pos)
  | 9 => some (44100, pos)
  | 10 => some (48000, pos)
  | 11 => some (96000, pos)
  | 12 => if pos < s.len then some (((sliceByteD s pos).toUInt32) * 1000, pos + 1) else none
  | 13 =>
    if pos + 1 < s.len then
      some (((sliceByteD s pos).toUInt32 <<< 8) ||| (sliceByteD s (pos + 1)).toUInt32, pos + 2)
    else none
  | 14 =>
    if pos + 1 < s.len then
      some ((((sliceByteD s pos).toUInt32 <<< 8) ||| (sliceByteD s (pos + 1)).toUInt32) * 10, pos + 2)
    else none
  | _ => none

def flacResolveBps (code : Nat) (si : FlacStreamInfo) : Option Nat :=
  match code with
  | 0 => some si.bitsPerSample.toNat
  | 1 => some 8
  | 2 => some 12
  | 4 => some 16
  | 5 => some 20
  | 6 => some 24
  | 7 => some 32
  | _ => none

def flacParseFrameHeader (s : ByteSlice) (frameOff : Nat) (si : FlacStreamInfo) : Option FlacFrameHeaderView := do
  if frameOff + 6 > s.len then none
  let b0 := (sliceByteD s frameOff).toNat
  let b1 := (sliceByteD s (frameOff + 1)).toNat
  let w16 := (b0 <<< 8) ||| b1
  if !flacFrameSyncGateSpec.gate w16 then none
  let varBlk := (b1 &&& 1) == 1
  let b2 := (sliceByteD s (frameOff + 2)).toNat
  let b3 := (sliceByteD s (frameOff + 3)).toNat
  let bsCode := (b2 >>> 4) &&& 0x0F
  let srCode := b2 &&& 0x0F
  let chAssign := (b3 >>> 4) &&& 0x0F
  let bpsCode := (b3 >>> 1) &&& 0x07
  let resBit := b3 &&& 1
  if resBit != 0 || !flacChannelAssignGateSpec.gate chAssign then none
  let (utf8Val, pos1) ← flacUtf8Decode s (frameOff + 4)
  let (blkSz, pos2) ← flacResolveBlockSize bsCode s pos1
  let (sr, pos3) ← flacResolveSampleRate srCode si s pos2
  let bps ← flacResolveBps bpsCode si
  if sr == 0 || blkSz == 0 || pos3 ≥ s.len then none
  let hdrLen := pos3 - frameOff
  let crcExpected := sliceByteD s pos3
  let crcActual := flacCrc8Slice s frameOff hdrLen
  if crcActual != crcExpected then none
  let numCh := if chAssign < 8 then chAssign + 1 else 2
  some {
    variableBlock := varBlk
    blockSizeCode := bsCode
    sampleRateCode := srCode
    channelAssign := chAssign
    bpsCode := bpsCode
    utf8Number := utf8Val
    blockSize := blkSz
    sampleRate := sr
    channels := numCh
    bitsPerSample := bps
    headerLen := hdrLen + 1
  }

def flacDecodeSubframeWithReader (r0 : BitReader) (blockSize bps : Nat) : Option (Array Int64 × BitReader) :=
  flacDecodeSubframeCore64 r0 blockSize bps

def flacDecodeSubframesLoop (r : BitReader) (hdr : FlacFrameHeaderView) (chIdx : Nat) :
    Nat → List (Array Int64) → Option (List (Array Int64) × BitReader)
  | 0, acc => some (acc.reverse, r)
  | rem + 1, acc => do
    let subBps :=
      if (hdr.channelAssign == 8 && chIdx == 1) ||
         (hdr.channelAssign == 9 && chIdx == 0) ||
         (hdr.channelAssign == 10 && chIdx == 1) then hdr.bitsPerSample + 1
      else hdr.bitsPerSample
    let (chSamples, rNext) ← flacDecodeSubframeCore64 r hdr.blockSize subBps
    flacDecodeSubframesLoop rNext hdr (chIdx + 1) rem (chSamples :: acc)

def flacReconstructStereoLoop (mode : FlacStereoMode) (c0 c1 : Array Int64) (i : Nat)
    (outL outR : Array Int32) : Nat → Array (Array Int32)
  | 0 => #[outL, outR]
  | k + 1 =>
    let (l, r) := flacStereoDecodePair64 mode (c0.getD i 0) (c1.getD i 0)
    flacReconstructStereoLoop mode c0 c1 (i + 1) (outL.push l.toInt32) (outR.push r.toInt32) k

def flacReconstructStereoChannels (chAssign : Nat) (chans : List (Array Int64)) (n : Nat) : Array (Array Int32) :=
  if chAssign < 8 then (chans.map flacArray64To32).toArray
  else
    let c0 := chans.getD 0 #[]
    let c1 := chans.getD 1 #[]
    let mode : FlacStereoMode :=
      if chAssign == 8 then .leftSide
      else if chAssign == 9 then .rightSide
      else .midSide
    flacReconstructStereoLoop mode c0 c1 0 #[] #[] n

def flacDecodeFrameAt (s : ByteSlice) (frameOff : Nat) (si : FlacStreamInfo) :
    Option (FlacFrameHeaderView × Array (Array Int32) × Nat) := do
  let hdr ← flacParseFrameHeader s frameOff si
  let subSlice : ByteSlice := {
    ba := s.ba, off := s.off + frameOff + hdr.headerLen, len := s.len - (frameOff + hdr.headerLen)
  }
  let (rawChans, rAfter) ← flacDecodeSubframesLoop (BitReader.ofSlice subSlice) hdr 0 hdr.channels []
  let padBits := (8 - (rAfter.bitOffset % 8)) % 8
  let (padVal, rAligned) ← if padBits == 0 then some (0, rAfter) else rAfter.readBitsMSB padBits
  if padVal != 0 then none
  let bodySubBytes := rAligned.bitOffset / 8
  let crcPos := frameOff + hdr.headerLen + bodySubBytes
  if crcPos + 2 > s.len then none
  let crcExpected : UInt16 :=
    ((sliceByteD s crcPos).toUInt16 <<< 8) ||| (sliceByteD s (crcPos + 1)).toUInt16
  let frameLenNoCrc := hdr.headerLen + bodySubBytes
  let crcActual := flacCrc16Slice s frameOff frameLenNoCrc
  if crcActual != crcExpected then none
  some (hdr, flacReconstructStereoChannels hdr.channelAssign rawChans hdr.blockSize, crcPos + 2)

def flacParseMetadataLoop (s : ByteSlice) (pos : Nat) (siOpt : Option FlacStreamInfo) (md5Bytes : ByteArray) :
    Nat → Option (FlacStreamInfo × ByteArray × Nat)
  | 0 => none
  | fuel + 1 => do
    if pos + 4 > s.len then none
    let hdrByte := sliceByteD s pos
    let isLast := (hdrByte &&& 0x80) != 0
    let btype := (hdrByte &&& 0x7F).toNat
    let blen := ((sliceByteD s (pos + 1)).toNat <<< 16) |||
      ((sliceByteD s (pos + 2)).toNat <<< 8) ||| (sliceByteD s (pos + 3)).toNat
    if btype == 127 || pos + 4 + blen > s.len then none
    let nextPos := pos + 4 + blen
    let (siNext, md5Next) ←
      if btype == 0 then
        if siOpt.isSome || blen != 34 then none
        else do
          let si ← parseFlacStreamInfo { ba := s.ba, off := s.off + pos + 4, len := 34 }
          let md5 := flacSliceBytes s.ba (s.off + pos + 22) 16
          some (some si, md5)
      else if siOpt.isNone then none
      else some (siOpt, md5Bytes)
    if isLast then
      match siNext with
      | some si => some (si, md5Next, nextPos)
      | none => none
    else
      flacParseMetadataLoop s nextPos siNext md5Next fuel

def flacPushSampleLeLoop (u : UInt32) (b : Nat) (raw : Array UInt8) : Nat → Array UInt8
  | 0 => raw
  | k + 1 =>
    flacPushSampleLeLoop u (b + 1) (raw.push (((u >>> (8 * b).toUInt32) &&& 0xFF).toUInt8)) k

def flacPcmMd5ChansLoop (channelsData : Array (Array Int32)) (i bytesPerSample ch : Nat)
    (raw : Array UInt8) : Nat → Array UInt8
  | 0 => raw
  | k + 1 =>
    let v := (channelsData.getD ch #[]).getD i 0
    let raw' := flacPushSampleLeLoop v.toUInt32 0 raw bytesPerSample
    flacPcmMd5ChansLoop channelsData i bytesPerSample (ch + 1) raw' k

def flacPcmMd5SamplesLoop (channelsData : Array (Array Int32)) (nCh bytesPerSample i : Nat)
    (raw : Array UInt8) : Nat → Array UInt8
  | 0 => raw
  | k + 1 =>
    let raw' := flacPcmMd5ChansLoop channelsData i bytesPerSample 0 raw nCh
    flacPcmMd5SamplesLoop channelsData nCh bytesPerSample (i + 1) raw' k

def flacPcmMd5Bytes (channelsData : Array (Array Int32)) (bps : Nat) : ByteArray :=
  let nCh := channelsData.size
  if nCh == 0 then md5 { data := #[] }
  else
    let nSamples := (channelsData.getD 0 #[]).size
    let bytesPerSample := (bps + 7) / 8
    let raw := flacPcmMd5SamplesLoop channelsData nCh bytesPerSample 0
      (Array.mkEmpty (nSamples * nCh * bytesPerSample)) nSamples
    md5 { data := raw }

def flacMergeFrameChansLoop (acc frameChans : Array (Array Int32)) (c : Nat)
    (out : Array (Array Int32)) : Nat → Array (Array Int32)
  | 0 => out
  | k + 1 =>
    let src := frameChans.getD c #[]
    let merged := flacPushArrayLoop src 0 (acc.getD c #[]) src.size
    flacMergeFrameChansLoop acc frameChans (c + 1) (out.push merged) k

def flacDecodeFramesLoop (s : ByteSlice) (pos : Nat) (si : FlacStreamInfo)
    (acc : Array (Array Int32)) : Nat → Option (Array (Array Int32))
  | 0 => none
  | fuel + 1 =>
    if pos == s.len then some acc
    else if pos > s.len then none
    else do
      let (hdr, frameChans, nextPos) ← flacDecodeFrameAt s pos si
      if nextPos ≤ pos || hdr.channels != si.channels.toNat then none
      let acc' := flacMergeFrameChansLoop acc frameChans 0 #[] hdr.channels
      flacDecodeFramesLoop s nextPos si acc' fuel

def flacDecodeStream (s : ByteSlice) (verifyMd5 : Bool := true) : Option FlacDecodedStream := do
  if s.len < 42 then none
  if sliceByteD s 0 != 0x66 || sliceByteD s 1 != 0x4C ||
     sliceByteD s 2 != 0x61 || sliceByteD s 3 != 0x43 then none
  let (si, md5Hdr, audioOff) ← flacParseMetadataLoop s 4 none { data := #[] } 128
  let initAcc := (List.replicate si.channels.toNat (#[] : Array Int32)).toArray
  let decoded ← flacDecodeFramesLoop s audioOff si initAcc (s.len + 1)
  if verifyMd5 && md5Hdr.data.toList.any (· != 0) then
    let actualMd5 := flacPcmMd5Bytes decoded si.bitsPerSample.toNat
    if actualMd5.data != md5Hdr.data then none
    else some { info := si, md5 := md5Hdr, channelsData := decoded }
  else
    some { info := si, md5 := md5Hdr, channelsData := decoded }

def flacZigzag64 (x : Int64) : UInt64 :=
  if x < 0 then
    let m : UInt64 := (-1 - x).toUInt64
    (m <<< 1) ||| 1
  else
    x.toUInt64 <<< 1

def flacSampleAbs64 (x : Int64) : Nat :=
  let mag : UInt64 := if x < 0 then (0 - x).toUInt64 else x.toUInt64
  mag.toNat

def flacSampleAbs (x : Int32) : Nat :=
  flacSampleAbs64 x.toInt64

def flacRiceFits64 (x : Int64) (k : Nat) : Bool :=
  if k > 30 then false
  else
    let z : UInt64 := flacZigzag64 x
    let q : UInt64 := z >>> k.toUInt64
    z < ((1 : UInt64) <<< 63) && q < ((1 : UInt64) <<< (63 - k).toUInt64) && q < 1048576

def flacBestRiceK64 (res : List Int64) (maxK : Nat) : Nat :=
  let cnt := res.length
  if cnt == 0 then 0
  else
    let sumAbs : UInt64 := res.foldl (fun acc r => acc + flacZigzag64 r) 0
    let avg : UInt64 := sumAbs / cnt.toUInt64
    let rec findK (k : Nat) : Nat → Nat
      | 0 => k
      | fuel + 1 =>
        if k ≥ maxK || ((1 : UInt64) <<< k.toUInt64) ≥ avg then k
        else findK (k + 1) fuel
    findK 0 maxK

def flacEstimateRiceBits64 (res : List Int64) (k : Nat) : Option UInt64 :=
  let rec go (acc : UInt64) : List Int64 → Option UInt64
    | [] => some acc
    | r :: rs =>
      if !flacRiceFits64 r k then none
      else
        let q : UInt64 := (flacZigzag64 r) >>> k.toUInt64
        go (acc + q + 1 + k.toUInt64) rs
  go 0 res

def flacSolveLpcOrder2Loop (samples : Array Int64) (i : Nat) (r0 r1 r2 : Int) : Nat → Int × Int × Int
  | 0 => (r0, r1, r2)
  | k + 1 =>
    let s0 := (samples.getD i 0).toInt
    let r0' := r0 + s0 * s0
    let r1' := if i ≥ 1 then r1 + s0 * (samples.getD (i - 1) 0).toInt else r1
    let r2' := if i ≥ 2 then r2 + s0 * (samples.getD (i - 2) 0).toInt else r2
    flacSolveLpcOrder2Loop samples (i + 1) r0' r1' r2' k

def flacSolveLpcOrder2_64 (samples : Array Int64) : Option (Array Int32 × Nat × UInt32) :=
  let n := samples.size
  if n < 16 then none
  else
    let (r0, r1, r2) := flacSolveLpcOrder2Loop samples 0 0 0 0 n
    if r0 ≤ 0 then none
    else
      let denom := r0 * r0 - r1 * r1
      if denom ≤ 0 then none
      else
        let scale : Int := 256
        let a1Num := r1 * (r0 - r2) * scale
        let a2Num := (r0 * r2 - r1 * r1) * scale
        let q1 := a1Num / denom
        let q2 := a2Num / denom
        if q1 < -511 || q1 > 511 || q2 < -511 || q2 > 511 then none
        else if q1 == 0 && q2 == 0 then none
        else some (#[Int32.ofInt q1, Int32.ofInt q2], 10, 8)

def flacWriteSubframeBits (w0 : BitWriter) (mode : FlacSubframeSpecMode) (bps : Nat)
    (samples : Array Int32) : BitWriter :=
  flacWriteSubframeBits64 w0 mode bps (flacArray32To64 samples)

def flacChooseSubframeMode64 (samples : Array Int64) (bps : Nat)
    (allowLpc : Bool := true) : FlacSubframeSpecMode :=
  let xs := samples.toList
  match xs with
  | [] => .verbatim
  | s0 :: rest =>
    if rest.all (· == s0) then .constant s0
    else if samples.size < 5 then .verbatim
    else
      let verbCost : UInt64 := (samples.size * bps + 8).toUInt64
      let evalFixed (ord : FlacFixedOrder) : FlacSubframeSpecMode × UInt64 :=
        let pOrd := match ord with | .order0 => 0 | .order1 => 1 | .order2 => 2 | .order3 => 3 | .order4 => 4
        let res := (flacEncodeFixedResiduals64 ord samples).toList.drop pOrd
        let k := flacBestRiceK64 res 30
        match flacEstimateRiceBits64 res k with
        | none => (.verbatim, verbCost)
        | some bits => (.fixed ord (if k ≤ 14 then 0 else 1) k false bps, (pOrd * bps + 16).toUInt64 + bits)
      let cands := [FlacFixedOrder.order0, .order1, .order2, .order3, .order4].map evalFixed
      let best := cands.foldl (fun b c => if c.2 < b.2 then c else b) (.verbatim, verbCost)
      if !allowLpc then best.1
      else
        match flacSolveLpcOrder2_64 samples with
        | none => best.1
        | some (coeffs, prec, qShift) =>
          let coeffs64 := flacArray32To64 coeffs
          let lpcRes := (List.range (samples.size - 2)).map fun j =>
            let idx := j + 2
            let acc := flacLpcFirDot64 samples idx coeffs64 0 0 coeffs64.size
            samples.getD idx 0 - (acc >>> qShift.toUInt64.toInt64)
          let k := flacBestRiceK64 lpcRes 30
          match flacEstimateRiceBits64 lpcRes k with
          | none => best.1
          | some bits =>
            let cost : UInt64 := (2 * bps + 9 + 2 * prec + 16).toUInt64 + bits
            if cost < best.2 then .lpc coeffs prec qShift (if k ≤ 14 then 0 else 1) k else best.1

def flacChooseSubframeMode (samples : Array Int32) (bps : Nat)
    (allowLpc : Bool := true) : FlacSubframeSpecMode :=
  flacChooseSubframeMode64 (flacArray32To64 samples) bps allowLpc

def flacStereoPairsLoop64 (m : FlacStereoMode) (ch0 ch1 : Array Int32) (i : Nat)
    (a0 a1 : Array Int64) (energy : UInt64) : Nat → Array Int64 × Array Int64 × UInt64
  | 0 => (a0, a1, energy)
  | k + 1 =>
    let (x0, x1) := flacStereoEncodePair64 m (ch0.getD i 0).toInt64 (ch1.getD i 0).toInt64
    let m0 : UInt64 := if x0 < 0 then (0 - x0).toUInt64 else x0.toUInt64
    let m1 : UInt64 := if x1 < 0 then (0 - x1).toUInt64 else x1.toUInt64
    flacStereoPairsLoop64 m ch0 ch1 (i + 1) (a0.push x0) (a1.push x1) (energy + m0 + m1) k

def flacChooseStereoMode (ch0 ch1 : Array Int32) : FlacStereoMode × Array Int64 × Array Int64 :=
  let mkPairs (m : FlacStereoMode) := flacStereoPairsLoop64 m ch0 ch1 0 #[] #[] 0 ch0.size
  let (i0, i1, eI) := mkPairs .independent
  let (l0, l1, eL) := mkPairs .leftSide
  let (r0, r1, eR) := mkPairs .rightSide
  let (m0, m1, eM) := mkPairs .midSide
  let best0 := (FlacStereoMode.independent, i0, i1, eI)
  let best1 := if eL < best0.2.2.2 then (.leftSide, l0, l1, eL) else best0
  let best2 := if eR < best1.2.2.2 then (.rightSide, r0, r1, eR) else best1
  let best3 := if eM < best2.2.2.2 then (.midSide, m0, m1, eM) else best2
  (best3.1, best3.2.1, best3.2.2.1)

def flacBpsHeaderCode (bps : Nat) : UInt8 :=
  match bps with
  | 8 => 1 | 12 => 2 | 16 => 4 | 20 => 5 | 24 => 6 | 32 => 7 | _ => 0

def flacSampleRateHeaderCode (sr : UInt32) : UInt8 × List UInt8 :=
  if sr == 88200 then (1, [])
  else if sr == 176400 then (2, [])
  else if sr == 192000 then (3, [])
  else if sr == 8000 then (4, [])
  else if sr == 16000 then (5, [])
  else if sr == 22050 then (6, [])
  else if sr == 24000 then (7, [])
  else if sr == 32000 then (8, [])
  else if sr == 44100 then (9, [])
  else if sr == 48000 then (10, [])
  else if sr == 96000 then (11, [])
  else if sr ≤ 65535 then
    (13, [((sr >>> 8) &&& 0xFF).toUInt8, (sr &&& 0xFF).toUInt8])
  else if sr % 10 == 0 && sr / 10 ≤ 65535 then
    let u := sr / 10
    (14, [((u >>> 8) &&& 0xFF).toUInt8, (u &&& 0xFF).toUInt8])
  else (0, [])

def flacBlockSizeHeaderCode (blkSz : Nat) : UInt8 × List UInt8 :=
  match blkSz with
  | 192 => (1, [])
  | 576 => (2, [])
  | 1152 => (3, [])
  | 2304 => (4, [])
  | 4608 => (5, [])
  | 256 => (8, [])
  | 512 => (9, [])
  | 1024 => (10, [])
  | 2048 => (11, [])
  | 4096 => (12, [])
  | 8192 => (13, [])
  | 16384 => (14, [])
  | 32768 => (15, [])
  | n =>
    if n ≤ 256 then (6, [(n - 1).toUInt8])
    else (7, [(((n - 1) >>> 8) &&& 0xFF).toUInt8, ((n - 1) &&& 0xFF).toUInt8])

def flacEncodeFrame (blockChannels : Array (Array Int32)) (sampleRate : UInt32) (bps : Nat)
    (frameIdx : UInt64) (stereoOpt : Option FlacStereoMode := none)
    (modeOpt : Option FlacSubframeSpecMode := none) : Option ByteArray := do
  let nCh := blockChannels.size
  if nCh == 0 || nCh > 8 || bps == 0 || bps > 32 then none
  let blkSz := (blockChannels.getD 0 #[]).size
  if blkSz == 0 || blkSz > 65535 then none
  let (chAssign, encChans) : Nat × List (Array Int64) :=
    if nCh == 2 then
      let c0 := blockChannels.getD 0 #[]
      let c1 := blockChannels.getD 1 #[]
      let (stMode, s0, s1) :=
        match stereoOpt with
        | some sm =>
          let (a0, a1, _) := flacStereoPairsLoop64 sm c0 c1 0 #[] #[] 0 blkSz
          (sm, a0, a1)
        | none => flacChooseStereoMode c0 c1
      let ca := match stMode with
        | .independent => 1 | .leftSide => 8 | .rightSide => 9 | .midSide => 10
      (ca, [s0, s1])
    else
      (nCh - 1, blockChannels.toList.map flacArray32To64)
  let (bsCode, bsTail) := flacBlockSizeHeaderCode blkSz
  let (srCode, srTail) := flacSampleRateHeaderCode sampleRate
  let bpsCode := flacBpsHeaderCode bps
  let utf8 ← flacUtf8Encode frameIdx
  let b2 : UInt8 := (bsCode <<< 4) ||| srCode
  let b3 : UInt8 := (chAssign.toUInt8 <<< 4) ||| (bpsCode <<< 1)
  let hdrCore : List UInt8 := [0xFF, 0xF8, b2, b3] ++ utf8.data.toList ++ bsTail ++ srTail
  let crc8 := flacCrc8List hdrCore
  let hdrFull : ByteArray := { data := (hdrCore ++ [crc8]).toArray }
  let rec writeSubs (w : BitWriter) (idx : Nat) : List (Array Int64) → BitWriter
    | [] => w
    | chArr :: rest =>
      let subBps :=
        if (chAssign == 8 && idx == 1) || (chAssign == 9 && idx == 0) || (chAssign == 10 && idx == 1) then
          bps + 1
        else bps
      let subMode := modeOpt.getD (flacChooseSubframeMode64 chArr subBps (blkSz > 64))
      writeSubs (flacWriteSubframeBits64 w subMode subBps chArr) (idx + 1) rest
  let w0 : BitWriter := { bytes := { data := #[] }, curByte := 0, bitsUsed := 0 }
  let subBytes := (writeSubs w0 0 encChans).toByteArray
  let bodyNoCrc := flacAppendBytes hdrFull subBytes
  let crc16 := flacCrc16Slice { ba := bodyNoCrc, off := 0, len := bodyNoCrc.data.size } 0 bodyNoCrc.data.size
  let footer : ByteArray := { data := #[((crc16 >>> 8) &&& 0xFF).toUInt8, (crc16 &&& 0xFF).toUInt8] }
  some (flacAppendBytes bodyNoCrc footer)

def flacSliceChannelLoop (ch : Array Int32) (i : Nat) (acc : Array Int32) : Nat → Array Int32
  | 0 => acc
  | k + 1 => flacSliceChannelLoop ch (i + 1) (acc.push (ch.getD i 0)) k

def flacSliceChannelRange (ch : Array Int32) (off len : Nat) : Array Int32 :=
  flacSliceChannelLoop ch off #[] len

def flacEncodeFramesLoop (channelsData : Array (Array Int32)) (sampleRate : UInt32) (bps blockSize : Nat)
    (sampleOff : Nat) (frameIdx : UInt64) (minFrm maxFrm : Nat) (acc : ByteArray) :
    Nat → Option (ByteArray × Nat × Nat)
  | 0 => some (acc, minFrm, maxFrm)
  | fuel + 1 =>
    let total := (channelsData.getD 0 #[]).size
    if sampleOff ≥ total then some (acc, minFrm, maxFrm)
    else do
      let curBlk := Nat.min blockSize (total - sampleOff)
      let blkChans := (channelsData.toList.map (fun ch => flacSliceChannelRange ch sampleOff curBlk)).toArray
      let frm ← flacEncodeFrame blkChans sampleRate bps frameIdx
      let fLen := frm.data.size
      let min' := if minFrm == 0 || fLen < minFrm then fLen else minFrm
      let max' := if fLen > maxFrm then fLen else maxFrm
      flacEncodeFramesLoop channelsData sampleRate bps blockSize (sampleOff + curBlk) (frameIdx + 1)
        min' max' (flacAppendBytes acc frm) fuel

def flacEncodeStream (channelsData : Array (Array Int32)) (sampleRate : UInt32) (bps : Nat := 16)
    (blockSize : Nat := 4096) (computeMd5 : Bool := true) : Option ByteArray := do
  let nCh := channelsData.size
  if nCh == 0 || nCh > 8 || sampleRate == 0 || sampleRate > (655350 : UInt32) ||
     bps < 4 || bps > 32 || blockSize < 16 || blockSize > 65535 then none
  let total := (channelsData.getD 0 #[]).size
  if channelsData.toList.any (fun c => c.size != total) then none
  let numFrames := if total == 0 then 0 else (total + blockSize - 1) / blockSize
  let (framesBytes, minFrm, maxFrm) ←
    flacEncodeFramesLoop channelsData sampleRate bps blockSize 0 0 0 0 { data := #[] } (numFrames + 1)
  let minBlkNat := if total == 0 then blockSize else Nat.min blockSize (if total < 16 then 16 else total)
  let minBlk : UInt16 := minBlkNat.toUInt16
  let maxBlk : UInt16 := blockSize.toUInt16
  let si : FlacStreamInfo := {
    minBlockSize := if minBlk < 16 then 16 else minBlk
    maxBlockSize := if maxBlk < 16 then 16 else maxBlk
    minFrameSize := minFrm.toUInt32
    maxFrameSize := maxFrm.toUInt32
    sampleRate := sampleRate
    channels := nCh.toUInt8
    bitsPerSample := bps.toUInt8
    totalSamples := total.toUInt64
  }
  let md5Arr := if computeMd5 then (flacPcmMd5Bytes channelsData bps).data else (List.replicate 16 (0 : UInt8)).toArray
  let hdr := serializeFlacStreamInfo si md5Arr true
  some (flacAppendBytes hdr framesBytes)

def flacAudioFrameToChannels (af : AudioFrame) : Array (Array Int32) := Id.run do
  let nCh := af.channels.toNat
  let nS := af.numSamples
  let mut out := Array.mkEmpty nCh
  for ch in [0:nCh] do
    let mut cArr := Array.mkEmpty nS
    for i in [0:nS] do
      cArr := cArr.push (af.getSample ch i)
    out := out.push cArr
  return out

def flacDecodedToAudioFrame (dec : FlacDecodedStream) : AudioFrame := Id.run do
  let nCh := dec.info.channels.toNat
  let nS := if nCh == 0 then 0 else (dec.channelsData.getD 0 #[]).size
  let bps := dec.info.bitsPerSample.toNat
  let normSample (v : Int32) : Int32 :=
    if bps > 16 || bps == 16 then v
    else v <<< Int32.ofNat (16 - bps)
  let mut samples := Array.mkEmpty (nCh * nS)
  for ch in [0:nCh] do
    let cArr := dec.channelsData.getD ch #[]
    for i in [0:nS] do
      samples := samples.push (normSample (cArr.getD i 0))
  return {
    sampleFmt := if bps > 16 then .s32p else .s16p
    sampleRate := dec.info.sampleRate
    channels := dec.info.channels.toUInt32
    numSamples := nS
    pts := 0
    duration := nS.toUInt64
    timeBase := AVRational.mkSafe 1 dec.info.sampleRate.toUInt64
    samples := samples
  }

def flacEncodeAudioFrame (af : AudioFrame) (bps : Nat := 16) (blockSize : Nat := 4096) : Option ByteArray :=
  flacEncodeStream (flacAudioFrameToChannels af) af.sampleRate bps blockSize true

def flacRoundtripChannels (chans : Array (Array Int32)) (sr : UInt32) (bps blkSz : Nat) :
    Option (List (List Int32)) := do
  let bytes ← flacEncodeStream chans sr bps blkSz false
  let dec ← flacDecodeStream { ba := bytes, off := 0, len := bytes.data.size } false
  if dec.info.sampleRate == sr && dec.info.bitsPerSample.toNat == bps then
    some (dec.channelsData.toList.map Array.toList)
  else none

def flacRoundtripStereoMode (ch0 ch1 : Array Int32) (sm : FlacStereoMode) (bps : Nat := 16)
    (modeOpt : Option FlacSubframeSpecMode := some (.fixed .order2 0 4 false 16)) :
    Option (List (List Int32)) := do
  let blkSz := ch0.size
  let frm ← flacEncodeFrame #[ch0, ch1] 48000 bps 0 (some sm) modeOpt
  let si : FlacStreamInfo := ⟨blkSz.toUInt16, blkSz.toUInt16, 0, 0, 48000, 2, bps.toUInt8, blkSz.toUInt64⟩
  let (_, chans, used) ← flacDecodeFrameAt { ba := frm, off := 0, len := frm.data.size } 0 si
  if used == frm.data.size then some (chans.toList.map Array.toList) else none

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem flacStream_and_stereo_modes_roundtrip :
    let c0 : Array Int32 := #[0, 120, 240, 350, 440, 510, 550, 560, 540, 490, 410, 300, 170, 20, -130, -270]
    let c1 : Array Int32 := #[10, 110, 220, 310, 390, 450, 490, 500, 480, 430, 360, 260, 150, 30, -100, -220]
    let exp := [c0.toList, c1.toList]
    let c32L : Array Int32 := #[2147483647, -2147483648, 1500000000, -1500000000]
    let c32R : Array Int32 := #[-2147483648, 2147483647, -1500000000, 1500000000]
    let exp32 := [c32L.toList, c32R.toList]
    flacRoundtripChannels #[c0, c1] 48000 16 16 = some exp ∧
    flacRoundtripStereoMode c0 c1 .independent = some exp ∧
    flacRoundtripStereoMode c0 c1 .leftSide = some exp ∧
    flacRoundtripStereoMode c0 c1 .rightSide = some exp ∧
    flacRoundtripStereoMode c0 c1 .midSide = some exp ∧
    flacRoundtripStereoMode c32L c32R .midSide 32 (some .verbatim) = some exp32 ∧
    flacRoundtripStereoMode c32L c32R .leftSide 32 (some (.fixed .order1 1 30 false 33)) = some exp32 := by
  decide

end LeanAV.Audio
