/-
  LeanAV.Core: Verified Core Multimedia Primitives (`libavutil` Replacement)
  - Exact rational timebases (`AVRational`, `rescaleTimestamp`, `rescaleTimestampRoundNear`)
  - Pixel & audio sample formats (`PixelFormat`, `SampleFormat`, `ColorSpace`, `ChannelLayout`)
  - Zero-copy packet views (`AVPacketView` over `LeanSys.Posix.ByteSlice`)
  - Multi-plane video/audio frames (`PlaneView`, `VideoFrame`, `AudioFrame`)
  - Verified disjoint tile partitioning (`TileRect`, `partitionTiles`) for lock-free tile threading
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanAV.Spec

namespace LeanAV.Core

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanAV.Spec

/-! ## 1. Rational Timebases (`AVRational`) & Exact Timestamp Rescaling -/

/-- Rational number `num / (denMinusOne + 1)` with strictly positive denominator by construction. -/
structure AVRational where
  num         : UInt64
  denMinusOne : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace AVRational

/-- Construct an `AVRational` from `num` and `den` (clamping `den = 0` to `1`). -/
@[inline]
def mkSafe (num den : UInt64) : AVRational :=
  { num := num, denMinusOne := if den == 0 then 0 else den - 1 }

/-- Strictly positive denominator `den ≥ 1`. -/
@[inline]
def den (q : AVRational) : UInt64 :=
  q.denMinusOne + 1

/-- Standard 90 kHz MPEG/RTP/MP4 video timebase (`1 / 90000`). -/
@[inline] def tb90kHz : AVRational := mkSafe 1 90000

/-- Standard 48 kHz Opus/broadcast audio timebase (`1 / 48000`). -/
@[inline] def tb48kHz : AVRational := mkSafe 1 48000

/-- Standard 44.1 kHz FLAC/CD audio timebase (`1 / 44100`). -/
@[inline] def tb44k1Hz : AVRational := mkSafe 1 44100

/-- Standard microsecond timebase (`1 / 1000000`, `AV_TIME_BASE_Q`). -/
@[inline] def tbMicros : AVRational := mkSafe 1 1000000

/-- Convert a timestamp `pts` from source timebase `bq` to destination timebase `cq`
    (`av_rescale_q`: `floor(pts * (bq.num * cq.den) / (bq.den * cq.num))`). -/
@[inline]
def rescalePts (pts : UInt64) (bq cq : AVRational) : UInt64 :=
  let b := bq.num * cq.den
  let c := bq.den * cq.num
  rescaleQ pts b c

/-- Convert a `Nat` timestamp using exact arbitrary-precision `Nat` arithmetic (`Law 1`). -/
@[inline]
def rescalePtsExactNat (pts : Nat) (bqNum bqDen cqNum cqDen : Nat) : Nat :=
  rescaleFloor pts (bqNum * cqDen) (bqDen * cqNum)

end AVRational

/-! ## 2. Pixel Formats, Color Spaces, and Audio Sample Formats -/

/-- Canonical pixel formats (`AVPixelFormat`). -/
inductive PixelFormat where
  | yuv420p
  | yuv422p
  | yuv444p
  | yuv420p10le
  | nv12
  | rgb24
  | rgba
  | gray8
  deriving Repr, DecidableEq, Inhabited

/-- ITU-R Color matrix coefficients (`AVColorSpace`). -/
inductive ColorMatrix where
  | bt601
  | bt709
  | bt2020
  | bt2020ncl
  | srgb
  deriving Repr, DecidableEq, Inhabited

/-- Clamp a signed 32-bit integer `v` into the signed 16-bit PCM range `[-32768, 32767]`. -/
@[inline]
def clipInt16 (v : Int32) : Int32 :=
  if v < -32768 then -32768
  else if v > 32767 then 32767
  else v

/-- Canonical audio sample formats (`AVSampleFormat`). -/
inductive SampleFormat where
  | s16le
  | s24le
  | s32le
  | f32le
  | s16p
  | s32p
  | fltp
  deriving Repr, DecidableEq, Inhabited

/-- Canonical codec identifiers (`AVCodecID`) covering the full FFmpeg ecosystem. -/
inductive CodecId where
  -- Video Codecs
  | av1
  | h264
  | hevc
  | vvc
  | vp9
  | vp8
  | prores
  | ffv1
  | dnxhd
  | mjpeg
  | png
  | mpeg2video
  | mpeg4
  | theora
  | rawvideo
  -- Audio Codecs
  | flac
  | opus
  | aac
  | mp3
  | vorbis
  | ac3
  | eac3
  | alac
  | pcm_s16le
  | pcm_s24le
  | pcm_f32le
  -- Subtitle / Data Codecs
  | webvtt
  | ass
  | subrip
  deriving Repr, DecidableEq, Inhabited

/-- Container format identifiers (`AVInputFormat` / `AVOutputFormat`). -/
inductive ContainerFormat where
  | ivf
  | mp4
  | mkv
  | webm
  | ogg
  | mpegts
  | flacRaw
  | wav
  | avi
  | flv
  | hls
  | dash
  deriving Repr, DecidableEq, Inhabited

/-! ## 3. Zero-Copy `AVPacketView` over `LeanSys.Posix.ByteSlice` -/

/--
  Zero-copy demuxed packet view (`AVPacket` replacement) backed by `LeanSys.Posix.ByteSlice`.
  Holds presentation/decompression timestamps (`pts`, `dts`), duration, stream index,
  keyframe flag, and a 64-bit XXH64 content digest (`xxh64Slice`).
-/
structure AVPacketView where
  streamIndex : UInt32
  codec       : CodecId
  pts         : UInt64
  dts         : UInt64
  duration    : UInt64
  isKeyframe  : Bool
  slice       : ByteSlice
  digest64    : UInt64

instance : Inhabited AVPacketView where
  default := {
    streamIndex := 0
    codec := .av1
    pts := 0
    dts := 0
    duration := 0
    isKeyframe := false
    slice := ByteSlice.ofByteArray ByteArray.empty
    digest64 := 0
  }

namespace AVPacketView

/-- Construct a verified `AVPacketView` over a `ByteSlice` with automatic 64-bit XXH64 digesting. -/
@[inline]
def mkVerified (streamIndex : UInt32) (codec : CodecId) (pts dts duration : UInt64)
    (isKeyframe : Bool) (slice : ByteSlice) : AVPacketView :=
  { streamIndex := streamIndex
    codec := codec
    pts := pts
    dts := dts
    duration := duration
    isKeyframe := isKeyframe
    slice := slice
    digest64 := xxh64Slice slice }

/-- Verify that the packet's `ByteSlice` bounds and 64-bit digest are intact. -/
@[inline]
def verifyIntegrity (pkt : AVPacketView) : Bool :=
  verifySliceBounds pkt.slice.off.toUInt64 pkt.slice.len.toUInt64 pkt.slice.ba.size.toUInt64 == 1 &&
  xxh64Slice pkt.slice == pkt.digest64

end AVPacketView

/-! ## 4. Multi-Plane `VideoFrame` & `AudioFrame` (`AVFrame` Replacement) -/

/-- Validated 2D plane buffer (`width × height` with row `stride` bytes). -/
structure Plane2D where
  data   : ByteArray
  width  : Nat
  height : Nat
  stride : Nat
  deriving Inhabited

namespace Plane2D

/-- Allocate a zero-initialized `Plane2D` gated by `verifyFrameDimensions`. -/
def alloc? (width height stride : Nat) (fill : UInt8 := 0) : Option Plane2D :=
  let totalBytes := stride * height
  if verifyFrameDimensions width.toUInt64 height.toUInt64 stride.toUInt64 totalBytes.toUInt64 == 1 then
    let arr := ByteArray.mk (Array.replicate totalBytes fill)
    some { data := arr, width := width, height := height, stride := stride }
  else
    none

/-- Total `Plane2D` allocation (clamping `stride` to `max width stride` and `width/height ≥ 1`). -/
def alloc (width height stride : Nat) (fill : UInt8 := 0) : Plane2D :=
  let w := if width == 0 then 1 else width
  let h := if height == 0 then 1 else height
  let st := if stride < w then w else stride
  let totalBytes := st * h
  let arr := ByteArray.mk (Array.replicate totalBytes fill)
  { data := arr, width := w, height := h, stride := st }

/-- Verify that `p` satisfies `verifyFrameDimensions`. -/
@[inline]
def verifyBounds (p : Plane2D) : Bool :=
  verifyFrameDimensions p.width.toUInt64 p.height.toUInt64 p.stride.toUInt64 p.data.size.toUInt64 == 1

/-- Total pixel read at `(row, col)` with zero-fallback out of bounds. -/
@[inline]
def getPixel (p : Plane2D) (row col : Nat) : UInt8 :=
  if col < p.width && row < p.height then
    let idx := row * p.stride + col
    if idx < p.data.size then p.data.get! idx else 0
  else 0

/-- Total pixel read at `(x, y)` with custom fallback. -/
@[inline]
def getPixelD (p : Plane2D) (x y : Nat) (fallback : UInt8 := 0) : UInt8 :=
  if x < p.width && y < p.height then
    let idx := y * p.stride + x
    if idx < p.data.size then p.data.get! idx else fallback
  else
    fallback

/-- Functional pixel update at `(row, col)` (in-place when `p.data` has `RC == 1`). -/
@[inline]
def setPixel (p : Plane2D) (row col : Nat) (v : UInt8) : Plane2D :=
  if col < p.width && row < p.height then
    let idx := row * p.stride + col
    if idx < p.data.size then
      { p with data := p.data.set! idx v }
    else p
  else p

end Plane2D

/-- Decoded planar video frame (`YUV420P` / `YUV444P` / `RGB24`). -/
structure VideoFrame where
  width       : Nat
  height      : Nat
  pixFmt      : PixelFormat
  colorMatrix : ColorMatrix
  pts         : UInt64
  duration    : UInt64
  timeBase    : AVRational := AVRational.tb90kHz
  planes      : Array Plane2D
  deriving Inhabited

namespace VideoFrame

/-- Allocate a planar `YUV420P` frame of dimensions `width × height`. -/
def allocYuv420p (width height : Nat) (pts : UInt64 := 0) (timeBase : AVRational := AVRational.tb90kHz)
    (colorMatrix : ColorMatrix := .bt709) : VideoFrame :=
  let cw := (width + 1) / 2
  let ch := (height + 1) / 2
  let yPlane := Plane2D.alloc width height width 16
  let uPlane := Plane2D.alloc cw ch cw 128
  let vPlane := Plane2D.alloc cw ch cw 128
  {
    width := width
    height := height
    pixFmt := .yuv420p
    colorMatrix := colorMatrix
    pts := pts
    duration := 1
    timeBase := timeBase
    planes := #[yPlane, uPlane, vPlane]
  }

/-- Verify that all planes in `vf` satisfy `Plane2D.verifyBounds`. -/
def verifyAllPlanes (vf : VideoFrame) : Bool :=
  vf.planes.all Plane2D.verifyBounds

end VideoFrame

/-- Decoded multi-channel PCM audio frame (`Int32` samples per channel, lossless up to 32-bit). -/
structure AudioFrame where
  sampleFmt  : SampleFormat := .s16p
  sampleRate : UInt32
  channels   : UInt32
  numSamples : Nat
  pts        : UInt64
  duration   : UInt64 := 0
  timeBase   : AVRational := AVRational.tb48kHz
  samples    : Array Int32
  deriving Repr, Inhabited

namespace AudioFrame

/-- Allocate a zero-initialized `AudioFrame`. -/
def alloc (sampleFmt : SampleFormat) (sampleRate channels : UInt32) (numSamples : Nat) (pts : UInt64 := 0) : AudioFrame :=
  let nCh := if channels == 0 then 1 else channels.toNat
  {
    sampleFmt := sampleFmt
    sampleRate := sampleRate
    channels := channels
    numSamples := numSamples
    pts := pts
    duration := numSamples.toUInt64
    timeBase := AVRational.mkSafe 1 sampleRate.toUInt64
    samples := Array.replicate (nCh * numSamples) 0
  }

/-- Total sample read for `(channel, sampleIdx)` in planar layout (`ch * numSamples + sampleIdx`). -/
@[inline]
def getSample (f : AudioFrame) (ch sampleIdx : Nat) : Int32 :=
  let idx := ch * f.numSamples + sampleIdx
  f.samples.getD idx 0

/-- Total sample update for `(channel, sampleIdx)` in planar layout (`ch * numSamples + sampleIdx`). -/
@[inline]
def setSample (f : AudioFrame) (ch sampleIdx : Nat) (v : Int32) : AudioFrame :=
  let idx := ch * f.numSamples + sampleIdx
  if idx < f.samples.size then
    { f with samples := f.samples.setIfInBounds idx v }
  else f

/-- Compute the 64-bit XXH64 / SplitMix digest of all PCM samples for bit-exact `R0` verification. -/
def pcmDigest64 (f : AudioFrame) : UInt64 := Id.run do
  let mut acc : UInt64 := 0x9E3779B97F4A7C15 ^^^ f.samples.size.toUInt64
  for s in f.samples do
    acc := mix64Word acc s.toUInt32.toUInt64
  return if acc == 0 then 1 else acc

end AudioFrame

/-! ## 5. Disjoint Tile Partitioning (`DisjointMut` / Wavefront Tile Threading) -/

/-- 1D flattened row-range tile `[rowStart, rowStart + rowCount)` covering `[byteOff, byteOff + byteLen)`. -/
structure FrameTile where
  tileId   : Nat
  rowStart : Nat
  rowCount : Nat
  byteOff  : UInt64
  byteLen  : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Partition a plane of `height` rows and `stride` bytes/row into `numTiles` pairwise-disjoint `FrameTile`s,
    verifying adjacent tile disjointness via `LeanAV.Spec.verifyTileDisjoint`. -/
def partitionPlaneRows (height stride numTiles : Nat) : Array FrameTile :=
  if height == 0 || stride == 0 || numTiles == 0 then #[]
  else
    let effTiles := Nat.min height numTiles
    let rowsPerTile := (height + effTiles - 1) / effTiles
    let cap : UInt64 := (height * stride).toUInt64
    let rec loop (r tid fuel : Nat) (acc : List FrameTile) : List FrameTile :=
      match fuel with
      | 0 => acc.reverse
      | fuel' + 1 =>
        if r >= height then acc.reverse
        else
          let cnt := Nat.min rowsPerTile (height - r)
          let bOff : UInt64 := (r * stride).toUInt64
          let bLen : UInt64 := (cnt * stride).toUInt64
          let curTile : FrameTile := { tileId := tid, rowStart := r, rowCount := cnt, byteOff := bOff, byteLen := bLen }
          let nextAcc :=
            match acc with
            | [] => if verifySliceBounds bOff bLen cap == 1 then [curTile] else []
            | prev :: _ =>
              if verifyTileDisjoint prev.byteOff prev.byteLen bOff bLen cap == 1 then curTile :: acc else acc
          loop (r + cnt) (tid + 1) fuel' nextAcc
    (loop 0 0 effTiles []).toArray

/-! ## 6. Wave 6 (C1): Formal Proofs for `AVRational.rescalePtsExactNat`, `Plane2D`, and `AudioFrame` -/

/-- Theorem: `rescalePtsExactNat` is monotone in `pts` (`pts1 ≤ pts2 → rescalePtsExactNat pts1 ... ≤ rescalePtsExactNat pts2 ...`). -/
theorem rescalePtsExactNat_monotone (pts1 pts2 bqNum bqDen cqNum cqDen : Nat) (h : pts1 ≤ pts2) :
    AVRational.rescalePtsExactNat pts1 bqNum bqDen cqNum cqDen ≤
      AVRational.rescalePtsExactNat pts2 bqNum bqDen cqNum cqDen := by
  unfold AVRational.rescalePtsExactNat rescaleFloor
  exact Nat.div_le_div_right (Nat.mul_le_mul_right (bqNum * cqDen) h)

/-- Theorem: `rescalePtsExactNat` is the exact identity on `pts` when timebases match (`tbNum, tbDen > 0`). -/
theorem rescalePtsExactNat_id (tbNum tbDen pts : Nat) (hNum : 0 < tbNum) (hDen : 0 < tbDen) :
    AVRational.rescalePtsExactNat pts tbNum tbDen tbNum tbDen = pts := by
  unfold AVRational.rescalePtsExactNat rescaleFloor
  have hPos : 0 < tbDen * tbNum := Nat.mul_pos hDen hNum
  have hComm : tbNum * tbDen = tbDen * tbNum := Nat.mul_comm tbNum tbDen
  rw [hComm]
  exact Nat.mul_div_cancel pts hPos

/-- Theorem: `Plane2D.verifyBounds` implies the exact `FrameDimSafe` stride and capacity bounds. -/
theorem plane2D_verifyBounds_sound (p : Plane2D)
    (h : p.verifyBounds = true) :
    FrameDimSafe ⟨p.width.toUInt64, p.height.toUInt64, p.stride.toUInt64, p.data.size.toUInt64⟩ := by
  exact frameDimGateSpec.sound ⟨p.width.toUInt64, p.height.toUInt64, p.stride.toUInt64, p.data.size.toUInt64⟩ h

/-- Theorem: 64-byte cache-line aligned stride utility (`alignStride64 w ≥ w` and `(alignStride64 w) % 64 = 0`). -/
@[inline]
def alignStride64 (w : Nat) : Nat :=
  ((w + 63) / 64) * 64

theorem alignStride64_ge_and_mod64 (w : Nat) :
    w ≤ alignStride64 w ∧ (alignStride64 w) % 64 = 0 := by
  unfold alignStride64
  omega

/-! ## 7. Wave 51 (P0): Non-Indexed `Plane` with Propositional Invariants, SIMD Tail-Padding, & Exact Signed `Timestamp` Rescaling -/

/-- Explicit error taxonomy for plane allocation and geometry validation (`Parse, Don't Validate`). -/
inductive PlaneError where
  | zeroDimension
  | invalidBytesPerSample (bps : Nat)
  | unsupportedSampleWidth (bps expectedBps : Nat)
  | exceedsMaxDimension (w h maxDim : Nat)
  | strideSmallerThanRowBytes (rowBytes stride : Nat)
  | unalignedStride64 (stride : Nat)
  | exceedsArenaBudget (requiredBytes maxArenaBytes : Nat)
  | insufficientBufferWithSimdPadding (requiredBytes actualBytes : Nat)
  | unexpectedKernelOutputSize (expectedBytes actualBytes : Nat)
  | lnirDescriptorRejected
  deriving Repr, DecidableEq, Inhabited

/-- Supported sample byte widths (`1` for 8-bit, `2` for 10/12/16-bit, `4` for 32-bit float/int, `8` for 64-bit). -/
@[inline]
def validBytesPerSample (bps : Nat) : Prop :=
  bps = 1 ∨ bps = 2 ∨ bps = 4 ∨ bps = 8

instance (bps : Nat) : Decidable (validBytesPerSample bps) := by
  unfold validBytesPerSample
  infer_instance

/--
  Non-indexed validated 2D media plane (`Plane`):
  Follows the Fable/Astra boundary-validation architecture ("Parse, Don't Validate"):
  - Dimensions (`w`, `h`), sample byte width (`bytesPerSample ∈ {1, 2, 4, 8}`), and `stride` are ordinary fields
    (avoiding dependent-type index explosion across dynamic resolution changes, cropping, and 4:2:0 subsampling).
  - Carries propositional invariants (`h_pos`, `h_bps`, `h_dim`, `h_ws`, `h_al`, `h_fit`, `h_cap`) checked **once**
    at the boundary by `Plane.mk?` / `Plane.alloc?`, including a mandatory **64-byte SIMD tail-padding**
    (`stride * h + 64 ≤ data.size`) so 16/32/64-byte unaligned vector loads (`vld1q_u8` / `_mm256_loadu_si256`)
    starting at any valid pixel coordinate never read past `data.size`.
  - Enforces an explicit single-plane logical byte-length cap (`data.size ≤ maxArenaBytes`); aggregate multi-plane
    decoder memory budgets and allocator capacity reservations remain tracked at the caller/runtime level.
-/
structure Plane where
  data           : ByteArray
  w              : Nat
  h              : Nat
  bytesPerSample : Nat := 1
  stride         : Nat
  maxDim         : Nat := 16384
  maxArenaBytes  : Nat := 134217728 -- 128 MiB default decompression-bomb cap
  h_pos          : 0 < w ∧ 0 < h ∧ 0 < bytesPerSample
  h_bps          : validBytesPerSample bytesPerSample
  h_dim          : w ≤ maxDim ∧ h ≤ maxDim
  h_ws           : w * bytesPerSample ≤ stride
  h_al           : stride % 64 = 0
  h_fit          : stride * h + 64 ≤ data.size
  h_cap          : data.size ≤ maxArenaBytes

namespace Plane

/-- Universal helper lemma: if `y < h`, then `y * stride + stride ≤ stride * h`. -/
theorem row_end_le_total (y h stride : Nat) :
    y < h → y * stride + stride ≤ stride * h := by
  intro hy
  have hy1 : y + 1 ≤ h := hy
  have hmul : (y + 1) * stride ≤ h * stride := Nat.mul_le_mul_right stride hy1
  have hcomm : h * stride = stride * h := Nat.mul_comm h stride
  have hdist : (y + 1) * stride = y * stride + stride := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/--
  Universal Theorem (P0 Scalar & Multi-Byte Sample Bounds):
  For any validated `p : Plane` and coordinates `x < p.w`, `y < p.h`, the byte offset
  `y * p.stride + x * p.bytesPerSample` and its entire sample footprint (`+ p.bytesPerSample`)
  are strictly within `p.data.size` (`0 cast`, `0 Fin` churn).
-/
theorem addr_lt (p : Plane) {x y : Nat} (hx : x < p.w) (hy : y < p.h) :
    y * p.stride + x * p.bytesPerSample < p.data.size ∧
    y * p.stride + x * p.bytesPerSample + p.bytesPerSample ≤ p.data.size := by
  have hx1 : x + 1 ≤ p.w := hx
  have hmulX : (x + 1) * p.bytesPerSample ≤ p.w * p.bytesPerSample :=
    Nat.mul_le_mul_right p.bytesPerSample hx1
  have hdistX : (x + 1) * p.bytesPerSample = x * p.bytesPerSample + p.bytesPerSample := by
    rw [Nat.add_mul, Nat.one_mul]
  have hRow : y * p.stride + p.stride ≤ p.stride * p.h := row_end_le_total y p.h p.stride hy
  have hWs := p.h_ws
  have hFit := p.h_fit
  have hBps := p.h_pos.2.2
  omega

/--
  Universal Theorem (P0/P4 SIMD Vector Tail-Safety):
  For any validated `p : Plane`, any coordinate `x < p.w`, `y < p.h`, and any SIMD vector width
  `vecBytes ≤ 64` (covering 128-bit NEON `16`, 256-bit AVX2 `32`, and 512-bit AVX-512 `64`),
  an unaligned vector load starting at `y * p.stride + x * p.bytesPerSample` stays strictly within `p.data.size`:
  `y * p.stride + x * p.bytesPerSample + vecBytes ≤ p.data.size`.
-/
theorem simd_load_safe (p : Plane) {x y vecBytes : Nat}
    (hx : x < p.w) (hy : y < p.h) (hVec : vecBytes ≤ 64) :
    y * p.stride + x * p.bytesPerSample + vecBytes ≤ p.data.size := by
  have hAddr := p.addr_lt hx hy
  have hRow : y * p.stride + p.stride ≤ p.stride * p.h := row_end_le_total y p.h p.stride hy
  have hx1 : x + 1 ≤ p.w := hx
  have hmulX : (x + 1) * p.bytesPerSample ≤ p.w * p.bytesPerSample :=
    Nat.mul_le_mul_right p.bytesPerSample hx1
  have hdistX : (x + 1) * p.bytesPerSample = x * p.bytesPerSample + p.bytesPerSample := by
    rw [Nat.add_mul, Nat.one_mul]
  have hWs := p.h_ws
  have hFit := p.h_fit
  have hBps := p.h_pos.2.2
  omega

/--
  Smart constructor (`Plane.mk?`): validates dimensions, `bytesPerSample ∈ {1, 2, 4, 8}`, 64-byte stride alignment,
  backing-allocation arena cap (`data.size ≤ maxArenaBytes`), and 64-byte SIMD tail padding at the boundary once,
  returning a `Plane` with bundled proof fields.
-/
def mk? (data : ByteArray) (w h stride : Nat) (bytesPerSample : Nat := 1)
    (maxDim : Nat := 16384) (maxArenaBytes : Nat := 134217728) : Except PlaneError Plane :=
  if hPos : 0 < w ∧ 0 < h ∧ 0 < bytesPerSample then
    if hBps : validBytesPerSample bytesPerSample then
      if hDim : w ≤ maxDim ∧ h ≤ maxDim then
        if hWs : w * bytesPerSample ≤ stride then
          if hAl : stride % 64 = 0 then
            if hFit : stride * h + 64 ≤ data.size then
              if hCap : data.size ≤ maxArenaBytes then
                .ok {
                  data := data
                  w := w
                  h := h
                  bytesPerSample := bytesPerSample
                  stride := stride
                  maxDim := maxDim
                  maxArenaBytes := maxArenaBytes
                  h_pos := hPos
                  h_bps := hBps
                  h_dim := hDim
                  h_ws := hWs
                  h_al := hAl
                  h_fit := hFit
                  h_cap := hCap
                }
              else
                .error (.exceedsArenaBudget data.size maxArenaBytes)
            else
              .error (.insufficientBufferWithSimdPadding (stride * h + 64) data.size)
          else
            .error (.unalignedStride64 stride)
        else
          .error (.strideSmallerThanRowBytes (w * bytesPerSample) stride)
      else
        .error (.exceedsMaxDimension w h maxDim)
    else
      .error (.invalidBytesPerSample bytesPerSample)
  else
    .error .zeroDimension

/--
  Allocate a fresh 64-byte-stride-aligned `Plane` with mandatory 64-byte SIMD tail padding,
  gated by `maxDim` and `maxArenaBytes` decompression-bomb limits.
-/
def alloc? (w h : Nat) (bytesPerSample : Nat := 1) (fill : UInt8 := 0)
    (maxDim : Nat := 16384) (maxArenaBytes : Nat := 134217728) : Except PlaneError Plane :=
  let stride := alignStride64 (w * bytesPerSample)
  let reqBytes := stride * h + 64
  if !(decide (validBytesPerSample bytesPerSample)) then
    .error (.invalidBytesPerSample bytesPerSample)
  else if w == 0 || h == 0 then
    .error .zeroDimension
  else if w > maxDim || h > maxDim then
    .error (.exceedsMaxDimension w h maxDim)
  else if reqBytes > maxArenaBytes then
    .error (.exceedsArenaBudget reqBytes maxArenaBytes)
  else
    let ba := ByteArray.mk (Array.replicate reqBytes fill)
    mk? ba w h stride bytesPerSample maxDim maxArenaBytes

/--
  Total proof-discharged byte read of the first byte of the sample at `(x, y)`
  (`y * p.stride + x * p.bytesPerSample < p.data.size` for any valid `bytesPerSample ∈ {1, 2, 4, 8}`).
-/
@[inline]
def getByte (p : Plane) (x y : Nat) (hx : x < p.w) (hy : y < p.h) : UInt8 :=
  let idx := y * p.stride + x * p.bytesPerSample
  have hLt : idx < p.data.size := (p.addr_lt hx hy).1
  p.data[idx]'hLt

/-- Chroma subsampled dimension helper `⌈d / 2⌉ = (d + 1) / 2` for odd/even YUV420/YUV422 planes. -/
@[inline]
def chromaSubsampleDim2 (d : Nat) : Nat :=
  (d + 1) / 2

/-- Theorem: `chromaSubsampleDim2 d > 0` whenever `d > 0` (handles odd dimensions without underflow to 0). -/
theorem chromaSubsampleDim2_pos {d : Nat} (hd : 0 < d) : 0 < chromaSubsampleDim2 d := by
  unfold chromaSubsampleDim2
  omega

end Plane

/-! ### Exact Signed `Rational`, Rounding Modes (`AVRounding`), and Overflow-Checked `Timestamp` Rescaling -/

/-- Exact rational timebase `num / den` with positive numerator and denominator (`den > 0` and `num > 0` by construction). -/
structure PosRational where
  num   : Nat
  den   : Nat
  h_num : 0 < num
  h_den : 0 < den
  deriving Repr, DecidableEq

namespace PosRational

/-- Smart constructor for `PosRational`: rejects `num = 0` or `den = 0` explicitly instead of silently clamping. -/
def mk? (num den : Nat) : Option PosRational :=
  if h : 0 < num ∧ 0 < den then
    some { num := num, den := den, h_num := h.1, h_den := h.2 }
  else
    none

end PosRational

/-- Explicit rounding modes matching FFmpeg `enum AVRounding` (`libavutil/mathematics.h`). -/
inductive AVRounding where
  | zero     -- Round toward zero (`AV_ROUND_ZERO`)
  | inf      -- Round away from zero (`AV_ROUND_INF`)
  | down     -- Round toward -infinity (`AV_ROUND_DOWN`)
  | up       -- Round toward +infinity (`AV_ROUND_UP`)
  | nearInf  -- Round to nearest and halfway cases away from zero (`AV_ROUND_NEAR_INF`, FFmpeg default)
  deriving Repr, DecidableEq, Inhabited

/-- Explicit error taxonomy for timestamp arithmetic (`No Silent Saturation`). -/
inductive TimeError where
  | invalidTimebase
  | noptsValue
  | int64Overflow (exactValue : Int)
  | discontinuity (prevDts curDts : Int)
  deriving Repr, DecidableEq, Inhabited

/-- Signed timestamp with explicit `none` sentinel for `AV_NOPTS_VALUE` (`0x8000000000000000`). -/
abbrev Timestamp := Option Int

/-- Minimum and maximum representable signed 64-bit timestamps (reserving `Int64.minValue` for `AV_NOPTS_VALUE`). -/
def minValidPtsInt64 : Int := -9223372036854775807
def maxValidPtsInt64 : Int :=  9223372036854775807

/-- Non-negative exact integer division with explicit `AVRounding` mode (`c > 0`). -/
def divRoundNat (n c : Nat) (rnd : AVRounding) : Nat :=
  match rnd with
  | .zero | .down => n / c
  | .inf  | .up   => (n + c - 1) / c
  | .nearInf      => (n + c / 2) / c

/--
  Exact arbitrary-precision signed rescaling (`av_rescale_rnd` mathematical model over `Int`):
  Computes `round(pts * b / c)` according to `rnd : AVRounding`, preserving negative `ctts` v1 offsets
  and never overflowing intermediate products.
-/
def rescaleIntExact (pts : Int) (b c : Nat) (rnd : AVRounding := .nearInf) : Int :=
  if pts ≥ 0 then
    Int.ofNat (divRoundNat (pts.toNat * b) c rnd)
  else
    let mag := (-pts).toNat * b
    let magRnd : AVRounding :=
      match rnd with
      | .zero    => .zero
      | .inf     => .inf
      | .down    => .up
      | .up      => .down
      | .nearInf => .nearInf
    0 - Int.ofNat (divRoundNat mag c magRnd)

/--
  Checked 64-bit timestamp rescaling (`rescaleTimestampChecked`):
  - Preserves `none` (`AV_NOPTS_VALUE`) explicitly when `allowNopts = true`, or returns `.error .noptsValue`.
  - Computes the exact mathematical rescaled value in `Int` via `rescaleIntExact`.
  - Checks `[minValidPtsInt64, maxValidPtsInt64]` bounds and returns `.error (.int64Overflow q)` instead of silently saturating.
-/
def rescaleTimestampChecked (ts : Timestamp) (bq cq : PosRational)
    (rnd : AVRounding := .nearInf) (allowNopts : Bool := true) : Except TimeError Timestamp :=
  match ts with
  | none =>
    if allowNopts then .ok none else .error .noptsValue
  | some pts =>
    let b := bq.num * cq.den
    let c := bq.den * cq.num
    let q := rescaleIntExact pts b c rnd
    if minValidPtsInt64 ≤ q ∧ q ≤ maxValidPtsInt64 then
      .ok (some q)
    else
      .error (.int64Overflow q)

/--
  Universal Theorem (P0 Exact Rescale Error Bound):
  For any non-negative `pts : Nat` and positive timebase product `c > 0`, the floor-rounded
  rescaled timestamp `q = divRoundNat (pts * b) c .zero` satisfies the exact inequality:
  `q * c ≤ pts * b ∧ pts * b < (q + 1) * c` (error strictly less than `1` destination tick, with zero silent saturation).
-/
theorem divRoundNat_zero_error_lt_one_tick (c pts b : Nat) (hc : 0 < c) :
    divRoundNat (pts * b) c .zero * c ≤ pts * b ∧
    pts * b < (divRoundNat (pts * b) c .zero + 1) * c := by
  dsimp [divRoundNat]
  have hMod : (pts * b) % c < c := Nat.mod_lt (pts * b) hc
  have hDivMod : c * ((pts * b) / c) + (pts * b) % c = pts * b := Nat.div_add_mod (pts * b) c
  have hComm1 : ((pts * b) / c) * c = c * ((pts * b) / c) := Nat.mul_comm _ _
  have hDist : ((pts * b) / c + 1) * c = ((pts * b) / c) * c + c := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/--
  Universal Theorem (P0 Nearest-Tie-Away-From-Zero Error Bound, `AV_ROUND_NEAR_INF`):
  For any non-negative `pts : Nat` and positive denominator `c > 0`, `q = divRoundNat (pts * b) c .nearInf`
  satisfies both the shifted quotient bracket `q * c ≤ pts * b + c / 2 ∧ pts * b + c / 2 < (q + 1) * c`
  and the explicit two-sided half-tick absolute-error bound:
  `2 * (q * c) ≤ 2 * (pts * b) + c ∧ 2 * (pts * b) < 2 * (q * c) + c` (i.e., `2 * |q * c - pts * b| ≤ c`).
-/
theorem divRoundNat_nearInf_error_bound (c pts b : Nat) (hc : 0 < c) :
    divRoundNat (pts * b) c .nearInf * c ≤ pts * b + c / 2 ∧
    pts * b + c / 2 < (divRoundNat (pts * b) c .nearInf + 1) * c ∧
    2 * (divRoundNat (pts * b) c .nearInf * c) ≤ 2 * (pts * b) + c ∧
    2 * (pts * b) < 2 * (divRoundNat (pts * b) c .nearInf * c) + c := by
  dsimp [divRoundNat]
  have hMod : (pts * b + c / 2) % c < c := Nat.mod_lt (pts * b + c / 2) hc
  have hDivMod : c * ((pts * b + c / 2) / c) + (pts * b + c / 2) % c = pts * b + c / 2 :=
    Nat.div_add_mod (pts * b + c / 2) c
  have hComm1 : ((pts * b + c / 2) / c) * c = c * ((pts * b + c / 2) / c) := Nat.mul_comm _ _
  have hDist : ((pts * b + c / 2) / c + 1) * c = ((pts * b + c / 2) / c) * c + c := by
    rw [Nat.add_mul, Nat.one_mul]
  have hHalf : 2 * (c / 2) ≤ c ∧ c ≤ 2 * (c / 2) + 1 := by omega
  omega

/--
  Universal Theorem (P0 No Silent Saturation):
  Whenever `rescaleTimestampChecked (some pts) bq cq rnd` succeeds with `.ok (some q)`,
  `q` equals the exact mathematical value `rescaleIntExact pts (bq.num * cq.den) (bq.den * cq.num) rnd`
  and lies within `[minValidPtsInt64, maxValidPtsInt64]` inclusively.
-/
theorem rescaleTimestampChecked_exact_and_bounded (pts q : Int) (bq cq : PosRational)
    (rnd : AVRounding) (allowNopts : Bool)
    (hOk : rescaleTimestampChecked (some pts) bq cq rnd allowNopts = .ok (some q)) :
    q = rescaleIntExact pts (bq.num * cq.den) (bq.den * cq.num) rnd ∧
    minValidPtsInt64 ≤ q ∧ q ≤ maxValidPtsInt64 := by
  unfold rescaleTimestampChecked at hOk
  dsimp at hOk
  split at hOk
  · rename_i hBounds
    injection hOk with hSome
    injection hSome with hEq
    subst hEq
    exact ⟨rfl, hBounds⟩
  · contradiction

end LeanAV.Core
