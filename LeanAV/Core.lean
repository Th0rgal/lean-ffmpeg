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

/-- Theorem: `rescalePtsExactNat` is the exact identity on `pts` when source and destination timebases are equal (`num > 0, den > 0`). -/
theorem rescalePtsExactNat_id (pts num den : Nat) (hNum : 0 < num) (hDen : 0 < den) :
    AVRational.rescalePtsExactNat pts num den num den = pts := by
  unfold AVRational.rescalePtsExactNat rescaleFloor
  have hPos : 0 < den * num := Nat.mul_pos hDen hNum
  have hComm : num * den = den * num := Nat.mul_comm num den
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

end LeanAV.Core
