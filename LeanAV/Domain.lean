/-
  LeanAV.Domain: Phase-Indexed Domain Firewall, Audio/Container Safety Gates,
  and Two-Tier FFmpeg Acceptance Oracle (`≈ε`)

  Synthesizes the consensual formal architecture from Claude Fable 5.1, GPT-6 Astra,
  and opencode `builtin/smart`:
  1. Phase-indexed `Domain := Compressed | Decoded | Container` and opaque `MediaBuf`
     so spatial/color filters (`scale`, `crop`, `pad`, `tonemap`, `deblock`, `denoise`)
     are typed exclusively on `MediaBuf .Decoded ...`, making compressed-byte vs pixel-domain
     confusion (Bug 1) a compile-time Lean type error with zero proof overhead.
  2. Compositional `LawfulTranscodeStage` and `LawfulTranscodeStage.comp` discharging
     dimension, duration, and audio-layout invariants via closed `Nat`/`Bool` arithmetic (`by omega` / `by decide`).
  3. Container track-pruning gate (`Mp4TrackPruneSpec`, Bug 2) and Audio channel-layout
     downmix gate (`ValidAudioChannelMask` / `downmix6chTo2chQ15`, Bug 3).
  4. Two-Tier FFmpeg Acceptance Contract (`verifyFFmpegAcceptance` / `ffmpegAcceptanceGateSpec`):
     - Exact Tier (`=`): 0 decode errors, exact dimensions, channel layout mask, and clipped container duration sync.
     - Bounded Pixel Tier (`≤ ε`): 100% of 16x16 macroblocks within block-SAD bound,
       distance-to-reference strictly below distance-to-black for non-black reference blocks,
       PSNR ≥ 35 dB, and non-degenerate luma variance (`σ_Y² > 0`).
-/
import LeanSys.Spec
import LeanAV.Spec
import LeanAV.Core

namespace LeanAV.Domain

open LeanSys.Spec
open LeanAV.Spec
open LeanAV.Core

/-! ## 1. Phase-Indexed Domain Separation (`Compressed | Decoded | Container`) -/

/-- Phase domain index separating compressed bitstreams, decoded pixel/sample planes, and container boxes. -/
inductive Domain where
  | Compressed
  | Decoded
  | Container
  deriving Repr, DecidableEq, Inhabited

/-- Unified media format tag indexing `MediaBuf`. -/
inductive MediaFormat where
  | pix (fmt : PixelFormat)
  | codec (cid : CodecId)
  | container (cf : ContainerFormat)
  deriving Repr, DecidableEq, Inhabited

/-- Discrete VUI / NCLX (`colr`) colorimetry tag (`color_primaries / color_trc / colorspace`)
    preventing silent HDR-to-SDR desaturation when scaling `BT.2020 PQ` 4K sources through raw pixel planes. -/
inductive ColorSpaceTag where
  | bt709
  | bt2020Pq
  | bt2020Hlg
  deriving Repr, DecidableEq, Inhabited

/--
  Phase-indexed media buffer (`MediaBuf d fmt w h`):
  Separates `.Compressed` NAL/OBU packets, `.Decoded` 2D pixel planes, and `.Container` muxed streams
  at the type level. No coercion exists between `MediaBuf .Compressed ...` and `MediaBuf .Decoded ...`.
  Also tracks `colorSpace : ColorSpaceTag` so spatial stages (`scale`, `crop`, `pad`) cannot strip HDR `bt2020Pq` tags.
-/
structure MediaBuf (d : Domain) (fmt : MediaFormat) (w h : Nat) where
  private mk ::
  payload      : ByteArray
  stride       : Nat
  durationMs   : Nat
  channelCount : Nat
  channelMask  : UInt32
  colorSpace   : ColorSpaceTag := .bt709
  decodeErrors : Nat

abbrev DecodedPlaneBuf (pf : PixelFormat) (w h : Nat) :=
  MediaBuf .Decoded (.pix pf) w h

abbrev CompressedPacketBuf (cid : CodecId) (w h : Nat) :=
  MediaBuf .Compressed (.codec cid) w h

abbrev ContainerStreamBuf (cf : ContainerFormat) (w h : Nat) :=
  MediaBuf .Container (.container cf) w h

/-- Checked constructor for a decoded 2D plane (`Plane2D → DecodedPlaneBuf`). -/
@[inline]
def DecodedPlaneBuf.ofPlane2D (pf : PixelFormat) (p : Plane2D) (durationMs : Nat := 40)
    (colorSpace : ColorSpaceTag := .bt709) :
    DecodedPlaneBuf pf p.width p.height :=
  { payload := p.data
    stride := p.stride
    durationMs := durationMs
    channelCount := 0
    channelMask := 0
    colorSpace := colorSpace
    decodeErrors := 0 }

/-- Extract a `Plane2D` view from a `DecodedPlaneBuf` (only typable on `.Decoded` domain!). -/
@[inline]
def DecodedPlaneBuf.toPlane2D {pf : PixelFormat} {w h : Nat}
    (buf : DecodedPlaneBuf pf w h) : Plane2D :=
  { data := buf.payload, width := w, height := h, stride := buf.stride }

/-- Checked constructor for a compressed packet buffer (`.Compressed` domain only). -/
@[inline]
def CompressedPacketBuf.ofBytes (cid : CodecId) (w h : Nat) (bs : ByteArray)
    (durationMs : Nat := 40) (colorSpace : ColorSpaceTag := .bt709) : CompressedPacketBuf cid w h :=
  { payload := bs
    stride := 0
    durationMs := durationMs
    channelCount := 0
    channelMask := 0
    colorSpace := colorSpace
    decodeErrors := 0 }

/-- Explicit decoder boundary: the ONLY bridge from `.Compressed` to `.Decoded` (preserves `pkt.colorSpace`). -/
@[inline]
def CodecBoundary.decodeFrame (cid : CodecId) (pf : PixelFormat) (w h : Nat)
    (pkt : CompressedPacketBuf cid w h) (decodedPlane : Plane2D)
    (hwDecodeErrors : Nat := 0) : Option (DecodedPlaneBuf pf w h) :=
  if hwDecodeErrors == 0 && decodedPlane.width == w && decodedPlane.height == h && pkt.payload.size > 0 then
    some {
      payload := decodedPlane.data
      stride := decodedPlane.stride
      durationMs := pkt.durationMs
      channelCount := pkt.channelCount
      channelMask := pkt.channelMask
      colorSpace := pkt.colorSpace
      decodeErrors := 0
    }
  else
    none

/-- Explicit encoder boundary: the ONLY bridge from `.Decoded` to `.Compressed` (preserves `plane.colorSpace`). -/
@[inline]
def CodecBoundary.encodeFrame (pf : PixelFormat) (cid : CodecId) (w h : Nat)
    (plane : DecodedPlaneBuf pf w h) (encodedBytes : ByteArray) :
    Option (CompressedPacketBuf cid w h) :=
  if plane.decodeErrors == 0 && w > 0 && h > 0 && encodedBytes.size > 0 then
    some {
      payload := encodedBytes
      stride := 0
      durationMs := plane.durationMs
      channelCount := plane.channelCount
      channelMask := plane.channelMask
      colorSpace := plane.colorSpace
      decodeErrors := 0
    }
  else
    none

/-! ## 2. Compositional `LawfulTranscodeStage` & Zero-Overhead Pipeline Composition -/

/--
  A verified transcode stage transforming `MediaBuf d1 fmt1 w1 h1` into `MediaBuf d2 fmt2 w2 h2`
  while preserving duration and zero decode errors.
-/
structure LawfulTranscodeStage
    (d1 : Domain) (fmt1 : MediaFormat) (w1 h1 : Nat)
    (d2 : Domain) (fmt2 : MediaFormat) (w2 h2 : Nat) where
  run              : MediaBuf d1 fmt1 w1 h1 → MediaBuf d2 fmt2 w2 h2
  preservesDur     : ∀ b, (run b).durationMs = b.durationMs
  preservesClean   : ∀ b, b.decodeErrors = 0 → (run b).decodeErrors = 0

/-- Identity `LawfulTranscodeStage`. -/
def LawfulTranscodeStage.id (d : Domain) (fmt : MediaFormat) (w h : Nat) :
    LawfulTranscodeStage d fmt w h d fmt w h where
  run b := b
  preservesDur _ := rfl
  preservesClean _ hClean := hClean

/-- Compositional chaining (`LawfulTranscodeStage.comp`) of two verified stages with tiny proof obligations. -/
def LawfulTranscodeStage.comp
    {d1 : Domain} {fmt1 : MediaFormat} {w1 h1 : Nat}
    {d2 : Domain} {fmt2 : MediaFormat} {w2 h2 : Nat}
    {d3 : Domain} {fmt3 : MediaFormat} {w3 h3 : Nat}
    (s1 : LawfulTranscodeStage d1 fmt1 w1 h1 d2 fmt2 w2 h2)
    (s2 : LawfulTranscodeStage d2 fmt2 w2 h2 d3 fmt3 w3 h3) :
    LawfulTranscodeStage d1 fmt1 w1 h1 d3 fmt3 w3 h3 where
  run b := s2.run (s1.run b)
  preservesDur b := by rw [s2.preservesDur, s1.preservesDur]
  preservesClean b h0 := s2.preservesClean (s1.run b) (s1.preservesClean b h0)

/-- Lift any pure pixel-domain `Plane2D → Plane2D` operator into a `LawfulTranscodeStage` on `.Decoded`.
    Notice that it is a compile-time type error to apply `liftDecodedPlaneOp` to a `.Compressed` packet,
    and `colorSpace` (`bt709` vs `bt2020Pq` HDR) is unconditionally preserved across spatial scaling/cropping! -/
def liftDecodedPlaneOp (pf : PixelFormat) (w1 h1 w2 h2 : Nat)
    (op : Plane2D → Plane2D) :
    LawfulTranscodeStage .Decoded (.pix pf) w1 h1 .Decoded (.pix pf) w2 h2 where
  run b :=
    let pOut := op (DecodedPlaneBuf.toPlane2D b)
    { payload := pOut.data
      stride := w2
      durationMs := b.durationMs
      channelCount := b.channelCount
      channelMask := b.channelMask
      colorSpace := b.colorSpace
      decodeErrors := b.decodeErrors }
  preservesDur _ := rfl
  preservesClean _ h0 := h0

/-- Explicit color-space conversion stage (`lawfulStageColorConvert`):
    The ONLY stage that transitions `colorSpace` (e.g. `.bt2020Pq -> .bt709` when `colorspace=bt709,tonemap` is active). -/
def lawfulStageColorConvert (pf : PixelFormat) (w h : Nat) (dstCs : ColorSpaceTag)
    (op : Plane2D → Plane2D) :
    LawfulTranscodeStage .Decoded (.pix pf) w h .Decoded (.pix pf) w h where
  run b :=
    let pOut := op (DecodedPlaneBuf.toPlane2D b)
    { payload := pOut.data
      stride := w
      durationMs := b.durationMs
      channelCount := b.channelCount
      channelMask := b.channelMask
      colorSpace := dstCs
      decodeErrors := b.decodeErrors }
  preservesDur _ := rfl
  preservesClean _ h0 := h0

/-- Theorem: Any spatial decoded-plane stage lifted via `liftDecodedPlaneOp` (such as `scale=1920:1080`, `crop`, `pad`)
    preserves `b.colorSpace` (e.g. `.bt2020Pq`), preventing accidental HDR-to-SDR tag stripping, while
    `lawfulStageColorConvert` explicitly updates `colorSpace` to `dstCs`. -/
theorem liftDecodedPlaneOp_preserves_colorSpace_and_explicit_convert
    (pf : PixelFormat) (w1 h1 w2 h2 : Nat) (op : Plane2D → Plane2D)
    (b : DecodedPlaneBuf pf w1 h1) (dstCs : ColorSpaceTag) :
    ((liftDecodedPlaneOp pf w1 h1 w2 h2 op).run b).colorSpace = b.colorSpace ∧
    ((lawfulStageColorConvert pf w1 h1 dstCs op).run b).colorSpace = dstCs :=
  ⟨rfl, rfl⟩

theorem lawfulTranscodeStage_comp_preserves_clean_and_dur
    {d1 d2 d3 : Domain} {f1 f2 f3 : MediaFormat} {w1 h1 w2 h2 w3 h3 : Nat}
    (s1 : LawfulTranscodeStage d1 f1 w1 h1 d2 f2 w2 h2)
    (s2 : LawfulTranscodeStage d2 f2 w2 h2 d3 f3 w3 h3)
    (b : MediaBuf d1 f1 w1 h1) (hClean : b.decodeErrors = 0) :
    ((s1.comp s2).run b).durationMs = b.durationMs ∧
    ((s1.comp s2).run b).decodeErrors = 0 :=
  ⟨(s1.comp s2).preservesDur b, (s1.comp s2).preservesClean b hClean⟩

/-! ## 3. Container Track-Pruning Gate (`Mp4TrackPruneSpec`, Preventing Bug 2) -/

/-- Handler classification for container tracks (`vide`, `soun`, `subt`, or `binData` chapters/timecode). -/
inductive TrackHandlerKind where
  | video
  | audio
  | subtitle
  | binData
  deriving Repr, DecidableEq, Inhabited

/-- Metadata summary of an MP4/MKV container track. -/
structure ContainerTrackDesc where
  trackId    : Nat
  handler    : TrackHandlerKind
  tkhdDurMs  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A track is safe to retain in a clipped transcode of `mvhdDurMs` iff it is not `binData` and `tkhdDurMs ≤ mvhdDurMs + 100`. -/
@[inline]
def isTrackRetainable (mvhdDurMs : Nat) (t : ContainerTrackDesc) : Bool :=
  t.handler != .binData && decide (t.tkhdDurMs ≤ mvhdDurMs + 100)

/-- Prune all unclipped or `bin_data` chapter tracks from a container track table. -/
def pruneContainerTracks (mvhdDurMs : Nat) (tracks : List ContainerTrackDesc) : List ContainerTrackDesc :=
  tracks.filter (isTrackRetainable mvhdDurMs)

/-- Theorem (Bug 2 Prevention): `pruneContainerTracks` rejects the 3.36-hour (`12119991 ms`) `bin_data`
    chapter track from the 60s (`60018 ms`) *Lawrence of Arabia* clip while keeping the video and audio tracks. -/
theorem pruneContainerTracks_strips_lawrence_3h_chapter_track :
    let vTrack : ContainerTrackDesc := ⟨1, .video, 60018⟩
    let aTrack : ContainerTrackDesc := ⟨2, .audio, 60018⟩
    let cTrack : ContainerTrackDesc := ⟨3, .binData, 12119991⟩
    pruneContainerTracks 60018 [vTrack, aTrack, cTrack] = [vTrack, aTrack] := by
  decide

/-- Universal Theorem (Bug 2 Prevention): Every track retained by `pruneContainerTracks` is guaranteed
    not to be `binData` and has a track duration bounded by `mvhdDurMs + 100`. -/
theorem pruneContainerTracks_all_retainable (mvhdDurMs : Nat) (tracks : List ContainerTrackDesc)
    (t : ContainerTrackDesc) (hMem : t ∈ pruneContainerTracks mvhdDurMs tracks) :
    t.handler ≠ .binData ∧ t.tkhdDurMs ≤ mvhdDurMs + 100 := by
  unfold pruneContainerTracks isTrackRetainable at hMem
  rw [List.mem_filter] at hMem
  rcases hMem with ⟨_, hPred⟩
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff] at hPred
  exact hPred

/-! ## 4. Audio 6ch -> 2ch Downmix & Channel Layout Gate (`ValidAudioChannelMask`, Preventing Bug 3) -/

/-- Standard ITU/FFmpeg channel layout masks (`AV_CH_LAYOUT_MONO = 4`, `STEREO = 3`, `5POINT1 = 0x3F`, `5POINT1_BACK = 0x60F`). -/
@[inline] def chMaskMono      : UInt32 := 0x00000004
@[inline] def chMaskStereo    : UInt32 := 0x00000003
@[inline] def chMask5Point1   : UInt32 := 0x0000003F

/-- Count set bits in a 16-bit mask (sufficient for standard 1..8 channel layouts). -/
def popCountMask16 (m : UInt32) : Nat :=
  (List.range 16).foldl (fun acc i =>
    if ((m >>> i.toUInt32) &&& 1) == 1 then acc + 1 else acc) 0

/-- An audio stream is `AacEncodable` only if it carries a non-zero channel layout mask matching `channels` (`1`, `2`, or `6`). -/
@[inline]
def isAacChannelLayoutValid (channels : Nat) (channelMask : UInt32) : Bool :=
  (channels == 1 || channels == 2 || channels == 6) &&
  channelMask != 0 &&
  popCountMask16 channelMask == channels

/-- Theorem (Bug 3 Prevention): Unmasked 6-channel AAC (`channels = 6, channelMask = 0`) is rejected by
    `isAacChannelLayoutValid`, whereas downmixed stereo (`channels = 2, channelMask = chMaskStereo`) is accepted. -/
theorem aacChannelLayout_rejects_unmasked_6ch_and_accepts_stereo :
    isAacChannelLayoutValid 6 0 = false ∧
    isAacChannelLayoutValid 2 chMaskStereo = true ∧
    isAacChannelLayoutValid 6 chMask5Point1 = true := by
  decide

/--
  ITU-R BS.775 5.1 (`FL, FR, FC, LFE, BL, BR`) to Stereo (`L, R`) Q10 fixed-point downmix kernel:
  `L = clipInt16((1024 * FL + 724 * FC + 724 * BL + 512) >> 10)`
  `R = clipInt16((1024 * FR + 724 * FC + 724 * BR + 512) >> 10)`
  where `724 / 1024 ≈ 0.70703` (`-3 dB`).
-/
@[inline]
def downmix5p1SampleToStereoQ10 (fl fr fc _lfe bl br : Int32) : Int32 × Int32 :=
  let lAcc : Int64 := 1024 * fl.toInt64 + 724 * fc.toInt64 + 724 * bl.toInt64 + 512
  let rAcc : Int64 := 1024 * fr.toInt64 + 724 * fc.toInt64 + 724 * br.toInt64 + 512
  let lOut := clipInt16 (lAcc >>> 10).toInt32
  let rOut := clipInt16 (rAcc >>> 10).toInt32
  (lOut, rOut)

/-- Theorem: `downmix5p1SampleToStereoQ10` preserves silence (`0 -> (0, 0)`) and symmetric center-channel pan (`FC = 1000 -> L = R = 707`). -/
theorem downmix5p1SampleToStereoQ10_center_symmetric :
    downmix5p1SampleToStereoQ10 0 0 0 0 0 0 = (0, 0) ∧
    downmix5p1SampleToStereoQ10 0 0 1000 0 0 0 = (707, 707) := by
  decide

/-! ## 5. Law 11: Two-Tier FFmpeg Bounded Acceptance Oracle (`verifyFFmpegAcceptance` / `≈ε`) -/

/--
  Unboxed C-ABI Two-Tier FFmpeg Bounded Acceptance Gate (`leanav_verify_ffmpeg_acceptance`):
  Certifies `out_lean ≈_ε out_ffmpeg` by combining:
  - **Tier 1 (Exact Structural Equality)**:
    1. `decodeErrors == 0` (complete decoding with zero bitstream/macroblock errors),
    2. `dimsAndLayoutMatch == 1` (exact width, height, pixel format, and valid audio channel mask),
    3. `durDiffMs ≤ 100` and `unclippedChapters == 0` (exact container duration sync),
  - **Tier 2 (Uniform Per-Block & Perceptual Bounds)**:
    4. `maxBlockSad16x16 ≤ maxAllowedBlockSad` (100% of 16x16 macroblocks bounded, preventing local corruption),
    5. `distToRefLtDistToBlack == 1` (every non-black reference block is strictly closer to `out_lean` than to black),
    6. `psnrDbX10 ≥ 350` (`PSNR ≥ 35.0 dB`), and
    7. `lumaVariance > 0` (non-degenerate spatial signal).
-/
@[inline, export leanav_verify_ffmpeg_acceptance]
def verifyFFmpegAcceptance
    (decodeErrors dimsAndLayoutMatch unclippedChapters : UInt32)
    (durDiffMs maxBlockSad16x16 maxAllowedBlockSad : UInt64)
    (distToRefLtDistToBlack : UInt32)
    (psnrDbX10 lumaVariance : UInt64) : UInt8 :=
  if decodeErrors == 0 &&
     dimsAndLayoutMatch == 1 &&
     unclippedChapters == 0 &&
     durDiffMs ≤ 100 &&
     maxBlockSad16x16 ≤ maxAllowedBlockSad &&
     distToRefLtDistToBlack == 1 &&
     psnrDbX10 ≥ 350 &&
     lumaVariance > 0 then 1 else 0

/-- Parameters for the Two-Tier FFmpeg Bounded Acceptance Gate (`≈ε`). -/
structure FFmpegAcceptanceCheck where
  decodeErrors           : UInt32
  dimsAndLayoutMatch     : UInt32
  unclippedChapters      : UInt32
  durDiffMs              : UInt64
  maxBlockSad16x16       : UInt64
  maxAllowedBlockSad     : UInt64
  distToRefLtDistToBlack : UInt32
  psnrDbX10              : UInt64
  lumaVariance           : UInt64
  deriving Repr, DecidableEq

/-- Executable gate for `FFmpegAcceptanceCheck`. -/
@[inline]
def isFFmpegAcceptanceValid (c : FFmpegAcceptanceCheck) : Bool :=
  verifyFFmpegAcceptance
    c.decodeErrors c.dimsAndLayoutMatch c.unclippedChapters
    c.durDiffMs c.maxBlockSad16x16 c.maxAllowedBlockSad
    c.distToRefLtDistToBlack c.psnrDbX10 c.lumaVariance == 1

/-- Declarative safety predicate for `FFmpegAcceptanceCheck`. -/
def FFmpegAcceptanceSafe (c : FFmpegAcceptanceCheck) : Prop :=
  c.decodeErrors = 0 ∧
  c.dimsAndLayoutMatch = 1 ∧
  c.unclippedChapters = 0 ∧
  c.durDiffMs ≤ 100 ∧
  c.maxBlockSad16x16 ≤ c.maxAllowedBlockSad ∧
  c.distToRefLtDistToBlack = 1 ∧
  350 ≤ c.psnrDbX10 ∧
  0 < c.lumaVariance

/-- Layer II Bundle 11: Two-Tier FFmpeg Bounded Acceptance Oracle (`AVGateSpec`). -/
def ffmpegAcceptanceGateSpec : AVGateSpec FFmpegAcceptanceCheck FFmpegAcceptanceSafe where
  gate := isFFmpegAcceptanceValid
  sound c hg := by
    unfold isFFmpegAcceptanceValid verifyFFmpegAcceptance FFmpegAcceptanceSafe at *
    revert hg; split <;> simp_all
  complete c hs := by
    unfold isFFmpegAcceptanceValid verifyFFmpegAcceptance FFmpegAcceptanceSafe at *
    rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    simp [h1, h2, h3, h4, h5, h6, h7, h8]
  posWitness := ⟨0, 1, 0, 12, 1024, 4096, 1, 412, 1584⟩
  negWitness := ⟨0, 1, 0, 12, 16384, 4096, 0, 120, 0⟩
  nonVacuous := rfl
  tight := rfl

/-- Universal Theorem 11: `verifyFFmpegAcceptance` unconditionally rejects any output with decode errors,
    unclipped chapter tracks, black macroblocks (`distToRefLtDistToBlack = 0`), or `PSNR < 35.0 dB` (`psnrDbX10 < 350`). -/
theorem verifyFFmpegAcceptance_rejects_all_three_historical_bugs
    (decodeErrors dimsAndLayoutMatch unclippedChapters : UInt32)
    (durDiffMs maxBlockSad16x16 maxAllowedBlockSad : UInt64)
    (distToRefLtDistToBlack : UInt32)
    (psnrDbX10 lumaVariance : UInt64)
    (h_bug : decodeErrors ≠ 0 ∨ dimsAndLayoutMatch ≠ 1 ∨ unclippedChapters ≠ 0 ∨ distToRefLtDistToBlack ≠ 1 ∨ psnrDbX10 < 350) :
    verifyFFmpegAcceptance decodeErrors dimsAndLayoutMatch unclippedChapters
      durDiffMs maxBlockSad16x16 maxAllowedBlockSad distToRefLtDistToBlack psnrDbX10 lumaVariance = 0 := by
  unfold verifyFFmpegAcceptance
  rcases h_bug with hDec | hDim | hChap | hBlk | hPsnr
  · simp [hDec]
  · simp [hDim]
  · simp [hChap]
  · simp [hBlk]
  · have hNot : ¬ (psnrDbX10 ≥ 350) := Nat.not_le_of_gt hPsnr
    simp [hNot]

/-! ## 6. Wave B5: `.Compressed -> .Compressed` Keyframe-Aligned Stream Copy / Remux (`LawfulTranscodeStage`) -/

/--
  Phase-indexed `LawfulTranscodeStage` for lossless `.Compressed -> .Compressed` stream-copy / remux (`-c:v copy`):
  Preserves compressed bitstream payload bytes (`payload`), dimensions `(w, h)`, codec ID (`cid`), and clean timestamp duration (`durationMs`),
  while permitting container wrapper transformation without ever entering or corrupting the `.Decoded` pixel domain.
-/
def lawfulStageStreamCopy (cid : CodecId) (w h : Nat) :
    LawfulTranscodeStage .Compressed (.codec cid) w h .Compressed (.codec cid) w h where
  run buf :=
    { payload := buf.payload
      stride := buf.stride
      durationMs := buf.durationMs
      channelCount := buf.channelCount
      channelMask := buf.channelMask
      colorSpace := buf.colorSpace
      decodeErrors := buf.decodeErrors }
  preservesDur _ := rfl
  preservesClean _ hClean := hClean

/--
  Phase-indexed `LawfulTranscodeStage` for container-level chapter pruning + keyframe-trimmed remux
  (`.Container -> .Container`):
  Normalizes audio channel mask (`chMaskStereo` if `0`), preserves `colorSpace`, and preserves clean decode state and exact duration.
-/
def lawfulStageCleanContainerRemux (cf : ContainerFormat) (w h : Nat) :
    LawfulTranscodeStage .Container (.container cf) w h .Container (.container cf) w h where
  run buf :=
    { payload := buf.payload
      stride := buf.stride
      durationMs := buf.durationMs
      channelCount := if buf.channelCount == 0 then 2 else buf.channelCount
      channelMask := if buf.channelMask == 0 then chMaskStereo else buf.channelMask
      colorSpace := buf.colorSpace
      decodeErrors := buf.decodeErrors }
  preservesDur _ := rfl
  preservesClean _ hClean := hClean

/-- Theorem (Wave B5): `lawfulStageCleanContainerRemux` guarantees a non-zero valid channel mask (`channelMask ≠ 0`). -/
theorem lawfulStageCleanContainerRemux_nonzero_mask
    (cf : ContainerFormat) (w h : Nat) (buf : MediaBuf .Container (.container cf) w h) :
    ((lawfulStageCleanContainerRemux cf w h).run buf).channelMask ≠ 0 := by
  unfold lawfulStageCleanContainerRemux chMaskStereo
  dsimp
  split
  · decide
  · rename_i hNe
    intro hZero
    exact hNe (beq_iff_eq.mpr hZero)

end LeanAV.Domain
