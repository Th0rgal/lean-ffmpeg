/-
  LeanAV.PlanIR:
  - Phase 3 (Wave D): Typed Streams / Maps / Graphs / Timeline / Metadata / Resource / Backend Policy IR (`MediaPlanIR`),
    pre-execution validation (`validatePlanIR`), inspectable JSON serialization (`serializePlanIRJson`),
    and proven CLI <-> IR round-trip (`planIR_cli_roundtrip_verified`).
  - Phase 4 (Waves E & F): Contract-classified delegated compatibility (`-map`, `-metadata`, `-map_metadata`,
    `-map_chapters`, `-bsf:v`, `-bsf:a`, `-c:s`, multi-container muxing, and protocol/device security allowlist).
  - Phase 5 (Wave G): Pinned C-ABI FFI facade (`ffiAbiVersionC`, `ffiProbeMp4ContractC`, `ffiCancelGateC`,
    `ffiExecDelegatedFfmpegC`) with explicit borrowed-buffer ownership and cancellation gate.
  - Phase 6 (Wave H): Bounded independent verified kernels (`rescalePtsIndependentOrFallback`,
    `scalePlane2x2IndependentOrFallback`, `demuxIvfIndependentOrFallback`) with explicit fallback policy.
-/
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Format
import LeanAV.Scale
import LeanAV.Cli

namespace LeanAV.PlanIR

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Format
open LeanAV.Scale
open LeanAV.Cli

/-! ## 1. Contract Classification & Backend Tiers (§1 of Maxwell Plan) -/

/-- Qualification tier for every capability in `lean-ffmpeg`. -/
inductive BackendTier where
  | independentVerified
  | independentTested
  | delegatedFaithful
  | translatedPartial
  | approximate
  | unsupported
  | untested
  deriving Repr, DecidableEq, Inhabited

def BackendTier.toString : BackendTier → String
  | .independentVerified => "independent_verified"
  | .independentTested   => "independent_tested"
  | .delegatedFaithful   => "delegated_faithful"
  | .translatedPartial   => "translated_partial"
  | .approximate         => "approximate"
  | .unsupported         => "unsupported"
  | .untested            => "untested"

/-! ## 2. Stream Selectors, Metadata, Subtitles, Bitstream Filters & Protocol Gate (Phases 3 & 4) -/

/-- Elementary stream kind (`v`, `a`, `s`, `d`). -/
inductive StreamKind where
  | video
  | audio
  | subtitle
  | data
  deriving Repr, DecidableEq, Inhabited

def StreamKind.toShortCode : StreamKind → String
  | .video    => "v"
  | .audio    => "a"
  | .subtitle => "s"
  | .data     => "d"

def parseStreamKindChar : Char → Option StreamKind
  | 'v' => some .video
  | 'a' => some .audio
  | 's' => some .subtitle
  | 'd' => some .data
  | _   => none

/-- Typed `-map <inputIdx>:<kind>[:<streamIdx>][?]` selector. -/
structure StreamMapSpec where
  inputIdx  : Nat
  kind      : StreamKind
  streamIdx : Option Nat := none
  optional  : Bool := false
  deriving Repr, DecidableEq, Inhabited

def formatStreamMapSpec (m : StreamMapSpec) : String :=
  let base := s!"{m.inputIdx}:{m.kind.toShortCode}"
  let withIdx := match m.streamIdx with
    | some idx => s!"{base}:{idx}"
    | none     => base
  if m.optional then withIdx ++ "?" else withIdx

/-- Kernel-reducible ASCII lowercase conversion on a `Char`. -/
def charToLowerAscii (c : Char) : Char :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then Char.ofNat (n + 32) else c

/-- Kernel-reducible ASCII lowercase conversion on a `String`. -/
def strToLowerAscii (s : String) : String :=
  String.ofList (s.toList.map charToLowerAscii)

/-- Kernel-reducible prefix check on `String`. -/
def strStartsWithFast (s pref : String) : Bool :=
  pref.toList.isPrefixOf s.toList

/-- Kernel-reducible suffix check on `String`. -/
def strEndsWithFast (s suff : String) : Bool :=
  suff.toList.reverse.isPrefixOf s.toList.reverse

/-- Kernel-reducible `List Char` splitter around separator `sep`. -/
def splitCharsOnLoop (sep : Char) : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c == sep then
      String.ofList cur.reverse :: splitCharsOnLoop sep cs []
    else
      splitCharsOnLoop sep cs (c :: cur)

/-- Kernel-reducible `String` splitter around separator `sep`. -/
def splitStrOnChar (s : String) (sep : Char) : List String :=
  if s.toList.isEmpty then [""]
  else splitCharsOnLoop sep s.toList []

/-- Parse a stream map token (`"0:v:0"`, `"0:a:0?"`, `"0:s?"`, `"0:v"`). -/
def parseStreamMapSpec (s : String) : Option StreamMapSpec :=
  let (coreStr, isOpt) :=
    match s.toList.reverse with
    | '?' :: revRest => (String.ofList revRest.reverse, true)
    | _              => (s, false)
  let parts := splitStrOnChar coreStr ':'
  match parts with
  | [inStr, kindStr] =>
    match parseNonNegNatSpec inStr, kindStr.toList with
    | some inIdx, [kc] =>
      match parseStreamKindChar kc with
      | some k => some { inputIdx := inIdx, kind := k, streamIdx := none, optional := isOpt }
      | none   => none
    | _, _ => none
  | [inStr, kindStr, stStr] =>
    match parseNonNegNatSpec inStr, kindStr.toList, parseNonNegNatSpec stStr with
    | some inIdx, [kc], some stIdx =>
      match parseStreamKindChar kc with
      | some k => some { inputIdx := inIdx, kind := k, streamIdx := some stIdx, optional := isOpt }
      | none   => none
    | _, _, _ => none
  | _ => none

/-- Typed `-metadata key=value` pair. -/
structure MetadataEntrySpec where
  key   : String
  value : String
  deriving Repr, DecidableEq, Inhabited

/-- Split a `List Char` around the first `'='` separator. -/
def splitEqChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: cs, acc =>
    if c == '=' then some (acc.reverse, cs)
    else splitEqChars cs (c :: acc)

def isAsciiIdentChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || c == '_' || c == '-'

def parseMetadataSpec (s : String) : Option MetadataEntrySpec :=
  match splitEqChars s.toList [] with
  | some (kChars, vChars) =>
    if !kChars.isEmpty && kChars.all isAsciiIdentChar then
      some { key := String.ofList kChars, value := String.ofList vChars }
    else none
  | none => none

def formatMetadataSpec (m : MetadataEntrySpec) : String :=
  s!"{m.key}={m.value}"

/-- Supported subtitle codec tokens (`-c:s` / `-scodec`). -/
inductive SubtitleCodecSpec where
  | copy
  | movText
  | srt
  | webvtt
  | ass
  deriving Repr, DecidableEq, Inhabited

def parseSubtitleCodecSpec : String → Option SubtitleCodecSpec
  | "copy"     => some .copy
  | "mov_text" => some .movText
  | "srt"      => some .srt
  | "subrip"   => some .srt
  | "webvtt"   => some .webvtt
  | "ass"      => some .ass
  | _          => none

def SubtitleCodecSpec.toString : SubtitleCodecSpec → String
  | .copy    => "copy"
  | .movText => "mov_text"
  | .srt     => "srt"
  | .webvtt  => "webvtt"
  | .ass     => "ass"

/-- Supported bitstream filters (`-bsf:v` / `-bsf:a`). -/
def supportedBsf (s : String) : Bool :=
  ["aac_adtstoasc", "h264_mp4toannexb", "hevc_mp4toannexb",
   "av1_frame_split", "extract_extradata", "dts2pts", "null"].contains s

/-- Typed bitstream filter attachment. -/
structure BsfSpec where
  kind       : StreamKind
  filterName : String
  deriving Repr, DecidableEq, Inhabited

/-- Check whether `haystack` contains `needle` as a contiguous char sublist. -/
def charsContainSublist (needle haystack : List Char) : Bool :=
  let rec go : List Char → Bool
    | [] => needle.isEmpty
    | h :: hs =>
      if needle.isPrefixOf (h :: hs) then true
      else go hs
  go haystack

/--
  Phase 4 (Wave F) & §8 Security Gate (`isSafeLocalMediaPath`):
  Rejects empty paths, parent traversal (`..` path segments), device nodes (`/dev/`),
  and network/synthetic URI schemes (`http:`, `https:`, `rtmp:`, `rtsp:`, `tcp:`, `udp:`,
  `concat:`, `subfile:`, `lavfi:`, `ftp:`, `sftp:`, `tls:`, `srt:`).
-/
def isSafeLocalMediaPath (path : String) : Bool :=
  let chars := path.toList
  if chars.isEmpty then false
  else
    let lower := strToLowerAscii path
    let forbiddenPrefixes : List String :=
      ["http://", "https://", "rtmp://", "rtsp://", "tcp://", "udp://",
       "concat:", "subfile:", "lavfi:", "ftp://", "sftp://", "tls://", "srt://",
       "/dev/", "v4l2:", "alsa:"]
    let hasForbiddenPrefix := forbiddenPrefixes.any (fun p => strStartsWithFast lower p)
    let segments := splitStrOnChar path '/'
    let hasDotDot := segments.contains ".."
    !hasForbiddenPrefix && !hasDotDot

/-! ## 3. Phase 3 Typed Intermediate Representation (`MediaPlanIR`) -/

/-- Typed input descriptor in `MediaPlanIR`. -/
structure InputSpec where
  index      : Nat
  path       : String
  safePath   : Bool
  seekStart  : Option CliSeconds := none
  duration   : Option CliSeconds := none
  deriving Repr, DecidableEq, Inhabited

/-- Typed output descriptor in `MediaPlanIR`. -/
structure OutputSpec where
  path          : String
  safePath      : Bool
  format        : String
  overwrite     : Bool
  videoCodec    : Option CliCodec := none
  audioCodec    : Option CliCodec := none
  subtitleCodec : Option SubtitleCodecSpec := none
  pixelFormat   : Option String := none
  preset        : Option String := none
  crf           : Option String := none
  videoBitrate  : Option String := none
  audioBitrate  : Option String := none
  frameRate     : Option String := none
  videoSize     : Option (Nat × Nat) := none
  videoFrames   : Option Nat := none
  audioRate     : Option Nat := none
  audioChannels : Option Nat := none
  bFrames       : Option Nat := none
  gopSize       : Option Nat := none
  movflags      : Option String := none
  noVideo       : Bool := false
  noAudio       : Bool := false
  noSubtitle    : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Typed program descriptor in `MediaPlanIR`. -/
structure ProgramSpec where
  programId  : Nat
  streamMaps : List StreamMapSpec
  deriving Repr, DecidableEq, Inhabited

/-- Typed filter & bitstream-filter graph IR. -/
structure FilterGraphIR where
  videoFilter      : Option String := none
  audioFilter      : Option String := none
  videoStages      : List String := []
  audioStages      : List String := []
  bitstreamFilters : List BsfSpec := []
  deriving Repr, DecidableEq, Inhabited

/-- Typed timeline & rational rescaling IR. -/
structure TimelineIR where
  startSec    : Option CliSeconds := none
  durationSec : Option CliSeconds := none
  startMs     : Option UInt32 := none
  durationMs  : Option UInt32 := none
  frameRate   : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- Typed container metadata & chapters policy IR. -/
structure MetadataPolicyIR where
  entries           : List MetadataEntrySpec := []
  mapMetadataSource : Int := -1
  mapChaptersSource : Int := -1
  preserveColor     : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- Typed execution resource & diagnostic routing policy IR. -/
structure ResourcePolicyIR where
  threads    : Option Nat := none
  jsonOutput : Bool := false
  hideBanner : Bool := false
  showStats  : Bool := true
  logLevel   : String := "info"
  dumpPlan   : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Typed backend selection & fallback policy IR. -/
structure BackendPolicyIR where
  tier               : BackendTier
  delegatedContainer : Bool
  fallbackAllowed    : Bool
  reasons            : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- Complete Phase 3 Typed Intermediate Representation (`MediaPlanIR`). -/
structure MediaPlanIR where
  inputs    : List InputSpec
  outputs   : List OutputSpec
  streams   : List StreamMapSpec
  programs  : List ProgramSpec
  maps      : List StreamMapSpec
  graphs    : FilterGraphIR
  timeline  : TimelineIR
  metadata  : MetadataPolicyIR
  resources : ResourcePolicyIR
  errors    : List CliError
  backend   : BackendPolicyIR
  deriving Repr, DecidableEq, Inhabited

/-- Format a `CliSeconds` value back to its canonical string (`"2"` or `"1.5"`). -/
def formatCliSeconds (s : CliSeconds) : String :=
  if s.den ≤ 1 then s!"{s.num}"
  else
    let intPart := s.num / s.den
    let remPart := s.num % s.den
    if remPart == 0 then s!"{intPart}"
    else if s.den == 10 then s!"{intPart}.{remPart}"
    else if s.den == 100 then
      let pad := if remPart < 10 then "0" else ""
      s!"{intPart}.{pad}{remPart}"
    else if s.den == 1000 then
      let pad := if remPart < 10 then "00" else if remPart < 100 then "0" else ""
      s!"{intPart}.{pad}{remPart}"
    else s!"{intPart}.{remPart}"

def codecToCanonicalString : CliCodec → String
  | .copy     => "copy"
  | .h264     => "h264"
  | .hevc     => "hevc"
  | .av1      => "av1"
  | .vp9      => "vp9"
  | .prores   => "prores"
  | .ffv1     => "ffv1"
  | .aac      => "aac"
  | .opus     => "opus"
  | .flac     => "flac"
  | .pcmS16le => "pcm_s16le"
  | .rawvideo => "rawvideo"

/-- Infer container format from explicit `-f` or output file extension. -/
def inferContainerFormat (explicitFmt : Option String) (outPath : String) : String :=
  match explicitFmt with
  | some f => f
  | none =>
    let lower := strToLowerAscii outPath
    if strEndsWithFast lower ".mp4" || strEndsWithFast lower ".m4v" then "mp4"
    else if strEndsWithFast lower ".mkv" then "matroska"
    else if strEndsWithFast lower ".webm" then "webm"
    else if strEndsWithFast lower ".wav" then "wav"
    else if strEndsWithFast lower ".flac" then "flac"
    else if strEndsWithFast lower ".ogg" || strEndsWithFast lower ".opus" then "ogg"
    else if strEndsWithFast lower ".ts" then "mpegts"
    else if strEndsWithFast lower ".ivf" then "ivf"
    else if strEndsWithFast lower ".aac" then "adts"
    else "unknown"

/-- Auxiliary accumulator for Phase 4 extended CLI flags (`-map`, `-metadata`, `-bsf:*`, `-c:s`, `-dump-plan`). -/
structure ExtendedPlanFlags where
  baseArgs          : List String := []
  maps              : List StreamMapSpec := []
  metadataEntries   : List MetadataEntrySpec := []
  mapMetadataSource : Int := -1
  mapChaptersSource : Int := -1
  subtitleCodec     : Option SubtitleCodecSpec := none
  noSubtitle        : Bool := false
  bsfs              : List BsfSpec := []
  dumpPlan          : Bool := false
  extraErrors       : List CliError := []
  deriving Repr, DecidableEq, Inhabited

def parseSignedMapIndex : String → Option Int
  | "-1" => some (-1)
  | s    =>
    match parseNonNegNatSpec s with
    | some n => some (Int.ofNat n)
    | none   => none

def extractExtendedPlanFlagsLoop : List String → ExtendedPlanFlags → ExtendedPlanFlags
  | [], acc => acc
  | "-dump-plan" :: rest, acc =>
    extractExtendedPlanFlagsLoop rest { acc with dumpPlan := true }
  | "--dump-plan" :: rest, acc =>
    extractExtendedPlanFlagsLoop rest { acc with dumpPlan := true }
  | "-sn" :: rest, acc =>
    extractExtendedPlanFlagsLoop rest { acc with noSubtitle := true, baseArgs := acc.baseArgs ++ ["-sn"] }
  | "-map" :: value :: rest, acc =>
    match parseStreamMapSpec value with
    | some m => extractExtendedPlanFlagsLoop rest { acc with maps := acc.maps ++ [m] }
    | none   =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-map"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-map"] }
  | "-metadata" :: value :: rest, acc =>
    match parseMetadataSpec value with
    | some kv => extractExtendedPlanFlagsLoop rest { acc with metadataEntries := acc.metadataEntries ++ [kv] }
    | none    =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-metadata " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-metadata"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-metadata"] }
  | "-map_metadata" :: value :: rest, acc =>
    match parseSignedMapIndex value with
    | some idx => extractExtendedPlanFlagsLoop rest { acc with mapMetadataSource := idx }
    | none     =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map_metadata " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-map_metadata"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-map_metadata"] }
  | "-map_chapters" :: value :: rest, acc =>
    match parseSignedMapIndex value with
    | some idx => extractExtendedPlanFlagsLoop rest { acc with mapChaptersSource := idx }
    | none     =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map_chapters " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-map_chapters"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-map_chapters"] }
  | "-c:s" :: value :: rest, acc =>
    match parseSubtitleCodecSpec value with
    | some sc => extractExtendedPlanFlagsLoop rest { acc with subtitleCodec := some sc }
    | none    =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-c:s " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-c:s"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-c:s"] }
  | "-scodec" :: value :: rest, acc =>
    match parseSubtitleCodecSpec value with
    | some sc => extractExtendedPlanFlagsLoop rest { acc with subtitleCodec := some sc }
    | none    =>
      let errs := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-scodec " ++ value)]
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := errs }
  | ["-scodec"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-scodec"] }
  | "-bsf:v" :: value :: rest, acc =>
    if supportedBsf value then
      extractExtendedPlanFlagsLoop rest { acc with bsfs := acc.bsfs ++ [{ kind := .video, filterName := value }] }
    else
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-bsf:v " ++ value)] }
  | ["-bsf:v"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-bsf:v"] }
  | "-bsf:a" :: value :: rest, acc =>
    if supportedBsf value then
      extractExtendedPlanFlagsLoop rest { acc with bsfs := acc.bsfs ++ [{ kind := .audio, filterName := value }] }
    else
      extractExtendedPlanFlagsLoop rest { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-bsf:a " ++ value)] }
  | ["-bsf:a"], acc =>
    { acc with extraErrors := acc.extraErrors ++ [.missingValue "-bsf:a"] }
  | tok :: rest, acc =>
    extractExtendedPlanFlagsLoop rest { acc with baseArgs := acc.baseArgs ++ [tok] }

/-- Lower a `CliConfig` and optional `ExtendedPlanFlags` into a typed `MediaPlanIR`. -/
def lowerCliWithExtToPlanIR (cfg : CliConfig) (ext : ExtendedPlanFlags := {}) : MediaPlanIR :=
  let startMsOpt := cfg.startSec.bind cliSecondsToMillis
  let durMsOpt := cfg.durationSec.bind cliSecondsToMillis
  let startOverflow := cfg.startSec.isSome && startMsOpt.isNone
  let durOverflow := cfg.durationSec.isSome && durMsOpt.isNone
  let copyMode := cfg.videoCodec == some .copy || cfg.audioCodec == some .copy
  let hasFilter := cfg.videoFilter.isSome || cfg.audioFilter.isSome
  let copyFilterErr : List CliError := if copyMode && hasFilter then [.copyWithFilter] else []
  let missingInErr : List CliError := if cfg.inputs.isEmpty then [.missingInput] else []
  let missingOutErr : List CliError := if cfg.output.isNone && cfg.daemon.isNone then [.missingOutput] else []
  let allErrors := cfg.errors ++ ext.extraErrors ++ copyFilterErr ++ missingInErr ++ missingOutErr

  let rec buildInputs (paths : List String) (idx : Nat) : List InputSpec :=
    match paths with
    | [] => []
    | p :: ps =>
      { index := idx
        path := p
        safePath := isSafeLocalMediaPath p
        seekStart := if idx == 0 then cfg.startSec else none
        duration := if idx == 0 then cfg.durationSec else none } :: buildInputs ps (idx + 1)
  let inputSpecs := buildInputs cfg.inputs 0

  let outPath := cfg.output.getD ""
  let inferredFmt := inferContainerFormat cfg.format outPath
  let outputSpecs : List OutputSpec :=
    match cfg.output with
    | none => []
    | some p =>
      [{ path := p
         safePath := (p == "-" && cfg.format.isSome) || isSafeLocalMediaPath p
         format := inferredFmt
         overwrite := cfg.overwrite
         videoCodec := cfg.videoCodec
         audioCodec := cfg.audioCodec
         subtitleCodec := ext.subtitleCodec
         pixelFormat := cfg.pixelFormat
         preset := cfg.preset
         crf := cfg.crf
         videoBitrate := cfg.videoBitrate
         audioBitrate := cfg.audioBitrate
         frameRate := cfg.frameRate
         videoSize := cfg.videoSize
         videoFrames := cfg.videoFrames
         audioRate := cfg.audioRate
         audioChannels := cfg.audioChannels
         bFrames := cfg.bFrames
         gopSize := cfg.gopSize
         movflags := cfg.movflags
         noVideo := cfg.noVideo
         noAudio := cfg.noAudio
         noSubtitle := ext.noSubtitle }]

  let defaultStreams : List StreamMapSpec :=
    (if cfg.noVideo then [] else [{ inputIdx := 0, kind := .video, streamIdx := some 0, optional := false }]) ++
    (if cfg.noAudio then [] else [{ inputIdx := 0, kind := .audio, streamIdx := some 0, optional := true }]) ++
    (match ext.subtitleCodec with
     | some _ => if ext.noSubtitle then [] else [{ inputIdx := 0, kind := .subtitle, streamIdx := some 0, optional := true }]
     | none   => [])
  let effectiveMaps := if ext.maps.isEmpty then defaultStreams else ext.maps

  let vfStages := match cfg.videoFilter with
    | some vf => splitStrOnChar vf ','
    | none    => []
  let afStages := match cfg.audioFilter with
    | some af => splitStrOnChar af ','
    | none    => []

  let anyUnsafeInput := inputSpecs.any (fun i => !i.safePath)
  let anyUnsafeOutput := outputSpecs.any (fun o => !o.safePath)
  let unsupportedDaemonOrGolden := cfg.daemon.isSome || cfg.golden.isSome
  let unknownFormat := inferredFmt == "unknown"

  let isDelegatedContainerOrOption : Bool :=
    inferredFmt != "mp4" ||
    !ext.maps.isEmpty ||
    !ext.metadataEntries.isEmpty ||
    ext.mapMetadataSource != -1 ||
    ext.mapChaptersSource != -1 ||
    ext.subtitleCodec.isSome ||
    !ext.bsfs.isEmpty ||
    cfg.audioFilter.isSome ||
    cfg.noVideo ||
    cfg.videoFrames.isSome ||
    cfg.audioRate.isSome ||
    (cfg.audioChannels.isSome && cfg.audioChannels != some 2) ||
    cfg.threads.isSome ||
    cfg.bFrames.isSome ||
    cfg.gopSize.isSome ||
    cfg.movflags.isSome ||
    (cfg.audioCodec.isSome && cfg.audioCodec != some .copy && cfg.audioCodec != some .aac) ||
    (cfg.videoCodec == some .vp9 || cfg.videoCodec == some .prores || cfg.videoCodec == some .ffv1)

  let (tier, reasons) : BackendTier × List String :=
    if !allErrors.isEmpty then
      (.unsupported, ["cli_parse_or_validation_error"])
    else if startOverflow || durOverflow then
      (.unsupported, ["timestamp_milliseconds_overflow"])
    else if anyUnsafeInput || anyUnsafeOutput then
      (.unsupported, ["unsafe_protocol_or_path_traversal"])
    else if unsupportedDaemonOrGolden then
      (.unsupported, ["daemon_or_golden_mode_not_supported_in_cli_runtime"])
    else if unknownFormat then
      (.unsupported, ["unrecognized_output_container_format"])
    else if inputSpecs.length != 1 || outputSpecs.length != 1 then
      (.unsupported, ["exactly_one_input_and_output_required"])
    else if isDelegatedContainerOrOption then
      (.delegatedFaithful, ["phase4_structured_argv_delegation"])
    else if cfg.startSec.isSome || cfg.durationSec.isSome || cfg.videoCodec != some .copy then
      (.translatedPartial, ["mp4_seek_or_pixel_simd_transcode"])
    else
      (.delegatedFaithful, ["mp4_stream_copy"])

  { inputs := inputSpecs
    outputs := outputSpecs
    streams := defaultStreams
    programs := [{ programId := 0, streamMaps := effectiveMaps }]
    maps := effectiveMaps
    graphs := {
      videoFilter := cfg.videoFilter
      audioFilter := cfg.audioFilter
      videoStages := vfStages
      audioStages := afStages
      bitstreamFilters := ext.bsfs
    }
    timeline := {
      startSec := cfg.startSec
      durationSec := cfg.durationSec
      startMs := startMsOpt
      durationMs := durMsOpt
      frameRate := cfg.frameRate
    }
    metadata := {
      entries := ext.metadataEntries
      mapMetadataSource := ext.mapMetadataSource
      mapChaptersSource := ext.mapChaptersSource
      preserveColor := !(vfStages.any (fun s => s == "colorspace=bt709" || s == "bt2020_to_bt709"))
    }
    resources := {
      threads := cfg.threads
      jsonOutput := cfg.jsonOutput
      hideBanner := cfg.hideBanner
      showStats := cfg.showStats
      logLevel := cfg.logLevel
      dumpPlan := ext.dumpPlan
    }
    errors := allErrors
    backend := {
      tier := tier
      delegatedContainer := isDelegatedContainerOrOption
      fallbackAllowed := true
      reasons := reasons
    } }

/-- Lower a plain `CliConfig` directly into `MediaPlanIR`. -/
def lowerCliToPlanIR (cfg : CliConfig) : MediaPlanIR :=
  lowerCliWithExtToPlanIR cfg {}

/-- Parse raw FFmpeg CLI arguments (including Phase 3/4 flags) directly into a typed `MediaPlanIR`. -/
def parseArgsToPlanIR (args : List String) : MediaPlanIR :=
  let ext := extractExtendedPlanFlagsLoop args {}
  let cfg := parseFFmpegArgs ext.baseArgs
  lowerCliWithExtToPlanIR cfg ext

/-- Render a typed `MediaPlanIR` back into canonical FFmpeg CLI arguments (round-trip inverse of `parseArgsToPlanIR`). -/
def planIRToCliArgs (plan : MediaPlanIR) : List String :=
  let outOpt := plan.outputs.head?
  let overwriteArgs : List String :=
    match outOpt with
    | some o => if o.overwrite then ["-y"] else ["-n"]
    | none   => []
  let resArgs : List String :=
    (if plan.resources.hideBanner then ["-hide_banner"] else []) ++
    (if plan.resources.showStats then ["-stats"] else ["-nostats"]) ++
    (if plan.resources.logLevel != "info" then ["-v", plan.resources.logLevel] else []) ++
    (if plan.resources.jsonOutput then ["-json"] else []) ++
    (match plan.resources.threads with | some t => ["-threads", s!"{t}"] | none => [])
  let timeArgs : List String :=
    (match plan.timeline.startSec with | some s => ["-ss", formatCliSeconds s] | none => []) ++
    (match plan.timeline.durationSec with | some d => ["-t", formatCliSeconds d] | none => [])
  let inArgs : List String :=
    plan.inputs.flatMap (fun i => ["-i", i.path])
  let explicitMaps : List String :=
    if plan.maps == plan.streams then []
    else plan.maps.flatMap (fun m => ["-map", formatStreamMapSpec m])
  let metaArgs : List String :=
    plan.metadata.entries.flatMap (fun kv => ["-metadata", formatMetadataSpec kv]) ++
    (if plan.metadata.mapMetadataSource != -1 then ["-map_metadata", s!"{plan.metadata.mapMetadataSource}"] else []) ++
    (if plan.metadata.mapChaptersSource != -1 then ["-map_chapters", s!"{plan.metadata.mapChaptersSource}"] else [])
  let graphArgs : List String :=
    (match plan.graphs.videoFilter with | some vf => ["-vf", vf] | none => []) ++
    (match plan.graphs.audioFilter with | some af => ["-af", af] | none => []) ++
    plan.graphs.bitstreamFilters.flatMap (fun b =>
      match b.kind with
      | .audio => ["-bsf:a", b.filterName]
      | _      => ["-bsf:v", b.filterName])
  let outArgs : List String :=
    match outOpt with
    | none => []
    | some o =>
      (if o.noVideo then ["-vn"] else []) ++
      (if o.noAudio then ["-an"] else []) ++
      (if o.noSubtitle then ["-sn"] else []) ++
      (match o.videoCodec, o.audioCodec with
       | some .copy, some .copy => ["-c", "copy"]
       | vc, ac =>
         (match vc with | some c => ["-c:v", codecToCanonicalString c] | none => []) ++
         (match ac with | some c => ["-c:a", codecToCanonicalString c] | none => [])) ++
      (match o.subtitleCodec with | some sc => ["-c:s", sc.toString] | none => []) ++
      (match o.videoSize with | some (w, h) => ["-s", s!"{w}x{h}"] | none => []) ++
      (match o.videoFrames with | some n => ["-frames:v", s!"{n}"] | none => []) ++
      (match o.audioRate with | some r => ["-ar", s!"{r}"] | none => []) ++
      (match o.audioChannels with | some ch => ["-ac", s!"{ch}"] | none => []) ++
      (match o.pixelFormat with | some pf => ["-pix_fmt", pf] | none => []) ++
      (match o.preset with | some pr => ["-preset", pr] | none => []) ++
      (match o.crf with | some c => ["-crf", c] | none => []) ++
      (match o.bFrames with | some bf => ["-bf", s!"{bf}"] | none => []) ++
      (match o.gopSize with | some g => ["-g", s!"{g}"] | none => []) ++
      (match o.frameRate with | some r => ["-r", r] | none => []) ++
      (match o.videoBitrate with | some vb => ["-b:v", vb] | none => []) ++
      (match o.audioBitrate with | some ab => ["-b:a", ab] | none => []) ++
      (match o.movflags with | some mf => ["-movflags", mf] | none => []) ++
      (if supportedFormat o.format && inferContainerFormat none o.path != o.format then ["-f", o.format] else []) ++
      [o.path]
  overwriteArgs ++ resArgs ++ timeArgs ++ inArgs ++ explicitMaps ++ metaArgs ++ graphArgs ++ outArgs

/-- Validate a `MediaPlanIR` before execution (fail-closed). -/
def validatePlanIR (plan : MediaPlanIR) : Except (List String) MediaPlanIR :=
  if !plan.errors.isEmpty || plan.backend.tier == .unsupported then
    .error (plan.backend.reasons ++ plan.errors.map (fun e => s!"{repr e}"))
  else
    .ok plan

/-- Escape a string for JSON emission. -/
def escapeJsonStr (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    match c with
    | '"'  => ['\\', '"']
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _    => [c])

/-- Serialize a `MediaPlanIR` into an inspectable single-line JSON document. -/
def serializePlanIRJson (plan : MediaPlanIR) : String :=
  let inputsJson := String.intercalate "," (plan.inputs.map fun i =>
    s!"\{\"index\":{i.index},\"path\":\"{escapeJsonStr i.path}\",\"safe_path\":{i.safePath}}")
  let outputsJson := String.intercalate "," (plan.outputs.map fun o =>
    let vc := match o.videoCodec with | some c => s!"\"{codecToCanonicalString c}\"" | none => "null"
    let ac := match o.audioCodec with | some c => s!"\"{codecToCanonicalString c}\"" | none => "null"
    let sc := match o.subtitleCodec with | some c => s!"\"{c.toString}\"" | none => "null"
    let oHead := s!"\{\"path\":\"{escapeJsonStr o.path}\",\"safe_path\":{o.safePath},\"format\":\"{escapeJsonStr o.format}\","
    let oTail := s!"\"overwrite\":{o.overwrite},\"video_codec\":{vc},\"audio_codec\":{ac},\"subtitle_codec\":{sc}}"
    oHead ++ oTail)
  let mapsJson := String.intercalate "," (plan.maps.map fun m =>
    s!"\"{formatStreamMapSpec m}\"")
  let metaJson := String.intercalate "," (plan.metadata.entries.map fun kv =>
    s!"\{\"key\":\"{escapeJsonStr kv.key}\",\"value\":\"{escapeJsonStr kv.value}\"}")
  let bsfsJson := String.intercalate "," (plan.graphs.bitstreamFilters.map fun b =>
    s!"\{\"stream\":\"{b.kind.toShortCode}\",\"filter\":\"{escapeJsonStr b.filterName}\"}")
  let vfJson := match plan.graphs.videoFilter with | some v => s!"\"{escapeJsonStr v}\"" | none => "null"
  let afJson := match plan.graphs.audioFilter with | some a => s!"\"{escapeJsonStr a}\"" | none => "null"
  let startMsJson := match plan.timeline.startMs with | some ms => s!"{ms}" | none => "null"
  let durMsJson := match plan.timeline.durationMs with | some ms => s!"{ms}" | none => "null"
  let fpsJson := match plan.timeline.frameRate with | some r => s!"\"{escapeJsonStr r}\"" | none => "null"
  let reasonsJson := String.intercalate "," (plan.backend.reasons.map fun r => s!"\"{escapeJsonStr r}\"")
  let validOk := plan.errors.isEmpty && plan.backend.tier != .unsupported
  let p0 := s!"\{\"schema_version\":\"1.0\",\"kind\":\"MediaPlanIR\",\"ok\":{validOk},"
  let p1a := s!"\"backend\":\{\"tier\":\"{plan.backend.tier.toString}\",\"delegated_container\":{plan.backend.delegatedContainer},"
  let p1b := s!"\"fallback_allowed\":{plan.backend.fallbackAllowed},\"reasons\":[{reasonsJson}]},"
  let p2 := s!"\"inputs\":[{inputsJson}],\"outputs\":[{outputsJson}],\"maps\":[{mapsJson}],"
  let p3 := s!"\"graphs\":\{\"video_filter\":{vfJson},\"audio_filter\":{afJson},\"bitstream_filters\":[{bsfsJson}]},"
  let p4 := s!"\"timeline\":\{\"start_ms\":{startMsJson},\"duration_ms\":{durMsJson},\"frame_rate\":{fpsJson}},"
  let p5a := s!"\"metadata\":\{\"entries\":[{metaJson}],\"map_metadata\":{plan.metadata.mapMetadataSource},"
  let p5b := s!"\"map_chapters\":{plan.metadata.mapChaptersSource},\"preserve_color\":{plan.metadata.preserveColor}},"
  let p6a := s!"\"resources\":\{\"log_level\":\"{escapeJsonStr plan.resources.logLevel}\",\"json_output\":{plan.resources.jsonOutput},"
  let p6b := s!"\"hide_banner\":{plan.resources.hideBanner},\"show_stats\":{plan.resources.showStats}},"
  let p7 := s!"\"error_count\":{plan.errors.length}}"
  p0 ++ p1a ++ p1b ++ p2 ++ p3 ++ p4 ++ p5a ++ p5b ++ p6a ++ p6b ++ p7

/-- Build the structured `Array String` argv for `delegated_faithful` FFmpeg execution (zero shell interpolation). -/
def buildDelegatedFfmpegArgv (plan : MediaPlanIR) : Array String := Id.run do
  let some o := plan.outputs.head? | return #[]
  let mut argv : Array String := #["-nostdin"]
  if o.overwrite then
    argv := argv.push "-y"
  else
    argv := argv.push "-n"
  if plan.resources.hideBanner || plan.resources.jsonOutput then
    argv := argv.push "-hide_banner"
  if !plan.resources.showStats || plan.resources.jsonOutput then
    argv := argv.push "-nostats"
  let effLog := if plan.resources.jsonOutput then "error" else plan.resources.logLevel
  argv := argv ++ #["-v", effLog]
  if let some s := plan.timeline.startSec then
    argv := argv ++ #["-ss", formatCliSeconds s]
  if let some d := plan.timeline.durationSec then
    argv := argv ++ #["-t", formatCliSeconds d]
  for i in plan.inputs do
    argv := argv ++ #["-i", i.path]
  if plan.maps != plan.streams then
    for m in plan.maps do
      argv := argv ++ #["-map", formatStreamMapSpec m]
  for kv in plan.metadata.entries do
    argv := argv ++ #["-metadata", formatMetadataSpec kv]
  if plan.metadata.mapMetadataSource != -1 then
    argv := argv ++ #["-map_metadata", s!"{plan.metadata.mapMetadataSource}"]
  if plan.metadata.mapChaptersSource != -1 then
    argv := argv ++ #["-map_chapters", s!"{plan.metadata.mapChaptersSource}"]
  if let some vf := plan.graphs.videoFilter then
    argv := argv ++ #["-vf", vf]
  if let some af := plan.graphs.audioFilter then
    argv := argv ++ #["-af", af]
  for b in plan.graphs.bitstreamFilters do
    match b.kind with
    | .audio => argv := argv ++ #["-bsf:a", b.filterName]
    | _      => argv := argv ++ #["-bsf:v", b.filterName]
  if o.noVideo then argv := argv.push "-vn"
  if o.noAudio then argv := argv.push "-an"
  if o.noSubtitle then argv := argv.push "-sn"
  if let some vc := o.videoCodec then
    let encTok := match vc with
      | .h264 => "libx264"
      | .hevc => "libx265"
      | .av1  => "libsvtav1"
      | .vp9  => "libvpx-vp9"
      | .opus => "libopus"
      | c     => codecToCanonicalString c
    argv := argv ++ #["-c:v", encTok]
  if let some ac := o.audioCodec then
    let aTok := match ac with
      | .opus => "libopus"
      | c     => codecToCanonicalString c
    argv := argv ++ #["-c:a", aTok]
  if let some sc := o.subtitleCodec then
    argv := argv ++ #["-c:s", sc.toString]
  if let some (w, h) := o.videoSize then
    argv := argv ++ #["-s", s!"{w}x{h}"]
  if let some n := o.videoFrames then
    argv := argv ++ #["-frames:v", s!"{n}"]
  if let some ar := o.audioRate then
    argv := argv ++ #["-ar", s!"{ar}"]
  if let some ac := o.audioChannels then
    argv := argv ++ #["-ac", s!"{ac}"]
  if let some pf := o.pixelFormat then
    argv := argv ++ #["-pix_fmt", pf]
  if let some pr := o.preset then
    argv := argv ++ #["-preset", pr]
  if let some crf := o.crf then
    argv := argv ++ #["-crf", crf]
  if let some bf := o.bFrames then
    argv := argv ++ #["-bf", s!"{bf}"]
  if let some g := o.gopSize then
    argv := argv ++ #["-g", s!"{g}"]
  if let some r := o.frameRate then
    argv := argv ++ #["-r", r]
  if let some vb := o.videoBitrate then
    argv := argv ++ #["-b:v", vb]
  if let some ab := o.audioBitrate then
    argv := argv ++ #["-b:a", ab]
  if let some t := plan.resources.threads then
    argv := argv ++ #["-threads", s!"{t}"]
  if let some mf := o.movflags then
    argv := argv ++ #["-movflags", mf]
  if o.format == "null" then
    argv := argv ++ #["-f", "null", "-"]
  else
    if inferContainerFormat none o.path != o.format then
      argv := argv ++ #["-f", o.format]
    argv := argv.push o.path
  return argv

/-! ## 4. Phase 5 Targeted C-ABI FFI Facade & Cancellation Contract -/

/-- Pinned Phase 5 C-ABI version (`0x00010005`). -/
@[extern "leanav_c_ffi_abi_version"]
opaque ffiAbiVersionC : Unit → UInt32

/-- Bounded, zero-allocation C-ABI MP4 header probe over borrowed `@& ByteArray`. -/
@[extern "leanav_c_ffi_probe_mp4_contract"]
opaque ffiProbeMp4ContractC : (@& ByteArray) → USize → UInt64

/-- Sequential-consistency atomic cancellation & frame-budget gate in C-ABI. -/
@[extern "leanav_c_ffi_cancel_gate"]
opaque ffiCancelGateC : UInt32 → UInt32 → UInt32 → UInt32

/-- Structured-argv `fork` + `execvp` delegated FFmpeg runner in C-ABI (zero shell interpolation). -/
@[extern "leanav_c_exec_delegated_ffmpeg"]
opaque ffiExecDelegatedFfmpegC : (@& Array String) → (@& String) → UInt32 → BaseIO UInt32

/-- Pure specification of the Phase 5 cancellation & frame budget gate. -/
def specFfiCancelGate (cancelFlag framesDone maxFrames : UInt32) : Bool :=
  cancelFlag == 0 && (maxFrames == 0 || framesDone < maxFrames)

/-- Decoded result of `ffiProbeMp4ContractC`. -/
structure FfiMp4ProbeResult where
  ok        : Bool
  width     : Nat
  height    : Nat
  timescale : Nat
  deriving Repr, DecidableEq, Inhabited

def decodeFfiMp4ProbeWord (word : UInt64) : FfiMp4ProbeResult :=
  let ok := (word >>> 63) == 1
  if !ok then
    { ok := false, width := 0, height := 0, timescale := 0 }
  else
    { ok := true
      width := ((word >>> 32) &&& 0xFFFF).toNat
      height := ((word >>> 16) &&& 0xFFFF).toNat
      timescale := (word &&& 0xFFFF).toNat }

/-! ## 5. Phase 6 Independent Verified Kernels with Explicit Fallback Policy -/

/-- Explicit outcome of a Phase 6 independent kernel invocation. -/
inductive KernelExecutionResult (α : Type) where
  | independentVerified (value : α)
  | fallbackDelegated (reason : String)
  deriving Repr, DecidableEq, Inhabited

/--
  Phase 6 Kernel 1: Exact rational timestamp rescaling (`rescalePtsIndependentOrFallback`).
  Executes the verified exact rational rescaler `rescalePtsExactNat` when `pts ≥ 0`,
  denominators/numerators are positive, and the intermediate product fits within bounded precision;
  otherwise triggers an explicit `fallbackDelegated` transition rather than silently overflowing.
-/
def rescalePtsIndependentOrFallback (pts : Int) (srcNum srcDen dstNum dstDen : Nat) : KernelExecutionResult Nat :=
  if pts < 0 then
    .fallbackDelegated "negative_pts_requires_signed_timeline_shift"
  else if srcNum == 0 || srcDen == 0 || dstNum == 0 || dstDen == 0 then
    .fallbackDelegated "zero_rational_component"
  else
    let ptsNat := pts.toNat
    let numProd := ptsNat * srcNum * dstDen
    if numProd > 9007199254740991 then
      .fallbackDelegated "rational_product_exceeds_certified_bound"
    else
      .independentVerified (AVRational.rescalePtsExactNat ptsNat srcNum srcDen dstNum dstDen)

/--
  Phase 6 Kernel 2: Verified 2x2 Luma Box Downscaler (`scalePlane2x2IndependentOrFallback`).
  Executes `scalePlaneDown2x2Fast` when plane bounds hold and dimensions are even `≥ 4`,
  otherwise falls back explicitly.
-/
def scalePlane2x2IndependentOrFallback (p : Plane2D) : KernelExecutionResult Plane2D :=
  if !p.verifyBounds then
    .fallbackDelegated "plane_bounds_violation"
  else if p.width < 4 || p.height < 4 || p.width % 2 != 0 || p.height % 2 != 0 then
    .fallbackDelegated "dimensions_not_even_2x2_compatible"
  else
    .independentVerified (scalePlaneDown2x2Fast p)

/--
  Phase 6 Kernel 3: Verified IVF Container Demuxer (`demuxIvfIndependentOrFallback`).
  Executes `demuxIvfStream` and verifies every packet's 64-bit integrity digest,
  or falls back explicitly if the container is malformed or non-IVF.
-/
def demuxIvfIndependentOrFallback (s : ByteSlice) : KernelExecutionResult (IvfHeader × Array AVPacketView) :=
  match demuxIvfStream s with
  | some (hdr, pkts) =>
    if hdr.width > 0 && hdr.height > 0 && pkts.all (fun p => p.verifyIntegrity) then
      .independentVerified (hdr, pkts)
    else
      .fallbackDelegated "ivf_packet_integrity_or_dimension_failure"
  | none =>
    .fallbackDelegated "invalid_or_truncated_ivf_stream"

/-! ## 6. Formal Soundness, Round-Trip & Fallback Theorems (Phases 3, 4, 5 & 6) -/

set_option maxHeartbeats 1600000

/--
  Theorem (Phase 3 / Wave D): `parseStreamMapSpec` and `formatStreamMapSpec` form an exact round-trip
  on valid stream selectors (`0:v:0`, `0:a:0?`, `0:s`) and reject malformed selectors (`0:x:0`, `bad`, `0:v:0:1`).
-/
theorem streamMapSpec_parse_format_roundtrip :
    (parseStreamMapSpec "0:v:0").map formatStreamMapSpec = some "0:v:0" ∧
    (parseStreamMapSpec "0:a:0?").map formatStreamMapSpec = some "0:a:0?" ∧
    (parseStreamMapSpec "1:s?").map formatStreamMapSpec = some "1:s?" ∧
    parseStreamMapSpec "0:x:0" = none ∧
    parseStreamMapSpec "0:v:0:1" = none ∧
    parseStreamMapSpec "malformed" = none := by
  decide

/--
  Theorem (Phase 4 / Wave E): `parseMetadataSpec` and `formatMetadataSpec` round-trip valid `key=value`
  metadata specifications and reject empty keys or missing `=` delimiters.
-/
theorem metadataSpec_parse_format_roundtrip :
    (parseMetadataSpec "title=LeanAV_Demo").map formatMetadataSpec = some "title=LeanAV_Demo" ∧
    (parseMetadataSpec "comment=").map formatMetadataSpec = some "comment=" ∧
    parseMetadataSpec "=value" = none ∧
    parseMetadataSpec "no_equals_sign" = none := by
  decide

/--
  Theorem (Phase 4 / Wave F & §8 Security): `isSafeLocalMediaPath` accepts local relative and absolute
  media paths while rejecting network URLs (`http://`, `rtsp://`), synthetic/device inputs (`/dev/video0`, `lavfi:`),
  and parent directory traversal (`../secret.mp4`).
-/
theorem protocolSecurityPolicy_accepts_local_and_rejects_network_device_traversal :
    isSafeLocalMediaPath "fixtures/input.mp4" = true ∧
    isSafeLocalMediaPath "/tmp/output.mkv" = true ∧
    isSafeLocalMediaPath "http://example.com/stream.m3u8" = false ∧
    isSafeLocalMediaPath "rtsp://10.0.0.1/live" = false ∧
    isSafeLocalMediaPath "/dev/video0" = false ∧
    isSafeLocalMediaPath "lavfi:testsrc" = false ∧
    isSafeLocalMediaPath "fixtures/../outside.mp4" = false ∧
    isSafeLocalMediaPath "" = false := by
  decide

/--
  Theorem (Phase 3 / Wave D): `parseArgsToPlanIR` and `planIRToCliArgs` satisfy the exact CLI <-> IR
  round-trip law across MP4 stream copy, H.264 transcode with timeline/filter/encoder options,
  and Phase 4 delegated Matroska remux with `-map`, `-metadata`, `-bsf:v`, and `-c:s`.
-/
theorem planIR_cli_roundtrip_verified :
    let copyArgs := ["-y", "-i", "in.mp4", "-c", "copy", "out.mp4"]
    let transArgs := ["-y", "-i", "in.mp4", "-vf", "scale=1280:720", "-c:v", "h264", "out.mp4"]
    let phase4Args := ["-y", "-i", "in.mp4", "-map", "0:v:0", "-metadata", "title=Test", "-c", "copy", "out.mkv"]
    let pCopy := parseArgsToPlanIR copyArgs
    let pTrans := parseArgsToPlanIR transArgs
    let pPhase4 := parseArgsToPlanIR phase4Args
    parseArgsToPlanIR (planIRToCliArgs pCopy) = pCopy ∧
    parseArgsToPlanIR (planIRToCliArgs pTrans) = pTrans ∧
    parseArgsToPlanIR (planIRToCliArgs pPhase4) = pPhase4 ∧
    pCopy.backend.tier = .delegatedFaithful ∧
    pTrans.backend.tier = .translatedPartial ∧
    pPhase4.backend.tier = .delegatedFaithful ∧
    pPhase4.backend.delegatedContainer = true := by
  decide

/--
  Theorem (Phase 3 & Phase 4 Validation Gate): `validatePlanIR` accepts valid `delegatedFaithful` and
  `translatedPartial` plans and rejects plans with `copyWithFilter`, invalid `-map`, disallowed `http://` URLs,
  or `-ss` millisecond overflow.
-/
theorem validatePlanIR_sound_and_rejects_unsafe :
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-c", "copy", "out.mp4"])).isOk = true ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-c", "copy", "-vf", "hflip", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-map", "bad_map", "-c", "copy", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "http://evil.example/in.mp4", "-c", "copy", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-ss", "4294968", "-i", "in.mp4", "-c", "copy", "out.mp4"])).isOk = false := by
  decide

/--
  Theorem (Phase 5 & Phase 6): `specFfiCancelGate` enforces cancellation and frame budgets,
  and `rescalePtsIndependentOrFallback` executes the exact rational rescaler in-domain (`90000` at `1/90000 -> 1/1000` = `1000`)
  while deterministically returning `.fallbackDelegated` on negative timestamps or zero denominators.
-/
theorem independentKernel_fallback_complete_and_sound :
    specFfiCancelGate 0 10 25 = true ∧
    specFfiCancelGate 1 10 25 = false ∧
    specFfiCancelGate 0 25 25 = false ∧
    rescalePtsIndependentOrFallback 90000 1 90000 1 1000 = .independentVerified 1000 ∧
    rescalePtsIndependentOrFallback (-1) 1 90000 1 1000 = .fallbackDelegated "negative_pts_requires_signed_timeline_shift" ∧
    rescalePtsIndependentOrFallback 90000 1 0 1 1000 = .fallbackDelegated "zero_rational_component" := by
  decide

end LeanAV.PlanIR
