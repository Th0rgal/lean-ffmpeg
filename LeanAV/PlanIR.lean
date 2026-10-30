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

/-- Elementary stream kind (`v`, `a`, `s`, `d`, or `all` for `-map 0` / `-map 0:1`). -/
inductive StreamKind where
  | video
  | audio
  | subtitle
  | data
  | all
  deriving Repr, DecidableEq, Inhabited

def StreamKind.toShortCode : StreamKind → String
  | .video    => "v"
  | .audio    => "a"
  | .subtitle => "s"
  | .data     => "d"
  | .all      => "*"

def StreamKind.toChar : StreamKind → Char
  | .video    => 'v'
  | .audio    => 'a'
  | .subtitle => 's'
  | .data     => 'd'
  | .all      => '*'

def parseStreamKindChar : Char → Option StreamKind
  | 'v' => some .video
  | 'a' => some .audio
  | 's' => some .subtitle
  | 'd' => some .data
  | _   => none

/-- Typed `-map <inputIdx>[:<kind>][:<streamIdx>][?]` selector. -/
structure StreamMapSpec where
  inputIdx  : Nat
  kind      : StreamKind
  streamIdx : Option Nat := none
  optional  : Bool := false
  deriving Repr, DecidableEq, Inhabited

def formatStreamMapSpec (m : StreamMapSpec) : String :=
  let withIdx :=
    match m.kind, m.streamIdx with
    | .all, none     => s!"{m.inputIdx}"
    | .all, some idx => s!"{m.inputIdx}:{idx}"
    | k, none        => s!"{m.inputIdx}:{k.toShortCode}"
    | k, some idx    => s!"{m.inputIdx}:{k.toShortCode}:{idx}"
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

/-- Parse a stream map token (`"0:v:0"`, `"0:a:0?"`, `"0:s?"`, `"0:v"`, `"0"`, `"0:1"`). -/
def parseStreamMapSpec (s : String) : Option StreamMapSpec :=
  let (coreStr, isOpt) :=
    match s.toList.reverse with
    | '?' :: revRest => (String.ofList revRest.reverse, true)
    | _              => (s, false)
  let parts := splitStrOnChar coreStr ':'
  match parts with
  | [inStr] =>
    match parseNonNegNatSpec inStr with
    | some inIdx => some { inputIdx := inIdx, kind := .all, streamIdx := none, optional := isOpt }
    | none       => none
  | [inStr, secondStr] =>
    match parseNonNegNatSpec inStr, secondStr.toList with
    | some inIdx, [kc] =>
      match parseStreamKindChar kc with
      | some k => some { inputIdx := inIdx, kind := k, streamIdx := none, optional := isOpt }
      | none   =>
        match parseNonNegNatSpec secondStr with
        | some stIdx => some { inputIdx := inIdx, kind := .all, streamIdx := some stIdx, optional := isOpt }
        | none       => none
    | some inIdx, _ =>
      match parseNonNegNatSpec secondStr with
      | some stIdx => some { inputIdx := inIdx, kind := .all, streamIdx := some stIdx, optional := isOpt }
      | none       => none
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
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
  c == '_' || c == '-' || c == '.' || c == ':'

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

def isExtendedSubtitleCodec (s : String) : Bool :=
  ["ssa", "dvbsub", "dvdsub", "hdmv_pgs_subtitle", "xsub", "ttml", "text"].contains s

def SubtitleCodecSpec.toString : SubtitleCodecSpec → String
  | .copy    => "copy"
  | .movText => "mov_text"
  | .srt     => "srt"
  | .webvtt  => "webvtt"
  | .ass     => "ass"

/-- Supported bitstream filters (`-bsf:v` / `-bsf:a` / `-bsf:s`). -/
def supportedBsf (s : String) : Bool :=
  -- av_strtok(stage, "=") skips leading equals before the name.
  let nameChars := s.toList.dropWhile (fun c => c == '=')
  let base := String.ofList (nameChars.takeWhile (fun c => c != '='))
  ["aac_adtstoasc", "h264_mp4toannexb", "hevc_mp4toannexb",
   "av1_frame_split", "av1_frame_merge", "av1_metadata",
   "h264_metadata", "h264_redundant_pps", "hevc_metadata", "vvc_metadata", "mpeg2_metadata",
   "vp9_superframe", "vp9_superframe_split", "vp9_raw_reorder", "vp9_metadata",
   "extract_extradata", "remove_extradata", "dump_extra", "dts2pts", "setts",
   "noise", "null", "chomp", "dca_core", "eac3_core", "truehd_core",
   "filter_units", "hapqa_extract", "imx_dump_header", "mjpeg2jpeg", "mjpega_dump_header",
   "mov2textsub", "text2movsub", "mp3_header_decompress", "mpeg4_unpack_bframes",
   "opus_metadata", "pcm_rechunk", "pgs_frame_merge", "prores_metadata", "trace_headers",
   "trim", "jpegapp", "apv_metadata", "dv_error_marker", "remove_extra",
   "dovi_split", "eia608_to_smpte436m", "smpte436m_to_eia608", "media100_to_mjpegb"].contains base

private def isBsfWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- Tokenize the outer BSF list like FFmpeg's `av_get_token` with comma terminators.
    `trailing` counts removable whitespace at the end of the reversed token.
    An escape or closing quote protects everything emitted so far, resetting it.
    The original CLI string is retained separately for backend delegation. -/
private def splitBsfChainAux : List Char → Bool → Bool → List Char → Nat → List String → List String
  | [], _, _, rev, trailing, stages =>
      (String.ofList ((rev.drop trailing).reverse) :: stages).reverse
  | c :: cs, leading, quoted, rev, trailing, stages =>
      if quoted then
        if c == '\'' then
          splitBsfChainAux cs false false rev 0 stages
        else
          splitBsfChainAux cs false true (c :: rev)
            (if isBsfWhitespace c then trailing + 1 else 0) stages
      else if leading && isBsfWhitespace c then
        splitBsfChainAux cs true false rev trailing stages
      else if c == '\\' then
        match cs with
        | [] => (String.ofList ((c :: rev).reverse) :: stages).reverse
        | next :: rest => splitBsfChainAux rest false false (next :: rev) 0 stages
      else if c == '\'' then
        splitBsfChainAux cs false true rev trailing stages
      else if c == ',' then
        let stage := String.ofList ((rev.drop trailing).reverse)
        -- av_bsf_list_parse_str tolerates one comma immediately before EOF.
        if cs.isEmpty then (stage :: stages).reverse
        else splitBsfChainAux cs true false [] 0 (stage :: stages)
      else
        splitBsfChainAux cs false false (c :: rev)
          (if isBsfWhitespace c then trailing + 1 else 0) stages

/-- Decode only the outer BSF list; option expressions remain backend semantics.
    Empty/interior stages survive tokenization so the name gate rejects them.
    Like upstream, unmatched single quotes consume to EOF without a lexer error. -/
def splitBsfChain (s : String) : List String :=
  splitBsfChainAux s.toList true false [] 0 []

def supportedBsfChain (s : String) : Bool :=
  let stages := splitBsfChain s
  !stages.isEmpty && stages.all supportedBsf

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
  Rejects empty paths, leading whitespace, double-slash roots (`//dev/null`),
  parent traversal (`..` path segments), device/kernel nodes (`/dev/`, `/proc/`, `/sys/`),
  and any URI/protocol scheme containing `':'` (`http:`, `https:`, `rtmp:`, `rtsp:`, `tcp:`, `udp:`,
  `file:`, `pipe:`, `fd:`, `data:`, `crypto:`, `hls:`, `concat:`, `subfile:`, `lavfi:`, `ftp:`, `sftp:`, `tls:`, `srt:`, `v4l2:`, `alsa:`).
-/
def isSafeLocalMediaPath (path : String) : Bool :=
  let chars := path.toList
  match chars with
  | [] => false
  | c0 :: _ =>
    if c0 == ' ' || c0 == '\t' || c0 == '\n' || c0 == '\r' then false
    else if chars.contains ':' then false
    else
      let lower := strToLowerAscii path
      let forbiddenPrefixes : List String :=
        ["//", "/dev/", "/proc/", "/sys/"]
      let hasForbiddenPrefix := forbiddenPrefixes.any (fun p => strStartsWithFast lower p)
      let segments := splitStrOnChar path '/'
      let hasDotDot := segments.contains ".."
      !hasForbiddenPrefix && !hasDotDot

/-- Validate a `concat:<seg1>|<seg2>|...` input path: requires `≥ 2` pipe-separated segments,
    every one of which satisfies `isSafeLocalMediaPath` (rejecting empty segments, `..`,
    device/kernel nodes, nested `concat:`, and any URI scheme). -/
def isSafeConcatInputPath (path : String) : Bool :=
  if !strStartsWithFast path "concat:" then false
  else
    let body := String.ofList (path.toList.drop 7)
    let segs := splitStrOnChar body '|'
    segs.length ≥ 2 && segs.all isSafeLocalMediaPath

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
  /-- Validated MPEG option/value pairs, retaining repetition and encounter order. -/
  mpegOptions : List (String × String) := []
  deriving Repr, DecidableEq, Inhabited

/-- Emit exact fractional digits for `rem / den` with leading-zero preservation (`50 / 10000` -> `"005"`). -/
def formatFracDigitsLoop (rem den : Nat) : Nat → List Char
  | 0 => []
  | fuel + 1 =>
    if rem == 0 then []
    else
      let prod := rem * 10
      let digit := prod / den
      let nextRem := prod % den
      Char.ofNat (48 + digit) :: formatFracDigitsLoop nextRem den fuel

/-- Format a `CliSeconds` value back to its canonical decimal string (`"2"`, `"1.5"`, `"0.005"`). -/
def formatCliSeconds (s : CliSeconds) : String :=
  if s.den ≤ 1 then s!"{s.num}"
  else
    let intPart := s.num / s.den
    let remPart := s.num % s.den
    if remPart == 0 then s!"{intPart}"
    else
      let fracStr := String.ofList (formatFracDigitsLoop remPart s.den 9)
      if fracStr == "" then s!"{intPart}" else s!"{intPart}.{fracStr}"

def codecToCanonicalString : CliCodec → String
  | .copy           => "copy"
  | .h264           => "h264"
  | .hevc           => "hevc"
  | .av1            => "av1"
  | .vp9            => "vp9"
  | .prores         => "prores"
  | .ffv1           => "ffv1"
  | .aac            => "aac"
  | .opus           => "opus"
  | .flac           => "flac"
  | .pcmS16le       => "pcm_s16le"
  | .rawvideo       => "rawvideo"
  | .vp8            => "vp8"
  | .mpeg4          => "mpeg4"
  | .mpeg2video     => "mpeg2video"
  | .mpeg1video     => "mpeg1video"
  | .mjpeg          => "mjpeg"
  | .png            => "png"
  | .gif            => "gif"
  | .mp2            => "mp2"
  | .mp3            => "mp3"
  | .vorbis         => "vorbis"
  | .alac           => "alac"
  | .ac3            => "ac3"
  | .eac3           => "eac3"
  | .dts            => "dts"
  | .otherDelegated => "other"

def codecToDelegatedVideoEncoder : CliCodec → String
  | .h264 => "libx264"
  | .hevc => "libx265"
  | .av1  => "libsvtav1"
  | .vp9  => "libvpx-vp9"
  | .opus => "libopus"
  | c     => codecToCanonicalString c

def codecToDelegatedAudioEncoder : CliCodec → String
  | .opus => "libopus"
  | c     => codecToCanonicalString c

/-- Infer container format from explicit `-f` or output file extension. -/
def inferContainerFormat (explicitFmt : Option String) (outPath : String) : String :=
  match explicitFmt with
  | some f => f
  | none =>
    if outPath == "/dev/null" then "null"
    else if outPath == "md5:" then "md5"
    else
      let lower := strToLowerAscii outPath
      if strEndsWithFast lower ".mp4" || strEndsWithFast lower ".m4v" then "mp4"
      else if strEndsWithFast lower ".mkv" then "matroska"
      else if strEndsWithFast lower ".webm" then "webm"
      else if strEndsWithFast lower ".mov" then "mov"
      else if strEndsWithFast lower ".wav" then "wav"
      else if strEndsWithFast lower ".flac" then "flac"
      else if strEndsWithFast lower ".ogg" || strEndsWithFast lower ".opus" then "ogg"
      else if strEndsWithFast lower ".ts" then "mpegts"
      else if strEndsWithFast lower ".ivf" then "ivf"
      else if strEndsWithFast lower ".m4a" then "ipod"
      else if strEndsWithFast lower ".mp3" then "mp3"
      else if strEndsWithFast lower ".aac" || strEndsWithFast lower ".adts" then "adts"
      else if strEndsWithFast lower ".avi" then "avi"
      else if strStartsWithFast lower "md5:" then "md5"
      else
        let parts := splitStrOnChar lower '.'
        if parts.length < 2 then "unknown"
        else
          let ext := parts.getLastD ""
          if ext == "3gp" || ext == "3g2" || ext == "f4v" || ext == "psp" then "mp4"
          else if ext == "mka" || ext == "mks" then "matroska"
          else if ext == "oga" || ext == "ogv" || ext == "spx" then "ogg"
          else if ext == "m2ts" || ext == "mts" then "mpegts"
          else if ext == "mp2" then "mp2"
          else if ext == "flv" then "flv"
          else if ext == "h264" || ext == "264" then "h264"
          else if ext == "hevc" || ext == "265" then "hevc"
          else if ext == "av1" || ext == "obu" then "av1"
          else if ext == "srt" then "srt"
          else if ext == "vtt" || ext == "webvtt" then "webvtt"
          else if ext == "ass" || ext == "ssa" then "ass"
          else if ext == "y4m" then "yuv4mpegpipe"
          else if ext == "yuv" || ext == "raw" || ext == "rgb" then "rawvideo"
          else if ext == "sw" || ext == "pcm" then "s16le"
          else if ext == "sb" then "s8"
          else if ext == "ub" then "u8"
          else if ext == "ul" then "mulaw"
          else if ext == "al" then "alaw"
          else if ext == "gif" then "gif"
          else if ext == "apng" then "apng"
          else if ext == "webp" then "webp"
          else if ext == "ismv" || ext == "isma" then "ismv"
          else if ext == "w64" then "w64"
          else if ext == "ac3" then "ac3"
          else if ext == "eac3" then "eac3"
          else if ext == "dts" then "dts"
          else if ext == "tta" then "tta"
          else if ext == "wv" then "wv"
          else if ext == "caf" then "caf"
          else if ext == "aiff" || ext == "aif" then "aiff"
          else if ext == "au" then "au"
          else if ext == "voc" then "voc"
          else if ext == "sox" then "sox"
          else if ext == "ircam" || ext == "sf" then "ircam"
          else if ext == "mmf" then "mmf"
          else if ext == "rso" then "rso"
          else if ext == "amr" then "amr"
          else if ext == "sbc" then "sbc"
          else if ext == "dfpwm" then "dfpwm"
          else if ext == "g722" then "g722"
          else if ext == "mpg" || ext == "mpeg" || ext == "vob" then "mpeg"
          else if ext == "m2v" then "mpeg2video"
          else if ext == "m1v" then "mpeg1video"
          else if ext == "asf" || ext == "wmv" || ext == "wma" then "asf"
          else if ext == "swf" then "swf"
          else if ext == "rm" then "rm"
          else if ext == "nut" then "nut"
          else if ext == "gxf" then "gxf"
          else if ext == "mxf" then "mxf"
          else if ext == "mxf_d10" then "mxf_d10"
          else if ext == "mxf_opatom" then "mxf_opatom"
          else if ext == "wtv" then "wtv"
          else if ext == "dv" || ext == "dif" then "dv"
          else if ext == "roq" then "roq"
          else if ext == "smjpeg" then "smjpeg"
          else if ext == "flm" then "flm"
          else if ext == "ast" then "ast"
          else if ext == "adx" then "adx"
          else if ext == "dnxhd" then "dnxhd"
          else if ext == "mpeg1video" then "mpeg1video"
          else if ext == "mpeg2video" then "mpeg2video"
          else if ext == "latm" || ext == "loas" then "latm"
          else if ext == "mjpg" || ext == "mjpeg" || ext == "jpg" || ext == "jpeg" || ext == "jls" then "mjpeg"
          else if ext == "lrc" then "lrc"
          else if ext == "ffmeta" || ext == "ffmetadata" then "ffmetadata"
          else if ext == "m3u8" then "hls"
          else if ext == "mpd" then "dash"
          else if ext == "iamf" then "iamf"
          else if ext == "fits" then "fits"
          else if ext == "astc" then "astc"
          else if ext == "ktx" then "ktx"
          else if ext == "pdv" then "pdv"
          else if ["png", "bmp", "pam", "pbm", "pgm", "pgmyuv", "ppm", "tga",
                   "tif", "tiff", "dpx", "sgi", "sun", "pcx", "qoi", "xbm", "xwd", "wbmp", "pfm", "vbn", "exr"].contains ext then "image2"
          else "unknown"

/-- Recognize group, view, view-index, view-position, disposition, and type-only selectors
    for delegated validation; group IDs and advanced selector tails remain upstream-owned. -/
def isDelegatedGroupMapSpec (s : String) : Bool :=
  match splitStrOnChar s ':' with
  | [kindStr] => ["v", "a", "s", "d", "t", "v?", "a?", "s?", "d?", "t?"].contains kindStr
  | [kindStr, idxStr] =>
    if ["v", "a", "s", "d", "t"].contains kindStr then
      let cleanIdx := if strEndsWithFast idxStr "?" then String.ofList (idxStr.toList.dropLast) else idxStr
      (parseNonNegNatSpec cleanIdx).isSome
    else false
  | input :: "g" :: tail => (parseNonNegNatSpec input).isSome && !tail.isEmpty
  | input :: "view" :: tail => (parseNonNegNatSpec input).isSome && !tail.isEmpty
  | input :: "vidx" :: tail => (parseNonNegNatSpec input).isSome && !tail.isEmpty
  | input :: "disp" :: tail => (parseNonNegNatSpec input).isSome && !tail.isEmpty
  | input :: kindStr :: "vpos" :: tail =>
    (parseNonNegNatSpec input).isSome && ["v", "a", "s", "d"].contains kindStr && !tail.isEmpty
  | input :: kindStr :: "disp" :: tail =>
    (parseNonNegNatSpec input).isSome && ["v", "a", "s", "d"].contains kindStr && !tail.isEmpty
  | _ => false

/-- Check whether a `-map` token is a valid negative map (`-0:a`), filtergraph label (`[v]`), or attachment map (`0:t`). -/
def isExtendedMapSpec (s : String) : Bool :=
  if strStartsWithFast s "-" then
    let rest := String.ofList (s.toList.drop 1)
    (parseStreamMapSpec rest).isSome || isDelegatedGroupMapSpec rest || rest == "0:t" || rest == "0:t:0"
  else if strStartsWithFast s "[" && strEndsWithFast s "]" then
    s.toList.length > 2
  else
    isDelegatedGroupMapSpec s || s == "0:t" || s == "0:t?" || s == "0:t:0" || s == "0:t:0?"

/-- Check whether a scale dimension char list is supported by the native MP4 pixel-SIMD pipeline. -/
def isNativeMp4ScaleDimChars (cs : List Char) : Bool :=
  cs == ['-', '1'] || cs == ['-', '2'] ||
  match parseNatCharsLoop cs 0 false with
  | some n => n ≥ 2 && n % 2 == 0
  | none   => false

/-- Check whether a single `-vf` stage is supported by the native MP4 pixel-SIMD pipeline. -/
def isNativeMp4VideoFilterStage (stage : String) : Bool :=
  if stage == "bt2020_to_bt709" || stage == "tonemap=reinhard" then
    true
  else
    let cs := stage.toList
    if ['s', 'c', 'a', 'l', 'e', '='].isPrefixOf cs then
      match splitColonCharsLoop (cs.drop 6) [] with
      | [wCs, hCs] =>
        isNativeMp4ScaleDimChars wCs && isNativeMp4ScaleDimChars hCs &&
        !(wCs == ['-', '1'] && hCs == ['-', '1']) && !(wCs == ['-', '2'] && hCs == ['-', '2'])
      | _ => false
    else
      false

/-- Check whether a full `-vf` filtergraph string is supported by the native MP4 pixel-SIMD pipeline. -/
def isNativeMp4VideoFilter (vf : String) : Bool :=
  let stages := splitStrOnChar vf ','
  !stages.isEmpty && stages.all isNativeMp4VideoFilterStage

/-- Check whether a `-f lavfi -i <graph>` synthetic source argument is free of network/device/traversal hazards. -/
def isSafeLavfiGraph (graph : String) : Bool :=
  let lower := strToLowerAscii graph
  let forbiddenPrefixes : List String :=
    ["http:", "https:", "rtmp:", "rtsp:", "tcp:", "udp:", "file:", "pipe:", "data:",
     "//", "/dev/", "/proc/", "/sys/"]
  let hasForbidden := forbiddenPrefixes.any (fun p => strStartsWithFast lower p)
  let segments := splitStrOnChar graph '/'
  !graph.toList.isEmpty && !hasForbidden && !(segments.contains "..")

/-- Check whether an output path/target is safe (`-`, `none` under `-f null`, `/dev/null`, `md5:`, `md5:<safePath>`, or `isSafeLocalMediaPath`). -/
def isSafeOutputTarget (p : String) (hasExplicitFmt : Bool) (explicitFmt : Option String := none) : Bool :=
  isSafeLocalMediaPath p ||
  (p == "-" && hasExplicitFmt) ||
  (p == "none" && explicitFmt == some "null") ||
  p == "/dev/null" ||
  p == "md5:" ||
  (strStartsWithFast p "md5:" && isSafeLocalMediaPath (String.ofList (p.toList.drop 4)))

/-- Strip `lffmpeg`-internal CLI flags (`-json`, `--json`, `-dump-plan`, `--dump-plan`) for direct FFmpeg passthrough. -/
def stripInternalLffmpegArgs : List String → List String
  | [] => []
  | tok :: rest =>
    if tok == "-json" || tok == "--json" || tok == "-dump-plan" || tok == "--dump-plan" then
      stripInternalLffmpegArgs rest
    else
      tok :: stripInternalLffmpegArgs rest

/-- Exact MPEG encoder option spellings supported by the delegated path. -/
def isMpegDelegatedValueFlag (tok : String) : Bool :=
  ["-mpv_flags", "-intra_vlc", "-data_partitioning"].contains tok

/-- Restricted MPEG flag grammar: `0` or `[+-]?ATOM([+-]ATOM)*`.
    Splitting after at most one leading sign preserves empty segments, so
    doubled/trailing signs fail the exact atom allowlist. -/
def isValidMpvFlags (value : String) : Bool :=
  if value == "0" then true
  else
    let body := match value.toList with
      | '+' :: rest | '-' :: rest => rest
      | chars => chars
    let normalized := String.ofList (body.map fun c => if c == '-' then '+' else c)
    (splitStrOnChar normalized '+').all fun atom =>
      ["skip_rd", "strict_gop", "qp_rd", "cbp_rd", "naq", "mv0"].contains atom

/-- Validate stream specifier suffix on `-pix_fmt:<spec>` / `-pixel_format:<spec>` (`0`, `v`, `v:0`). -/
def isValidPixFmtStreamQualifier (qual : String) : Bool :=
  (parseNonNegNatSpec qual).isSome ||
  qual == "v" ||
  (strStartsWithFast qual "v:" && (parseNonNegNatSpec (String.ofList (qual.toList.drop 2))).isSome)

/-- Extended 1-argument FFmpeg & FATE flags routed to `delegated_faithful`. -/
def isExtendedDelegatedValueFlag (tok : String) : Bool :=
  if tok == "-y" || tok == "-n" || tok == "-vn" || tok == "-an" || tok == "-sn" ||
     tok == "-hide_banner" || tok == "-stats" || tok == "-nostats" || tok == "-nostdin" ||
     tok == "-json" || tok == "--json" || flagTakesValue tok then
    false
  else if !strStartsWithFast tok "-" then
    false
  else if isMpegDelegatedValueFlag tok then true
  else if strStartsWithFast tok "-export_side_data:" ||
          strStartsWithFast tok "-metadata:" ||
          strStartsWithFast tok "-disposition" ||
          strStartsWithFast tok "-map_metadata:" ||
          strStartsWithFast tok "-keep_metadata:" ||
          strStartsWithFast tok "-bsf:" ||
          strStartsWithFast tok "-c:v:" ||
          strStartsWithFast tok "-c:a:" ||
          strStartsWithFast tok "-c:s:" ||
          strStartsWithFast tok "-codec:v:" ||
          strStartsWithFast tok "-codec:a:" ||
          strStartsWithFast tok "-codec:s:" ||
          strStartsWithFast tok "-b:v:" ||
          strStartsWithFast tok "-b:a:" ||
          strStartsWithFast tok "-filter:v:" ||
          strStartsWithFast tok "-filter:a:" ||
          strStartsWithFast tok "-frames:" ||
          strStartsWithFast tok "-qscale:" ||
          strStartsWithFast tok "-q:" ||
          strStartsWithFast tok "-maxrate:" ||
          strStartsWithFast tok "-minrate:" ||
          strStartsWithFast tok "-bufsize:" ||
          strStartsWithFast tok "-sar:" ||
          strStartsWithFast tok "-tag:" ||
          strStartsWithFast tok "-stereo3d:" ||
          strStartsWithFast tok "-display_rotation:" ||
          strStartsWithFast tok "-time_base:" ||
          strStartsWithFast tok "-color_primaries:" ||
          strStartsWithFast tok "-color_range:" ||
          strStartsWithFast tok "-color_trc:" ||
          strStartsWithFast tok "-colorspace:" ||
          (strStartsWithFast tok "-pix_fmt:" && isValidPixFmtStreamQualifier (String.ofList (tok.toList.drop 9))) ||
          (strStartsWithFast tok "-pixel_format:" && isValidPixFmtStreamQualifier (String.ofList (tok.toList.drop 14))) ||
          (strStartsWithFast tok "-apply_cropping:" && isValidPixFmtStreamQualifier (String.ofList (tok.toList.drop 16))) ||
          strStartsWithFast tok "-/filter:" then true
  else
    ["-c:d", "-dcodec", "-codec:d", "-c:t", "-c:0", "-c:1", "-c:2", "-c:3",
     "-frames:a", "-aframes", "-frames:d", "-dframes", "-frames:s",
     "-max_frames", "-frames_per_packet", "-shortest_buf_duration", "-max_delay",
     "-max_muxing_queue_size", "-frag_interleave",
     "-apply_cropping", "-block_size", "-srgb", "-dec_profile",
     "-layer", "-compression", "-compression_algo",
     "-to", "-sseof", "-itsoffset", "-output_ts_offset", "-seek_timestamp", "-avoid_negative_ts",
     "-qp", "-q", "-qscale", "-qmin", "-qmax", "-qdiff", "-qblur", "-qcomp",
     "-maxrate", "-minrate", "-bufsize", "-rc_init_occupancy", "-rc_max_vbv_use", "-rc_min_vbv_use",
     "-pass", "-passlogfile",
     "-tune", "-profile", "-profile:v", "-profile:a", "-level", "-level:v",
     "-x264-params", "-x264opts", "-x265-params", "-svtav1-params", "-aom-params",
     "-row-mt", "-cpu-used", "-deadline", "-lag-in-frames", "-auto-alt-ref",
     "-arnr-maxframes", "-arnr-strength", "-tile-columns", "-tile-rows",
     "-slices", "-keyint_min", "-sc_threshold", "-b_strategy", "-b_sensitivity", "-refs", "-coder",
     "-subq", "-me_method", "-me_range", "-motion_est", "-trellis", "-mbd", "-cmp", "-subcmp",
     "-mbcmp", "-precmp", "-ildctcmp", "-skip_cmp", "-dia_size", "-last_pred", "-preme",
      "-pred", "-huffman", "-context", "-slicecrc", "-strict", "-mpeg_quant", "-alternate_scan",
     "-intra_dc_precision", "-non_linear_quant", "-noise_reduction", "-scplx_mask", "-error_rate",
     "-aiv", "-umv", "-ps", "-aic", "-obmc", "-loop", "-part",
     "-wavelet_type",
     "-flags", "-flags2", "-fflags", "-avioflags", "-flvflags", "-spdif_flags",
     "-export_side_data", "-sws_flags", "-swr_flags", "-idct", "-dct",
     "-cpuflags", "-hwaccel", "-thread_type", "-filter_threads", "-filter_complex_threads",
     "-filter_buffered_frames", "-reinit_filter", "-dec",
     "-top", "-field_order", "-intra_matrix", "-inter_matrix",
     "-chroma_sample_location", "-color_range", "-colorspace", "-color_primaries", "-color_trc",
     "-aspect", "-sar", "-dar", "-timecode", "-bits_per_raw_sample", "-compression_level",
     "-frame_size", "-cutoff", "-application", "-vbr", "-mapping_family",
     "-channel_layout", "-ch_layout", "-channel_order", "-ch_mode", "-channel_coupling",
     "-downmix", "-sample_fmt", "-request_sample_fmt", "-guess_layout_max", "-stereo_rematrixing",
     "-hash",
     "-fps_mode", "-vsync", "-async",
     "-brand", "-empty_hdlr_name", "-use_editlist", "-frag_duration", "-frag_size",
     "-min_frag_duration", "-use_mfra_for", "-write_tmcd", "-write_bext", "-write_id3v1", "-write_id3v2",
     "-id3v2_version", "-write_xing", "-write_apetag", "-write_peak", "-write_crc32",
     "-mpegts_copyts", "-mpegts_flags", "-mpegts_m2ts_mode", "-mpegts_transport_stream_id",
     "-loopstart", "-loopend", "-sample_rate", "-strip_number_adaptivity",
     "-streamid", "-stream_group", "-/stream_group", "-/filter_complex", "-/filter", "-/vf", "-/af",
     "-use_stream_ids_as_track_ids", "-keep_metadata", "-default_mode",
     "-cues_to_front", "-reserve_index_space", "-cluster_size_limit", "-cluster_time_limit",
     "-metadata_header_padding", "-store_user_comments", "-creation_time",
     "-serial_offset", "-muxrate", "-muxdelay", "-muxpreload", "-syncpoints",
     "-gifflags", "-final_delay", "-update", "-update_filemtime",
     "-start_number", "-pattern_type", "-ts_from_file", "-attach", "-dump_attachment",
     "-aac_coder", "-aac_is", "-aac_ms", "-aac_pce", "-aac_pns", "-aac_rc", "-aac_tns",
     "-lpc_type", "-lpc_passes", "-exact_rice_parameters", "-multi_dim_quant",
     "-min_prediction_order", "-max_prediction_order",
     "-analyzeduration", "-bug", "-ec", "-err_detect", "-max_error_rate", "-lowres",
     "-skip_frame", "-skip_loop_filter", "-skip_alpha", "-skip_cursor",
     "-stream_loop", "-force_key_frames", "-enc_time_base", "-time_base", "-tag",
     "-display_rotation", "-stereo3d", "-target_level", "-dtshd_rate", "-sbc_delay",
     "-mxf_audio_edit_rate", "-override_time_code_rate",
     "-allow_raw_vfw", "-blank_value", "-chars_per_frame", "-code_size", "-cons_noisegen",
     "-eia608_extract", "-format", "-max_size", "-postfilter", "-precision", "-real_time",
     "-stride", "-sub_charenc", "-trans_color", "-type", "-window_size",
     "-graph", "-graph_file", "-print_graphs_file", "-print_graphs_format",
     "-cryptokey", "-decryption_key", "-decryption_keys", "-encryption_key",
     "-encryption_kid", "-encryption_scheme", "-password",
     "-fifo_format", "-segment_format_options", "-segment_header_filename",
     "-segment_list", "-segment_time",
     "-hls_flags", "-hls_fmp4_init_filename", "-hls_init_time", "-hls_list_size",
     "-hls_playlist_type", "-hls_segment_filename", "-hls_segment_size",
     "-hls_segment_type", "-hls_time", "-master_pl_name", "-var_stream_map",
     "-adaptation_sets", "-availability_start_time_ms", "-bandwidth", "-chunk_duration_ms",
     "-chunk_start_index", "-dash", "-dash_track_number", "-live", "-minimum_update_period",
     "-streaming", "-suggested_presentation_delay", "-time_shift_buffer_depth"].contains tok

/-- Validate local constraints on an extended 1-argument FFmpeg/FATE flag.
    Codec-specific `-flags2` expressions and `-downmix` channel layouts retain
    FFmpeg's value grammar and are validated by the delegated backend. -/
def isValidExtendedFlagValue (tok value : String) : Bool :=
  if value == "" then false
  else if tok == "-/stream_group" || tok == "-/filter_complex" ||
          tok == "-/filter" || tok == "-/vf" || tok == "-/af" ||
          strStartsWithFast tok "-/filter:" || tok == "-graph_file" then
    isSafeLocalMediaPath value
  else if tok == "-print_graphs_file" then
    value == "-" || isSafeLocalMediaPath value
  else if tok == "-hls_fmp4_init_filename" || tok == "-hls_segment_filename" ||
          tok == "-master_pl_name" || tok == "-segment_header_filename" ||
          tok == "-segment_list" then
    isSafeLocalMediaPath value
  else if tok == "-mpv_flags" then isValidMpvFlags value
  else if tok == "-intra_vlc" || tok == "-data_partitioning" then
    value == "0" || value == "1"
  else if tok == "-hash" then
    ["md5", "murmur3", "ripemd128", "ripemd160", "ripemd256", "ripemd320",
     "sha160", "sha224", "sha256", "sha512/224", "sha512/256", "sha384", "sha512",
     "crc32", "adler32"].contains (strToLowerAscii value)
  else if tok == "-channel_order" then
    ["default", "coded", "0", "1"].contains value
  else if tok == "-wavelet_type" then
    ["9_7", "5_3", "haar", "haar_noshift"].contains value
  else if strStartsWithFast tok "-metadata:" then
    (parseMetadataSpec value).isSome
  else if strStartsWithFast tok "-bsf:" then
    supportedBsfChain value
  else if strStartsWithFast tok "-c:v:" || strStartsWithFast tok "-c:a:" ||
          strStartsWithFast tok "-codec:v:" || strStartsWithFast tok "-codec:a:" ||
          tok == "-c:0" || tok == "-c:1" || tok == "-c:2" || tok == "-c:3" then
    (parseCliCodec value).isSome || (parseSubtitleCodecSpec value).isSome || isExtendedSubtitleCodec value
  else if strStartsWithFast tok "-c:s:" || strStartsWithFast tok "-codec:s:" then
    (parseSubtitleCodecSpec value).isSome || isExtendedSubtitleCodec value
  else if strStartsWithFast tok "-b:v:" || strStartsWithFast tok "-b:a:" then
    isValidBitrateSpec value
  else if strStartsWithFast tok "-pix_fmt:" || strStartsWithFast tok "-pixel_format:" then
    supportedPixFmt value
  else if strStartsWithFast tok "-frames:" || tok == "-aframes" || tok == "-dframes" || tok == "-max_frames" then
    (parseNonNegNatSpec value).isSome
  else if tok == "-to" then
    (parseCliSeconds value).isSome
  else if tok == "-sseof" || tok == "-itsoffset" || tok == "-output_ts_offset" then
    let stripped := if strStartsWithFast value "-" then String.ofList (value.toList.drop 1) else value
    (parseCliSeconds stripped).isSome
  else if tok == "-slicecrc" then
    value == "0" || value == "1"
  else
    true

/-- Auxiliary accumulator for Phase 4 extended CLI flags (`-map`, `-metadata`, `-bsf:*`, `-c:s`, `-dump-plan`). -/
structure ExtendedPlanFlags where
  baseArgs               : List String := []
  passthroughArgs        : List String := []
  maps                   : List StreamMapSpec := []
  metadataEntries        : List MetadataEntrySpec := []
  mapMetadataSource      : Int := -1
  mapChaptersSource      : Int := -1
  subtitleCodec          : Option SubtitleCodecSpec := none
  noSubtitle             : Bool := false
  bsfs                   : List BsfSpec := []
  dumpPlan               : Bool := false
  seenInput              : Bool := false
  hasLavfiFmt            : Bool := false
  hasLavfiInput          : Bool := false
  hasExtraDelegatedFlags : Bool := false
  extraErrors            : List CliError := []
  mpegOptions            : List (String × String) := []
  seenFirstOutput        : Bool := false
  pendingOutputFmt       : Option String := none
  extraOutputs           : List (String × Option String) := []
  deriving Repr, DecidableEq, Inhabited

def parseSignedMapIndex : String → Option Int
  | "-1" => some (-1)
  | s    =>
    match parseNonNegNatSpec s with
    | some n => some (Int.ofNat n)
    | none   => none

/-- FFmpeg `fftools` `OPT_TYPE_BOOL` flags (and their `-no<opt>` negations), which take 0 CLI arguments. -/
def isZeroArgDelegatedFlag (tok : String) : Bool :=
  if !strStartsWithFast tok "-" || tok == "-" then false
  else
    let body := String.ofList (tok.toList.drop 1)
    let base := (splitStrOnChar body ':').headD ""
    let boolNames : List String :=
      ["dn", "bitexact", "auto_conversion_filters", "shortest", "copyts",
       "start_at_zero", "intra", "xerror", "re", "accurate_seek", "autorotate",
       "autoscale", "find_stream_info", "force_fps", "fix_sub_duration",
       "fix_sub_duration_heartbeat", "ignore_unknown", "copy_unknown",
       "recast_media", "benchmark", "benchmark_all", "stdin", "dump", "hex",
       "copyinkf", "print_graphs", "stats", "debug_ts", "display_hflip", "display_vflip"]
    let strippedNo :=
      if strStartsWithFast base "no" then String.ofList (base.toList.drop 2) else ""
    boolNames.contains base || (strippedNo != "" && boolNames.contains strippedNo)

def isOneArgExtendedPrimaryFlag (tok : String) : Bool :=
  tok == "-i" || tok == "-lavfi" || tok == "-filter_complex" || tok == "-map" ||
  tok == "-metadata" || tok == "-map_metadata" || tok == "-map_chapters" ||
  tok == "-c:s" || tok == "-scodec" || tok == "-codec:s" ||
  tok == "-bsf:v" || tok == "-bsf:a" || tok == "-bsf:s" ||
  tok == "-bsf" || tok == "-vbsf" || tok == "-absf" || tok == "-sbsf" ||
  tok == "-f" || tok == "-c" || tok == "-codec" ||
  tok == "-c:v" || tok == "-vcodec" || tok == "-codec:v" ||
  tok == "-c:a" || tok == "-acodec" || tok == "-codec:a" ||
  tok == "-s" || tok == "-video_size" || tok == "-r" || tok == "-framerate" ||
  tok == "-ar" || tok == "-ac" || tok == "-pix_fmt" || tok == "-pixel_format" ||
  tok == "-ss"

def hasLavfiSourceFilter (graph : String) : Bool :=
  ["sine=", "color=", "testsrc", "nullsrc", "aevalsrc", "anullsrc", "smptebars",
   "mandelbrot", "life=", "cellauto", "gradients", "allrgb", "allyuv", "haldclutsrc",
   "pal75bars", "pal100bars", "rgbtestsrc", "sierpinski", "hilbert", "afirsrc",
   "anoisesrc", "movie=", "amovie="].any (fun src => strStartsWithFast graph src)

def applyExtendedFlagValue (tok value : String) (rest : List String) (acc : ExtendedPlanFlags) : ExtendedPlanFlags :=
  if tok == "-i" then
    { acc with seenInput := true, baseArgs := acc.baseArgs ++ ["-i", value] }
  else if tok == "-lavfi" then
    if value == "" then { acc with extraErrors := acc.extraErrors ++ [.emptyValue "-lavfi"] }
    else { acc with hasExtraDelegatedFlags := true, hasLavfiInput := true }
  else if tok == "-filter_complex" then
    if value == "" then { acc with extraErrors := acc.extraErrors ++ [.emptyValue "-filter_complex"] }
    else { acc with hasExtraDelegatedFlags := true, hasLavfiInput := acc.hasLavfiInput || hasLavfiSourceFilter value }
  else if tok == "-/filter_complex" then
    if isSafeLocalMediaPath value then
      { acc with hasExtraDelegatedFlags := true, hasLavfiInput := true }
    else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag (tok ++ " " ++ value)] }
  else if tok == "-map" then
    match parseStreamMapSpec value with
    | some m => { acc with maps := acc.maps ++ [m] }
    | none   =>
      if isExtendedMapSpec value then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map " ++ value)] }
  else if tok == "-metadata" then
    match parseMetadataSpec value with
    | some kv => { acc with metadataEntries := acc.metadataEntries ++ [kv] }
    | none    => { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-metadata " ++ value)] }
  else if tok == "-map_metadata" then
    match parseSignedMapIndex value with
    | some idx => { acc with mapMetadataSource := idx, hasExtraDelegatedFlags := true }
    | none =>
      if value != "" && (strStartsWithFast value "0:" || strStartsWithFast value "1:") then
        { acc with hasExtraDelegatedFlags := true }
      else
        { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map_metadata " ++ value)] }
  else if tok == "-map_chapters" then
    match parseSignedMapIndex value with
    | some idx => { acc with mapChaptersSource := idx, hasExtraDelegatedFlags := true }
    | none => { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-map_chapters " ++ value)] }
  else if tok == "-c:s" || tok == "-scodec" || tok == "-codec:s" then
    match parseSubtitleCodecSpec value with
    | some sc => { acc with subtitleCodec := some sc }
    | none    =>
      if isExtendedSubtitleCodec value then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-c:s " ++ value)] }
  else if tok == "-bsf:v" then
    if supportedBsfChain value then { acc with bsfs := acc.bsfs ++ [{ kind := .video, filterName := value }] }
    else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-bsf:v " ++ value)] }
  else if tok == "-bsf:a" then
    if supportedBsfChain value then { acc with bsfs := acc.bsfs ++ [{ kind := .audio, filterName := value }] }
    else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-bsf:a " ++ value)] }
  else if tok == "-bsf:s" || tok == "-bsf" || tok == "-vbsf" || tok == "-absf" || tok == "-sbsf" then
    if supportedBsfChain value then { acc with hasExtraDelegatedFlags := true }
    else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-bsf " ++ value)] }
  else if tok == "-f" then
    if rest.contains "-i" then
      if supportedFormat value then
        { acc with hasExtraDelegatedFlags := true, hasLavfiFmt := acc.hasLavfiFmt || value == "lavfi" }
      else
        { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-f " ++ value)] }
    else if !acc.seenFirstOutput then
      { acc with pendingOutputFmt := some value, baseArgs := acc.baseArgs ++ ["-f", value] }
    else
      if supportedFormat value then
        { acc with pendingOutputFmt := some value, hasExtraDelegatedFlags := true }
      else
        { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-f " ++ value)] }
  else if tok == "-c" || tok == "-codec" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parseCliCodec value).isSome || (parseSubtitleCodecSpec value).isSome || isExtendedSubtitleCodec value then
        { acc with hasExtraDelegatedFlags := true }
      else
        { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-c " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ [tok, value] }
  else if tok == "-c:v" || tok == "-vcodec" || tok == "-codec:v" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parseCliCodec value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-c:v " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-c:v", value] }
  else if tok == "-c:a" || tok == "-acodec" || tok == "-codec:a" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parseCliCodec value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-c:a " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-c:a", value] }
  else if tok == "-s" || tok == "-video_size" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parseVideoSizeSpec value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-s " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-s", value] }
  else if tok == "-r" || tok == "-framerate" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if isValidFrameRateSpec value then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-r " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-r", value] }
  else if tok == "-ar" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parsePosNatSpec value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-ar " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-ar", value] }
  else if tok == "-ac" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if (parsePosNatSpec value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-ac " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-ac", value] }
  else if tok == "-pix_fmt" || tok == "-pixel_format" then
    if rest.contains "-i" || acc.seenFirstOutput then
      if supportedPixFmt value then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-pix_fmt " ++ value)] }
    else
      { acc with baseArgs := acc.baseArgs ++ ["-pix_fmt", value] }
  else if tok == "-ss" then
    if acc.seenFirstOutput then
      if (parseCliSeconds value).isSome then { acc with hasExtraDelegatedFlags := true }
      else { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag ("-ss " ++ value)] }
    else
      { acc with hasExtraDelegatedFlags := acc.hasExtraDelegatedFlags || acc.seenInput, baseArgs := acc.baseArgs ++ ["-ss", value] }
  else if isValidExtendedFlagValue tok value then
    { acc with
      hasExtraDelegatedFlags := true
      mpegOptions := if isMpegDelegatedValueFlag tok then
        acc.mpegOptions ++ [(tok, value)] else acc.mpegOptions }
  else
    { acc with extraErrors := acc.extraErrors ++ [.unsupportedCodecOrFlag (tok ++ " " ++ value)] }

def isPassthroughBaseZeroFlag (tok : String) : Bool :=
  tok == "-y" || tok == "-n" || tok == "-stats" || tok == "-nostats" ||
  tok == "-hide_banner" || tok == "-vn" || tok == "-an" || tok == "-nostdin" ||
  tok == "-json" || tok == "--json"

def isPassthroughBaseOneFlag (tok : String) : Bool :=
  tok == "-vf" || tok == "-filter:v" ||
  tok == "-af" || tok == "-filter:a" || tok == "-t" || tok == "-crf" ||
  tok == "-preset" || tok == "-b:v" || tok == "-vb" || tok == "-b" ||
  tok == "-b:a" || tok == "-ab" || tok == "-threads" ||
  tok == "-bf" || tok == "-g" || tok == "-movflags" || tok == "-frames:v" ||
  tok == "-vframes" || tok == "-frames" || tok == "-v" || tok == "-loglevel" ||
  tok == "-daemon" || tok == "-golden"

def extractExtendedPlanFlagsStep : List String → Option String → ExtendedPlanFlags → ExtendedPlanFlags
  | [], none, acc => acc
  | [], some tok, acc =>
    if isPassthroughBaseOneFlag tok ||
       tok == "-i" || tok == "-f" || tok == "-c" || tok == "-codec" ||
       tok == "-c:v" || tok == "-vcodec" || tok == "-codec:v" ||
       tok == "-c:a" || tok == "-acodec" || tok == "-codec:a" || tok == "-s" || tok == "-video_size" ||
       tok == "-r" || tok == "-framerate" || tok == "-ar" || tok == "-ac" ||
       tok == "-pix_fmt" || tok == "-pixel_format" || tok == "-ss" then
      { acc with baseArgs := acc.baseArgs ++ [tok] }
    else
      let canon :=
        if tok == "-scodec" || tok == "-codec:s" then "-c:s"
        else if tok == "-bsf:s" || tok == "-vbsf" || tok == "-absf" || tok == "-sbsf" then "-bsf"
        else tok
      { acc with extraErrors := acc.extraErrors ++ [.missingValue canon] }
  | value :: tail, some tok, acc =>
    if isPassthroughBaseOneFlag tok then
      extractExtendedPlanFlagsStep tail none { acc with baseArgs := acc.baseArgs ++ [tok, value] }
    else
      extractExtendedPlanFlagsStep tail none (applyExtendedFlagValue tok value tail acc)
  | tok :: tail, none, acc =>
    if isPassthroughBaseZeroFlag tok then
      extractExtendedPlanFlagsStep tail none { acc with baseArgs := acc.baseArgs ++ [tok] }
    else if isPassthroughBaseOneFlag tok then
      extractExtendedPlanFlagsStep tail (some tok) acc
    else if tok == "-dump-plan" || tok == "--dump-plan" then
      extractExtendedPlanFlagsStep tail none { acc with dumpPlan := true }
    else if tok == "-sn" then
      extractExtendedPlanFlagsStep tail none { acc with noSubtitle := true, baseArgs := acc.baseArgs ++ ["-sn"] }
    else if !strStartsWithFast tok "-" || tok == "-" then
      if !acc.seenFirstOutput then
        extractExtendedPlanFlagsStep tail none
          { acc with seenFirstOutput := true, pendingOutputFmt := none, baseArgs := acc.baseArgs ++ [tok] }
      else
        extractExtendedPlanFlagsStep tail none
          { acc with
              extraOutputs := acc.extraOutputs ++ [(tok, acc.pendingOutputFmt)],
              pendingOutputFmt := none,
              hasExtraDelegatedFlags := true }
    else if isOneArgExtendedPrimaryFlag tok then
      extractExtendedPlanFlagsStep tail (some tok) acc
    else if isZeroArgDelegatedFlag tok then
      extractExtendedPlanFlagsStep tail none { acc with hasExtraDelegatedFlags := true }
    else if isExtendedDelegatedValueFlag tok then
      extractExtendedPlanFlagsStep tail (some tok) acc
    else
      extractExtendedPlanFlagsStep tail none { acc with baseArgs := acc.baseArgs ++ [tok] }

def extractExtendedPlanFlagsLoop (args : List String) (acc : ExtendedPlanFlags) : ExtendedPlanFlags :=
  extractExtendedPlanFlagsStep args none acc

/-- Lower a `CliConfig` and optional `ExtendedPlanFlags` into a typed `MediaPlanIR`. -/
def lowerCliWithExtToPlanIR (cfg : CliConfig) (ext : ExtendedPlanFlags := {}) : MediaPlanIR :=
  CliConfig.casesOn cfg fun cfgInputs cfgVideoCodec cfgAudioCodec cfgVideoFilter cfgAudioFilter
      cfgStartSec cfgDurationSec cfgFormat cfgDaemon cfgGolden cfgOutput cfgOverwrite
      cfgNoVideo cfgNoAudio cfgJsonOutput cfgHideBanner cfgShowStats cfgLogLevel
      cfgVideoSize cfgVideoFrames cfgAudioRate cfgAudioChannels cfgPixelFormat cfgPreset
      cfgCrf cfgVideoBitrate cfgAudioBitrate cfgFrameRate cfgBFrames cfgGopSize
      cfgThreads cfgMovflags cfgErrors =>
  ExtendedPlanFlags.casesOn ext fun _extBaseArgs _extPassthroughArgs extMaps extMetadataEntries
      extMapMetadataSource extMapChaptersSource extSubtitleCodec extNoSubtitle extBsfs
      extDumpPlan _extSeenInput extHasLavfiFmt extHasLavfiInput extHasExtraDelegatedFlags
      extExtraErrors extMpegOptions _extSeenFirstOut _extPendingFmt extExtraOutputs =>
  let startMsOpt := cfgStartSec.bind cliSecondsToMillis
  let durMsOpt := cfgDurationSec.bind cliSecondsToMillis
  let startOverflow := cfgStartSec.isSome && startMsOpt.isNone
  let durOverflow := cfgDurationSec.isSome && durMsOpt.isNone
  let hasCopyFilterConflict : Bool :=
    (cfgVideoCodec == some .copy && cfgVideoFilter.isSome) ||
    (cfgAudioCodec == some .copy && cfgAudioFilter.isSome)
  let copyFilterErr : List CliError := if hasCopyFilterConflict then [.copyWithFilter] else []
  let effectiveInputs : List String :=
    if !cfgInputs.isEmpty then cfgInputs
    else if extHasLavfiInput then ["lavfi_graph"]
    else []
  let missingInErr : List CliError := if effectiveInputs.isEmpty then [.missingInput] else []
  let missingOutErr : List CliError := if cfgOutput.isNone && cfgDaemon.isNone then [.missingOutput] else []
  let allErrors := cfgErrors ++ extExtraErrors ++ copyFilterErr ++ missingInErr ++ missingOutErr

  let rec buildInputs (paths : List String) (idx : Nat) : List InputSpec :=
    match paths with
    | [] => []
    | p :: ps =>
      let isSafeIn :=
        if extHasLavfiFmt || (extHasLavfiInput && cfgInputs.isEmpty) then isSafeLavfiGraph p
        else isSafeLocalMediaPath p || isSafeConcatInputPath p
      { index := idx
        path := p
        safePath := isSafeIn
        seekStart := if idx == 0 then cfgStartSec else none
        duration := if idx == 0 then cfgDurationSec else none } :: buildInputs ps (idx + 1)
  let inputSpecs := buildInputs effectiveInputs 0
  let anyConcatInput := effectiveInputs.any isSafeConcatInputPath

  let outPath := cfgOutput.getD ""
  let inferredFmt := inferContainerFormat cfgFormat outPath
  let extraOutSpecs : List OutputSpec :=
    extExtraOutputs.map fun (ep, efmt) =>
      let einf := inferContainerFormat efmt ep
      { path := ep
        safePath := isSafeOutputTarget ep efmt.isSome efmt
        format := einf
        overwrite := cfgOverwrite }
  let outputSpecs : List OutputSpec :=
    match cfgOutput with
    | none => []
    | some p =>
      [{ path := p
         safePath := isSafeOutputTarget p cfgFormat.isSome cfgFormat
         format := inferredFmt
         overwrite := cfgOverwrite
         videoCodec := cfgVideoCodec
         audioCodec := cfgAudioCodec
         subtitleCodec := extSubtitleCodec
         pixelFormat := cfgPixelFormat
         preset := cfgPreset
         crf := cfgCrf
         videoBitrate := cfgVideoBitrate
         audioBitrate := cfgAudioBitrate
         frameRate := cfgFrameRate
         videoSize := cfgVideoSize
         videoFrames := cfgVideoFrames
         audioRate := cfgAudioRate
         audioChannels := cfgAudioChannels
         bFrames := cfgBFrames
         gopSize := cfgGopSize
         movflags := cfgMovflags
         noVideo := cfgNoVideo
         noAudio := cfgNoAudio
         noSubtitle := extNoSubtitle }] ++ extraOutSpecs

  let defaultStreams : List StreamMapSpec :=
    (if cfgNoVideo then [] else [{ inputIdx := 0, kind := .video, streamIdx := some 0, optional := false }]) ++
    (if cfgNoAudio then [] else [{ inputIdx := 0, kind := .audio, streamIdx := some 0, optional := true }]) ++
    (match extSubtitleCodec with
     | some _ => if extNoSubtitle then [] else [{ inputIdx := 0, kind := .subtitle, streamIdx := some 0, optional := true }]
     | none   => [])
  let effectiveMaps := if extMaps.isEmpty then defaultStreams else extMaps

  let vfStages := match cfgVideoFilter with
    | some vf => splitStrOnChar vf ','
    | none    => []
  let afStages := match cfgAudioFilter with
    | some af => splitStrOnChar af ','
    | none    => []

  let anyUnsafeInput := inputSpecs.any (fun i => !i.safePath)
  let anyUnsafeOutput := outputSpecs.any (fun o => !o.safePath)
  let unsupportedDaemonOrGolden := cfgDaemon.isSome || cfgGolden.isSome
  let unknownFormat := outputSpecs.any (fun o => o.format == "unknown")

  let isMixedCopyTranscode : Bool :=
    (cfgAudioCodec == some .copy && cfgVideoCodec != some .copy) ||
    (cfgVideoCodec == some .copy && cfgAudioCodec.isSome && cfgAudioCodec != some .copy)

  let isSingleMp4Input : Bool :=
    match inputSpecs with
    | [i] =>
      let lowerIn := strToLowerAscii i.path
      !anyConcatInput && (strEndsWithFast lowerIn ".mp4" || strEndsWithFast lowerIn ".m4v")
    | _ => false

  let isDelegatedVideoCodec : Bool :=
    match cfgVideoCodec with
    | none | some .copy | some .h264 | some .hevc | some .av1 => false
    | _ => true

  let isDelegatedVideoFilter : Bool :=
    match cfgVideoFilter with
    | none => false
    | some vf => !isNativeMp4VideoFilter vf

  let isDelegatedPixFmt : Bool :=
    match cfgPixelFormat with
    | none => false
    | some pf => !nativeMp4PixFmt pf

  let isDelegatedContainerOrOption : Bool :=
    inferredFmt != "mp4" ||
    !extExtraOutputs.isEmpty ||
    anyConcatInput ||
    !isSingleMp4Input ||
    extHasExtraDelegatedFlags ||
    !extMpegOptions.isEmpty ||
    extNoSubtitle ||
    !extMaps.isEmpty ||
    !extMetadataEntries.isEmpty ||
    extMapMetadataSource != -1 ||
    extMapChaptersSource != -1 ||
    extSubtitleCodec.isSome ||
    !extBsfs.isEmpty ||
    cfgAudioFilter.isSome ||
    cfgNoVideo ||
    cfgVideoFrames.isSome ||
    cfgAudioRate.isSome ||
    (cfgAudioChannels.isSome && cfgAudioChannels != some 2) ||
    cfgThreads.isSome ||
    cfgBFrames.isSome ||
    cfgGopSize.isSome ||
    cfgMovflags.isSome ||
    isMixedCopyTranscode ||
    isDelegatedVideoFilter ||
    isDelegatedPixFmt ||
    (cfgAudioCodec.isSome && cfgAudioCodec != some .copy && cfgAudioCodec != some .aac) ||
    isDelegatedVideoCodec

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
    else if inputSpecs.isEmpty || outputSpecs.isEmpty then
      (.unsupported, ["at_least_one_input_and_one_output_required"])
    else if isDelegatedContainerOrOption then
      (.delegatedFaithful, ["phase4_structured_argv_delegation"])
    else if cfgStartSec.isSome || cfgDurationSec.isSome || cfgVideoCodec != some .copy then
      (.translatedPartial, ["mp4_seek_or_pixel_simd_transcode"])
    else
      (.delegatedFaithful, ["mp4_stream_copy"])

  { inputs := inputSpecs
    outputs := outputSpecs
    streams := defaultStreams
    programs := [{ programId := 0, streamMaps := effectiveMaps }]
    maps := effectiveMaps
    graphs := {
      videoFilter := cfgVideoFilter
      audioFilter := cfgAudioFilter
      videoStages := vfStages
      audioStages := afStages
      bitstreamFilters := extBsfs
    }
    timeline := {
      startSec := cfgStartSec
      durationSec := cfgDurationSec
      startMs := startMsOpt
      durationMs := durMsOpt
      frameRate := cfgFrameRate
    }
    metadata := {
      entries := extMetadataEntries
      mapMetadataSource := extMapMetadataSource
      mapChaptersSource := extMapChaptersSource
      preserveColor := !(vfStages.any (fun s => s == "colorspace=bt709" || s == "bt2020_to_bt709"))
    }
    resources := {
      threads := cfgThreads
      jsonOutput := cfgJsonOutput
      hideBanner := cfgHideBanner
      showStats := cfgShowStats
      logLevel := cfgLogLevel
      dumpPlan := extDumpPlan
    }
    mpegOptions := extMpegOptions
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

/-- Single-pass parse and lowering returning `(CliConfig, ExtendedPlanFlags, MediaPlanIR)`. -/
def parseArgsWithPlanIRBase (args : List String) : CliConfig × ExtendedPlanFlags × MediaPlanIR :=
  let ext0 := extractExtendedPlanFlagsLoop args {}
  let ext := { ext0 with passthroughArgs := stripInternalLffmpegArgs args }
  let cfg := parseFFmpegArgs ext0.baseArgs
  let plan := lowerCliWithExtToPlanIR cfg ext0
  (cfg, ext, plan)

def isNativeFfv1PixFmt (pf : String) : Bool :=
  pf == "yuv420p" || pf == "gray" || pf == "rgb24" || pf == "bgr0"

def isNativeFfv1OptionPair (tok val : String) : Bool :=
  if tok == "-level" || tok == "-level:v" then val == "3"
  else if tok == "-coder" then
    val == "0" || val == "1" || val == "2" || val == "-2" ||
    val == "rice" || val == "ac" || val == "range_def" || val == "range_tab"
  else if tok == "-context" then val == "0" || val == "1"
  else if tok == "-slicecrc" then val == "0" || val == "1"
  else if tok == "-slices" then
    match parsePosNatSpec val with
    | some n => n >= 1 && n <= 64
    | none => false
  else false

def scanNativeFfv1PreInput : List String → Option String → Bool → Bool → Bool
  | [], some "rawvideo", hasSize, hasPix => hasSize && hasPix
  | [], some _, false, false => true
  | [], none, false, false => true
  | [], _, _, _ => false
  | "-y" :: rest, fmt, hs, hp | "-n" :: rest, fmt, hs, hp | "-nostdin" :: rest, fmt, hs, hp |
    "-hide_banner" :: rest, fmt, hs, hp | "-stats" :: rest, fmt, hs, hp | "-nostats" :: rest, fmt, hs, hp |
    "-an" :: rest, fmt, hs, hp | "-json" :: rest, fmt, hs, hp | "--json" :: rest, fmt, hs, hp |
    "-dump-plan" :: rest, fmt, hs, hp | "--dump-plan" :: rest, fmt, hs, hp =>
    scanNativeFfv1PreInput rest fmt hs hp
  | "-v" :: _ :: rest, fmt, hs, hp | "-loglevel" :: _ :: rest, fmt, hs, hp =>
    scanNativeFfv1PreInput rest fmt hs hp
  | "-f" :: fStr :: rest, _, hs, hp =>
    let fl := strToLowerAscii fStr
    if fl == "rawvideo" || fl == "yuv4mpegpipe" || fl == "y4m" ||
       fl == "matroska" || fl == "mkv" || fl == "mov" || fl == "avi" then
      scanNativeFfv1PreInput rest (some fl) hs hp
    else false
  | "-s" :: sz :: rest, fmt, _, hp | "-video_size" :: sz :: rest, fmt, _, hp =>
    if (parseVideoSizeSpec sz).isSome then scanNativeFfv1PreInput rest fmt true hp else false
  | "-pix_fmt" :: pf :: rest, fmt, hs, _ | "-pixel_format" :: pf :: rest, fmt, hs, _ =>
    if isNativeFfv1PixFmt pf then scanNativeFfv1PreInput rest fmt hs true else false
  | "-r" :: rStr :: rest, fmt, hs, hp | "-framerate" :: rStr :: rest, fmt, hs, hp =>
    if isValidFrameRateSpec rStr then scanNativeFfv1PreInput rest fmt hs hp else false
  | "-c:v" :: cv :: rest, fmt, hs, hp | "-vcodec" :: cv :: rest, fmt, hs, hp |
    "-codec:v" :: cv :: rest, fmt, hs, hp | "-c" :: cv :: rest, fmt, hs, hp | "-codec" :: cv :: rest, fmt, hs, hp =>
    if cv == "ffv1" || cv == "rawvideo" then scanNativeFfv1PreInput rest fmt hs hp else false
  | _, _, _, _ => false

def scanNativeFfv1PostInput : List String → Option String → Option String → Bool → Option (Option String × Option String)
  | [], outFmt, outPix, true => some (outFmt, outPix)
  | [], _, _, false => none
  | "-y" :: rest, ofmt, opix, so | "-n" :: rest, ofmt, opix, so | "-nostdin" :: rest, ofmt, opix, so |
    "-hide_banner" :: rest, ofmt, opix, so | "-stats" :: rest, ofmt, opix, so | "-nostats" :: rest, ofmt, opix, so |
    "-an" :: rest, ofmt, opix, so | "-json" :: rest, ofmt, opix, so | "--json" :: rest, ofmt, opix, so |
    "-dump-plan" :: rest, ofmt, opix, so | "--dump-plan" :: rest, ofmt, opix, so =>
    scanNativeFfv1PostInput rest ofmt opix so
  | "-v" :: _ :: rest, ofmt, opix, so | "-loglevel" :: _ :: rest, ofmt, opix, so =>
    scanNativeFfv1PostInput rest ofmt opix so
  | "-f" :: fStr :: rest, _, opix, false =>
    scanNativeFfv1PostInput rest (some (strToLowerAscii fStr)) opix false
  | "-pix_fmt" :: pf :: rest, ofmt, _, false | "-pixel_format" :: pf :: rest, ofmt, _, false =>
    if isNativeFfv1PixFmt pf then scanNativeFfv1PostInput rest ofmt (some pf) false else none
  | "-c:v" :: _ :: rest, ofmt, opix, false | "-vcodec" :: _ :: rest, ofmt, opix, false |
    "-codec:v" :: _ :: rest, ofmt, opix, false | "-c" :: _ :: rest, ofmt, opix, false |
    "-codec" :: _ :: rest, ofmt, opix, false | "-r" :: _ :: rest, ofmt, opix, false |
    "-framerate" :: _ :: rest, ofmt, opix, false | "-frames:v" :: _ :: rest, ofmt, opix, false |
    "-vframes" :: _ :: rest, ofmt, opix, false | "-frames" :: _ :: rest, ofmt, opix, false |
    "-g" :: _ :: rest, ofmt, opix, false =>
    scanNativeFfv1PostInput rest ofmt opix false
  | tok :: val :: rest, ofmt, opix, false =>
    if !strStartsWithFast tok "-" || tok == "-" then
      scanNativeFfv1PostInput (val :: rest) ofmt opix true
    else if isNativeFfv1OptionPair tok val then
      scanNativeFfv1PostInput rest ofmt opix false
    else none
  | [tok], ofmt, opix, false =>
    if !strStartsWithFast tok "-" || tok == "-" then some (ofmt, opix) else none
  | _, _, _, true => none

def splitAtFirstInput : List String → List String → Option (List String × String × List String)
  | [], _ => none
  | "-i" :: inPath :: rest, revPre => some (revPre.reverse, inPath, rest)
  | tok :: rest, revPre => splitAtFirstInput rest (tok :: revPre)

def resolveNativeFfv1PlanFormat (args : List String) (cfg : CliConfig) (plan : MediaPlanIR) : Option String :=
  if !plan.errors.isEmpty || plan.backend.tier == .unsupported ||
     plan.inputs.length != 1 || plan.outputs.length != 1 then none
  else
    match splitAtFirstInput args [], plan.outputs.head? with
    | some (preArgs, inPath, postArgs), some outSpec =>
      if !scanNativeFfv1PreInput preArgs none false false then none
      else
        match scanNativeFfv1PostInput postArgs none none false with
        | none => none
        | some (postFmtOpt, postPixOpt) =>
          let effOutFmt := strToLowerAscii (inferContainerFormat postFmtOpt outSpec.path)
          let lowerIn := strToLowerAscii inPath
          let isRawOrY4mIn :=
            preArgs.contains "rawvideo" || preArgs.contains "yuv4mpegpipe" ||
            preArgs.contains "y4m" || strEndsWithFast lowerIn ".y4m"
          let isFfv1ContIn :=
            preArgs.contains "matroska" || preArgs.contains "mkv" ||
            preArgs.contains "mov" || preArgs.contains "avi" ||
            strEndsWithFast lowerIn ".mkv" || strEndsWithFast lowerIn ".mov" || strEndsWithFast lowerIn ".avi"
          let ok :=
            if cfg.videoCodec == some .ffv1 then
              (isRawOrY4mIn || isFfv1ContIn) &&
              (effOutFmt == "matroska" || effOutFmt == "mkv" || effOutFmt == "mov" || effOutFmt == "avi" || effOutFmt == "null")
            else if !isFfv1ContIn || isRawOrY4mIn then
              false
            else if postArgs.contains "-level" || postArgs.contains "-level:v" ||
                    postArgs.contains "-coder" || postArgs.contains "-context" ||
                    postArgs.contains "-slices" || postArgs.contains "-slicecrc" || cfg.gopSize.isSome then
              false
            else if cfg.videoCodec == some .copy then
              effOutFmt == "matroska" || effOutFmt == "mkv" || effOutFmt == "mov" || effOutFmt == "avi" || effOutFmt == "null"
            else if cfg.videoCodec.isNone || cfg.videoCodec == some .rawvideo then
              (effOutFmt == "rawvideo" || effOutFmt == "null" || effOutFmt == "md5" || effOutFmt == "framemd5") ||
              ((effOutFmt == "yuv4mpegpipe" || effOutFmt == "y4m") &&
               (postPixOpt.isNone || postPixOpt == some "yuv420p" || postPixOpt == some "gray"))
            else false
          if ok then some effOutFmt else none
    | _, _ => none

def isNativeFfv1ArgvEligible (args : List String) (cfg : CliConfig) (plan : MediaPlanIR) : Bool :=
  (resolveNativeFfv1PlanFormat args cfg plan).isSome

def promoteNativeFfv1Plan (args : List String) (cfg : CliConfig) (plan : MediaPlanIR) : MediaPlanIR :=
  match resolveNativeFfv1PlanFormat args cfg plan with
  | some effOutFmt =>
    { plan with
      outputs := plan.outputs.map fun o =>
        { o with
          format := effOutFmt
          safePath := isSafeOutputTarget o.path (effOutFmt != "unknown") (some effOutFmt) }
      backend := {
        tier := .independentVerified
        delegatedContainer := false
        fallbackAllowed := cfg.videoCodec != some .ffv1 && !(args.contains "ffv1")
        reasons := ["ffv1_v3_native_verified_codec"]
      } }
  | none => plan

/-- Single-pass parse and lowering returning `(CliConfig, ExtendedPlanFlags, MediaPlanIR)` with FFV1 promotion. -/
def parseArgsWithPlanIR (args : List String) : CliConfig × ExtendedPlanFlags × MediaPlanIR :=
  let (cfg, ext, plan0) := parseArgsWithPlanIRBase args
  (cfg, ext, promoteNativeFfv1Plan args cfg plan0)

/-- Parse raw FFmpeg CLI arguments (including Phase 3/4 flags) directly into a typed `MediaPlanIR`. -/
def parseArgsToPlanIR (args : List String) : MediaPlanIR :=
  let ext0 := extractExtendedPlanFlagsLoop args {}
  let cfg := parseFFmpegArgs ext0.baseArgs
  promoteNativeFfv1Plan args cfg (lowerCliWithExtToPlanIR cfg ext0)

/--
  Unified argv renderer for `MediaPlanIR`:
  - `forDelegation = false`: renders canonical `lffmpeg` CLI arguments (round-trip inverse of `parseArgsToPlanIR`).
  - `forDelegation = true`: renders structured `ffmpeg` argv for `fork` + `execvp` (`-nostdin`, encoder names).
-/
def renderPlanIRArgv (plan : MediaPlanIR) (forDelegation : Bool) : List String :=
  MediaPlanIR.casesOn plan fun planInputs planOutputs planStreams _planPrograms planMaps
      planGraphs planTimeline planMetadata planResources _planErrors _planBackend planMpegOptions =>
  ResourcePolicyIR.casesOn planResources fun resThreads resJsonOutput resHideBanner
      resShowStats resLogLevel resDumpPlan =>
  TimelineIR.casesOn planTimeline fun timeStartSec timeDurationSec _timeStartMs _timeDurMs _timeFps =>
  MetadataPolicyIR.casesOn planMetadata fun metaEntries metaMapSource metaChaptersSource _metaColor =>
  FilterGraphIR.casesOn planGraphs fun graphVf graphAf _graphVfStages _graphAfStages graphBsfs =>
  let outOpt := planOutputs.head?
  let preArgs : List String := if forDelegation then ["-nostdin"] else []
  let overwriteArgs : List String :=
    match outOpt with
    | some o => if o.overwrite then ["-y"] else ["-n"]
    | none   => []
  let resArgs : List String :=
    if forDelegation then
      (if resHideBanner || resJsonOutput then ["-hide_banner"] else []) ++
      (if !resShowStats || resJsonOutput then ["-nostats"] else []) ++
      ["-v", if resJsonOutput then "error" else resLogLevel]
    else
      (if resDumpPlan then ["-dump-plan"] else []) ++
      (if resHideBanner then ["-hide_banner"] else []) ++
      (if resShowStats then ["-stats"] else ["-nostats"]) ++
      (if resLogLevel != "info" then ["-v", resLogLevel] else []) ++
      (if resJsonOutput then ["-json"] else []) ++
      (match resThreads with | some t => ["-threads", s!"{t}"] | none => [])
  let timeArgs : List String :=
    (match timeStartSec with | some s => ["-ss", formatCliSeconds s] | none => []) ++
    (match timeDurationSec with | some d => ["-t", formatCliSeconds d] | none => [])
  let inArgs : List String :=
    planInputs.flatMap (fun i => ["-i", i.path])
  let explicitMaps : List String :=
    if planMaps == planStreams then []
    else planMaps.flatMap (fun m => ["-map", formatStreamMapSpec m])
  let metaArgs : List String :=
    metaEntries.flatMap (fun kv => ["-metadata", formatMetadataSpec kv]) ++
    (if metaMapSource != -1 then ["-map_metadata", s!"{metaMapSource}"] else []) ++
    (if metaChaptersSource != -1 then ["-map_chapters", s!"{metaChaptersSource}"] else [])
  let graphArgs : List String :=
    (match graphVf with | some vf => ["-vf", vf] | none => []) ++
    (match graphAf with | some af => ["-af", af] | none => []) ++
    graphBsfs.flatMap (fun b =>
      match b.kind with
      | .audio => ["-bsf:a", b.filterName]
      | _      => ["-bsf:v", b.filterName])
  let outArgs : List String :=
    match outOpt with
    | none => []
    | some o =>
      OutputSpec.casesOn o fun oPath _oSafe oFormat _oOverwrite oVideoCodec oAudioCodec
          oSubtitleCodec oPixelFormat oPreset oCrf oVideoBitrate oAudioBitrate oFrameRate
          oVideoSize oVideoFrames oAudioRate oAudioChannels oBFrames oGopSize oMovflags
          oNoVideo oNoAudio oNoSubtitle =>
      (if oNoVideo then ["-vn"] else []) ++
      (if oNoAudio then ["-an"] else []) ++
      (if oNoSubtitle then ["-sn"] else []) ++
      (if forDelegation then
        (match oVideoCodec with | some vc => ["-c:v", codecToDelegatedVideoEncoder vc] | none => []) ++
        (match oAudioCodec with | some ac => ["-c:a", codecToDelegatedAudioEncoder ac] | none => [])
       else
        match oVideoCodec, oAudioCodec with
        | some .copy, some .copy => ["-c", "copy"]
        | vc, ac =>
          (match vc with | some c => ["-c:v", codecToCanonicalString c] | none => []) ++
          (match ac with | some c => ["-c:a", codecToCanonicalString c] | none => [])) ++
      (match oSubtitleCodec with | some sc => ["-c:s", sc.toString] | none => []) ++
      (match oVideoSize with | some (w, h) => ["-s", s!"{w}x{h}"] | none => []) ++
      (match oVideoFrames with | some n => ["-frames:v", s!"{n}"] | none => []) ++
      (match oAudioRate with | some r => ["-ar", s!"{r}"] | none => []) ++
      (match oAudioChannels with | some ch => ["-ac", s!"{ch}"] | none => []) ++
      (match oPixelFormat with | some pf => ["-pix_fmt", pf] | none => []) ++
      (match oPreset with | some pr => ["-preset", pr] | none => []) ++
      (match oCrf with | some c => ["-crf", c] | none => []) ++
      (match oBFrames with | some bf => ["-bf", s!"{bf}"] | none => []) ++
      (match oGopSize with | some g => ["-g", s!"{g}"] | none => []) ++
      (match oFrameRate with | some r => ["-r", r] | none => []) ++
      (match oVideoBitrate with | some vb => ["-b:v", vb] | none => []) ++
      (match oAudioBitrate with | some ab => ["-b:a", ab] | none => []) ++
      (if forDelegation then (match resThreads with | some t => ["-threads", s!"{t}"] | none => []) else []) ++
      (match oMovflags with | some mf => ["-movflags", mf] | none => []) ++
      planMpegOptions.flatMap (fun (flag, value) => [flag, value]) ++
      (if forDelegation && oFormat == "null" then
        ["-f", "null", "-"]
       else
        (if inferContainerFormat none oPath != oFormat && supportedFormat oFormat then ["-f", oFormat] else []) ++
        [oPath])
  preArgs ++ overwriteArgs ++ resArgs ++ timeArgs ++ inArgs ++ explicitMaps ++ metaArgs ++ graphArgs ++ outArgs

/-- Render a typed `MediaPlanIR` back into canonical FFmpeg CLI arguments (round-trip inverse of `parseArgsToPlanIR`). -/
def planIRToCliArgs (plan : MediaPlanIR) : List String :=
  renderPlanIRArgv plan false

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
  let mpegJson := String.intercalate "," (plan.mpegOptions.map fun (flag, value) =>
    s!"\{\"flag\":\"{escapeJsonStr flag}\",\"value\":\"{escapeJsonStr value}\"}")
  let p7 := s!"\"mpeg_options\":[{mpegJson}],\"error_count\":{plan.errors.length}}"
  p0 ++ p1a ++ p1b ++ p2 ++ p3 ++ p4 ++ p5a ++ p5b ++ p6a ++ p6b ++ p7

/-- Shell-free `execvp` argv hygiene gate: guarantees non-empty token list with zero empty `""` tokens or embedded NUL bytes. -/
def verifyExecArgvHygiene (argv : List String) : Bool :=
  !argv.isEmpty && argv.all (fun tok => !tok.isEmpty && !(tok.contains '\x00'))

/-- Check whether a muxer format uses FFmpeg's `AVFMT_NOFILE` contract (skips `assert_file_overwrite` unless `image2` without `%`). -/
def isNoFileOutputFormat (fmt : String) (outPath : String) : Bool :=
  fmt == "null" || fmt == "hls" || fmt == "dash" || fmt == "segment" ||
  fmt == "stream_segment" || fmt == "ssegment" ||
  (fmt == "image2" && outPath.toList.contains '%')

/-- Build the structured `Array String` argv for `delegated_faithful` FFmpeg execution (zero shell interpolation), gated by `verifyExecArgvHygiene`. -/
def buildDelegatedFfmpegArgv (plan : MediaPlanIR) (passthroughArgs : List String := []) : Array String :=
  if plan.outputs.isEmpty then #[]
  else
    let rawList : List String :=
      if passthroughArgs.isEmpty then
        renderPlanIRArgv plan true
      else
        let hasYorN := passthroughArgs.contains "-y" || passthroughArgs.contains "-n"
        let hasLogLevel := passthroughArgs.contains "-v" || passthroughArgs.contains "-loglevel"
        let hasNostdin := passthroughArgs.contains "-nostdin"
        let allNoFile := !plan.outputs.isEmpty && plan.outputs.all (fun o => isNoFileOutputFormat o.format o.path)
        let pre : List String :=
          (if hasNostdin then [] else ["-nostdin"]) ++
          (if hasYorN then [] else
            match plan.outputs.head? with
            | some o =>
              if o.overwrite then ["-y"]
              else if allNoFile then []
              else ["-n"]
            | none   => []) ++
          (if plan.resources.jsonOutput && !passthroughArgs.contains "-hide_banner" then ["-hide_banner"] else []) ++
          (if plan.resources.jsonOutput && !passthroughArgs.contains "-nostats" then ["-nostats"] else []) ++
          (if plan.resources.jsonOutput && !hasLogLevel then ["-v", "error"] else [])
        pre ++ passthroughArgs
    if verifyExecArgvHygiene rawList then rawList.toArray else #[]

/-! ## 4. Phase 5 Targeted C-ABI FFI Facade & Cancellation Contract (Direct Lean 4 `@[export]` + Borrowed C-ABI Shim) -/

/-- Pure specification of the Phase 5 cancellation & frame budget gate. -/
def specFfiCancelGate (cancelFlag framesDone maxFrames : UInt32) : Bool :=
  cancelFlag == 0 && (maxFrames == 0 || framesDone < maxFrames)

/-- Pinned Phase 5 ABI version (`0x00010005`), exported from Lean 4 to the C-ABI shim. -/
@[export leanav_lean_ffi_abi_version]
def ffiAbiVersionExport (_ : Unit) : UInt32 :=
  0x00010005

/-- Cooperative/preemptive cancellation & frame-budget gate, exported from Lean 4 to the C-ABI shim. -/
@[export leanav_lean_ffi_cancel_gate]
def ffiCancelGateExport (cancelFlag framesDone maxFrames : UInt32) : UInt32 :=
  if specFfiCancelGate cancelFlag framesDone maxFrames then 1 else 0

/-- Pinned Phase 5 C-ABI version (`0x00010005`). -/
@[extern "leanav_c_ffi_abi_version"]
opaque ffiAbiVersionC : Unit → UInt32

/-- Sequential-consistency atomic cancellation & frame-budget gate in C-ABI. -/
@[extern "leanav_c_ffi_cancel_gate"]
opaque ffiCancelGateC : UInt32 → UInt32 → UInt32 → UInt32

/-- Read a big-endian 32-bit unsigned integer from `ba` at byte offset `pos`. -/
def rdMp4U32Be (ba : ByteArray) (pos : Nat) : Nat :=
  if pos + 4 <= ba.size then
    (ba[pos]!.toNat <<< 24) ||| (ba[pos + 1]!.toNat <<< 16) |||
    (ba[pos + 2]!.toNat <<< 8) ||| ba[pos + 3]!.toNat
  else 0

/-- Bounded recursive MP4 child box scanner in pure Lean 4 (`moov`/`trak`/`mdia`/`minf`/`stbl`/`tkhd`/`mdhd`). -/
def scanMp4ChildrenPure (ba : ByteArray) (start len : Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, w, h, ts => (w, h, ts)
  | depth + 1, wInit, hInit, tsInit =>
    if len < 8 then (wInit, hInit, tsInit)
    else
      let rec loop (fuel : Nat) (pos w h ts : Nat) : Nat × Nat × Nat :=
        match fuel with
        | 0 => (w, h, ts)
        | fuel' + 1 =>
          if pos + 8 > len then (w, h, ts)
          else
            let absPos := start + pos
            let sz32 := rdMp4U32Be ba absPos
            let fcc := rdMp4U32Be ba (absPos + 4)
            let (validHdr, boxLen, hdrLen) :=
              if sz32 == 1 then
                if pos + 16 > len then (false, 0, 16)
                else
                  let sz64 := (rdMp4U32Be ba (absPos + 8) <<< 32) ||| rdMp4U32Be ba (absPos + 12)
                  if sz64 < 16 || sz64 > len - pos then (false, 0, 16)
                  else (true, sz64, 16)
              else if sz32 == 0 then
                (true, len - pos, 8)
              else if sz32 < 8 || sz32 > len - pos then
                (false, 0, 8)
              else
                (true, sz32, 8)
            if !validHdr then (w, h, ts)
            else
              let bodyStart := absPos + hdrLen
              let bodyLen := boxLen - hdrLen
              let (w', h', ts') :=
                if fcc == 0x6D6F6F76 || fcc == 0x7472616B || fcc == 0x6D646961 ||
                   fcc == 0x6D696E66 || fcc == 0x7374626C then
                  scanMp4ChildrenPure ba bodyStart bodyLen depth w h ts
                else if fcc == 0x746B6864 && bodyLen >= 84 then
                  let ver := if bodyStart < ba.size then ba[bodyStart]!.toNat else 0
                  let wOff := if ver == 1 && bodyLen >= 96 then 88 else 76
                  if wOff + 8 <= bodyLen then
                    let w16 := rdMp4U32Be ba (bodyStart + wOff) >>> 16
                    let h16 := rdMp4U32Be ba (bodyStart + wOff + 4) >>> 16
                    if w == 0 && w16 > 0 && h16 > 0 then (w16, h16, ts) else (w, h, ts)
                  else (w, h, ts)
                else if fcc == 0x6D646864 && bodyLen >= 20 then
                  let ver := if bodyStart < ba.size then ba[bodyStart]!.toNat else 0
                  let tsOff := if ver == 1 && bodyLen >= 24 then 20 else 12
                  if tsOff + 4 <= bodyLen then
                    let tsVal := rdMp4U32Be ba (bodyStart + tsOff)
                    if ts == 0 && tsVal > 0 then (w, h, tsVal) else (w, h, ts)
                  else (w, h, ts)
                else (w, h, ts)
              loop fuel' (pos + boxLen) w' h' ts'
      loop 128 0 wInit hInit tsInit

/-- Pure Lean 4 bounded MP4 header contract probe over `ByteArray` (zero C pointer arithmetic). -/
def ffiProbeMp4ContractPure (ba : ByteArray) (maxRead : Nat) : UInt64 :=
  if maxRead < 32 || ba.size < 32 then 0
  else
    let actualSize := ba.size
    let cap := Nat.min actualSize maxRead
    let rec topLoop (fuel : Nat) (pos : Nat) (sawFtyp sawMoov : Bool) (w h ts : Nat) : Bool × Bool × Nat × Nat × Nat :=
      match fuel with
      | 0 => (sawFtyp, sawMoov, w, h, ts)
      | fuel' + 1 =>
        if pos + 8 > cap then (sawFtyp, sawMoov, w, h, ts)
        else
          let sz32 := rdMp4U32Be ba pos
          let fcc := rdMp4U32Be ba (pos + 4)
          if sz32 == 1 then
            if pos + 16 > cap then (false, false, 0, 0, 0)
            else
              let sz64 := (rdMp4U32Be ba (pos + 8) <<< 32) ||| rdMp4U32Be ba (pos + 12)
              if sz64 < 16 || sz64 > cap - pos then (false, false, 0, 0, 0)
              else
                let sawFtyp' := sawFtyp || fcc == 0x66747970
                let (sawMoov', w', h', ts') :=
                  if fcc == 0x6D6F6F76 then
                    let (w1, h1, ts1) := scanMp4ChildrenPure ba (pos + 16) (sz64 - 16) 6 w h ts
                    (true, w1, h1, ts1)
                  else (sawMoov, w, h, ts)
                topLoop fuel' (pos + sz64) sawFtyp' sawMoov' w' h' ts'
          else if sz32 < 8 then
            (false, false, 0, 0, 0)
          else if sz32 > cap - pos then
            if fcc == 0x6D646174 && sawFtyp && sawMoov && sz32 <= actualSize - pos then
              (sawFtyp, sawMoov, w, h, ts)
            else
              (false, false, 0, 0, 0)
          else
            let sawFtyp' := sawFtyp || fcc == 0x66747970
            let (sawMoov', w', h', ts') :=
              if fcc == 0x6D6F6F76 then
                let (w1, h1, ts1) := scanMp4ChildrenPure ba (pos + 8) (sz32 - 8) 6 w h ts
                (true, w1, h1, ts1)
              else (sawMoov, w, h, ts)
            topLoop fuel' (pos + sz32) sawFtyp' sawMoov' w' h' ts'
    let (sawFtyp, sawMoov, width, height, timescale) := topLoop 64 0 false false 0 0 0
    if !sawFtyp || !sawMoov || width == 0 || height == 0 || width > 65535 || height > 65535 then 0
    else
      let ts16 := if timescale > 0 && timescale <= 65535 then timescale else 15360
      ((1 : UInt64) <<< 63) ||| (width.toUInt64 <<< 32) ||| (height.toUInt64 <<< 16) ||| ts16.toUInt64

/-- Pure Lean 4 MP4 header probe exported to the C-ABI shim (`leanav_c_ffi_probe_mp4_contract` preserves borrowed `@& ByteArray` ownership via `lean_inc`). -/
@[export leanav_lean_ffi_probe_mp4_contract]
def ffiProbeMp4ContractExport (ba : ByteArray) (maxReadBytes : USize) : UInt64 :=
  ffiProbeMp4ContractPure ba maxReadBytes.toNat

/-- Bounded, zero-allocation C-ABI MP4 header probe over borrowed `@& ByteArray`. -/
@[extern "leanav_c_ffi_probe_mp4_contract"]
opaque ffiProbeMp4ContractC : (@& ByteArray) → USize → UInt64

/-- Structured-argv `fork` + `execvp` delegated FFmpeg runner in C-ABI (zero shell interpolation). -/
@[extern "leanav_c_exec_delegated_ffmpeg"]
opaque ffiExecDelegatedFfmpegC : (@& Array String) → (@& String) → UInt32 → BaseIO UInt32

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

/--
  Phase 6 Kernel 4: Verified Matroska / WebM EBML `SimpleBlock` Demuxer (`demuxMatroskaIndependentOrFallback`).
  Executes `demuxMatroskaSimpleBlockSpec` and verifies non-zero track number and non-empty payload,
  or falls back explicitly if the EBML header/VINT/SimpleBlock is malformed.
-/
def demuxMatroskaIndependentOrFallback (bytes : List UInt8) : KernelExecutionResult MkvSimpleBlock :=
  match demuxMatroskaSimpleBlockSpec bytes with
  | some blk =>
    if blk.trackNum > 0 && !blk.payload.isEmpty then
      .independentVerified blk
    else
      .fallbackDelegated "matroska_empty_payload_or_zero_track"
  | none =>
    .fallbackDelegated "invalid_or_truncated_ebml_matroska_block"

/-- Check that every 188-byte packet boundary in `s` (`0, 188, ..., s.len - 188`) starts with the `0x47` MPEG-TS sync byte. -/
def allMpegTsSyncBytesValid (s : ByteSlice) : Bool :=
  let nPkts := s.len / 188
  (List.range nPkts).all (fun i => s.getByteD (i * 188) 0 == 0x47)

/--
  Phase 6 Kernel 5: Verified MPEG-TS 188-Byte Packet Stream Demuxer (`demuxMpegTsIndependentOrFallback`).
  Verifies 188-byte alignment and `0x47` sync byte at every 188-byte packet boundary before executing
  `demuxMpegTsPackets`, or falls back explicitly.
-/
def demuxMpegTsIndependentOrFallback (s : ByteSlice) : KernelExecutionResult (Array (UInt16 × ByteSlice)) :=
  if s.len < 188 || s.len % 188 != 0 then
    .fallbackDelegated "mpegts_length_not_multiple_of_188"
  else if !allMpegTsSyncBytesValid s then
    .fallbackDelegated "mpegts_missing_sync_byte_or_empty_packets"
  else
    let pkts := demuxMpegTsPackets s
    if pkts.size > 0 then
      .independentVerified pkts
    else
      .fallbackDelegated "mpegts_missing_sync_byte_or_empty_packets"

/-! ## 6. Formal Soundness, Round-Trip & Fallback Theorems (Phases 3, 4, 5 & 6) -/

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/--
  Theorem (Phase 3 / Wave D): `parseStreamMapSpec` and `formatStreamMapSpec` form an exact round-trip
  on valid stream selectors (`0:v:0`, `0:a:0?`, `1:s?`, `0`, `0:1`) and reject malformed selectors (`0:x:0`, `bad`, `0:v:0:1`).
-/
theorem streamMapSpec_parse_format_roundtrip :
    (parseStreamMapSpec "0:v:0").map formatStreamMapSpec = some "0:v:0" ∧
    (parseStreamMapSpec "0:a:0?").map formatStreamMapSpec = some "0:a:0?" ∧
    (parseStreamMapSpec "1:s?").map formatStreamMapSpec = some "1:s?" ∧
    (parseStreamMapSpec "0").map formatStreamMapSpec = some "0" ∧
    (parseStreamMapSpec "0:1").map formatStreamMapSpec = some "0:1" ∧
    parseStreamMapSpec "0:x:0" = none ∧
    parseStreamMapSpec "0:v:0:1" = none ∧
    parseStreamMapSpec "malformed" = none := by
  decide

/--
  Universal Theorem: Every elementary `StreamKind` (`video`, `audio`, `subtitle`, `data`)
  round-trips exactly through `toChar` and `parseStreamKindChar`.
-/
theorem streamKind_roundtrip_universal (k : StreamKind) (h : k ≠ .all) :
    parseStreamKindChar k.toChar = some k := by
  cases k <;> first | rfl | contradiction

/--
  Universal Theorem: Every `SubtitleCodecSpec` round-trips through `toString` and `parseSubtitleCodecSpec`.
-/
theorem subtitleCodec_roundtrip_universal (c : SubtitleCodecSpec) :
    parseSubtitleCodecSpec c.toString = some c := by
  cases c <;> rfl

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
  media paths while rejecting network URLs (`http://`, `rtsp://`), `file:`/`pipe:`/`data:` URI schemes,
  double-slash roots (`//dev/null`), synthetic/device inputs (`/dev/video0`, `lavfi:`),
  and parent directory traversal (`../secret.mp4`).
-/
theorem protocolSecurityPolicy_accepts_local_and_rejects_network_device_traversal :
    isSafeLocalMediaPath "fixtures/input.mp4" = true ∧
    isSafeLocalMediaPath "/tmp/output.mkv" = true ∧
    isSafeLocalMediaPath "http://example.com/stream.m3u8" = false ∧
    isSafeLocalMediaPath "rtsp://10.0.0.1/live" = false ∧
    isSafeLocalMediaPath "file:///etc/passwd" = false ∧
    isSafeLocalMediaPath "pipe:0" = false ∧
    isSafeLocalMediaPath "//dev/null" = false ∧
    isSafeLocalMediaPath "/dev/video0" = false ∧
    isSafeLocalMediaPath "lavfi:testsrc" = false ∧
    isSafeLocalMediaPath "fixtures/../outside.mp4" = false ∧
    isSafeLocalMediaPath "" = false := by
  decide

/--
  Theorem (Phase 3 / Wave D): `parseArgsToPlanIR` and `planIRToCliArgs` satisfy the exact CLI <-> IR
  round-trip law across MP4 stream copy, H.264 transcode with timeline/filter/encoder options,
  and Phase 4 delegated Matroska remux with `-map`, `-metadata`, `-bsf:v`, and `-c:s`,
  and `formatCliSeconds` preserves leading fractional zeros (`50/10000` -> `"0.005"`, `10005/10000` -> `"1.0005"`).
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
    formatCliSeconds { num := 50, den := 10000 } = "0.005" ∧
    formatCliSeconds { num := 10005, den := 10000 } = "1.0005" ∧
    pCopy.backend.tier = .delegatedFaithful ∧
    pTrans.backend.tier = .translatedPartial ∧
    pPhase4.backend.tier = .delegatedFaithful ∧
    pPhase4.backend.delegatedContainer = true := by
  decide

/--
  Universal Theorem: `validatePlanIR` succeeds with `.ok plan'` if and only if `plan' = plan`,
  `plan.errors.isEmpty = true`, and `plan.backend.tier ≠ .unsupported`.
-/
theorem validatePlanIR_sound_universal (plan plan' : MediaPlanIR)
    (h : validatePlanIR plan = .ok plan') :
    plan' = plan ∧ plan.errors.isEmpty = true ∧ plan.backend.tier ≠ .unsupported := by
  unfold validatePlanIR at h
  split at h
  · contradiction
  · injection h with hEq
    rename_i hCond
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne] at hCond
    exact ⟨hEq.symm, hCond.1, hCond.2⟩

/--
  Theorem (Phase 3 & Phase 4 Validation Gate): `validatePlanIR` accepts valid `delegatedFaithful`,
  `translatedPartial`, and mixed `-vf scale=... -c:v h264 -c:a copy` plans, and rejects plans with
  same-stream `copyWithFilter`, invalid `-map`, disallowed `http://` URLs, or `-ss` millisecond overflow.
-/
theorem validatePlanIR_sound_and_rejects_unsafe :
    let mixedArgs :=
      ["-y", "-i", "in.mp4", "-vf", "scale=160:90", "-c:v", "h264", "-c:a", "copy", "out.mp4"]
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-c", "copy", "out.mp4"])).isOk = true ∧
    (validatePlanIR (parseArgsToPlanIR mixedArgs)).isOk = true ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-c", "copy", "-vf", "hflip", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "in.mp4", "-map", "bad_map", "-c", "copy", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-i", "http://evil.example/in.mp4", "-c", "copy", "out.mp4"])).isOk = false ∧
    (validatePlanIR (parseArgsToPlanIR ["-y", "-ss", "4294968", "-i", "in.mp4", "-c", "copy", "out.mp4"])).isOk = false := by
  decide

/--
  Universal Theorem: `specFfiCancelGate` returns `true` iff `cancelFlag = 0` and `(maxFrames = 0 ∨ framesDone < maxFrames)`.
-/
theorem specFfiCancelGate_iff_universal (c f m : UInt32) :
    specFfiCancelGate c f m = true ↔ (c = 0 ∧ (m = 0 ∨ f < m)) := by
  simp [specFfiCancelGate]

/--
  Universal Theorem: `rescalePtsIndependentOrFallback` deterministically falls back on any negative timestamp `Int.negSucc n`.
-/
theorem rescalePtsIndependentOrFallback_negative_universal (n sn sd dn dd : Nat) :
    rescalePtsIndependentOrFallback (Int.negSucc n) sn sd dn dd =
      .fallbackDelegated "negative_pts_requires_signed_timeline_shift" := by
  unfold rescalePtsIndependentOrFallback
  simp [Int.negSucc_lt_zero]

/--
  Theorem (Phase 5 & Phase 6): `specFfiCancelGate` enforces cancellation and frame budgets,
  `rescalePtsIndependentOrFallback` executes the exact rational rescaler in-domain (`90000` at `1/90000 -> 1/1000` = `1000`)
  while deterministically returning `.fallbackDelegated` on negative timestamps or zero denominators,
  and `demuxMatroskaIndependentOrFallback` round-trips a valid Matroska/WebM `SimpleBlock` into `.independentVerified`
  while returning `.fallbackDelegated` on empty/malformed inputs.
-/
theorem independentKernel_fallback_complete_and_sound :
    let mkvBlk : MkvSimpleBlock := { trackNum := 1, relTimecodeMs := 33, isKeyframe := true, payload := [0x00, 0x00, 0x01, 0x65] }
    specFfiCancelGate 0 10 25 = true ∧
    specFfiCancelGate 1 10 25 = false ∧
    specFfiCancelGate 0 25 25 = false ∧
    rescalePtsIndependentOrFallback 90000 1 90000 1 1000 = .independentVerified 1000 ∧
    rescalePtsIndependentOrFallback (-1) 1 90000 1 1000 = .fallbackDelegated "negative_pts_requires_signed_timeline_shift" ∧
    rescalePtsIndependentOrFallback 90000 1 0 1 1000 = .fallbackDelegated "zero_rational_component" ∧
    demuxMatroskaIndependentOrFallback (muxMatroskaSimpleBlockSpec mkvBlk) = .independentVerified mkvBlk ∧
    demuxMatroskaIndependentOrFallback [] = .fallbackDelegated "invalid_or_truncated_ebml_matroska_block" := by
  decide

/--
  Universal Theorem: `demuxMpegTsIndependentOrFallback` deterministically falls back on any slice shorter than 188 bytes.
-/
theorem demuxMpegTsIndependentOrFallback_rejects_short_universal (s : ByteSlice)
    (hShort : s.len < 188) :
    demuxMpegTsIndependentOrFallback s = .fallbackDelegated "mpegts_length_not_multiple_of_188" := by
  unfold demuxMpegTsIndependentOrFallback
  have hCond : (s.len < 188 || s.len % 188 != 0) = true := by simp [hShort]
  simp [hCond]

/--
  Universal Theorem: `demuxMpegTsIndependentOrFallback` deterministically falls back whenever any
  188-byte packet boundary in `s` lacks the `0x47` sync byte (`allMpegTsSyncBytesValid s = false`).
-/
theorem demuxMpegTsIndependentOrFallback_rejects_bad_sync_universal (s : ByteSlice)
    (hLen : s.len ≥ 188) (hMod : s.len % 188 = 0) (hBad : allMpegTsSyncBytesValid s = false) :
    demuxMpegTsIndependentOrFallback s = .fallbackDelegated "mpegts_missing_sync_byte_or_empty_packets" := by
  unfold demuxMpegTsIndependentOrFallback
  have hNotLen : (s.len < 188 || s.len % 188 != 0) = false := by
    have h1 : ¬ (s.len < 188) := Nat.not_lt.mpr hLen
    simp [h1, hMod]
  simp [hNotLen, hBad]

/--
  Universal Theorem: If `verifyExecArgvHygiene argv = true`, every token `tok ∈ argv`
  is non-empty (`tok.isEmpty = false`) and free of embedded NUL bytes (`tok.contains '\x00' = false`).
-/
theorem verifyExecArgvHygiene_rejects_empty_and_nul_universal (argv : List String) (tok : String)
    (hMem : tok ∈ argv) (hOk : verifyExecArgvHygiene argv = true) :
    tok.isEmpty = false ∧ tok.contains '\x00' = false := by
  unfold verifyExecArgvHygiene at hOk
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hOk
  exact hOk.2 tok hMem

/--
  Universal Theorem: `ffiProbeMp4ContractPure` rejects any buffer or read budget shorter than 32 bytes.
-/
theorem ffiProbeMp4ContractPure_rejects_short_universal (ba : ByteArray) (maxRead : Nat)
    (hShort : maxRead < 32 ∨ ba.size < 32) :
    ffiProbeMp4ContractPure ba maxRead = 0 := by
  unfold ffiProbeMp4ContractPure
  have hCond : (maxRead < 32 || ba.size < 32) = true := by
    cases hShort with
    | inl h1 => simp [h1]
    | inr h2 => simp [h2]
  simp [hCond]

/--
  Universal Theorem: `isNoFileOutputFormat` rejects regular single-file formats (`mp4`, `image2` without `%`)
  and accepts `AVFMT_NOFILE` formats (`hls`, `dash`, `segment`, `null`, and `%`-templated `image2`).
-/
theorem isNoFileOutputFormat_characterization_universal (fmt outPath : String) :
    isNoFileOutputFormat fmt outPath = true ↔
      ((((((fmt = "null" ∨ fmt = "hls") ∨ fmt = "dash") ∨ fmt = "segment") ∨
          fmt = "stream_segment") ∨ fmt = "ssegment") ∨
       (fmt = "image2" ∧ outPath.toList.contains '%' = true)) := by
  unfold isNoFileOutputFormat
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem isNoFileOutputFormat_non_vacuous :
    isNoFileOutputFormat "hls" "playlist.m3u8" = true ∧
    isNoFileOutputFormat "mp4" "out.mp4" = false ∧
    isNoFileOutputFormat "image2" "frame.png" = false ∧
    isNoFileOutputFormat "image2" "frame-%03d.png" = true := by
  decide

end LeanAV.PlanIR
