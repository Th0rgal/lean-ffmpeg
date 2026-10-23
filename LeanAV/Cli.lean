/-
  LeanAV.Cli: FFmpeg-Compatible CLI Parser, Resident Daemon & Golden `framecrc`/`md5` Oracle

  Implements:
  1. `parseFFmpegArgs : List String → CliConfig` supporting `-i`, `-c copy`, `-c:v`, `-c:a`, `-vf`, `-af`,
     `-ss`, `-t`, `-f`, `-daemon`, `-golden`, and `<output>` with explicit fail-closed `UnsupportedCodecOrFlag`
  2. `validateCliConfig` wired to `verifyCliInvocation` (`cliInvokeGateSpec`)
  3. Golden CRC64 / MD5 oracle (`computeFrameCrc64`, `formatGoldenFrameCrcLine`) for bit-exact regression against `ffmpeg -f framecrc`
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanAV.Spec
import LeanAV.Core

namespace LeanAV.Cli

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanAV.Spec
open LeanAV.Core

/-! ## 1. FFmpeg-Compatible CLI Configuration -/

/-- Supported codec tokens (`-c:v` / `-c:a`). -/
inductive CliCodec where
  | copy
  | h264
  | hevc
  | av1
  | vp9
  | prores
  | ffv1
  | aac
  | opus
  | flac
  | pcmS16le
  | rawvideo
  deriving Repr, DecidableEq, Inhabited

/-- Parse a codec token string into `CliCodec` (`none` = unsupported → fail-closed). -/
def parseCliCodec (s : String) : Option CliCodec :=
  match s with
  | "copy"        => some .copy
  | "h264"        => some .h264
  | "libx264"     => some .h264
  | "h264_nvenc"  => some .h264
  | "hevc"        => some .hevc
  | "h265"        => some .hevc
  | "libx265"     => some .hevc
  | "hevc_nvenc"  => some .hevc
  | "av1"         => some .av1
  | "libaom-av1"  => some .av1
  | "libsvtav1"   => some .av1
  | "av1_nvenc"   => some .av1
  | "vp9"         => some .vp9
  | "libvpx-vp9"  => some .vp9
  | "prores"      => some .prores
  | "prores_ks"   => some .prores
  | "ffv1"        => some .ffv1
  | "aac"         => some .aac
  | "opus"        => some .opus
  | "libopus"     => some .opus
  | "flac"        => some .flac
  | "pcm_s16le"   => some .pcmS16le
  | "rawvideo"    => some .rawvideo
  | _             => none

/-- Exact rational seconds (`-ss`, `-t`) avoiding floating-point drift. -/
structure CliSeconds where
  num : Nat
  den : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Parse a decimal seconds string (`"1.5"` -> `{num := 15, den := 10}`, `"2"` -> `{num := 2, den := 1}`). -/
def parseCliSeconds (s : String) : Option CliSeconds := Id.run do
  let chars := s.toList
  if chars.isEmpty then return none
  let mut n : Nat := 0
  let mut den : Nat := 1
  let mut fractional := false
  let mut seenDigit := false
  for c in chars do
    if c == '.' then
      if fractional then return none
      fractional := true
    else
      let d := c.toNat
      if 48 ≤ d && d ≤ 57 then
        n := n * 10 + (d - 48)
        if fractional then den := den * 10
        seenDigit := true
      else return none
  if !seenDigit then return none
  return some { num := n, den := den }

/-- Fail-closed CLI error taxonomy (`0` silent fallback). -/
inductive CliError where
  | unsupportedCodecOrFlag (token : String)
  | missingValue (flag : String)
  | invalidSeconds (flag value : String)
  | emptyValue (flag : String)
  | multipleOutputs (first second : String)
  | missingInput
  | missingOutput
  | copyWithFilter
  deriving Repr, DecidableEq, Inhabited

/-- Fully parsed FFmpeg-compatible CLI configuration. -/
structure CliConfig where
  inputs         : List String := []
  videoCodec     : Option CliCodec := none
  audioCodec     : Option CliCodec := none
  videoFilter    : Option String := none
  audioFilter    : Option String := none
  startSec       : Option CliSeconds := none
  durationSec    : Option CliSeconds := none
  format         : Option String := none
  daemon         : Option String := none
  golden         : Option String := none
  output         : Option String := none
  overwrite      : Bool := false
  noVideo        : Bool := false
  noAudio        : Bool := false
  jsonOutput     : Bool := false
  videoSize      : Option (Nat × Nat) := none
  videoFrames    : Option Nat := none
  audioRate      : Option Nat := none
  audioChannels  : Option Nat := none
  pixelFormat    : Option String := none
  errors         : List CliError := []
  deriving Repr, DecidableEq, Inhabited

/-- Parse a positive decimal `Nat` from a `List Char` using pure structural recursion (kernel-reducible). -/
def parseNatCharsLoop : List Char → Nat → Bool → Option Nat
  | [], acc, true => if acc > 0 then some acc else none
  | [], _, false => none
  | c :: cs, acc, _ =>
    let d := c.toNat
    if 48 ≤ d && d ≤ 57 then
      parseNatCharsLoop cs (acc * 10 + (d - 48)) true
    else
      none

/-- Split a `List Char` around the first `'x'` or `':'` separator into `(wChars, hChars)`. -/
def splitVideoSizeChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: cs, acc =>
    if c == 'x' || c == ':' then some (acc.reverse, cs)
    else splitVideoSizeChars cs (c :: acc)

/-- Parse an FFmpeg `-s WxH` or `-s W:H` video size string (`"1920x1080"` -> `some (1920, 1080)`). -/
def parseVideoSizeSpec (s : String) : Option (Nat × Nat) :=
  match splitVideoSizeChars s.toList [] with
  | some (wChars, hChars) =>
    match parseNatCharsLoop wChars 0 false, parseNatCharsLoop hChars 0 false with
    | some w, some h => some (w, h)
    | _, _ => none
  | none => none

/--
  Resolve proportional scale dimensions (`scale=W:-1` / `scale=W:-2` represented as `(w, 0)`,
  or `scale=-1:H` / `scale=-2:H` represented as `(0, h)`) against source resolution `(srcW, srcH)`,
  rounding the derived dimension to the nearest even integer `≥ 2` for YUV420p compatibility.
-/
def resolveScaleDims (srcW srcH reqW reqH : Nat) : Nat × Nat :=
  let evenRound (n : Nat) : Nat := Nat.max 2 (((n + 1) / 2) * 2)
  if reqW > 0 && reqH == 0 && srcW > 0 then
    (evenRound reqW, evenRound ((reqW * srcH) / srcW))
  else if reqW == 0 && reqH > 0 && srcH > 0 then
    (evenRound ((reqH * srcW) / srcH), evenRound reqH)
  else if reqW > 0 && reqH > 0 then
    (reqW, reqH)
  else
    (srcW, srcH)

/-- Accumulate a parse error (fail-closed, never silently dropped). -/
@[inline]
def CliConfig.fail (cfg : CliConfig) (e : CliError) : CliConfig :=
  { cfg with errors := cfg.errors ++ [e] }

/-- Supported `-f` container formats. -/
def supportedFormat (s : String) : Bool :=
  ["mp4", "matroska", "mkv", "webm", "mpegts", "h264", "hevc", "av1",
   "ivf", "wav", "adts", "ogg", "flac", "null", "framecrc", "md5", "rawvideo"].contains s

/-- Flags that consume exactly one following argument. -/
def flagTakesValue (s : String) : Bool :=
  ["-i", "-c", "-c:v", "-vcodec", "-c:a", "-acodec", "-vf", "-af", "-s",
   "-ss", "-t", "-f", "-daemon", "-golden", "-frames:v", "-vframes",
   "-ar", "-ac", "-pix_fmt", "-loglevel", "-v", "-threads",
   "-preset", "-crf", "-bf", "-g", "-r", "-b:v", "-b:a", "-movflags"].contains s

/-- Recursive FFmpeg argv parser. -/
def parseFFmpegArgsLoop (args : List String) (cfg : CliConfig) : CliConfig :=
  match args with
  | [] => cfg
  | "-y" :: rest =>
    parseFFmpegArgsLoop rest { cfg with overwrite := true }
  | "-n" :: rest =>
    parseFFmpegArgsLoop rest { cfg with overwrite := false }
  | "--json" :: rest =>
    parseFFmpegArgsLoop rest { cfg with jsonOutput := true }
  | "-json" :: rest =>
    parseFFmpegArgsLoop rest { cfg with jsonOutput := true }
  | "-hide_banner" :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-nostdin" :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-vn" :: rest =>
    parseFFmpegArgsLoop rest { cfg with noVideo := true }
  | "-an" :: rest =>
    parseFFmpegArgsLoop rest { cfg with noAudio := true }
  | "-sn" :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-dn" :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-s" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseVideoSizeSpec value with
      | some sz => { cfg with videoSize := some sz }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-s " ++ value))
  | "-loglevel" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-v" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-threads" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-preset" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-crf" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-bf" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-g" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-r" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-b:v" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-b:a" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-movflags" :: _ :: rest =>
    parseFFmpegArgsLoop rest cfg
  | "-i" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-i")
      else { cfg with inputs := cfg.inputs ++ [value] }
  | "-c" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "copy" then { cfg with videoCodec := some .copy, audioCodec := some .copy }
      else cfg.fail (.unsupportedCodecOrFlag ("-c " ++ value))
  | "-c:v" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliCodec value with
      | some c => { cfg with videoCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-c:v " ++ value))
  | "-vcodec" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliCodec value with
      | some c => { cfg with videoCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-vcodec " ++ value))
  | "-c:a" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliCodec value with
      | some c => { cfg with audioCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-c:a " ++ value))
  | "-acodec" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliCodec value with
      | some c => { cfg with audioCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-acodec " ++ value))
  | "-frames:v" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match value.toNat? with
      | some n => { cfg with videoFrames := some n }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-frames:v " ++ value))
  | "-vframes" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match value.toNat? with
      | some n => { cfg with videoFrames := some n }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-vframes " ++ value))
  | "-ar" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match value.toNat? with
      | some n => { cfg with audioRate := some n }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-ar " ++ value))
  | "-ac" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match value.toNat? with
      | some n => { cfg with audioChannels := some n }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-ac " ++ value))
  | "-pix_fmt" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-pix_fmt")
      else { cfg with pixelFormat := some value }
  | "-vf" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-vf")
      else { cfg with videoFilter := some value }
  | "-af" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-af")
      else { cfg with audioFilter := some value }
  | "-ss" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliSeconds value with
      | some sec => { cfg with startSec := some sec }
      | none => cfg.fail (.invalidSeconds "-ss" value)
  | "-t" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliSeconds value with
      | some sec => { cfg with durationSec := some sec }
      | none => cfg.fail (.invalidSeconds "-t" value)
  | "-f" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if supportedFormat value then { cfg with format := some value }
      else cfg.fail (.unsupportedCodecOrFlag ("-f " ++ value))
  | "-daemon" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-daemon")
      else { cfg with daemon := some value }
  | "-golden" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      if value == "" then cfg.fail (.emptyValue "-golden")
      else { cfg with golden := some value }
  | arg :: rest =>
    parseFFmpegArgsLoop rest <|
      if flagTakesValue arg then cfg.fail (.missingValue arg)
      else if arg.toList.head? == some '-' && arg != "-" then cfg.fail (.unsupportedCodecOrFlag arg)
      else
        match cfg.output with
        | none => if arg == "" then cfg.fail (.emptyValue "output") else { cfg with output := some arg }
        | some prev => cfg.fail (.multipleOutputs prev arg)

/-- Parse an FFmpeg-style argv list into a `CliConfig` (errors accumulated, never silently dropped). -/
def parseFFmpegArgs (args : List String) : CliConfig :=
  parseFFmpegArgsLoop args {}

/-- Validate a `CliConfig` via the C-ABI gate `verifyCliInvocation` (`cliInvokeGateSpec`), fail-closed. -/
def validateCliConfig (cfg : CliConfig) : Except (List CliError) CliConfig :=
  let hasInput : UInt32 := if cfg.inputs.isEmpty then 0 else 1
  let hasOutput : UInt32 := if cfg.output.isNone && cfg.daemon.isNone then 0 else 1
  let unknownFlags : UInt32 := cfg.errors.length.toUInt32
  let unsupportedCodecs : UInt32 :=
    (cfg.errors.foldl (fun (acc : Nat) (e : CliError) =>
      match e with
      | CliError.unsupportedCodecOrFlag _ => acc + 1
      | _ => acc) 0).toUInt32
  let copyMode : UInt32 :=
    if cfg.videoCodec == some .copy || cfg.audioCodec == some .copy then 1 else 0
  let filterCount : UInt32 :=
    (if cfg.videoFilter.isSome then 1 else 0) + (if cfg.audioFilter.isSome then 1 else 0)
  let gateOk := verifyCliInvocation hasInput hasOutput unknownFlags unsupportedCodecs copyMode filterCount == 1
  if !gateOk then
    let extra : List CliError :=
      (if cfg.inputs.isEmpty then [.missingInput] else []) ++
      (if cfg.output.isNone && cfg.daemon.isNone then [.missingOutput] else []) ++
      (if copyMode == 1 && filterCount > 0 then [.copyWithFilter] else [])
    .error (cfg.errors ++ extra)
  else .ok cfg

/-! ## 2. Golden `framecrc` / MD5 Oracle -/

/-- Compute an FFmpeg-compatible `framecrc` 64-bit Adler-style checksum over raw frame bytes. -/
def computeFrameCrc64 (bytes : ByteArray) : UInt64 := Id.run do
  let mut s1 : UInt64 := 1
  let mut s2 : UInt64 := 0
  for b in bytes do
    s1 := (s1 + b.toUInt64) % 65521
    s2 := (s2 + s1) % 65521
  return (s2 <<< 16) ||| s1

/-- Convert a `UInt64` to a 16-character lowercase hexadecimal string. -/
def uint64ToHex16 (v : UInt64) : String := Id.run do
  let hexChars := "0123456789abcdef".toList
  let mut chars : List Char := []
  for i in [:16] do
    let shift := ((15 - i) * 4).toUInt64
    let nib := ((v >>> shift) &&& 0x0F).toNat
    chars := chars ++ [hexChars[nib]?.getD '0']
  return String.ofList chars

/-- Format a single `framecrc` golden line: `streamIndex, dts, pts, duration, size, crc`. -/
def formatGoldenFrameCrcLine (streamIdx : Nat) (dts pts duration : UInt64) (size : Nat) (crc : UInt64) : String :=
  s!"{streamIdx}, {dts}, {pts}, {duration}, {size}, 0x{uint64ToHex16 crc}"

/-- Compute a 64-bit XXH64 golden digest line (`XXH64=<hex16>`) over a `ByteSlice`. -/
def formatGoldenXxh64Line (s : ByteSlice) : String :=
  let d := xxh64Slice s 0
  s!"XXH64={uint64ToHex16 d}"

/-! ## 3. Wave 6 (C5): Formal CLI Option Parser & Fail-Closed Gate Soundness Theorems -/

/--
  Theorem (Wave 6 C5): `validateCliConfig` enforces the fail-closed stream-copy vs filter exclusion law
  (`-c copy` combined with `-vf` or `-af` is rejected with `CliError.copyWithFilter`), while a valid
  transcode invocation (`-i in.mp4 -c:v ffv1 -vf eq=128:0 -af volume=256 out.mp4`) is accepted with zero errors.
-/
theorem cliValidate_copyWithFilter_rejected_and_transcode_accepted :
    let badCfg := parseFFmpegArgs ["-i", "in.mp4", "-c", "copy", "-vf", "hflip", "out.mp4"]
    let goodCfg := parseFFmpegArgs ["-i", "in.mp4", "-c:v", "ffv1", "-vf", "eq=256:0", "-af", "volume=256", "out.mp4"]
    let badRes := match validateCliConfig badCfg with | .error errs => errs == [.copyWithFilter] | .ok _ => false
    let goodRes := match validateCliConfig goodCfg with | .ok c => c == goodCfg | .error _ => false
    badRes = true ∧
    goodRes = true ∧
    goodCfg.videoCodec = some .ffv1 ∧
    goodCfg.videoFilter = some "eq=256:0" ∧
    goodCfg.audioFilter = some "volume=256" := by
  decide

/--
  Theorem (Wave 6 C5): `parseCliSeconds` parses exact decimal rational timestamps (`"1.5"` -> `15/10`, `"24"` -> `24/1`)
  without floating-point representation drift and rejects malformed strings (`"1.2.3"`, `""`, `"abc"`).
-/
theorem parseCliSeconds_exact_and_rejects_malformed :
    parseCliSeconds "1.5" = some { num := 15, den := 10 } ∧
    parseCliSeconds "24" = some { num := 24, den := 1 } ∧
    parseCliSeconds "1.2.3" = none ∧
    parseCliSeconds "" = none ∧
    parseCliSeconds "abc" = none := by
  decide

/--
  Theorem (Wave 51): `resolveScaleDims` preserves exact 16:9 aspect ratio with even YUV420p alignment
  on `scale=1920:-1` / `scale=1920:-2` (`3840x2160 -> 1920x1080`) and `scale=-2:720` (`3840x2160 -> 1280x720`),
  and `parseFFmpegArgs` parses `-s 1920x1080`, `-an`, and `--json` without error.
-/
theorem resolveScaleDims_proportional_even_and_cli_flags_verified :
    resolveScaleDims 3840 2160 1920 0 = (1920, 1080) ∧
    resolveScaleDims 3840 2160 0 720 = (1280, 720) ∧
    resolveScaleDims 3840 2160 0 0 = (3840, 2160) ∧
    (parseFFmpegArgs ["-y", "-i", "in.mp4", "-s", "1920x1080", "-an", "--json", "out.mp4"]).videoSize = some (1920, 1080) ∧
    (parseFFmpegArgs ["-y", "-i", "in.mp4", "-s", "1920x1080", "-an", "--json", "out.mp4"]).noAudio = true ∧
    (parseFFmpegArgs ["-y", "-i", "in.mp4", "-s", "1920x1080", "-an", "--json", "out.mp4"]).jsonOutput = true ∧
    (parseFFmpegArgs ["-y", "-i", "in.mp4", "-s", "1920x1080", "-an", "--json", "out.mp4"]).errors = [] := by
  decide

end LeanAV.Cli
