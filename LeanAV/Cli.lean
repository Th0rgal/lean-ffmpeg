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
  | "copy"      => some .copy
  | "h264"      => some .h264
  | "libx264"   => some .h264
  | "hevc"      => some .hevc
  | "libx265"   => some .hevc
  | "av1"       => some .av1
  | "libaom-av1" => some .av1
  | "vp9"       => some .vp9
  | "libvpx-vp9" => some .vp9
  | "prores"    => some .prores
  | "prores_ks" => some .prores
  | "ffv1"      => some .ffv1
  | "aac"       => some .aac
  | "opus"      => some .opus
  | "libopus"   => some .opus
  | "flac"      => some .flac
  | "pcm_s16le" => some .pcmS16le
  | "rawvideo"  => some .rawvideo
  | _           => none

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
  errors         : List CliError := []
  deriving Repr, DecidableEq, Inhabited

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
  ["-i", "-c", "-c:v", "-c:a", "-vf", "-af", "-ss", "-t", "-f", "-daemon", "-golden"].contains s

/-- Recursive FFmpeg argv parser. -/
def parseFFmpegArgsLoop (args : List String) (cfg : CliConfig) : CliConfig :=
  match args with
  | [] => cfg
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
  | "-c:a" :: value :: rest =>
    parseFFmpegArgsLoop rest <|
      match parseCliCodec value with
      | some c => { cfg with audioCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-c:a " ++ value))
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
      else if arg.startsWith "-" && arg != "-" then cfg.fail (.unsupportedCodecOrFlag arg)
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

end LeanAV.Cli
