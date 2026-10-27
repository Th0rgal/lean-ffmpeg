/-
  LeanAV.Cli: FFmpeg-Flavoured CLI Parser, Resident Daemon & Golden Digest Oracle

  Implements:
  1. `parseFFmpegArgs : List String → CliConfig` supporting `-i`, `-c copy`, `-c:v`, `-c:a`, `-vf`, `-af`,
     `-ss`, `-t`, `-f`, `-daemon`, `-golden`, and `<output>` with explicit fail-closed `UnsupportedCodecOrFlag`
  2. `validateCliConfig` wired to `verifyCliInvocation` (`cliInvokeGateSpec`)
  3. Internal Adler-style 64-bit digest oracle (`computeFrameCrc64`, `formatGoldenFrameCrcLine`) for project regression checks
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

/-- Supported CLI video/audio codec selectors (pure enum for O(1) kernel `DecidableEq`). -/
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
  | vp8
  | mpeg4
  | mpeg2video
  | mpeg1video
  | mjpeg
  | png
  | gif
  | mp2
  | mp3
  | vorbis
  | alac
  | ac3
  | eac3
  | dts
  | otherDelegated
  deriving Repr, DecidableEq, Inhabited

/-- Recognise standard FFmpeg video/audio codec names for delegated execution. -/
def isOtherFFmpegCodecName (s : String) : Bool :=
  let cs := s.toList
  let isPcm := ['p', 'c', 'm', '_'].isPrefixOf cs && cs.length > 4
  let isAdpcm := ['a', 'd', 'p', 'c', 'm', '_'].isPrefixOf cs && cs.length > 6
  isPcm || isAdpcm ||
  ["ljpeg", "jpegls", "apng", "bmp", "pam", "pbm", "pgm", "pgmyuv", "ppm", "pnm", "targa", "tiff",
   "dpx", "sgi", "sunrast", "pcx", "qoi", "webp", "libwebp", "libwebp_anim", "xbm", "xwd",
   "dnxhd", "dvvideo", "flv", "flv1", "h261", "h263", "h263p", "msmpeg4", "msmpeg4v2", "msmpeg4v1",
   "wmv1", "wmv2", "rv10", "rv20", "svq1", "qtrle", "cinepak", "msvideo1", "cljr",
   "r210", "v210", "v308", "v408", "v410", "y41p", "yuv4", "zlib", "snow", "asv1", "asv2",
   "roqvideo", "amv", "vc2", "vvc", "dirac", "theora", "libtheora", "utvideo", "magicyuv", "cfhd",
   "speedhq", "vnull", "wrapped_avframe", "libx264rgb", "librav1e", "prores_aw", "ffvhuff", "huffyuv",
   "aac_fixed", "libfdk_aac", "mp2fixed", "tta", "wavpack", "wmav1", "wmav2", "truehd", "mlp",
   "real_144", "roq_dpcm", "nellymoser", "speex", "libspeex", "amr_nb", "libopencore_amrnb", "amr_wb",
   "g722", "g723_1", "g726", "g726le", "sbc", "aptx", "aptx_hd", "dfpwm", "sonic", "sonicls", "anull"].contains s

/-- Parse a codec token string into `CliCodec` (`none` = unsupported → fail-closed). -/
def parseCliCodec (s : String) : Option CliCodec :=
  if s == "copy" then some .copy
  else if s == "h264" || s == "libx264" || s == "h264_nvenc" then some .h264
  else if s == "hevc" || s == "h265" || s == "libx265" || s == "hevc_nvenc" then some .hevc
  else if s == "av1" || s == "libaom-av1" || s == "libsvtav1" || s == "av1_nvenc" then some .av1
  else if s == "vp9" || s == "libvpx-vp9" then some .vp9
  else if s == "prores" || s == "prores_ks" then some .prores
  else if s == "ffv1" then some .ffv1
  else if s == "aac" then some .aac
  else if s == "opus" || s == "libopus" then some .opus
  else if s == "flac" then some .flac
  else if s == "pcm_s16le" then some .pcmS16le
  else if s == "rawvideo" then some .rawvideo
  else if s == "vp8" || s == "libvpx" then some .vp8
  else if s == "mpeg4" || s == "libxvid" then some .mpeg4
  else if s == "mpeg2video" then some .mpeg2video
  else if s == "mpeg1video" then some .mpeg1video
  else if s == "mjpeg" then some .mjpeg
  else if s == "png" then some .png
  else if s == "gif" then some .gif
  else if s == "mp2" then some .mp2
  else if s == "mp3" || s == "libmp3lame" then some .mp3
  else if s == "vorbis" || s == "libvorbis" then some .vorbis
  else if s == "alac" then some .alac
  else if s == "ac3" || s == "ac3_fixed" then some .ac3
  else if s == "eac3" then some .eac3
  else if s == "dca" || s == "dts" then some .dts
  else if isOtherFFmpegCodecName s then some .otherDelegated
  else none

/-- Exact rational seconds (`-ss`, `-t`) avoiding floating-point drift. -/
structure CliSeconds where
  num : Nat
  den : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Parse a plain decimal char list (`"1.5"` -> `{num := 15, den := 10}`, `"2"` -> `{num := 2, den := 1}`). -/
def parseDecimalSecondsChars (chars : List Char) : Option CliSeconds := Id.run do
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

/-- Parse a non-negative integer from a non-empty `List Char`. -/
def parseNonNegIntChars (chars : List Char) : Option Nat := Id.run do
  if chars.isEmpty then return none
  let mut acc : Nat := 0
  for c in chars do
    let d := c.toNat
    if 48 ≤ d && d ≤ 57 then
      acc := acc * 10 + (d - 48)
    else return none
  return some acc

/-- Split a `List Char` on `':'` into segments. -/
def splitColonCharsLoop : List Char → List Char → List (List Char)
  | [], cur => [cur.reverse]
  | c :: cs, cur =>
    if c == ':' then cur.reverse :: splitColonCharsLoop cs []
    else splitColonCharsLoop cs (c :: cur)

/--
  Parse an FFmpeg timestamp/duration string (`"1.5"`, `"2"`, `"00:00:00.5"`, `"01:30"`,
  `"500ms"`, `"250000us"`, `"2.5s"`) into exact rational `CliSeconds`.
-/
def parseCliSeconds (s : String) : Option CliSeconds :=
  let chars := s.toList
  if chars.isEmpty then none
  else
    match chars.reverse with
    | 's' :: 'm' :: revBase =>
      match parseDecimalSecondsChars revBase.reverse with
      | some r => some { num := r.num, den := r.den * 1000 }
      | none   => none
    | 's' :: 'u' :: revBase =>
      match parseDecimalSecondsChars revBase.reverse with
      | some r => some { num := r.num, den := r.den * 1000000 }
      | none   => none
    | 's' :: revBase =>
      parseDecimalSecondsChars revBase.reverse
    | _ =>
      match splitColonCharsLoop chars [] with
      | [only] => parseDecimalSecondsChars only
      | [mmChars, ssChars] =>
        match parseNonNegIntChars mmChars, parseDecimalSecondsChars ssChars with
        | some mm, some sec =>
          if sec.num < 60 * sec.den then
            some { num := mm * 60 * sec.den + sec.num, den := sec.den }
          else none
        | _, _ => none
      | [hhChars, mmChars, ssChars] =>
        match parseNonNegIntChars hhChars, parseNonNegIntChars mmChars, parseDecimalSecondsChars ssChars with
        | some hh, some mm, some sec =>
          if mm < 60 && sec.num < 60 * sec.den then
            some { num := (hh * 3600 + mm * 60) * sec.den + sec.num, den := sec.den }
          else none
        | _, _, _ => none
      | _ => none

def cliSecondsToMillis (s : CliSeconds) : Option UInt32 :=
  if s.den == 0 then
    none
  else
    let millis := (s.num * 1000) / s.den
    if millis ≤ 4294967295 then some millis.toUInt32 else none

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
  hideBanner     : Bool := false
  showStats      : Bool := true
  logLevel       : String := "info"
  videoSize      : Option (Nat × Nat) := none
  videoFrames    : Option Nat := none
  audioRate      : Option Nat := none
  audioChannels  : Option Nat := none
  pixelFormat    : Option String := none
  preset         : Option String := none
  crf            : Option String := none
  videoBitrate   : Option String := none
  audioBitrate   : Option String := none
  frameRate      : Option String := none
  bFrames        : Option Nat := none
  gopSize        : Option Nat := none
  threads        : Option Nat := none
  movflags       : Option String := none
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

/-- Parse a non-negative decimal `Nat` (`>= 0`) from a `String` using pure structural recursion. -/
def parseNonNegNatLoop : List Char → Nat → Bool → Option Nat
  | [], acc, true => some acc
  | [], _, false => none
  | c :: cs, acc, _ =>
    let d := c.toNat
    if 48 ≤ d && d ≤ 57 then
      parseNonNegNatLoop cs (acc * 10 + (d - 48)) true
    else
      none

def parseNonNegNatSpec (s : String) : Option Nat :=
  parseNonNegNatLoop s.toList 0 false

def parsePosNatSpec (s : String) : Option Nat :=
  parseNatCharsLoop s.toList 0 false

/-- Split a `List Char` around the first `'x'` or `':'` separator into `(wChars, hChars)`. -/
def splitVideoSizeChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: cs, acc =>
    if c == 'x' || c == ':' then some (acc.reverse, cs)
    else splitVideoSizeChars cs (c :: acc)

/-- Parse an FFmpeg `-s WxH`, `-s W:H`, or standard named video size string (`"1920x1080"`, `"pal"`, `"hd720"`, `"sqcif"`). -/
def parseVideoSizeSpec (s : String) : Option (Nat × Nat) :=
  if s == "pal" then some (720, 576)
  else if s == "ntsc" then some (720, 480)
  else if s == "sqcif" then some (128, 96)
  else if s == "qcif" then some (176, 144)
  else if s == "cif" then some (352, 288)
  else if s == "4cif" then some (704, 576)
  else if s == "16cif" then some (1408, 1152)
  else if s == "qqvga" then some (160, 120)
  else if s == "qvga" then some (320, 240)
  else if s == "vga" then some (640, 480)
  else if s == "svga" then some (800, 600)
  else if s == "xga" then some (1024, 768)
  else if s == "uxga" then some (1600, 1200)
  else if s == "qxga" then some (2048, 1536)
  else if s == "sxga" then some (1280, 1024)
  else if s == "hd480" then some (852, 480)
  else if s == "hd720" then some (1280, 720)
  else if s == "hd1080" then some (1920, 1080)
  else if s == "2k" then some (2048, 1080)
  else if s == "4k" || s == "uhd2160" then some (3840, 2160)
  else if s == "uhd4320" then some (7680, 4320)
  else
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
  ["mp4", "matroska", "mkv", "webm", "mov", "wav", "flac", "ogg", "mpegts", "ts", "ivf",
   "null", "framecrc", "framemd5", "md5", "crc", "rawvideo", "s16le", "image2", "lavfi",
   "m4v", "3gp", "3g2", "ipod", "m4a", "f4v", "ismv", "psp", "mka", "mks",
   "m2ts", "mts", "mpeg", "mpg", "vob", "svcd", "dvd", "mpeg1video", "mpeg2video", "m2v",
   "avi", "asf", "wmv", "wma", "flv", "swf", "rm", "nut", "gxf", "mxf", "mxf_d10", "mxf_opatom",
   "wtv", "dv", "roq", "smjpeg", "wc3movie", "film_cpk", "segafilm",
   "w64", "rf64", "aiff", "aif", "au", "caf", "voc", "sox", "ircam", "avr", "ast", "oma",
   "ac3", "eac3", "dts", "dtshd", "spdif", "truehd", "mlp", "adts", "aac", "latm", "mp2", "mp3",
   "oga", "ogv", "opus", "spx", "tta", "wv", "ape", "amr", "g722", "g723_1", "g726", "g726le",
   "sbc", "dfpwm", "rso", "mmf", "aea", "ilbc", "adx", "flm",
   "s16be", "s24le", "s24be", "s32le", "s32be", "s8", "u8",
   "u16le", "u16be", "u24le", "u24be", "u32le", "u32be", "f32le", "f32be", "f64le", "f64be", "alaw", "mulaw", "vidc",
   "h264", "hevc", "vvc", "av1", "mjpeg", "dnxhd", "h261", "h263", "yuv4mpegpipe", "y4m",
   "image2pipe", "apng", "gif", "webp",
   "srt", "subrip", "webvtt", "vtt", "ass", "ssa", "jacosub", "microdvd", "mpl2", "pjs",
   "realtext", "sami", "scc", "stl", "subviewer", "ttml", "vplayer", "lrc",
   "ffmetadata", "hash", "framehash", "streamhash",
   "tee", "fifo", "segment", "stream_segment", "hls", "dash"].contains s

/-- Supported `-preset` encoder tokens. -/
def supportedPreset (s : String) : Bool :=
  ["ultrafast", "superfast", "veryfast", "faster", "fast", "medium",
   "slow", "slower", "veryslow", "placebo", "default", "hq", "ll", "llhq", "llhp",
   "p1", "p2", "p3", "p4", "p5", "p6", "p7",
   "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13"].contains s

/-- Pixel formats natively handled by the in-process MP4 SIMD pipeline. -/
def nativeMp4PixFmt (s : String) : Bool :=
  s == "yuv420p" || s == "yuv420p10le" || s == "p010le"

/-- Supported `-pix_fmt` tokens across native and delegated execution. -/
def supportedPixFmt (s : String) : Bool :=
  nativeMp4PixFmt s ||
  ["nv12", "yuv422p", "yuv444p", "yuv410p", "yuv411p", "yuv440p",
   "yuvj420p", "yuvj422p", "yuvj444p", "yuvj411p", "yuvj440p",
   "yuva420p", "yuva422p", "yuva444p",
   "yuv420p9le", "yuv420p9be", "yuv422p9le", "yuv422p9be", "yuv444p9le", "yuv444p9be",
   "yuv420p10be", "yuv422p10", "yuv422p10le", "yuv422p10be", "yuv444p10le", "yuv444p10be",
   "yuv420p12le", "yuv420p12be", "yuv422p12le", "yuv422p12be", "yuv444p12le", "yuv444p12be",
   "yuv420p14le", "yuv420p14be", "yuv422p14le", "yuv422p14be", "yuv444p14le", "yuv444p14be",
   "yuv420p16le", "yuv420p16be", "yuv422p16le", "yuv422p16be", "yuv444p16le", "yuv444p16be",
   "nv21", "nv16", "nv24", "nv42", "p010be", "p016le", "p016be",
   "p410le", "p410be", "p412le", "p412be", "p416le", "p416be",
   "gray", "gray8", "ya8", "gray9le", "gray9be", "gray10le", "gray10be",
   "gray12le", "gray12be", "gray14le", "gray14be", "gray16le", "gray16be", "ya16le", "ya16be",
   "monow", "monob", "pal8",
   "rgb24", "bgr24", "argb", "rgba", "abgr", "bgra", "0rgb", "rgb0", "0bgr", "bgr0",
   "rgb32", "bgr32", "rgb565", "bgr565", "rgb555", "bgr555", "rgb444", "bgr444",
   "rgb48le", "rgb48be", "bgr48le", "bgr48be", "rgba64le", "rgba64be", "bgra64le", "bgra64be",
   "rgb565le", "rgb565be", "rgb555le", "rgb555be", "rgb444le", "rgb444be",
   "bgr565le", "bgr565be", "bgr555le", "bgr555be", "bgr444le", "bgr444be",
   "rgb8", "bgr8", "rgb4_byte", "bgr4_byte", "rgb4", "bgr4",
   "uyvy422", "yuyv422", "yvyu422", "uyyv411",
   "gbrp", "gbrp9le", "gbrp9be", "gbrp10le", "gbrp10be", "gbrp12le", "gbrp12be",
   "gbrp14le", "gbrp14be", "gbrp16le", "gbrp16be",
   "gbrap", "gbrap10le", "gbrap10be", "gbrap12le", "gbrap12be", "gbrap16le", "gbrap16be",
   "xyz12le", "xyz12be", "ayuv64le", "ayuv64be"].contains s

/-- Supported `-loglevel` / `-v` tokens. -/
def supportedLogLevel (s : String) : Bool :=
  ["quiet", "panic", "fatal", "error", "warning", "info", "verbose", "debug", "trace",
   "-8", "0", "8", "16", "24", "32", "40", "48", "56"].contains s

/-- Check if a string is a valid non-negative integer or decimal (`"23"`, `"22.6"`, up to `63` for VP9/AV1). -/
def isValidCrfSpec (s : String) : Bool :=
  match parseCliSeconds s with
  | some sec => sec.den > 0 && sec.num <= 63 * sec.den
  | none => false

/-- Check if a string is a valid bitrate token (`"4M"`, `"4500k"`, `"192k"`, `"5000000"`). -/
def isValidBitrateSpec (s : String) : Bool :=
  let chars := s.toList
  match chars.reverse with
  | [] => false
  | last :: revInit =>
    if last == 'k' || last == 'K' || last == 'm' || last == 'M' then
      (parseNatCharsLoop revInit.reverse 0 false).isSome
    else
      (parseNatCharsLoop chars 0 false).isSome

/-- Split a `List Char` around the first `'/'` separator into `(numChars, denChars)`. -/
def splitSlashChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: cs, acc =>
    if c == '/' then some (acc.reverse, cs)
    else splitSlashChars cs (c :: acc)

/-- Check if a string is a valid frame rate (`"24"`, `"23.976"`, `"24000/1001"`, `"60/1"`). -/
def isValidFrameRateSpec (s : String) : Bool :=
  match splitSlashChars s.toList [] with
  | some (numChars, denChars) =>
    match parseNatCharsLoop numChars 0 false, parseNatCharsLoop denChars 0 false with
    | some n, some d => n > 0 && d > 0
    | _, _ => false
  | none =>
    match parseCliSeconds s with
    | some sec => sec.num > 0 && sec.den > 0
    | none => false

/-- Flags that consume exactly one following argument. -/
def flagTakesValue (s : String) : Bool :=
  ["-i", "-c", "-codec", "-c:v", "-vcodec", "-codec:v", "-c:a", "-acodec", "-codec:a",
   "-vf", "-filter:v", "-af", "-filter:a", "-s", "-video_size",
   "-ss", "-t", "-f", "-daemon", "-golden", "-frames:v", "-vframes", "-frames",
   "-ar", "-ac", "-pix_fmt", "-pixel_format", "-loglevel", "-v", "-threads",
   "-preset", "-crf", "-bf", "-g", "-r", "-framerate", "-b:v", "-vb", "-b", "-b:a", "-ab", "-movflags"].contains s

/-- Apply a 1-value CLI flag `(flag, value)` to `CliConfig`. -/
def applyCliFlagValue (flag value : String) (cfg : CliConfig) : CliConfig :=
  if flag == "-i" then
    if value == "" then cfg.fail (.emptyValue "-i")
    else { cfg with inputs := cfg.inputs ++ [value] }
  else if flag == "-c" || flag == "-codec" then
    if value == "copy" then { cfg with videoCodec := some .copy, audioCodec := some .copy }
    else
      match parseCliCodec value with
      | some c => { cfg with videoCodec := some c }
      | none => cfg.fail (.unsupportedCodecOrFlag ("-c " ++ value))
  else if flag == "-c:v" || flag == "-vcodec" || flag == "-codec:v" then
    match parseCliCodec value with
    | some c => { cfg with videoCodec := some c }
    | none => cfg.fail (.unsupportedCodecOrFlag (flag ++ " " ++ value))
  else if flag == "-c:a" || flag == "-acodec" || flag == "-codec:a" then
    match parseCliCodec value with
    | some c => { cfg with audioCodec := some c }
    | none => cfg.fail (.unsupportedCodecOrFlag (flag ++ " " ++ value))
  else if flag == "-vf" || flag == "-filter:v" then
    if value == "" then cfg.fail (.emptyValue "-vf")
    else { cfg with videoFilter := some value }
  else if flag == "-af" || flag == "-filter:a" then
    if value == "" then cfg.fail (.emptyValue "-af")
    else { cfg with audioFilter := some value }
  else if flag == "-s" || flag == "-video_size" then
    match parseVideoSizeSpec value with
    | some sz => { cfg with videoSize := some sz }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-s " ++ value))
  else if flag == "-ss" then
    match parseCliSeconds value with
    | some sec => { cfg with startSec := some sec }
    | none => cfg.fail (.invalidSeconds "-ss" value)
  else if flag == "-t" then
    match parseCliSeconds value with
    | some sec => { cfg with durationSec := some sec }
    | none => cfg.fail (.invalidSeconds "-t" value)
  else if flag == "-f" then
    if supportedFormat value then { cfg with format := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-f " ++ value))
  else if flag == "-preset" then
    if supportedPreset value then { cfg with preset := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-preset " ++ value))
  else if flag == "-crf" then
    if isValidCrfSpec value then { cfg with crf := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-crf " ++ value))
  else if flag == "-b:v" || flag == "-vb" || flag == "-b" then
    if isValidBitrateSpec value then { cfg with videoBitrate := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-b:v " ++ value))
  else if flag == "-b:a" || flag == "-ab" then
    if isValidBitrateSpec value then { cfg with audioBitrate := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-b:a " ++ value))
  else if flag == "-r" || flag == "-framerate" then
    if isValidFrameRateSpec value then { cfg with frameRate := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-r " ++ value))
  else if flag == "-pix_fmt" || flag == "-pixel_format" then
    if supportedPixFmt value then { cfg with pixelFormat := some value }
    else cfg.fail (.unsupportedCodecOrFlag ("-pix_fmt " ++ value))
  else if flag == "-loglevel" || flag == "-v" then
    if value == "" then cfg.fail (.emptyValue flag)
    else if supportedLogLevel value then
      let quietLike := ["quiet", "panic", "fatal", "error", "warning", "-8", "0", "8", "16", "24"].contains value
      { cfg with
        logLevel := value
        showStats := if quietLike then false else cfg.showStats
        hideBanner := if quietLike then true else cfg.hideBanner }
    else cfg.fail (.unsupportedCodecOrFlag (flag ++ " " ++ value))
  else if flag == "-threads" then
    match parseNonNegNatSpec value with
    | some n => { cfg with threads := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-threads " ++ value))
  else if flag == "-bf" then
    match parseNonNegNatSpec value with
    | some n => { cfg with bFrames := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-bf " ++ value))
  else if flag == "-g" then
    match parsePosNatSpec value with
    | some n => { cfg with gopSize := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-g " ++ value))
  else if flag == "-frames:v" || flag == "-vframes" || flag == "-frames" then
    match parsePosNatSpec value with
    | some n => { cfg with videoFrames := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag (flag ++ " " ++ value))
  else if flag == "-ar" then
    match parsePosNatSpec value with
    | some n => { cfg with audioRate := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-ar " ++ value))
  else if flag == "-ac" then
    match parsePosNatSpec value with
    | some n => { cfg with audioChannels := some n }
    | none => cfg.fail (.unsupportedCodecOrFlag ("-ac " ++ value))
  else if flag == "-movflags" then
    if value == "" then cfg.fail (.emptyValue "-movflags")
    else { cfg with movflags := some value }
  else if flag == "-daemon" then
    if value == "" then cfg.fail (.emptyValue "-daemon")
    else { cfg with daemon := some value }
  else if flag == "-golden" then
    if value == "" then cfg.fail (.emptyValue "-golden")
    else { cfg with golden := some value }
  else
    cfg.fail (.unsupportedCodecOrFlag flag)

/-- Linear `List.rec` FFmpeg argv parser (avoids `List.brecOn` exponential kernel unfolding). -/
def parseFFmpegArgsStep : List String → Option String → CliConfig → CliConfig
  | [], none, cfg => cfg
  | [], some flag, cfg => cfg.fail (.missingValue flag)
  | value :: rest, some flag, cfg =>
    parseFFmpegArgsStep rest none (applyCliFlagValue flag value cfg)
  | arg :: rest, none, cfg =>
    if arg == "-y" then
      parseFFmpegArgsStep rest none { cfg with overwrite := true }
    else if arg == "-n" then
      parseFFmpegArgsStep rest none { cfg with overwrite := false }
    else if arg == "--json" || arg == "-json" then
      parseFFmpegArgsStep rest none { cfg with jsonOutput := true }
    else if arg == "-hide_banner" then
      parseFFmpegArgsStep rest none { cfg with hideBanner := true }
    else if arg == "-stats" then
      parseFFmpegArgsStep rest none { cfg with showStats := true }
    else if arg == "-nostats" then
      parseFFmpegArgsStep rest none { cfg with showStats := false }
    else if arg == "-nostdin" || arg == "-sn" || arg == "-dn" then
      parseFFmpegArgsStep rest none cfg
    else if arg == "-vn" then
      parseFFmpegArgsStep rest none { cfg with noVideo := true }
    else if arg == "-an" then
      parseFFmpegArgsStep rest none { cfg with noAudio := true }
    else if flagTakesValue arg then
      parseFFmpegArgsStep rest (some arg) cfg
    else if arg.toList.head? == some '-' && arg != "-" then
      parseFFmpegArgsStep rest none (cfg.fail (.unsupportedCodecOrFlag arg))
    else
      let cfg' :=
        match cfg.output with
        | none => if arg == "" then cfg.fail (.emptyValue "output") else { cfg with output := some arg }
        | some prev => cfg.fail (.multipleOutputs prev arg)
      parseFFmpegArgsStep rest none cfg'

/-- Recursive FFmpeg argv parser. -/
def parseFFmpegArgsLoop (args : List String) (cfg : CliConfig) : CliConfig :=
  parseFFmpegArgsStep args none cfg

/-- Parse an FFmpeg-style argv list into a `CliConfig` (errors accumulated, never silently dropped). -/
def parseFFmpegArgs (args : List String) : CliConfig :=
  parseFFmpegArgsLoop args {}

/-- Validate a `CliConfig` via the C-ABI gate `verifyCliInvocation` (`cliInvokeGateSpec`), fail-closed.
    Per-stream filter vs copy check: `-vf` only conflicts with `-c:v copy`, and `-af` only conflicts with `-c:a copy`. -/
def validateCliConfig (cfg : CliConfig) : Except (List CliError) CliConfig :=
  let hasInput : UInt32 := if cfg.inputs.isEmpty then 0 else 1
  let hasOutput : UInt32 := if cfg.output.isNone && cfg.daemon.isNone then 0 else 1
  let unknownFlags : UInt32 := cfg.errors.length.toUInt32
  let unsupportedCodecs : UInt32 :=
    (cfg.errors.foldl (fun (acc : Nat) (e : CliError) =>
      match e with
      | CliError.unsupportedCodecOrFlag _ => acc + 1
      | _ => acc) 0).toUInt32
  let hasCopyFilterConflict : Bool :=
    (cfg.videoCodec == some .copy && cfg.videoFilter.isSome) ||
    (cfg.audioCodec == some .copy && cfg.audioFilter.isSome)
  let copyMode : UInt32 := if hasCopyFilterConflict then 1 else 0
  let filterCount : UInt32 := if hasCopyFilterConflict then 1 else 0
  let gateOk := verifyCliInvocation hasInput hasOutput unknownFlags unsupportedCodecs copyMode filterCount == 1
  if !gateOk then
    let extra : List CliError :=
      (if cfg.inputs.isEmpty then [.missingInput] else []) ++
      (if cfg.output.isNone && cfg.daemon.isNone then [.missingOutput] else []) ++
      (if hasCopyFilterConflict then [.copyWithFilter] else [])
    .error (cfg.errors ++ extra)
  else .ok cfg

/-! ## 2. Golden `framecrc` / MD5 Oracle -/

/-- Compute the project's 64-bit Adler-style digest over raw frame bytes. -/
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

/-- Format a project digest line: `streamIndex, dts, pts, duration, size, crc`. -/
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
    parseCliSeconds "00:00:00.5" = some { num := 5, den := 10 } ∧
    parseCliSeconds "500ms" = some { num := 500, den := 1000 } ∧
    parseCliSeconds "1.2.3" = none ∧
    parseCliSeconds "" = none ∧
    parseCliSeconds "abc" = none := by
  decide

theorem cliSecondsToMillis_exact_and_rejects_overflow :
    (parseCliSeconds "0.5").bind cliSecondsToMillis = some 500 ∧
    (parseCliSeconds "00:00:00.5").bind cliSecondsToMillis = some 500 ∧
    (parseCliSeconds "1.25").bind cliSecondsToMillis = some 1250 ∧
    (parseCliSeconds "4294967").bind cliSecondsToMillis = some 4294967000 ∧
    (parseCliSeconds "4294968").bind cliSecondsToMillis = none ∧
    cliSecondsToMillis { num := 1, den := 0 } = none := by
  decide

/-- Universal Theorem: Any `CliSeconds` with a zero denominator is rejected (`none`) by `cliSecondsToMillis`. -/
theorem cliSecondsToMillis_zero_den_universal (n : Nat) :
    cliSecondsToMillis { num := n, den := 0 } = none := by
  rfl

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

/--
  Theorem (Wave 52): `parseFFmpegArgs` stores `-preset`, `-crf`, `-b:v`, `-b:a`, `-r`, and `-pix_fmt`
  into `CliConfig` and fail-closes (`errors ≠ []`) on invalid `-crf`, `-preset`, `-r`, or unknown flags (`-foobar`).
-/
theorem cli_encoder_options_retained_and_invalid_rejected :
    let cfg := parseFFmpegArgs [
      "-hide_banner", "-nostats", "-v", "warning", "-json", "-i", "in.mp4",
      "-preset", "veryfast", "-crf", "18", "-b:v", "4M", "-b:a", "192k",
      "-r", "60/1", "-pix_fmt", "yuv420p10le", "out.mp4"
    ]
    let defCfg := parseFFmpegArgs ["-i", "in.mp4", "out.mp4"]
    let badCrf := parseFFmpegArgs ["-i", "in.mp4", "-crf", "99", "out.mp4"]
    let badPreset := parseFFmpegArgs ["-i", "in.mp4", "-preset", "bogus_preset", "out.mp4"]
    let badFlag := parseFFmpegArgs ["-i", "in.mp4", "-unknown_flag", "out.mp4"]
    cfg.preset = some "veryfast" ∧
    cfg.crf = some "18" ∧
    cfg.videoBitrate = some "4M" ∧
    cfg.audioBitrate = some "192k" ∧
    cfg.frameRate = some "60/1" ∧
    cfg.pixelFormat = some "yuv420p10le" ∧
    cfg.hideBanner = true ∧
    cfg.showStats = false ∧
    cfg.logLevel = "warning" ∧
    cfg.jsonOutput = true ∧
    defCfg.jsonOutput = false ∧
    defCfg.showStats = true ∧
    defCfg.hideBanner = false ∧
    cfg.errors = [] ∧
    badCrf.errors ≠ [] ∧
    badPreset.errors ≠ [] ∧
    badFlag.errors ≠ [] ∧
    supportedPixFmt "yuv420p" = true ∧
    supportedPixFmt "yuv420p10le" = true ∧
    nativeMp4PixFmt "nv12" = false ∧
    supportedPixFmt "nv12" = true ∧
    supportedPixFmt "bogus_pix_fmt" = false := by
  decide

end LeanAV.Cli
