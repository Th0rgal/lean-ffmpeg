import LeanAV.Cli
import LeanAV.PlanIR
import LeanAV.Md5
import LeanAV.Ffv1
import LeanAV.Ffv1Container
import LeanAV.IO

namespace LeanAV.Ffv1Pipeline

open LeanAV.Cli
open LeanAV.PlanIR
open LeanAV.Md5
open LeanAV.Ffv1
open LeanAV.Ffv1Container
open LeanAV.IO

inductive Ffv1JobMode where
  | encode
  | decode
  | remux
  deriving Repr, DecidableEq, Inhabited

structure Ffv1CliJob where
  mode : Ffv1JobMode
  inPath : String
  outPath : String
  inFmt : Option String := none
  outFmt : String
  inSize : Option (Nat × Nat) := none
  inPixFmt : Option Ffv1PixelFormat := none
  outPixFmt : Option Ffv1PixelFormat := none
  inRate : Option (Nat × Nat) := none
  outRate : Option (Nat × Nat) := none
  coder : Nat := 2
  ctxModel : Nat := 0
  slices : Nat := 4
  sliceCrc : Nat := 1
  gopSize : Nat := 12
  maxFrames : Option Nat := none
  overwrite : Bool := false
  noOverwrite : Bool := false
  jsonOutput : Bool := false
  logLevel : Option String := none
  deriving Repr, DecidableEq, Inhabited

def parseFfv1FrameRate (s : String) : Option (Nat × Nat) :=
  let low := strToLowerAscii s
  if low == "ntsc" then some (1001, 30000)
  else if low == "pal" || low == "qpal" || low == "spal" then some (1, 25)
  else if low == "film" then some (1, 24)
  else if low == "ntsc-film" then some (1001, 24000)
  else
    match splitStrOnChar s '/' with
    | [fpsStr] =>
      match splitStrOnChar fpsStr '.' with
      | [intStr] =>
        match parsePosNatSpec intStr with
        | some fps => some (1, fps)
        | none => none
      | [intStr, fracStr] =>
        match parseNonNegNatSpec intStr, parseNonNegNatSpec fracStr with
        | some iPart, some fPart =>
          let scale := 10 ^ fracStr.length
          let fpsNum := iPart * scale + fPart
          if fpsNum == 0 then none
          else
            let g := Nat.gcd scale fpsNum
            some (scale / g, fpsNum / g)
        | _, _ => none
      | _ => none
    | [fpsDenStr, fpsNumStr] =>
      match parsePosNatSpec fpsDenStr, parsePosNatSpec fpsNumStr with
      | some fpsN, some fpsD =>
        let g := Nat.gcd fpsD fpsN
        some (fpsD / g, fpsN / g)
      | _, _ => none
    | _ => none

private structure RawFfv1ParseState where
  seenIn : Bool := false
  seenOut : Bool := false
  inPath : Option String := none
  outPath : Option String := none
  inFmt : Option String := none
  outFmt : Option String := none
  inSize : Option (Nat × Nat) := none
  inPix : Option Ffv1PixelFormat := none
  outPix : Option Ffv1PixelFormat := none
  inRate : Option (Nat × Nat) := none
  outRate : Option (Nat × Nat) := none
  vCodec : Option String := none
  coder : Nat := 2
  ctxModel : Nat := 0
  slices : Nat := 4
  sliceCrc : Nat := 1
  gopSize : Nat := 12
  hasEncOpts : Bool := false
  maxFrames : Option Nat := none
  overwrite : Bool := false
  noOverwrite : Bool := false
  jsonOutput : Bool := false
  logLevel : Option String := none

private def parseFfv1Tokens : List String → RawFfv1ParseState → Option RawFfv1ParseState
  | [], st => some st
  | "-y" :: rest, st => parseFfv1Tokens rest { st with overwrite := true, noOverwrite := false }
  | "-n" :: rest, st => parseFfv1Tokens rest { st with overwrite := false, noOverwrite := true }
  | "-json" :: rest, st | "--json" :: rest, st => parseFfv1Tokens rest { st with jsonOutput := true }
  | "-nostdin" :: rest, st | "-hide_banner" :: rest, st | "-stats" :: rest, st |
    "-nostats" :: rest, st | "-an" :: rest, st | "-dump-plan" :: rest, st | "--dump-plan" :: rest, st =>
    parseFfv1Tokens rest st
  | "-v" :: lvl :: rest, st | "-loglevel" :: lvl :: rest, st =>
    parseFfv1Tokens rest { st with logLevel := some lvl }
  | "-i" :: path :: rest, st =>
    if st.seenIn || st.seenOut then none
    else parseFfv1Tokens rest { st with seenIn := true, inPath := some path }
  | "-f" :: fmt :: rest, st =>
    if st.seenOut then none
    else
      let fl := strToLowerAscii fmt
      if !st.seenIn then parseFfv1Tokens rest { st with inFmt := some fl }
      else parseFfv1Tokens rest { st with outFmt := some fl }
  | "-s" :: sz :: rest, st | "-video_size" :: sz :: rest, st =>
    if st.seenIn || st.seenOut then none
    else
      match parseVideoSizeSpec sz with
      | some wh => parseFfv1Tokens rest { st with inSize := some wh }
      | none => none
  | "-pix_fmt" :: pf :: rest, st | "-pixel_format" :: pf :: rest, st =>
    if st.seenOut then none
    else
      match Ffv1PixelFormat.parse pf with
      | some p =>
        if !st.seenIn then parseFfv1Tokens rest { st with inPix := some p }
        else parseFfv1Tokens rest { st with outPix := some p }
      | none => none
  | "-r" :: rStr :: rest, st | "-framerate" :: rStr :: rest, st =>
    if st.seenOut then none
    else
      match parseFfv1FrameRate rStr with
      | some r =>
        if !st.seenIn then parseFfv1Tokens rest { st with inRate := some r }
        else parseFfv1Tokens rest { st with outRate := some r }
      | none => none
  | "-c:v" :: cv :: rest, st | "-vcodec" :: cv :: rest, st |
    "-codec:v" :: cv :: rest, st | "-c" :: cv :: rest, st | "-codec" :: cv :: rest, st =>
    if st.seenOut then none
    else
      let cl := strToLowerAscii cv
      if !st.seenIn then
        if cl == "ffv1" || cl == "rawvideo" then parseFfv1Tokens rest st else none
      else
        if cl == "ffv1" || cl == "libffv1" then parseFfv1Tokens rest { st with vCodec := some "ffv1" }
        else if cl == "rawvideo" then parseFfv1Tokens rest { st with vCodec := some "rawvideo" }
        else if cl == "copy" then parseFfv1Tokens rest { st with vCodec := some "copy" }
        else none
  | "-level" :: lvl :: rest, st | "-level:v" :: lvl :: rest, st =>
    if !st.seenIn || st.seenOut || lvl != "3" then none
    else parseFfv1Tokens rest { st with hasEncOpts := true }
  | "-coder" :: cStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else
      match parseCoderOption cStr with
      | some c => parseFfv1Tokens rest { st with coder := c, hasEncOpts := true }
      | none => none
  | "-context" :: ctxStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else if ctxStr == "0" then parseFfv1Tokens rest { st with ctxModel := 0, hasEncOpts := true }
    else if ctxStr == "1" then parseFfv1Tokens rest { st with ctxModel := 1, hasEncOpts := true }
    else none
  | "-slices" :: slStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else
      match parsePosNatSpec slStr with
      | some sl =>
        if (sliceGridForCount sl).isSome then parseFfv1Tokens rest { st with slices := sl, hasEncOpts := true }
        else none
      | none => none
  | "-slicecrc" :: scStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else if scStr == "0" then parseFfv1Tokens rest { st with sliceCrc := 0, hasEncOpts := true }
    else if scStr == "1" then parseFfv1Tokens rest { st with sliceCrc := 1, hasEncOpts := true }
    else none
  | "-g" :: gStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else
      match parseNonNegNatSpec gStr with
      | some g => parseFfv1Tokens rest { st with gopSize := if g == 0 then 1 else g, hasEncOpts := true }
      | none => none
  | "-frames:v" :: fStr :: rest, st | "-vframes" :: fStr :: rest, st | "-frames" :: fStr :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else
      match parseNonNegNatSpec fStr with
      | some n => parseFfv1Tokens rest { st with maxFrames := some n }
      | none => none
  | tok :: rest, st =>
    if !st.seenIn || st.seenOut then none
    else if !strStartsWithFast tok "-" || tok == "-" then
      parseFfv1Tokens rest { st with seenOut := true, outPath := some tok }
    else none

private def inferFfv1InputFormat (inFmt : Option String) (inPath : String) : String :=
  match inFmt with
  | some f =>
    if f == "mkv" || f == "matroska" then "matroska"
    else if f == "y4m" || f == "yuv4mpegpipe" then "yuv4mpegpipe"
    else f
  | none =>
    let low := strToLowerAscii inPath
    if strEndsWithFast low ".mkv" then "matroska"
    else if strEndsWithFast low ".mov" then "mov"
    else if strEndsWithFast low ".avi" then "avi"
    else if strEndsWithFast low ".y4m" then "yuv4mpegpipe"
    else "unknown"

private def isFfv1ContainerFmt (f : String) : Bool :=
  f == "matroska" || f == "mkv" || f == "mov" || f == "avi"

def parseFfv1CliArgs (args : List String) : Option Ffv1CliJob := do
  let st ← parseFfv1Tokens args {}
  let inPath ← st.inPath
  let outPath ← st.outPath
  if !isSafeLocalMediaPath inPath then none
  if !isSafeOutputTarget outPath st.outFmt.isSome st.outFmt then none
  let effInFmt := inferFfv1InputFormat st.inFmt inPath
  let effOutFmt := strToLowerAscii (inferContainerFormat st.outFmt outPath)
  if effInFmt == "rawvideo" then
    if st.inSize.isNone || st.inPix.isNone then none
  else
    if st.inSize.isSome || st.inPix.isSome then none
  let mode ←
    if st.vCodec == some "ffv1" then
      if (effInFmt == "rawvideo" || effInFmt == "yuv4mpegpipe" || isFfv1ContainerFmt effInFmt) &&
         (isFfv1ContainerFmt effOutFmt || effOutFmt == "null") then
        some Ffv1JobMode.encode
      else none
    else if !isFfv1ContainerFmt effInFmt || st.hasEncOpts then
      none
    else if st.vCodec == some "copy" then
      if st.outPix.isNone && st.outRate.isNone && st.maxFrames.isNone &&
         (isFfv1ContainerFmt effOutFmt || effOutFmt == "null") then
        some Ffv1JobMode.remux
      else none
    else if st.vCodec.isNone || st.vCodec == some "rawvideo" then
      if effOutFmt == "rawvideo" || effOutFmt == "null" || effOutFmt == "md5" || effOutFmt == "framemd5" then
        some Ffv1JobMode.decode
      else if effOutFmt == "yuv4mpegpipe" || effOutFmt == "y4m" then
        if st.outPix.isNone || st.outPix == some .yuv420p || st.outPix == some .gray then
          some Ffv1JobMode.decode
        else none
      else none
    else none
  pure {
    mode := mode
    inPath := inPath
    outPath := outPath
    inFmt := some effInFmt
    outFmt := effOutFmt
    inSize := st.inSize
    inPixFmt := st.inPix
    outPixFmt := st.outPix
    inRate := st.inRate
    outRate := st.outRate
    coder := st.coder
    ctxModel := st.ctxModel
    slices := st.slices
    sliceCrc := st.sliceCrc
    gopSize := st.gopSize
    maxFrames := st.maxFrames
    overwrite := st.overwrite
    noOverwrite := st.noOverwrite
    jsonOutput := st.jsonOutput
    logLevel := st.logLevel
  }

private def ffv1CliQuiet (logLevel : Option String) : Bool :=
  match logLevel with
  | some s =>
    let low := strToLowerAscii s
    low == "quiet" || low == "-8" || low == "panic" || low == "0" || low == "fatal" || low == "8"
  | none => false

private def ffv1JsonEsc (s : String) : String :=
  String.ofList <| s.toList.foldr (fun c acc =>
    if c == '"' then '\\' :: '"' :: acc
    else if c == '\\' then '\\' :: '\\' :: acc
    else if c == '\n' then '\\' :: 'n' :: acc
    else c :: acc) []

private def isSpecialFfv1Out (outPath outFmt : String) : Bool :=
  outPath == "-" || outPath == "/dev/null" || outPath == "md5:" ||
  strStartsWithFast outPath "md5:" || strStartsWithFast outPath "pipe:" ||
  isNoFileOutputFormat outFmt outPath

private def checkFfv1Overwrite (job : Ffv1CliJob) : IO (Option UInt32) := do
  if job.overwrite || isSpecialFfv1Out job.outPath job.outFmt then
    return none
  if !(← System.FilePath.pathExists job.outPath) then
    return none
  if job.jsonOutput then
    IO.println "{\"ok\":false,\"mode\":\"ffmpeg-cli\",\"error\":\"File exists\"}"
    return some 1
  if !job.noOverwrite then
    if !ffv1CliQuiet job.logLevel then
      IO.eprintln s!"File '{job.outPath}' already exists. Overwrite? [y/N] Not overwriting - exiting"
    return some 0
  if !ffv1CliQuiet job.logLevel then
    IO.eprintln s!"File '{job.outPath}' already exists. Exiting."
  return some 1

private def writeFfv1OutputTarget (outPath outFmt : String) (payload : ByteArray) : IO (Except String Nat) := do
  if outFmt == "null" || outPath == "/dev/null" then
    return .ok 0
  let actualPath :=
    if outFmt == "md5" && strStartsWithFast outPath "md5:" then
      let stripped := String.ofList (outPath.toList.drop 4)
      if stripped.isEmpty then "-" else stripped
    else
      outPath
  if actualPath == "-" || actualPath == "pipe:1" then
    let stdout ← IO.getStdout
    stdout.write payload
    stdout.flush
    return .ok payload.size
  match ← writeMediaFileAtomic actualPath payload with
  | .ok _ => return .ok payload.size
  | .error e => return .error s!"output write error: {repr e}"

private structure RawFrameSeq where
  width : Nat
  height : Nat
  timeNum : Nat
  timeDen : Nat
  sarNum : Nat
  sarDen : Nat
  pixFmt : Ffv1PixelFormat
  frames : Array ByteArray

private def takeMaxFrames (frames : Array ByteArray) (maxF : Option Nat) : Array ByteArray :=
  match maxF with
  | some n => frames.extract 0 (min n frames.size)
  | none => frames

private def concatByteArrays (frames : Array ByteArray) : ByteArray := Id.run do
  let total := frames.foldl (fun acc b => acc + b.size) 0
  let mut out := ByteArray.emptyWithCapacity total
  for b in frames do
    out := out ++ b
  return out

private def decodeStreamToFrames (s : Stream) (outPix : Option Ffv1PixelFormat)
    (maxF : Option Nat) : Except String RawFrameSeq := do
  let cfg ← parseConfiguration s.config
  let effPix := outPix.getD cfg.defaultDecodedPixFmt
  let pkts := takeMaxFrames s.packets maxF
  let mut gop : GopState := #[]
  let mut decoded : Array ByteArray := Array.emptyWithCapacity pkts.size
  for p in pkts do
    let (frm, _, nextGop) ← decodeFrameV3 cfg s.width s.height p gop (some effPix)
    decoded := decoded.push frm
    gop := nextGop
  return {
    width := s.width
    height := s.height
    timeNum := s.timeNum
    timeDen := s.timeDen
    sarNum := s.sarNum
    sarDen := s.sarDen
    pixFmt := effPix
    frames := decoded
  }

private def loadEncodeSource (job : Ffv1CliJob) (inBytes : ByteArray) :
    Except String RawFrameSeq := do
  let inFmt := job.inFmt.getD "unknown"
  if inFmt == "rawvideo" then
    let some (w, h) := job.inSize | throw "rawvideo input requires -video_size"
    let some pf := job.inPixFmt | throw "rawvideo input requires -pix_fmt"
    let some fsz := pf.frameByteSize w h | throw "invalid rawvideo dimensions for pixel format"
    if fsz == 0 || inBytes.size % fsz != 0 then
      throw "rawvideo byte length is not an exact multiple of frame size"
    let nFrames := inBytes.size / fsz
    let count := match job.maxFrames with | some m => min m nFrames | none => nFrames
    let mut frames : Array ByteArray := Array.emptyWithCapacity count
    for i in [:count] do
      frames := frames.push (inBytes.extract (i * fsz) ((i + 1) * fsz))
    let (tn, td) := job.inRate.getD (1, 25)
    return { width := w, height := h, timeNum := tn, timeDen := td, sarNum := 0, sarDen := 1, pixFmt := pf, frames := frames }
  else if inFmt == "yuv4mpegpipe" then
    let y4m ← parseY4M inBytes
    let (tn, td) := job.inRate.getD (y4m.timeNum, y4m.timeDen)
    return {
      width := y4m.width, height := y4m.height, timeNum := tn, timeDen := td,
      sarNum := y4m.sarNum, sarDen := y4m.sarDen, pixFmt := y4m.pixelFormat,
      frames := takeMaxFrames y4m.frames job.maxFrames
    }
  else
    let s ← demux inBytes
    decodeStreamToFrames s none job.maxFrames

private def convertLosslessPixFmt (srcFmt dstFmt : Ffv1PixelFormat) (frm : ByteArray) :
    Except String ByteArray :=
  if srcFmt == dstFmt then .ok frm
  else if srcFmt == .rgb24 && dstFmt == .bgr0 then .ok (convertRgb24ToBgr0 frm)
  else if srcFmt == .bgr0 && dstFmt == .rgb24 then .ok (convertBgr0ToRgb24 frm)
  else .error "unsupported cross-colorspace pixel format conversion"

private def runEncodePure (job : Ffv1CliJob) (inBytes : ByteArray) :
    Except String (ByteArray × Nat) := do
  let src ← loadEncodeSource job inBytes
  let targetPix := job.outPixFmt.getD src.pixFmt
  let mut convFrames : Array ByteArray := Array.emptyWithCapacity src.frames.size
  for frm in src.frames do
    let cf ← convertLosslessPixFmt src.pixFmt targetPix frm
    convFrames := convFrames.push cf
  let encCfg ← makeEncoderConfiguration targetPix job.coder job.slices job.sliceCrc job.gopSize
  let cfgRecord := encodeConfiguration encCfg
  let mut gop : GopState := #[]
  let mut pkts : Array ByteArray := Array.emptyWithCapacity convFrames.size
  let mut kfs : Array Bool := Array.emptyWithCapacity convFrames.size
  let gStep := if job.gopSize == 0 then 1 else job.gopSize
  for i in [:convFrames.size] do
    let isKf := (i % gStep) == 0
    let (pkt, nextGop) ← encodeFrameV3 encCfg src.width src.height targetPix convFrames[i]! job.ctxModel isKf gop
    pkts := pkts.push pkt
    kfs := kfs.push isKf
    gop := nextGop
  if job.outFmt == "null" then
    return (ByteArray.empty, convFrames.size)
  let (tn, td) := job.outRate.getD (src.timeNum, src.timeDen)
  let outStream : Stream := {
    width := src.width, height := src.height,
    timeNum := tn, timeDen := td,
    sarNum := src.sarNum, sarDen := src.sarDen,
    config := cfgRecord, packets := pkts, keyframes := kfs
  }
  let muxed ← mux job.outFmt outStream
  return (muxed, convFrames.size)

private def runDecodePure (job : Ffv1CliJob) (inBytes : ByteArray) :
    Except String (ByteArray × Nat) := do
  let s ← demux inBytes
  let decoded ← decodeStreamToFrames s job.outPixFmt job.maxFrames
  let (tn, td) := job.outRate.getD (decoded.timeNum, decoded.timeDen)
  if job.outFmt == "null" then
    return (ByteArray.empty, decoded.frames.size)
  else if job.outFmt == "rawvideo" then
    return (concatByteArrays decoded.frames, decoded.frames.size)
  else if job.outFmt == "md5" then
    let text := formatMd5Muxer (concatByteArrays decoded.frames)
    return (text.toUTF8, decoded.frames.size)
  else if job.outFmt == "framemd5" then
    let text := formatFrameMd5Muxer decoded.width decoded.height tn td decoded.sarNum decoded.sarDen decoded.frames
    return (text.toUTF8, decoded.frames.size)
  else if job.outFmt == "yuv4mpegpipe" || job.outFmt == "y4m" then
    let y4mBytes ← writeY4M {
      width := decoded.width, height := decoded.height,
      timeNum := tn, timeDen := td,
      sarNum := decoded.sarNum, sarDen := decoded.sarDen,
      pixelFormat := decoded.pixFmt, frames := decoded.frames
    }
    return (y4mBytes, decoded.frames.size)
  else
    throw "unsupported decode output format"

private def runRemuxPure (job : Ffv1CliJob) (inBytes : ByteArray) :
    Except String (ByteArray × Nat) := do
  let s ← demux inBytes
  let cfg ← parseConfiguration s.config
  for p in s.packets do
    let _ ← splitV3Slices p cfg.errorCorrection
  if job.outFmt == "null" then
    return (ByteArray.empty, s.packets.size)
  let muxed ← mux job.outFmt s
  return (muxed, s.packets.size)

def executeFfv1Pure (job : Ffv1CliJob) (inBytes : ByteArray) :
    Except String (ByteArray × Nat) :=
  match job.mode with
  | .encode => runEncodePure job inBytes
  | .decode => runDecodePure job inBytes
  | .remux  => runRemuxPure job inBytes

private def shouldDelegateDemuxMiss (_job : Ffv1CliJob) (err : String) : Bool :=
  err == "multi-stream container" || err == "not FFV1" ||
  err == "unsupported cross-colorspace pixel format conversion" ||
  err == "Incompatible output pixel format for FFV1 stream" ||
  err == "Unsupported Y4M pixel format" ||
  err == "FFV1 version 0/1 stream requires configuration record"

def tryExecuteNativeFfv1Cli (args : List String) : IO (Option UInt32) := do
  let some job := parseFfv1CliArgs args | return none
  let t0 ← IO.monoNanosNow
  if !(← System.FilePath.pathExists job.inPath) then
    if job.jsonOutput then
      IO.println "{\"ok\":false,\"mode\":\"ffmpeg-cli\",\"error\":\"input file does not exist\"}"
    else if !ffv1CliQuiet job.logLevel then
      IO.eprintln s!"{job.inPath}: No such file or directory"
    return some 1
  if let some owRc ← checkFfv1Overwrite job then
    return some owRc
  let inBytes ←
    try
      IO.FS.readBinFile job.inPath
    catch e =>
      if job.jsonOutput then
        IO.println s!"\{\"ok\":false,\"mode\":\"ffmpeg-cli-native-ffv1\",\"error\":\"{ffv1JsonEsc (toString e)}\"}"
      else if !ffv1CliQuiet job.logLevel then
        IO.eprintln s!"{job.inPath}: {e}"
      return some 1
  match executeFfv1Pure job inBytes with
  | .error err =>
    if shouldDelegateDemuxMiss job err then
      return none
    if job.jsonOutput then
      IO.println s!"\{\"ok\":false,\"mode\":\"ffmpeg-cli-native-ffv1\",\"error\":\"{ffv1JsonEsc err}\"}"
    else if !ffv1CliQuiet job.logLevel then
      IO.eprintln s!"FFV1 error: {err}"
    return some 1
  | .ok (outPayload, frameCount) =>
    match ← writeFfv1OutputTarget job.outPath job.outFmt outPayload with
    | .error wErr =>
      if job.jsonOutput then
        IO.println s!"\{\"ok\":false,\"mode\":\"ffmpeg-cli-native-ffv1\",\"error\":\"{ffv1JsonEsc wErr}\"}"
      else if !ffv1CliQuiet job.logLevel then
        IO.eprintln s!"FFV1 write error: {wErr}"
      return some 1
    | .ok writtenBytes =>
      let t1 ← IO.monoNanosNow
      if job.jsonOutput then
        let pfx := s!"\{\"ok\":true,\"mode\":\"ffmpeg-cli-native-ffv1\",\"tier\":\"independent_verified\","
        let mid := s!"\"format\":\"{ffv1JsonEsc job.outFmt}\",\"frames\":{frameCount},"
        let sfx := s!"\"in_bytes\":{inBytes.size},\"out_bytes\":{writtenBytes},\"total_us\":{(t1 - t0) / 1000}}"
        IO.println (pfx ++ mid ++ sfx)
      return some 0

end LeanAV.Ffv1Pipeline
