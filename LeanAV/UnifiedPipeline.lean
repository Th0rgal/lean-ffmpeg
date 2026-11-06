import LeanAV.Cli
import LeanAV.InprocTranscode
import LeanAV.HevcMain
import LeanAV.Av1Main
import LeanAV.LavfiGraph

namespace LeanAV.UnifiedPipeline

open LeanSys.Posix LeanAV.Spec LeanAV.Core LeanAV.Format LeanAV.LavfiGraph

structure Media where
  video : Array VideoFrame := #[]
  audio : Option AudioFrame := none
  audioBits : Nat := 16
  fps : Nat := 25
  audioCopy : Option SynthMp4Track := none
  deriving Inhabited

structure Options where
  videoCodec : String := "h264"
  audioCodec : String := "aac"
  format : String := "mp4"
  videoFilter : String := ""
  audioFilter : String := ""
  filterComplex : String := ""
  maps : Array String := #[]
  noVideo : Bool := false
  noAudio : Bool := false
  qp : Nat := 28
  log2Ctb : Nat := 6
  tileColumns : Nat := 1
  tileRows : Nat := 1
  av1TileColumns : Nat := 0
  av1TileRows : Nat := 0
  maxFrames : Option Nat := none
  deriving Inhabited

def RawVideoSafe (x : Nat × Nat × Nat) : Prop :=
  0 < x.1 ∧ 0 < x.2.1 ∧ x.1 % 2 = 0 ∧ x.2.1 % 2 = 0 ∧
  0 < x.2.2 ∧ x.2.2 % (x.1 * x.2.1 * 3 / 2) = 0

instance (x : Nat × Nat × Nat) : Decidable (RawVideoSafe x) :=
  inferInstanceAs (Decidable (0 < x.1 ∧ 0 < x.2.1 ∧ x.1 % 2 = 0 ∧ x.2.1 % 2 = 0 ∧
    0 < x.2.2 ∧ x.2.2 % (x.1 * x.2.1 * 3 / 2) = 0))

def rawVideoGateSpec : AVGateSpec (Nat × Nat × Nat) RawVideoSafe where
  gate x := decide (RawVideoSafe x)
  sound _ h := of_decide_eq_true h
  complete _ h := decide_eq_true h
  posWitness := (2, 2, 6)
  negWitness := (2, 2, 7)
  nonVacuous := rfl
  tight := rfl

theorem rawVideoGateSpec_iff (x : Nat × Nat × Nat) :
    rawVideoGateSpec.gate x = true ↔ RawVideoSafe x := rawVideoGateSpec.iff_safe x

def unpackYuv420p (width height : Nat) (raw : ByteArray) : Option (Array VideoFrame) := do
  if !rawVideoGateSpec.gate (width, height, raw.size) then none
  else
    let frameBytes := width * height * 3 / 2
    let mut out := #[]
    for i in [:raw.size / frameBytes] do
      let mut vf := VideoFrame.allocYuv420p width height i.toUInt64
      let mut cursor := i * frameBytes
      let mut planes := vf.planes
      for p in [:3] do
        let mut plane := planes[p]!
        for r in [:plane.height] do
          for c in [:plane.width] do
            plane := plane.setPixel r c (raw.get! cursor)
            cursor := cursor + 1
        planes := planes.set! p plane
      vf := { vf with planes := planes }
      out := out.push vf
    some out

def decodedVideo (decoded : Option (Nat × Nat × Nat × ByteArray)) (fps : Nat := 25) : Option Media := do
  let (w, h, count, raw) ← decoded
  let frames ← unpackYuv420p w h raw
  if count != frames.size then none else some { video := frames, fps := fps }

def decodeMp4 (raw : ByteArray) (noAudio : Bool := false) : Option Media := do
  let tracks ← demuxNativeMp4ContainerTracks (ByteSlice.ofByteArray raw)
  let mut media : Media := {}
  for tr in tracks do
    if tr.hasEncrypted || tr.multiStsd || tr.timescale == 0 then none
    else if tr.kind == .video then
      if !media.video.isEmpty then none
      let frames ←
        if tr.stsdFourcc == "avc1" || tr.stsdFourcc == "avc3" then do
          let (frames, _, _) ← LeanAV.InprocTranscode.decodeMp4AvcTrackToFrames raw tr
          some frames
        else if tr.stsdFourcc == "hvc1" || tr.stsdFourcc == "hev1" then do
          let m ← decodedVideo (LeanAV.HevcMain.decodeHevcToYuv420p raw)
          some m.video
        else if tr.stsdFourcc == "av01" then do
          let m ← decodedVideo (LeanAV.Av1Main.decodeAv1ToYuv420p raw)
          some m.video
        else if tr.stsdFourcc == "apcn" then do
          let mut frames := #[]
          for s in tr.samples do
            if s.fileOff + s.byteLen > raw.size then none
            let vf ← LeanAV.Video.decodeProResFrameToYuv420p
              (ByteSlice.ofByteArray (raw.extract s.fileOff (s.fileOff + s.byteLen))) s.dts.toUInt64
            frames := frames.push vf
          some frames
        else none
      if frames.isEmpty then none
      let duration := tr.samples.foldl (fun n s => n + s.dur) 0
      let fps := if duration == 0 then 25 else Nat.max 1 (frames.size * tr.timescale / duration)
      media := { media with video := frames, fps := fps }
    else if tr.kind == .audio then
      if noAudio then
        pure ()
      else if media.audio.isSome then none
      else if tr.stsdFourcc == "mp4a" then
        let (channels, sr, bps) ← LeanAV.InprocTranscode.decodeMp4AacTrackToChannels raw tr
        let copied ← LeanAV.InprocTranscode.copyMp4AacTrackToSynth raw tr
        media := { media with
          audio := some (channelArraysToAudioFrame (scaleChannelsBps channels bps 16) sr)
          audioCopy := some copied }
      else if tr.stsdFourcc == "Opus" then
        let dops ← extractMp4StsdChildBody tr.stsdBox ["Opus"] "dOps"
        if dops.size < 10 || dops.get! 0 != 0 then none
        let outCh := dops.get! 1
        let preSkip := ((dops.get! 2).toNat <<< 8) ||| (dops.get! 3).toNat
        let mut opusPackets := #[]
        for s in tr.samples do
          if s.fileOff + s.byteLen > raw.size then none
          opusPackets := opusPackets.push (ByteSlice.ofByteArray (raw.extract s.fileOff (s.fileOff + s.byteLen)))
        let af ← LeanAV.Audio.decodeOpusPacketsToAudioFrame opusPackets outCh preSkip
        media := { media with audio := some af }
      else none
    else none
  if media.video.isEmpty && media.audio.isNone then none else some media

def decodeOggOpus (raw : ByteArray) : Option Media := do
  let packets ← demuxOggLogicalPackets (ByteSlice.ofByteArray raw)
  if packets.size < 3 then none
  let header ← LeanAV.Audio.parseOpusHeadPacket (ByteSlice.ofByteArray packets[0]!.data)
  if !LeanAV.Audio.verifyOpusTagsPacket (ByteSlice.ofByteArray packets[1]!.data) then none
  if packets.any (fun p => p.serialNo != packets[0]!.serialNo) then none
  let audioPackets := (packets.extract 2 packets.size).map (fun p => ByteSlice.ofByteArray p.data)
  let af ← LeanAV.Audio.decodeOpusPacketsToAudioFrame audioPackets header.channels header.preSkip.toNat
    (some packets[packets.size - 1]!.granulePos)
  some { audio := some af }

def decodeMpegTs (raw : ByteArray) : Option Media := do
  let streams ← demuxMpegTsProgram (ByteSlice.ofByteArray raw)
  let mut media : Media := {}
  for stream in streams do
    let payload := stream.packets.foldl (fun bytes p => bytes ++ p.1) ByteArray.empty
    if stream.streamType == 0x1B || stream.streamType == 0x24 then
      if !media.video.isEmpty then none
      let frames ←
        if stream.streamType == 0x1B then LeanAV.InprocTranscode.decodeAnnexBH264StreamToFrames payload
        else do
          let decoded ← decodedVideo (LeanAV.HevcMain.decodeHevcToYuv420p payload)
          some decoded.video
      if frames.size < 2 || stream.packets.size != frames.size then none
      let firstPts := stream.packets[0]!.2.toNat
      let nextPts := stream.packets[1]!.2.toNat
      if nextPts <= firstPts || nextPts >= 8589934592 then none
      let step := nextPts - firstPts
      if 90000 % step != 0 then none
      for i in [:stream.packets.size] do
        let pts := stream.packets[i]!.2.toNat
        if pts >= 8589934592 || pts != firstPts + i * step then none
      let frames := frames.mapIdx fun i vf =>
        { vf with
          pts := (i * step).toUInt64
          duration := step.toUInt64
          timeBase := AVRational.mkSafe 1 90000 }
      media := { media with video := frames, fps := 90000 / step }
    else if stream.streamType == 0x0F then
      if media.audio.isSome then none
      let (pcm, sr, bps) ← LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray payload) true
      media := { media with audio := some (channelArraysToAudioFrame (scaleChannelsBps pcm bps 16) sr) }
    else none
  some media

def decode (raw : ByteArray) (format : String) (width height : Nat := 0)
    (sampleRate : UInt32 := 48000) (channels : Nat := 2) (noAudio : Bool := false) : Option Media := do
  if raw.isEmpty then none
  else if format == "rawvideo" then
    let frames ← unpackYuv420p width height raw
    some { video := frames }
  else if format == "s16le" || format == "s24le" || format == "s32le" then
    let bps := if format == "s32le" then 32 else if format == "s24le" then 24 else 16
    let pcm ← pcmRawLEToChannels (ByteSlice.ofByteArray raw) channels bps
    if sampleRate == 0 then none
    some { audio := some (channelArraysToAudioFrame pcm sampleRate bps), audioBits := bps }
  else if format == "mp4" || format == "mov" then decodeMp4 raw noAudio
  else if format == "hevc" then decodedVideo (LeanAV.HevcMain.decodeHevcToYuv420p raw)
  else if format == "av1" || format == "obu" || format == "ivf" then
    decodedVideo (LeanAV.Av1Main.decodeAv1ToYuv420p raw)
  else if format == "h264" then
    let frames ← LeanAV.InprocTranscode.decodeAnnexBH264StreamToFrames raw
    some { video := frames }
  else if format == "wav" || format == "adts" then
    let (pcm, sr, bps) ←
      if format == "wav" then demuxWavPcmLE (ByteSlice.ofByteArray raw)
      else LeanAV.AacLc.aacDecodeAdtsStream (ByteSlice.ofByteArray raw) true
    let outBits := if format == "wav" then bps else 16
    some {
      audio := some (channelArraysToAudioFrame (scaleChannelsBps pcm bps outBits) sr outBits)
      audioBits := outBits }
  else if format == "flac" then
    let decoded ← LeanAV.Audio.flacDecodeStream (ByteSlice.ofByteArray raw)
    some {
      audio := some (LeanAV.Audio.flacDecodedToAudioFrame decoded)
      audioBits := decoded.info.bitsPerSample.toNat }
  else if format == "ogg" || format == "opus" then decodeOggOpus raw
  else if format == "mpegts" then decodeMpegTs raw
  else none

def filter (media : Media) (options : Options) : Except String Media := do
  if media.video.isEmpty && options.videoFilter != "" then throw "video filter without video stream"
  if media.audio.isNone && options.audioFilter != "" then throw "audio filter without audio stream"
  let (frames, outFps) ← runSingleStreamVideoFilterGraph options.videoFilter media.video media.fps
  let frames := match options.maxFrames with
    | some n => frames.extract 0 n
    | none => frames
  let audio ← match media.audio with
    | some af => do
      let filtered ← runSingleStreamAudioFilterGraph options.audioFilter af
      pure (some filtered)
    | none => pure none
  let audioBits := if options.audioFilter != "" then 16 else media.audioBits
  return { media with
    video := if options.noVideo then #[] else frames
    fps := outFps
    audio := if options.noAudio then none else audio
    audioBits := audioBits
    audioCopy := if options.noAudio || options.audioFilter != "" then none else media.audioCopy }

def encodeVideoTrack (media : Media) (options : Options) : Option SynthMp4Track := do
  let first ← media.video[0]?
  let fps := Nat.max 1 media.fps
  let mut stsd := ByteArray.empty
  let mut packets : Array (ByteArray × Bool) := #[]
  if options.videoCodec == "h264" then
    let (avcc, _, _, encoded) ← LeanAV.InprocTranscode.encodeFramesToH264Cavlc media.video options.qp
    stsd := buildAvc1StsdBox first.width first.height avcc
    packets := encoded.map (fun p => (p, true))
  else if options.videoCodec == "hevc" then
    let (vps, sps, pps, encoded) ← LeanAV.HevcMain.encodeHevcNals first.width first.height
      (packVideoFramesYuv420pRaw media.video) options.qp options.log2Ctb options.tileColumns options.tileRows
    stsd := buildHvc1StsdBox first.width first.height (LeanAV.HevcMain.buildHvccRecord vps sps pps)
    packets := encoded.mapIdx (fun i p => (LeanAV.HevcMain.packLenPrefixed4 p, i == 0))
  else if options.videoCodec == "av1" then
    let (av1c, encoded) ← LeanAV.Av1Main.encodeAv1Mp4TrackPayloads first.width first.height
      (packVideoFramesYuv420pRaw media.video) options.qp options.av1TileColumns options.av1TileRows
    stsd := buildAv01StsdBox first.width first.height av1c
    packets := encoded
  else if options.videoCodec == "prores" then
    stsd := buildApcnStsdBox first.width first.height
    for vf in media.video do
      let p ← LeanAV.Video.encodeYuv420pToProResFrame vf
      packets := packets.push (p, true)
  else none
  some {
    kind := .video
    timescale := fps * 1000
    width := first.width
    height := first.height
    stsdBox := stsd
    samples := packets.map fun p => { data := p.1, dur := 1000, cttsOff := 0, isSync := p.2 }
  }

def audioChannels16 (media : Media) (af : AudioFrame) : Array (Array Int32) :=
  let raw := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
  scaleChannelsBps raw media.audioBits 16

def encodeAudioTrack (media : Media) (options : Options) : Option SynthMp4Track := do
  let af ← media.audio
  if options.audioCodec == "copy" then media.audioCopy
  else if options.audioCodec == "aac" then
    LeanAV.InprocTranscode.encodeChannelsToMp4AacTrack (audioChannels16 media af) af.sampleRate
  else if options.audioCodec == "opus" then
    let af16 := if media.audioBits == 16 && af.sampleFmt == .s16p then af
      else channelArraysToAudioFrame (audioChannels16 media af) af.sampleRate 16
    let (channels, packets) ← LeanAV.Audio.encodeAudioFrameToOpusPackets af16
    some {
      kind := .audio
      timescale := 48000
      width := 0
      height := 0
      stsdBox := buildOpusMp4StsdBox channels.toNat
      samples := packets.map fun p => { data := p.1, dur := 960, cttsOff := 0, isSync := true }
    }
  else none

def muxMpegTs (media : Media) (options : Options) : Option ByteArray := do
  let mut streams : Array MpegTsElementaryStream := #[]
  if !media.video.isEmpty then
    let first ← media.video[0]?
    let packets ←
      if options.videoCodec == "h264" then
        LeanAV.InprocTranscode.encodeFramesToH264AnnexBPackets media.video options.qp
      else if options.videoCodec == "hevc" then do
        let (vps, sps, pps, slices) ← LeanAV.HevcMain.encodeHevcNals first.width first.height
          (packVideoFramesYuv420pRaw media.video) options.qp options.log2Ctb options.tileColumns options.tileRows
        some (slices.mapIdx fun i s => LeanAV.HevcMain.muxAnnexB
          (if i == 0 then #[vps, sps, pps, s] else #[s]))
      else none
    streams := streams.push {
      pid := 0x100
      streamType := if options.videoCodec == "h264" then 0x1B else 0x24
      packets := packets.mapIdx fun i p => (p, (i * 90000 / Nat.max 1 media.fps).toUInt64)
    }
  if let some af := media.audio then
    if options.audioCodec != "aac" then none
    let adts ← LeanAV.AacLc.aacEncodeAdtsStream (audioChannels16 media af) af.sampleRate 16 128000 true
    streams := streams.push { pid := 0x101, streamType := 0x0F, packets := #[(adts, 0)] }
  muxMpegTsProgram streams

def pcmCodecDepth? : String → Option Nat
  | "pcm_u8" => some 8
  | "pcm_s16le" => some 16
  | "pcm_s24le" => some 24
  | "pcm_s32le" => some 32
  | _ => none

def mux (media : Media) (options : Options) : Option ByteArray := do
  if media.video.isEmpty && media.audio.isNone then none
  else if options.format == "mp4" || options.format == "mov" then
    let mut tracks := #[]
    if !media.video.isEmpty then
      let video ← encodeVideoTrack media options
      tracks := tracks.push video
    if media.audio.isSome then
      let audio ← encodeAudioTrack media options
      tracks := tracks.push audio
    muxSynthMp4Container tracks
  else if options.format == "null" then some ByteArray.empty
  else if options.format == "rawvideo" || options.format == "framemd5" then
    if media.video.isEmpty || media.audio.isSome then none
    else if options.format == "framemd5" then muxLavfiFrameMd5Bytes media.video media.fps
    else some (packVideoFramesYuv420pRaw media.video)
  else if options.format == "md5" then
    if !media.video.isEmpty && media.audio.isNone then some (muxLavfiMd5Bytes (packVideoFramesYuv420pRaw media.video))
    else if media.video.isEmpty then do
      let af ← media.audio
      some (muxLavfiMd5Bytes (channelsToPcmRawLE (audioChannels16 media af) 16))
    else none
  else if options.format == "ogg" || options.format == "opus" then
    if !media.video.isEmpty || options.audioCodec != "opus" then none
    let af ← media.audio
    let af16 := if media.audioBits == 16 && af.sampleFmt == .s16p then af
      else channelArraysToAudioFrame (audioChannels16 media af) af.sampleRate 16
    let (channels, packets) ← LeanAV.Audio.encodeAudioFrameToOpusPackets af16
    let header := LeanAV.Audio.buildOpusHeadPacket channels
    let tags := LeanAV.Audio.buildOpusTagsPacket
    muxOggLogicalStream (#[(header, 0), (tags, 0)] ++ packets)
  else if options.format == "mpegts" then muxMpegTs media options
  else if options.format == "wav" then
    if !media.video.isEmpty then none
    let af ← media.audio
    let srcChans := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
    let outBps ←
      if options.audioCodec == "" then some media.audioBits
      else pcmCodecDepth? options.audioCodec
    let outChans := scaleChannelsBps srcChans media.audioBits outBps
    some (muxWavPcmLE outChans af.sampleRate outBps)
  else if options.format == "s16le" || options.format == "s24le" || options.format == "s32le" then
    let targetBps := if options.format == "s32le" then 32 else if options.format == "s24le" then 24 else 16
    let expectedCodec := if targetBps == 32 then "pcm_s32le" else if targetBps == 24 then "pcm_s24le" else "pcm_s16le"
    if !media.video.isEmpty || (options.audioCodec != expectedCodec && options.audioCodec != "") then none
    let af ← media.audio
    let srcChans := LeanAV.Audio.flacAudioFrameToChannels af media.audioBits
    let outChans := scaleChannelsBps srcChans media.audioBits targetBps
    some (channelsToPcmRawLE outChans targetBps)
  else if options.format == "flac" then
    if !media.video.isEmpty || (options.audioCodec != "flac" && options.audioCodec != "") then none
    let af ← media.audio
    let bps := if 4 ≤ media.audioBits && media.audioBits ≤ 32 then media.audioBits else 16
    LeanAV.Audio.flacEncodeAudioFrame af bps
  else if options.format == "adts" then
    if !media.video.isEmpty || (options.audioCodec != "aac" && options.audioCodec != "") then none
    let af ← media.audio
    LeanAV.AacLc.aacEncodeAdtsStream (audioChannels16 media af) af.sampleRate 16 128000 true
  else if options.format == "mkv" || options.format == "avi" then
    if media.video.isEmpty || media.audio.isSome || options.videoCodec != "ffv1" then none
    muxLavfiFfv1Bytes options.format media.video media.fps
  else if options.format == "hevc" || options.format == "h264" || options.format == "ivf" || options.format == "obu" then
    if media.video.isEmpty || media.audio.isSome then none
    let first ← media.video[0]?
    let raw := packVideoFramesYuv420pRaw media.video
    if options.format == "hevc" && options.videoCodec == "hevc" then
      LeanAV.HevcMain.encodeHevcFromYuv420p first.width first.height raw options.qp false
        options.log2Ctb options.tileColumns options.tileRows
    else if options.format == "h264" && options.videoCodec == "h264" then
      let packets ← LeanAV.InprocTranscode.encodeFramesToH264AnnexBPackets media.video options.qp
      some (packets.foldl (· ++ ·) ByteArray.empty)
    else if options.videoCodec == "av1" && (options.format == "ivf" || options.format == "obu") then
      LeanAV.Av1Main.encodeAv1FromYuv420p first.width first.height raw options.qp options.format
        options.av1TileColumns options.av1TileRows
    else none
  else none

def normalizePadLabel (raw : String) : String :=
  if raw.startsWith "[" && raw.endsWith "]" && raw.length ≥ 2 then
    String.ofList ((raw.toList.drop 1).dropLast)
  else raw

def filterStreams (inputs : Array Media) (options : Options) : Except String Media := do
  if inputs.isEmpty then throw "no decoded inputs"
  if options.filterComplex != "" then
    if options.videoFilter != "" || options.audioFilter != "" then
      throw "cannot combine -filter_complex with -vf or -af"
    if options.audioCodec == "copy" then
      throw "cannot combine -filter_complex with -c:a copy"
    let graph ← parseFilterGraph options.filterComplex
    let inputLabels := graph.nodes.toList.flatMap (·.inputs)
    let mut videoIn : List (String × Array VideoFrame × Nat) := []
    let mut audioIn : List (String × AudioFrame) := []
    for idx in [:inputs.size] do
      if (inputLabels.contains s!"{idx}:v" && inputLabels.contains s!"{idx}:v:0") ||
         (inputLabels.contains s!"{idx}:a" && inputLabels.contains s!"{idx}:a:0") then
        throw "input stream consumed through multiple aliases without split/asplit (fail-closed)"
      let m := inputs[idx]!
      if !m.video.isEmpty then
        videoIn := videoIn ++ [(s!"{idx}:v", m.video, m.fps), (s!"{idx}:v:0", m.video, m.fps)]
      if let some af := m.audio then
        audioIn := audioIn ++ [(s!"{idx}:a", af), (s!"{idx}:a:0", af)]
    let outs ← runMultiStreamFilterGraph options.filterComplex videoIn audioIn
    let selected ←
      if options.maps.isEmpty then pure outs
      else do
        let mut sel : List (String × PadFormat × EdgeBufferQueue) := []
        for rawMap in options.maps do
          let lbl := normalizePadLabel rawMap
          match outs.find? (fun (oLbl, _, _) => oLbl == lbl) with
          | some hit => sel := sel ++ [hit]
          | none => throw s!"unmapped filter_complex output pad {rawMap} (fail-closed)"
        pure sel
    if (selected.filter (fun (_, fmt, _) => fmt.kind == .video)).length > 1 ||
       (selected.filter (fun (_, fmt, _) => fmt.kind == .audio)).length > 1 then
      throw "multiple output streams of the same kind are unsupported (fail-closed)"
    let (frames, fps) :=
      if options.noVideo then (#[], 25)
      else match selected.find? (fun (_, fmt, _) => fmt.kind == .video) with
        | some (_, fmt, q) =>
          let all := drainVideoQueue q
          let capped := match options.maxFrames with | some n => all.extract 0 n | none => all
          (capped, Nat.max 1 fmt.fpsNum)
        | none => (#[], 25)
    let audio :=
      if options.noAudio then none
      else match selected.find? (fun (_, fmt, _) => fmt.kind == .audio) with
        | some (_, _, q) => some (drainAudioQueue q)
        | none => none
    return { video := frames, audio := audio, fps := fps, audioCopy := none }
  if inputs.size != 1 || !options.maps.isEmpty then
    throw "multiple inputs or explicit -map require -filter_complex (fail-closed)"
  filter inputs[0]! options

def runStreams (inputs : Array Media) (options : Options) : Except String ByteArray := do
  let filtered ← filterStreams inputs options
  match mux filtered options with
  | some bytes => return bytes
  | none => throw "unsupported codec/container combination or encoding failure (fail-closed)"

def run (media : Media) (options : Options) : Except String ByteArray :=
  runStreams #[media] options

structure Input where
  path : String
  format : String
  width : Nat := 0
  height : Nat := 0
  sampleRate : UInt32 := 48000
  channels : Nat := 2
  deriving Inhabited

structure Invocation where
  inputs : Array Input := #[]
  output : String := ""
  options : Options := {}
  deriving Inhabited

def inferFormat (path : String) : String :=
  let p := path.toLower
  if p.endsWith ".mp4" || p.endsWith ".m4v" || p.endsWith ".m4a" then "mp4"
  else if p.endsWith ".mov" then "mov"
  else if p.endsWith ".hevc" || p.endsWith ".265" then "hevc"
  else if p.endsWith ".h264" || p.endsWith ".264" then "h264"
  else if p.endsWith ".obu" then "obu"
  else if p.endsWith ".ivf" then "ivf"
  else if p.endsWith ".yuv" || p.endsWith ".raw" then "rawvideo"
  else if p.endsWith ".wav" then "wav"
  else if p.endsWith ".flac" then "flac"
  else if p.endsWith ".aac" then "adts"
  else if p.endsWith ".ogg" || p.endsWith ".opus" || p.endsWith ".oga" then "ogg"
  else if p.endsWith ".ts" then "mpegts"
  else if p.endsWith ".mkv" then "mkv"
  else if p.endsWith ".avi" then "avi"
  else "unknown"

def scan (args : List String) : Option Invocation := do
  let mut job : Invocation := {}
  let mut pending : Input := { path := "", format := "" }
  let mut fmt := ""
  let mut explicitVideo := false
  let mut explicitAudio := false
  let mut pendingInputOptions := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "-i" :: path :: xs =>
      if job.output != "" then none
      let input := { pending with path := path, format := if fmt == "" then inferFormat path else fmt }
      job := { job with inputs := job.inputs.push input }
      pending := { path := "", format := "" }
      pendingInputOptions := false
      fmt := ""
      rest := xs
    | "-f" :: value :: xs =>
      fmt := value
      rest := xs
    | "-s" :: value :: xs =>
      if job.output != "" then none
      let [w, h] := value.splitOn "x" | none
      let w ← w.toNat?
      let h ← h.toNat?
      pending := { pending with width := w, height := h }
      pendingInputOptions := true
      rest := xs
    | "-pix_fmt" :: value :: xs =>
      if value != "yuv420p" then none
      rest := xs
    | "-c:v" :: value :: xs =>
      if !["h264", "hevc", "av1", "prores", "ffv1", "rawvideo", "wrapped_avframe"].contains value then none
      explicitVideo := true
      job := { job with options := { job.options with videoCodec := value } }
      rest := xs
    | "-c:a" :: value :: xs =>
      if !["aac", "opus", "flac", "pcm_u8", "pcm_s16le", "pcm_s24le", "pcm_s32le", "copy"].contains value then none
      explicitAudio := true
      job := { job with options := { job.options with audioCodec := value } }
      rest := xs
    | "-filter_complex" :: value :: xs =>
      if job.options.filterComplex != "" then none
      job := { job with options := { job.options with filterComplex := value } }
      rest := xs
    | "-map" :: value :: xs =>
      job := { job with options := { job.options with maps := job.options.maps.push value } }
      rest := xs
    | "-vf" :: value :: xs =>
      job := { job with options := { job.options with videoFilter := value } }
      rest := xs
    | "-af" :: value :: xs =>
      job := { job with options := { job.options with audioFilter := value } }
      rest := xs
    | "-frames:v" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 then none
      job := { job with options := { job.options with maxFrames := some n } }
      rest := xs
    | "-crf" :: value :: xs =>
      let n ← value.toNat?
      if n > 51 then none
      job := { job with options := { job.options with qp := n } }
      rest := xs
    | "-qp" :: value :: xs =>
      let n ← value.toNat?
      if n > 255 then none
      job := { job with options := { job.options with qp := n } }
      rest := xs
    | "-ar" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 192000 || job.output != "" then none
      pending := { pending with sampleRate := n.toUInt32 }
      pendingInputOptions := true
      rest := xs
    | "-ac" :: value :: xs =>
      let n ← value.toNat?
      if n == 0 || n > 8 || job.output != "" then none
      pending := { pending with channels := n }
      pendingInputOptions := true
      rest := xs
    | "-tile-columns" :: value :: xs =>
      let n ← value.toNat?
      if n > 6 then none
      job := { job with options := { job.options with av1TileColumns := n } }
      rest := xs
    | "-tile-rows" :: value :: xs =>
      let n ← value.toNat?
      if n > 6 then none
      job := { job with options := { job.options with av1TileRows := n } }
      rest := xs
    | "-x265-params" :: value :: xs =>
      let mut log2Ctb := job.options.log2Ctb
      let mut tileColumns := job.options.tileColumns
      let mut tileRows := job.options.tileRows
      for item in value.splitOn ":" do
        let [k, v] := item.splitOn "=" | none
        if k == "ctu" then
          let n ← v.toNat?
          log2Ctb ← if n == 16 then some 4 else if n == 32 then some 5 else if n == 64 then some 6 else none
        else if k == "tiles" then
          let [cols, rows] := v.splitOn "x" | none
          let cols ← cols.toNat?
          let rows ← rows.toNat?
          if cols == 0 || rows == 0 || cols > 8 || rows > 8 then none
          tileColumns := cols
          tileRows := rows
        else none
      job := { job with options := { job.options with log2Ctb := log2Ctb, tileColumns := tileColumns, tileRows := tileRows } }
      rest := xs
    | "-an" :: xs =>
      job := { job with options := { job.options with noAudio := true } }
      rest := xs
    | "-vn" :: xs =>
      job := { job with options := { job.options with noVideo := true } }
      rest := xs
    | flag :: value :: xs =>
      if flag == "-loglevel" || flag == "-v" then
        if !LeanAV.Cli.supportedLogLevel value then none
        rest := xs
      else if ["-y", "-n", "-json", "-hide_banner", "-nostdin"].contains flag then
        rest := value :: xs
      else if flag.startsWith "-" && flag != "-" then none
      else
        if job.output != "" then none
        job := { job with output := flag }
        rest := value :: xs
    | [flag] =>
      if ["-y", "-n", "-json", "-hide_banner", "-nostdin"].contains flag then rest := []
      else if flag.startsWith "-" && flag != "-" then none
      else
        if job.output != "" then none
        job := { job with output := flag }
        rest := []
    | [] => pure ()
  if job.inputs.isEmpty || job.output == "" || pendingInputOptions then none
  if (job.inputs.size > 1 || !job.options.maps.isEmpty) && job.options.filterComplex == "" then none
  let outputFormat := if fmt == "" then inferFormat job.output else fmt
  if outputFormat == "unknown" || (job.output == "-" && outputFormat != "null") then none
  if !explicitVideo && (job.options.videoFilter != "" || job.options.filterComplex != "") &&
     outputFormat != "null" && outputFormat != "rawvideo" && outputFormat != "md5" && outputFormat != "framemd5" &&
     outputFormat != "ogg" && outputFormat != "opus" && outputFormat != "wav" && outputFormat != "s16le" &&
     outputFormat != "s24le" && outputFormat != "s32le" && outputFormat != "flac" && outputFormat != "adts" then none
  let options := { job.options with
    format := outputFormat
    videoCodec := if explicitVideo then job.options.videoCodec
      else if outputFormat == "rawvideo" || outputFormat == "null" || outputFormat == "md5" || outputFormat == "framemd5" then "rawvideo"
      else job.options.videoCodec
    audioCodec := if explicitAudio then job.options.audioCodec
      else if outputFormat == "ogg" || outputFormat == "opus" then "opus"
      else if outputFormat == "wav" then ""
      else if outputFormat == "s16le" || outputFormat == "null" then "pcm_s16le"
      else if outputFormat == "s24le" then "pcm_s24le"
      else if outputFormat == "s32le" then "pcm_s32le"
      else if outputFormat == "flac" then "flac" else job.options.audioCodec }
  some { job with options := options }

example : rawVideoGateSpec.gate (2, 2, 6) = true := by decide
example : rawVideoGateSpec.gate (2, 2, 7) = false := by decide
example : rawVideoGateSpec.gate (0, 2, 6) = false := by decide
example : rawVideoGateSpec.gate (3, 2, 9) = false := by decide
example : rawVideoGateSpec.gate (2, 2, 0) = false := by decide

end LeanAV.UnifiedPipeline
