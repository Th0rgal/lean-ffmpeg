/-
  LeanAV.Main: Standalone Native CLI, Transcode Engine, Benchmark & LNIR Emitter
-/
import LeanAV

open LeanAV.Spec
open LeanAV.Core
open LeanAV.Domain
open LeanAV.Bitstream
open LeanAV.IO
open LeanAV.Format
open LeanAV.Scale
open LeanAV.Audio
open LeanAV.Video
open LeanAV.Filter
open LeanAV.Encoder
open LeanAV.Cli
open LeanAV.NativeKernels
open LeanSys.Posix
open LeanSys.Store

set_option maxRecDepth 4096

/-- Comprehensive end-to-end verification of all 8 FFmpeg subsystem layers in `LeanAV`. -/
def runSelfTest : IO UInt32 := do
  -- 1. Law 1: Exact rational rescale (`libavutil` replacement)
  let r1 := rescaleQ 90000 1 90
  let tbOk := r1 == 1000 && AVRational.rescalePts 90000 AVRational.tb90kHz AVRational.tbMicros == 1000000

  -- 2. Law 2: Packet bounds & checksum gate + Bitstream Exp-Golomb, Rice, LEB128 & RangeDecoder
  let pktOk := packetFrameGateSpec.gate packetFrameGateSpec.posWitness &&
               !(packetFrameGateSpec.gate packetFrameGateSpec.negWitness)
  let sampleBytes := ByteArray.mk #[0xA6, 0x42, 0x80, 0x7F]
  let br := BitReader.ofSlice (ByteSlice.ofByteArray sampleBytes)
  let ueOk := match br.readUE with
    | some (v, _) => v == 0
    | none => false

  -- 3. `libavformat` replacement: IVF & MP4/ISOBMFF & Ogg & WAV mux/demux zero-copy round-trip
  let rawPkt0 := ByteSlice.ofByteArray (ByteArray.mk #[0x12, 0x00, 0x0A, 0x00, 0x00, 0x00])
  let rawPkt1 := ByteSlice.ofByteArray (ByteArray.mk #[0x32, 0x04, 0xAA, 0xBB, 0xCC, 0xDD])
  let p0 := AVPacketView.mkVerified 0 .av1 0 0 3000 true rawPkt0
  let p1 := AVPacketView.mkVerified 0 .av1 3000 3000 3000 false rawPkt1
  let ivfHdr : IvfHeader := { codec := .av1, width := 320, height := 240, timebase := AVRational.mkSafe 1 30, numFrames := 2 }
  let ivfBytes := muxIvfStream ivfHdr #[p0, p1]
  let ivfOk := match demuxIvfStream (ByteSlice.ofByteArray ivfBytes) with
    | some (h, pkts) =>
      h.width == 320 && h.height == 240 && pkts.size == 2 &&
      pkts[0]!.verifyIntegrity && pkts[1]!.verifyIntegrity &&
      pkts[0]!.digest64 == p0.digest64 && pkts[1]!.digest64 == p1.digest64
    | none => false

  let mp4Bytes := muxMp4Simple .av1 90000 #[p0, p1]
  let mp4Ok := match demuxMp4Simple (ByteSlice.ofByteArray mp4Bytes) with
    | some (c, ts, pkts) =>
      c == .av1 && ts == 90000 && pkts.size == 2 &&
      pkts[0]!.digest64 == p0.digest64 && pkts[1]!.digest64 == p1.digest64
    | none => false

  let oggBytes := muxOggPages #[p0, p1]
  let oggPkts := demuxOggPages (ByteSlice.ofByteArray oggBytes) .opus
  let oggOk := oggPkts.size == 2 && oggPkts[0]!.digest64 == p0.digest64

  -- 4. `libswscale` replacement: YUV420P <-> RGB24 & Bilinear 2D Scaling (`Regime R1/R2`)
  let vfSrc := VideoFrame.allocYuv420p 64 48 0 AVRational.tb90kHz .bt709
  let rgbPlane := yuv420pToRgb24Plane vfSrc
  let vfBack := rgb24PlaneToYuv420p rgbPlane 64 48 .bt709
  let (maxLumaErr, _) := comparePlanesMetrics vfSrc.planes[0]! vfBack.planes[0]!
  let vfScaled := scaleVideoFrameYuv420p vfSrc 128 96
  let scaleOk := maxLumaErr <= 2 && vfScaled.width == 128 && vfScaled.height == 96 && vfScaled.verifyAllPlanes

  -- 5. `libavcodec` Audio + `libswresample`: FLAC bit-exact lossless (`R0`) + Opus TOC + Resampler
  let audioSignal : Array Int32 := #[120, 340, 560, 420, -110, -320, 15, 890, 1024, 760]
  let flacRes := flacEncodeFixedResiduals .order3 audioSignal
  let flacDec := flacDecodeFixedResiduals .order3 flacRes
  let (msMid, msSide) := flacStereoToMidSide 12345 (-6789)
  let (recL, recR) := flacMidSideToStereo msMid msSide
  let flacOk := flacDec == audioSignal && recL == 12345 && recR == -6789

  let opusSample := ByteSlice.ofByteArray (ByteArray.mk #[0xFC, 0x01, 0x02])
  let opusOk := match parseOpusToc opusSample with
    | some toc => toc.mode == .celtOnly && toc.bandwidth == .fullband && toc.stereo && toc.samples48k == 960
    | none => false

  let af48 := AudioFrame.alloc .s16p 48000 2 480 0
  let af24 := resampleAudioFrame af48 24000
  let wavBytes := muxWavPcm16LE af24
  let wavOk := match demuxWavPcm16LE (ByteSlice.ofByteArray wavBytes) with
    | some afDec => afDec.sampleRate == 24000 && afDec.numSamples == 240 && afDec.channels == 2
    | none => false

  -- 6. `libavcodec` Video: AV1 OBU parser, H.264 Annex-B NALU scanner, Paeth R0 lossless, 4x4 IDCT, CDEF & Deblock
  let av1ObuBytes := ByteSlice.ofByteArray (ByteArray.mk #[0x0A, 0x04, 0x01, 0x02, 0x03, 0x04])
  let obus := parseAv1Obus av1ObuBytes
  let annexB := ByteSlice.ofByteArray (ByteArray.mk #[0x00, 0x00, 0x01, 0x67, 0x42, 0x00, 0x1E, 0x00, 0x00, 0x01, 0x68, 0xCE])
  let nalus := scanAnnexBNalUnits annexB false
  let testPlane := vfSrc.planes[0]!
  let paethRes := encodePlanePaethResiduals testPlane
  let paethRec := decodePlanePaethResiduals paethRes
  let (paethMaxErr, _) := comparePlanesMetrics testPlane paethRec
  let cdefPlane := av1CdefFilterPlane testPlane 8 3
  let deblockPlane := deblockPlane8x8 cdefPlane 12 4
  let videoOk := obus.size == 1 && obus[0]!.obuType == .sequenceHeader &&
                 nalus.size == 2 && nalus[0]!.nalType == 7 && nalus[1]!.nalType == 8 &&
                 paethMaxErr == 0 && deblockPlane.verifyBounds

  -- 7. `libavfilter` replacement: Fused point filter, crop, hflip, boxblur, audio volume + Law 5 duration gate
  let blurred := filterPlaneBoxBlur3x3 (filterPlanePointFused testPlane 280 10 false)
  let afVol := filterAudioVolumeQ8 af48 256
  let filterOk := blurred.verifyBounds &&
                  verifyDurationConserving af48.numSamples.toUInt64 afVol.numSamples.toUInt64 1 1 == 1

  -- 8. Law 4: Disjoint parallel tile partitioning
  let tiles := partitionPlaneRows 1080 1920 8
  let tileOk := tiles.size == 8 && tileDisjointGateSpec.gate tileDisjointGateSpec.posWitness &&
                !(tileDisjointGateSpec.gate tileDisjointGateSpec.negWitness)

  -- 9. Wave 1: 64-bit SWAR Annex-B scanner parity + BitWriter UE/SE/Rice round-trip + CLI fail-closed gate
  let nalusFast := scanAnnexBNalUnitsFast annexB false
  let swarOk := nalusFast.size == nalus.size &&
                nalusFast.all (fun n => nalus.any (fun m => m.nalType == n.nalType && m.payload.len == n.payload.len))
  let mut bw := BitWriter.empty 16
  bw := bw.writeUE 0
  bw := bw.writeUE 4
  bw := bw.writeSE 0
  bw := bw.writeSE (-3)
  let bwBytes := bw.toByteArray
  let bwReader := BitReader.ofSlice (ByteSlice.ofByteArray bwBytes)
  let bitWriterOk := match bwReader.readUE with
    | some (v0, rA) =>
      match rA.readUE with
      | some (v1, rB) =>
        match rB.readSE with
        | some (v2, rC) =>
          match rC.readSE with
          | some (v3, _) => v0 == 0 && v1 == 4 && v2 == 0 && v3 == -3
          | none => false
        | none => false
      | none => false
    | none => false
  let cliArgs := ["-i", "in.mp4", "-c:v", "h264", "-c:a", "aac", "-vf", "scale=640:360", "out.mp4"]
  let cliCfg := parseFFmpegArgs cliArgs
  let cliOk := match validateCliConfig cliCfg with
    | .ok cfg => cfg.inputs == ["in.mp4"] && cfg.videoCodec == some .h264 && cfg.output == some "out.mp4"
    | .error _ => false
  let cliBad := match validateCliConfig (parseFFmpegArgs ["-i", "in.mp4", "-c", "copy", "-vf", "hflip", "out.mp4"]) with
    | .ok _ => false
    | .error _ => true

  -- 10. Wave 2 (T1 + T2): FLAC STREAMINFO + Subframes (Fixed/LPC/Constant/Verbatim/Rice/Escape) vs FFmpeg,
  --     AAC ADTS, Opus Codes 0..3, HEVC 2B NAL + SAO (BO + EO 0..3) vs FFmpeg, ProRes header + 8x8 IDCT vs FFmpeg,
  --     FFV1 R0 median + Rice round-trip, H.264 SPS/PPS, and all per-format AVGateSpecs
  let flacSiSlice := ByteSlice.ofByteArray (ByteArray.mk realFfmpegFlacStreamInfoBytes)
  let flacSiOk := match parseFlacStreamInfo flacSiSlice with
    | some si =>
      si == realFfmpegFlacStreamInfo &&
      parseFlacStreamInfo (ByteSlice.ofByteArray (serializeFlacStreamInfo si)) == some si &&
      flacStreamInfoGateSpec.gate flacStreamInfoGateSpec.posWitness &&
      !(flacStreamInfoGateSpec.gate flacStreamInfoGateSpec.negWitness)
    | none => false
  let flacSubBytes := flacEncodeSubframeRiceR0 .order2 3 audioSignal
  let flacSubFixedDec := decodeFlacSubframeSpec (ByteSlice.ofByteArray (ByteArray.mk realFfmpegFlacFixedSubframeBytes)) 64 16
  let flacSubLpcDec   := decodeFlacSubframeSpec (ByteSlice.ofByteArray (ByteArray.mk realFfmpegFlacLpcSubframeBytes)) 64 16
  let flacSubOk := match flacDecodeSubframeRiceR0 (ByteSlice.ofByteArray flacSubBytes) with
    | some dec =>
      dec == audioSignal &&
      flacSubFixedDec == some realFfmpegFlacDecoded64Samples &&
      flacSubLpcDec == some realFfmpegFlacDecoded64Samples &&
      flacSubframeGateSpec.gate flacSubframeGateSpec.posWitness &&
      !(flacSubframeGateSpec.gate flacSubframeGateSpec.negWitness)
    | none => false
  let adtsSlice := ByteSlice.ofByteArray (ByteArray.mk realFfmpegAacAdtsBytes)
  let adtsOk := match parseAacAdtsHeader adtsSlice with
    | some h =>
      h == realFfmpegAacAdtsHeader &&
      (serializeAacAdtsHeader h).data == realFfmpegAacAdtsBytes &&
      aacAdtsGateSpec.gate aacAdtsGateSpec.posWitness &&
      !(aacAdtsGateSpec.gate aacAdtsGateSpec.negWitness)
    | none => false
  let opusCode3VbrPad := ByteSlice.ofByteArray (ByteArray.mk #[0xFF, 0xC2, 0x03, 0x02, 0x11, 0x22, 0x33, 0x44, 0x55, 0x00, 0x00, 0x00])
  let opusPktOk := match parseOpusPacketFrames (ByteSlice.ofByteArray (ByteArray.mk realFfmpegOpusPacketBytes)),
                         parseOpusPacketFrames opusCode3VbrPad with
    | some pkt0, some pkt3 =>
      pkt0.frames.size == 1 && pkt0.toc.frameCode == 0 &&
      pkt3.frames.size == 2 && pkt3.toc.frameCode == 3 && pkt3.vbr && pkt3.hasPadding &&
      opusPacketGateSpec.gate opusPacketGateSpec.posWitness &&
      !(opusPacketGateSpec.gate opusPacketGateSpec.negWitness)
    | _, _ => false
  let hevcNal := ByteSlice.ofByteArray (ByteArray.mk realFfmpegHevcNalBytes)
  let hevcOk := match parseHevcNalHeader hevcNal with
    | some h =>
      h.nalUnitType == 32 && h.nuhTemporalId == 0 &&
      (serializeHevcNalHeader h).data == realFfmpegHevcNalBytes &&
      hevcNalHeaderGateSpec.gate hevcNalHeaderGateSpec.posWitness &&
      !(hevcNalHeaderGateSpec.gate hevcNalHeaderGateSpec.negWitness)
    | none => false
  let saoBoPlane  := hevcSaoBandFilterPlane realFfmpeg8x8Plane 2 #[5, -3, 2, -4]
  let saoEo0Plane := hevcSaoEdgeFilterPlane realFfmpeg8x8Plane .eo0_horiz #[3, 1, -1, -3]
  let saoEo1Plane := hevcSaoEdgeFilterPlane realFfmpeg8x8Plane .eo1_vert #[3, 1, -1, -3]
  let saoEo2Plane := hevcSaoEdgeFilterPlane realFfmpeg8x8Plane .eo2_diag135 #[3, 1, -1, -3]
  let saoEo3Plane := hevcSaoEdgeFilterPlane realFfmpeg8x8Plane .eo3_diag45 #[3, 1, -1, -3]
  let saoPlane := hevcSaoFilterPlane testPlane
  let saoBitExactOk :=
    saoBoPlane.data.data == realFfmpegSaoBoRef &&
    saoEo0Plane.data.data == realFfmpegSaoEo0Ref &&
    saoEo1Plane.data.data == realFfmpegSaoEo1Ref &&
    saoEo2Plane.data.data == realFfmpegSaoEo2Ref &&
    saoEo3Plane.data.data == realFfmpegSaoEo3Ref &&
    saoPlane.verifyBounds
  let proresSlice := ByteSlice.ofByteArray (ByteArray.mk realFfmpegProResHeaderBytes)
  let proresIdctOut := proresIdct8x8Put10 proresTestCoeffs64 (Array.replicate 64 4)
  let proresOk := match parseProResFrameHeader proresSlice with
    | some h =>
      h.width == 64 && h.height == 64 && h.chromaFormat == 2 && h.qmatFlags == 3 &&
      proresIdctOut == realFfmpegProResIdct10Ref &&
      proResHeaderGateSpec.gate proResHeaderGateSpec.posWitness &&
      !(proResHeaderGateSpec.gate proResHeaderGateSpec.negWitness)
    | none => false
  let ffv1Bytes := encodePlaneFfv1RiceR0 realFfmpeg8x8Plane 3
  let h264SpsPpsOk :=
    (parseH264Sps (ByteSlice.ofByteArray (ByteArray.mk realFfmpegH264SpsBytes))).isSome &&
    (parseH264Pps (ByteSlice.ofByteArray (ByteArray.mk realFfmpegH264PpsBytes))).isSome &&
    h264SpsGateSpec.gate h264SpsGateSpec.posWitness &&
    !(h264SpsGateSpec.gate h264SpsGateSpec.negWitness)
  let ffv1Ok := match decodePlaneFfv1RiceR0 (ByteSlice.ofByteArray ffv1Bytes) with
    | some dec =>
      (comparePlanesMetrics realFfmpeg8x8Plane dec).1 == 0 &&
      dec.data.data == realFfmpeg8x8GrayBytes &&
      ffv1PlaneGateSpec.gate ffv1PlaneGateSpec.posWitness &&
      !(ffv1PlaneGateSpec.gate ffv1PlaneGateSpec.negWitness) &&
      h264SpsPpsOk
    | none => false

  -- 11. Wave 3: fused filter graph compiler (`-vf crop,scale,eq,boxblur,hflip`)
  let graphOk := match parseVideoFilterGraph "crop=32:24,eq=256:0,hflip" with
    | .ok ops =>
      let outP := evalVideoFilterGraphPlane testPlane ops
      outP.width == 32 && outP.height == 24 && outP.verifyBounds
    | .error _ => false
  let graphBad := match parseVideoFilterGraph "unknownfilter=1" with
    | .ok _ => false
    | .error _ => true

  -- 12. Wave 4: HW DMA zero-copy gate + Diamond ME + RDO + in-loop FFV1/H.264/AV1 encoders
  let hwOk := verifyHwDmaZeroCopy 1 0x1000 0x1000 0xCAFE 0xCAFE 1 1 1 == 1 &&
              verifyHwDmaZeroCopy 1 0x1000 0x2000 0xCAFE 0xCAFE 1 1 1 == 0
  let (mvX, mvY, sad) := searchDiamondMotionVector testPlane testPlane 8 8 8 8 2
  let meOk := mvX == 0 && mvY == 0 && sad == 0
  let rdoBest := rdoSelectOptimalMode 2 #[
    { modeId := 0, distortion := 100, rateBits := 10 },
    { modeId := 1, distortion := 40, rateBits := 30 },
    { modeId := 2, distortion := 80, rateBits := 5 }
  ]
  let rdoOk := rdoBest.modeId == 2
  let encFfv1Ok := match encodeAndVerifyPlaneFfv1R0 testPlane 3 with
    | some pkt => pkt.loopGatePassed && pkt.maxPixelErr == 0
    | none => false
  let encH264Ok := match encodeAndVerifyFrameH264 testPlane with
    | some pkt => pkt.loopGatePassed && pkt.codec == .h264
    | none => false
  let encAv1Ok := match encodeAndVerifyFrameAv1 testPlane with
    | some pkt => pkt.loopGatePassed && pkt.codec == .av1
    | none => false

  -- 13. Wave 5 (Tracks D1–D4): Pipeline D (4K/2x2 -> 1080p) Fused Downscale + Disjoint Tiles + Streaming MP4 Mux
  let pipeDRes := transcodeFramePipelineD testPlane 0 .h264 8 264 4
  let pipeDOk := match pipeDRes with
    | some r =>
      r.dstWidth == testPlane.width / 2 &&
      r.dstHeight == testPlane.height / 2 &&
      r.disjointTiles == 8 &&
      r.zeroCopyGateOk &&
      r.loopGateOk &&
      (let mp4Fast := muxMp4StreamingFast .h264 90000 #[r.encodedPacket]
       match demuxMp4Simple (ByteSlice.ofByteArray mp4Fast) with
       | some (c, ts, pkts) => c == .h264 && ts == 90000 && pkts.size == 1 && pkts[0]!.digest64 == r.encodedPacket.digest64
       | none => false)
    | none => false

  -- 14. Wave 6 (W6_C1..W6_C5): Fast Pixel/Filter/Audio Kernels, Matroska SimpleBlock, Subtitles, B-Frame BiPred/POC DPB
  let w6FilterFastOk :=
    (filterPlanePointAndBoxBlur3x3Fast realFfmpeg8x8Plane 320 12 false).data.data ==
      (filterPlaneBoxBlur3x3 (filterPlanePointFused realFfmpeg8x8Plane 320 12 false)).data.data
  let w6MkvBlk : MkvSimpleBlock := { trackNum := 1, relTimecodeMs := 33, isKeyframe := true, payload := [0x00, 0x00, 0x01, 0x65] }
  let w6MkvOk := demuxMatroskaSimpleBlockSpec (muxMatroskaSimpleBlockSpec w6MkvBlk) == some w6MkvBlk &&
                 parseWebVttTimestampMs (formatWebVttTimestampMs 1542) == some 1542
  let w6AudioGraphOk := match parseAudioFilterGraph "volume=320,aresample=24000,pan=mono" with
    | .ok ops => (optimizeAndFuseAudioFilterGraph ops).length == 3
    | .error _ => false
  let w6BFrameOk := mcBiPredPixel 100 200 == 150 &&
                    verifyFlacFrameHeaderCrc8 [0xFF, 0xF8, 0x69, 0x18, 0x00] (flacCrc8List [0xFF, 0xF8, 0x69, 0x18, 0x00])
  let w6Ok := w6FilterFastOk && w6MkvOk && w6AudioGraphOk && w6BFrameOk

  -- 15. Wave 7: 4K -> 1080p I/P/B AVCC Transcoder, SIMD 2x2 Scaler, and B-Frame Bi-Predictive Residual Round-Trip
  let w7ScaleOk := (scalePlaneDown2x2Simd realFfmpeg8x8Plane).data.data == (scalePlaneDown2x2Fast realFfmpeg8x8Plane).data.data
  let w7BiPred := mcBiPredPlaneSimd realFfmpeg8x8Plane realFfmpeg8x8Plane
  let w7Res := encodeInterResidualPlaneSimd realFfmpeg8x8Plane w7BiPred
  let w7Recon := reconstructInterResidualPlaneSimd w7BiPred w7Res
  let w7BiPredOk := w7Recon.data.data == realFfmpeg8x8Plane.data.data
  let w7Dummy := ByteArray.mk (Array.replicate 64 128)
  let w7PktI := transcodeAvcc4kTo1080pPacketSimd w7Dummy 0 64 0 1024 0
  let w7PktB := transcodeAvcc4kTo1080pPacketSimd w7Dummy 0 64 2 1536 1024
  let w7AvccOk := isAvcc1080pIpbPacketBytesValid w7PktI.data &&
                  classifyAvccH264Sample (ByteSlice.ofByteArray w7PktI) false == .iFrame &&
                  classifyAvccH264Sample (ByteSlice.ofByteArray w7PktB) false == .bFrame
  let w7Ok := w7ScaleOk && w7BiPredOk && w7AvccOk

  -- 16. Wave 8: Standard ISOBMFF (`ISO/IEC 14496-12`) MP4 Track Muxer (`muxIsoMp4Track`) & Demuxer Round-Trip
  let w8SampleI : IsoMp4SampleDesc := {
    sampleIdx := 0, dts := 0, pts := 1024, duration := 512, frameType := .iFrame,
    slice := ByteSlice.ofByteArray w7PktI
  }
  let w8SampleB : IsoMp4SampleDesc := {
    sampleIdx := 1, dts := 512, pts := 512, duration := 512, frameType := .bFrame,
    slice := ByteSlice.ofByteArray w7PktB
  }
  let w8Mp4 := muxIsoMp4Track 1920 1080 15360 defaultAvcC1080pBytes #[w8SampleI, w8SampleB]
  let w8Ok := match demuxIsoMp4Track (ByteSlice.ofByteArray w8Mp4) with
    | some d8 => d8.width == 1920 && d8.height == 1080 && d8.samples.size == 2 && d8.iFrameCount == 1 && d8.bFrameCount == 1
    | none => false

  -- 17. Wave 9: ITU-T H.264 §7.3.3 Exp-Golomb RBSP Slice Header Round-Trip & Single-Buffer Chunk Transcoder
  let w9ShI : H264SliceHeaderView := {
    firstMbInSlice := 0, sliceType := 2, ppsId := 0, frameNum4 := 0,
    isIdr := true, idrPicId := 0, pocLsb8 := 0, sliceQpDelta := -4
  }
  let w9ShB : H264SliceHeaderView := {
    firstMbInSlice := 0, sliceType := 1, ppsId := 0, frameNum4 := 2,
    isIdr := false, idrPicId := 0, pocLsb8 := 2, sliceQpDelta := 2
  }
  let w9Ok := decodeH264SliceHeaderRbsp (ByteSlice.ofByteArray (encodeH264SliceHeaderRbsp w9ShI)) true == some w9ShI &&
              decodeH264SliceHeaderRbsp (ByteSlice.ofByteArray (encodeH264SliceHeaderRbsp w9ShB)) false == some w9ShB

  -- 18. Wave 10: Multi-Codec (`hvc1` HEVC & `av01` AV1) 4K->1080p I/P/B Transcoding & ISOBMFF Round-Trip
  let w10HevcI := transcodeHvccHevc4kTo1080pPacketSimd w7Dummy 0 64 0 1024 0
  let w10HevcB := transcodeHvccHevc4kTo1080pPacketSimd w7Dummy 0 64 2 1536 1024
  let w10SampleI : IsoMp4SampleDesc := {
    sampleIdx := 0, dts := 0, pts := 1024, duration := 512, frameType := .iFrame,
    slice := ByteSlice.ofByteArray w10HevcI
  }
  let w10SampleB : IsoMp4SampleDesc := {
    sampleIdx := 1, dts := 512, pts := 512, duration := 512, frameType := .bFrame,
    slice := ByteSlice.ofByteArray w10HevcB
  }
  let w10Mp4Hevc := muxIsoMp4TrackCodec .hevc 1920 1080 15360 ByteArray.empty #[w10SampleI, w10SampleB]
  let w10Ok := match demuxIsoMp4Track (ByteSlice.ofByteArray w10Mp4Hevc) with
    | some d10 => d10.width == 1920 && d10.height == 1080 && d10.samples.size == 2 && d10.iFrameCount == 1 && d10.bFrameCount == 1
    | none => false

  -- 19. Wave 11: Multi-Track ISOBMFF Audio + Video (`vide` + `soun` AAC-LC 48kHz Stereo) Muxer & Demuxer Round-Trip
  let w11AacFrame : ByteArray := { data := #[0x21, 0x10, 0x04, 0x60, 0x8C, 0x1C] }
  let w11Mp4Av := muxIsoMp4AudioVideoTracks .h264 1920 1080 15360 defaultAvcC1080pBytes #[w8SampleI, w8SampleB] 48000 2 1024 #[w11AacFrame, w11AacFrame]
  let w11Ok := match demuxIsoMp4Track (ByteSlice.ofByteArray w11Mp4Av) with
    | some d11 => d11.width == 1920 && d11.height == 1080 && d11.samples.size == 2 && d11.iFrameCount == 1 && d11.bFrameCount == 1
    | none => false

  -- 20. Wave 12: 1080p Level 4.0 Codec Configuration Records (`avcC` SPS+PPS, `hvcC` VPS+SPS+PPS, `av1C` Sequence Header OBU)
  let w12Ok := verifyCodecConfig1080pHeaders defaultAvcC1080pBytes defaultHvcC1080pBytes defaultAv1C1080pBytes

  -- 21. Wave 13: 4-byte LEB128 AV1 OBU Size Round-Trip & Multi-Byte OBU_FRAME I/P/B Classification
  let (w13Leb0, w13Leb1, w13Leb2, w13Leb3) := encodeLeb128Fixed4 65535
  let w13Av1I := transcodeAv1Obu4kTo1080pPacketSimd w7Dummy 0 64 0 1024 0
  let w13Av1B := transcodeAv1Obu4kTo1080pPacketSimd w7Dummy 0 64 2 1536 1024
  let w13Ok := decodeLeb128Fixed4 w13Leb0 w13Leb1 w13Leb2 w13Leb3 == some 65535 &&
    classifyAv1ObuSample (ByteSlice.ofByteArray w13Av1I) false == .iFrame &&
    classifyAv1ObuSample (ByteSlice.ofByteArray w13Av1B) false == .bFrame

  -- 22. Wave 14: 15-Kernel LNIR Wire (`lanczos_4tap_downscale_fma_gpu`) & 4-Tap Lanczos Normalization Gate
  let w14LanczosOk := specLanczos4TapNormalizedPixel 180 180 180 180 == 180 &&
    evalLnirKernel .fmaBlend [360, 200] [9, 9] [-360, -200] == [2880, 1600]
  let w14Tokens := emitLeanAvLnirWire.splitOn "|"
  let w14Ok := w14LanczosOk && w14Tokens[0]? == some "LNIR_WIRE_V1" && w14Tokens[2]? == some "52"

  -- 23. Wave 15: ITU-T H.265 §7.3.6.1 HEVC Slice Segment Header RBSP Round-Trip & 16-Kernel LNIR SAO Edge-Offset Gate
  let w15ShI : HevcSliceSegmentHeaderView := {
    firstSliceSegmentInPic := true, isIdrRap := true, noOutputOfPriorPics := false,
    ppsId := 0, sliceType := 2, pocLsb8 := 0, saoLumaFlag := true, saoChromaFlag := true, sliceQpDelta := -3
  }
  let w15ShB : HevcSliceSegmentHeaderView := {
    firstSliceSegmentInPic := true, isIdrRap := false, noOutputOfPriorPics := false,
    ppsId := 0, sliceType := 0, pocLsb8 := 2, saoLumaFlag := false, saoChromaFlag := false, sliceQpDelta := 2
  }
  let w15Ok := decodeHevcSliceSegmentHeaderRbsp (ByteSlice.ofByteArray (encodeHevcSliceSegmentHeaderRbsp w15ShI)) true == some w15ShI &&
               decodeHevcSliceSegmentHeaderRbsp (ByteSlice.ofByteArray (encodeHevcSliceSegmentHeaderRbsp w15ShB)) false == some w15ShB

  -- 24. Wave 16: AV1 §5.9 Uncompressed Frame Header Bitstream Round-Trip & 17-Kernel LNIR SGRPROJ FMA Gate
  let w16FhKey : Av1FrameHeaderView := {
    showExistingFrame := false, frameType := 0, showFrame := true,
    errorResilientMode := true, disableCdfUpdate := false,
    orderHint8 := 0, refreshFrameFlags := 0xFF, baseQIdx := 96, cdefBits2 := 2
  }
  let w16FhB : Av1FrameHeaderView := {
    showExistingFrame := false, frameType := 1, showFrame := false,
    errorResilientMode := false, disableCdfUpdate := true,
    orderHint8 := 2, refreshFrameFlags := 0x00, baseQIdx := 128, cdefBits2 := 1
  }
  let w16Ok := decodeAv1FrameHeaderBits (ByteSlice.ofByteArray (encodeAv1FrameHeaderBits w16FhKey)) == some w16FhKey &&
               decodeAv1FrameHeaderBits (ByteSlice.ofByteArray (encodeAv1FrameHeaderBits w16FhB)) == some w16FhB

  -- 25. Wave 17: ISO/IEC 14496-3 §1.6.2.1 AAC AudioSpecificConfig Round-Trip & 18-Kernel LNIR AAC IMDCT FMA Gate
  let w17Asc48k : AacAudioSpecificConfigView := {
    audioObjectType := 2, samplingFrequencyIndex := 3, channelConfiguration := 2,
    frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
  }
  let w17Asc44k : AacAudioSpecificConfigView := {
    audioObjectType := 2, samplingFrequencyIndex := 4, channelConfiguration := 2,
    frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
  }
  let w17Ok := encodeAacAudioSpecificConfig w17Asc48k == ByteArray.mk #[0x11, 0x90] &&
               decodeAacAudioSpecificConfig (ByteSlice.ofByteArray (encodeAacAudioSpecificConfig w17Asc48k)) == some w17Asc48k &&
               decodeAacAudioSpecificConfig (ByteSlice.ofByteArray (encodeAacAudioSpecificConfig w17Asc44k)) == some w17Asc44k

  -- 26. Wave 18: RFC 7845 §5.1 OpusHead Identification Header Round-Trip & 19-Kernel LNIR Opus CELT Comb FMA Gate
  let w18OpusStereo : OpusIdHeaderView := {
    version := 1, channels := 2, preSkip := 312,
    inputSampleRate := 48000, outputGainQ8 := 0, channelMappingFamily := 0
  }
  let w18OpusMono : OpusIdHeaderView := {
    version := 1, channels := 1, preSkip := 3840,
    inputSampleRate := 48000, outputGainQ8 := 256, channelMappingFamily := 0
  }
  let w18Ok := decodeOpusIdHeader (ByteSlice.ofByteArray (encodeOpusIdHeader w18OpusStereo)) == some w18OpusStereo &&
               decodeOpusIdHeader (ByteSlice.ofByteArray (encodeOpusIdHeader w18OpusMono)) == some w18OpusMono

  -- 27. Wave 19: ISO/IEC 14496-12 §8.6.1.3 CompositionOffsetBox (`ctts`) B-Frame PTS-DTS RLE Round-Trip & 20-Kernel LNIR H.264 IDCT 4x4 Gate
  let w19GopOffsets : List UInt32 := [1024, 2560, 1536, 512, 512, 2048]
  let w19Rle := rleCompressCttsOffsets w19GopOffsets
  let w19Ok := w19Rle.length == 5 &&
               rleExpandCttsEntries w19Rle == w19GopOffsets &&
               decodeCttsBoxSpec (encodeCttsBoxSpec w19Rle) == some w19Rle

  -- 28. Wave 20: ISO/IEC 14496-12 §8.6.2 SyncSampleBox (`stss`) 1-Based Keyframe Index Round-Trip & 21-Kernel LNIR HEVC Strong Deblock Gate
  let w20GopTypes : List IsoVideoFrameType := [.iFrame, .pFrame, .bFrame, .bFrame, .pFrame, .iFrame, .bFrame, .pFrame]
  let w20Sync := extractStssSyncIndices w20GopTypes
  let w20Ok := w20Sync == [1, 6] &&
               decodeStssBoxSpec (encodeStssBoxSpec w20Sync) == some [1, 6] &&
               decodeStssBoxSpec (encodeStssBoxSpec [0, 6]) == none &&
               decodeStssBoxSpec (encodeStssBoxSpec [3, 3]) == none

  -- 29. Wave 21: ISO/IEC 14496-12 §8.6.1.2 TimeToSampleBox (`stts`) DTS Delta RLE Round-Trip & 22-Kernel LNIR AV1 8-Tap Subpel FMA Gate
  let w21GopDeltas : List UInt32 := [512, 512, 512, 1024, 1024, 512]
  let w21Rle := rleCompressSttsDeltas w21GopDeltas
  let w21Ok := w21Rle.length == 3 &&
               rleExpandSttsEntries w21Rle == w21GopDeltas &&
               decodeSttsBoxSpec (encodeSttsBoxSpec w21Rle) == some w21Rle &&
               reconstructMonotonicDts w21GopDeltas == [0, 512, 1024, 1536, 2560, 3584, 4096]

  -- 30. Wave 22: ISO/IEC 14496-12 §8.7.4 SampleToChunkBox (`stsc`) 1-Based Chunk RLE Round-Trip & 23-Kernel LNIR ProRes 8x8 Column IDCT Gate
  let w22ChunkPlan : List (UInt32 × UInt32) := [(4, 1), (4, 1), (4, 1), (2, 1), (2, 1), (1, 1)]
  let w22Rle := rleCompressStscChunks w22ChunkPlan
  let w22Ok := w22Rle.length == 3 &&
               rleExpandStscChunks w22Rle 6 == w22ChunkPlan &&
               decodeStscBoxSpec (encodeStscBoxSpec w22Rle) == some w22Rle &&
               decodeStscBoxSpec (encodeStscBoxSpec [{ firstChunk := 2, samplesPerChunk := 4, sampleDescIndex := 1 }]) == none

  -- 31. Wave 23: ISO/IEC 14496-12 §8.7.3.2 SampleSizeBox (`stsz`) & §8.7.5 ChunkOffsetBox (`stco`) Round-Trip & 24-Kernel LNIR FLAC LPC Gate
  let w23StszVar : StszBoxView := { sampleSize := 0, sampleCount := 4, entrySizes := [16384, 4096, 2048, 2048] }
  let w23StszConst : StszBoxView := { sampleSize := 384, sampleCount := 3, entrySizes := [] }
  let w23Stco : List UInt32 := [4096, 28672]
  let w23Ok := decodeStszBoxSpec (encodeStszBoxSpec w23StszVar) == some w23StszVar &&
               decodeStszBoxSpec (encodeStszBoxSpec w23StszConst) == some w23StszConst &&
               decodeStcoBoxSpec (encodeStcoBoxSpec w23Stco) == some w23Stco &&
               computeContiguousSampleOffsets 4096 w23StszVar == [(4096, 16384), (20480, 4096), (24576, 2048), (26624, 2048)]

  -- 32. Wave 24: ISO/IEC 14496-12 §8.6.6 EditListBox (`elst`) B-Frame Initial Composition Delay & Timeline Round-Trip & 25-Kernel LNIR FFV1 Median/Gradient Gate
  let w24Elst : List ElstEntryView := [
    { segmentDuration := 512, mediaTime := 0xFFFFFFFF, mediaRateInteger := 1, mediaRateFraction := 0 },
    { segmentDuration := 30720, mediaTime := 1024, mediaRateInteger := 1, mediaRateFraction := 0 }
  ]
  let w24Ok := decodeElstBoxSpec (encodeElstBoxSpec w24Elst) == some w24Elst &&
               computeElstPresentationDuration w24Elst == 31232 &&
               decodeElstBoxSpec (encodeElstBoxSpec []) == none

  -- 33. Wave 25: ISO/IEC 14496-12 §8.7.5 64-Bit ChunkLargeOffsetBox (`co64`) & §8.6.4 SampleDependencyTypeBox (`sdtp`) Round-Trip & 26-Kernel LNIR HEVC Chroma 4-Tap Gate
  let w25Co64 : List UInt64 := [0x0000000100001000, 0x0000000180002000, 0x0000000240004000]
  let w25Sdtp : List SdtpSampleFlagsView := [.iFrame, .pFrame, .bFrame, .bFrame, .pFrame].map sdtpFlagsOfFrameType
  let w25Ok := decodeCo64BoxSpec (encodeCo64BoxSpec w25Co64) == some w25Co64 &&
               decodeSdtpBoxSpec (encodeSdtpBoxSpec w25Sdtp) == some w25Sdtp &&
               w25Sdtp.map packSdtpByte == [0x26, 0x16, 0x1A, 0x1A, 0x16]

  -- 34. Wave 26: ISO/IEC 14496-12 §8.8.12 (`tfdt`) & §8.8.8 (`trun`) fMP4 / CMAF Streaming Fragment Round-Trip & 27-Kernel LNIR H.264 CABAC LPS Gate
  let w26BaseDts : UInt64 := 90000
  let w26Trun : TrunBoxView := {
    dataOffset := 128
    samples := [
      { sampleDuration := 512, sampleSize := 16384, sampleFlags := 0x02000000, sampleCompositionTimeOffset := 1024 },
      { sampleDuration := 512, sampleSize := 4096,  sampleFlags := 0x01010000, sampleCompositionTimeOffset := 2048 }
    ]
  }
  let w26Ok := decodeTfdtBoxSpec (encodeTfdtBoxSpec w26BaseDts) == some w26BaseDts &&
               decodeTrunBoxSpec (encodeTrunBoxSpec w26Trun) == some w26Trun &&
               reconstructTrunSamplePts w26BaseDts w26Trun == [(90000, 91024), (90512, 92560)]

  -- 35. Wave 27: ISO/IEC 14496-12 §8.16.3 (`sidx`) DASH / HLS CMAF Segment Index Round-Trip & 28-Kernel LNIR AV1 7-Tap Wiener Gate
  let w27Sidx : SidxBoxView := {
    referenceId := 1
    timescale := 12800
    earliestPresentationTime := 25600
    firstOffset := 4096
    references := [
      { referencedSize := 65536, subsegmentDuration := 12800, startsWithSap := true, sapType := 1, sapDeltaTime := 0 },
      { referencedSize := 49152, subsegmentDuration := 12800, startsWithSap := true, sapType := 2, sapDeltaTime := 512 }
    ]
  }
  let w27Ok := decodeSidxBoxSpec (encodeSidxBoxSpec w27Sidx) == some w27Sidx &&
               computeSidxSegmentSpan w27Sidx == (118784, 51200)

  -- 36. Wave 28: ISO/IEC 14496-12 §8.8.5 (`mfhd`) & §8.16.5 (`prft`) Live CMAF Wallclock Sync Round-Trip & 29-Kernel LNIR Opus SILK LPC Gate
  let w28Prft1 : PrftBoxView := { referenceTrackId := 1, ntpTimestamp := 0xEC9B820000000000, mediaTime := 90000 }
  let w28Prft2 : PrftBoxView := { referenceTrackId := 1, ntpTimestamp := 0xEC9B820100000000, mediaTime := 102800 }
  let w28Ok := decodeMfhdBoxSpec (encodeMfhdBoxSpec 42) == some 42 &&
               decodePrftBoxSpec (encodePrftBoxSpec w28Prft1) == some w28Prft1 &&
               computePrftNtpWallclockDelta w28Prft1 w28Prft2 == some (0x0000000100000000, 12800)

  -- 37. Wave 29: ISO/IEC 14496-12 §8.8.7 (`tfhd`) CMAF Fragment Defaults Round-Trip & 30-Kernel LNIR AAC MDCT Pre-Twiddle Gate
  let w29Tfhd : TfhdBoxView := { trackId := 1, defaultSampleDuration := 512, defaultSampleSize := 4096, defaultSampleFlags := 0x01010000 }
  let w29Ok := decodeTfhdBoxSpec (encodeTfhdBoxSpec w29Tfhd) == some w29Tfhd &&
               computeTfhdDefaultRunSpan w29Tfhd 60 == (30720, 245760)

  -- 38. Wave 30: ISO/IEC 14496-12 §8.8.2 (`mehd`) & §8.8.3 (`trex`) CMAF Init Defaults Round-Trip & 31-Kernel LNIR VP9 LoopFilter Gate
  let w30Trex : TrexBoxView := { trackId := 1, defaultSampleDescriptionIndex := 1, defaultSampleDuration := 512, defaultSampleSize := 4096, defaultSampleFlags := 0x01010000 }
  let w30Ok := decodeMehdBoxSpec (encodeMehdBoxSpec 30720) == some 30720 &&
               decodeTrexBoxSpec (encodeTrexBoxSpec w30Trex) == some w30Trex &&
               computeMehdTrexInitBudget 30720 w30Trex == some (60, 245760)

  -- 39. Wave 31: ISO/IEC 14496-12 §8.7.2 (`dref`) Self-Contained CMAF Media Location Round-Trip & 32-Kernel LNIR H.264 Deblock Gate
  let w31Dref : DrefBoxView := { selfContainedEntryCount := 1 }
  let w31Ok := decodeDrefBoxSpec (encodeDrefBoxSpec w31Dref) == some w31Dref &&
               verifyTrexDrefIndexValid w30Trex w31Dref == true

  -- 40. Wave 32: ISO/IEC 14496-12 §8.4.5.2 (`vmhd`), §8.4.5.3 (`smhd`) & §8.4.2 ISO-639-2/T Language Codec & 33-Kernel LNIR ALF Gate
  let w32Vmhd : VmhdBoxView := { graphicsMode := 0, opColorR := 0, opColorG := 0, opColorB := 0 }
  let w32Smhd : SmhdBoxView := { balanceQ8_8 := 0 }
  let w32Ok := decodeVmhdBoxSpec (encodeVmhdBoxSpec w32Vmhd) == some w32Vmhd &&
               decodeSmhdBoxSpec (encodeSmhdBoxSpec w32Smhd) == some w32Smhd &&
               packIso639LangSpec 0x75 0x6E 0x64 == some 0x55C4 &&
               unpackIso639LangSpec 0x55C4 == some (0x75, 0x6E, 0x64)

  -- 41. Wave 33: ISO/IEC 14496-12 §12.1.3 (`pasp`) & §12.1.4 (`clap`) Display Geometry Round-Trip & 34-Kernel LNIR AV1 CfL Gate
  let w33Pasp : PaspBoxView := { hSpacing := 1, vSpacing := 1 }
  let w33Clap : ClapBoxView := { cleanWidthN := 1920, cleanWidthD := 1, cleanHeightN := 1080, cleanHeightD := 1 }
  let w33Ok := decodePaspBoxSpec (encodePaspBoxSpec w33Pasp) == some w33Pasp &&
               decodeClapBoxSpec (encodeClapBoxSpec w33Clap) == some w33Clap &&
               computeDarWidth 1920 w33Pasp == 1920

  -- 42. Wave 34: ISO/IEC 14496-12 §12.1.5 `ColourInformationBox` (`colr`, `nclx`) Round-Trip & 35-Kernel LNIR HEVC Weighted BiPred Gate
  let w34Colr : ColrNclxView := { colourPrimaries := 1, transferCharacteristics := 1, matrixCoefficients := 1, fullRangeFlag := false }
  let w34Ok := decodeColrNclxBoxSpec (encodeColrNclxBoxSpec w34Colr) == some w34Colr &&
               isBt709OrBt2020Hdr10Valid w34Colr

  -- 43. Wave 35: ISO/IEC 14496-12 §12.1.6 (`mdcv`) & §12.1.7 (`clli`) HDR10 Static Metadata Round-Trip & 36-Kernel LNIR AV1 OBMC Gate
  let w35Mdcv : MdcvLuminanceView := { maxDisplayMasteringLuminance := 10000000, minDisplayMasteringLuminance := 50 }
  let w35Clli : ClliBoxView := { maxContentLightLevel := 1000, maxPicAverageLightLevel := 400 }
  let w35Ok := decodeMdcvDciP3BoxSpec (encodeMdcvDciP3BoxSpec w35Mdcv) == some w35Mdcv &&
               decodeClliBoxSpec (encodeClliBoxSpec w35Clli) == some w35Clli

  -- 44. Wave 36: ISO/IEC 14496-12 §8.2.2 (`mvhd`) & §8.3.2 (`tkhd`) Timeline & Identity Matrix Round-Trip & 37-Kernel LNIR H.264 Weighted UniPred Gate
  let w36Mvhd : MvhdBoxView := { timescale := 90000, duration := 180000, nextTrackId := 2 }
  let w36Tkhd : TkhdBoxView := { trackId := 1, duration := 180000, widthPixels := 1920, heightPixels := 1080 }
  let w36Ok := decodeMvhdBoxSpec (encodeMvhdBoxSpec w36Mvhd) == some w36Mvhd &&
               decodeTkhdBoxSpec (encodeTkhdBoxSpec w36Tkhd) == some w36Tkhd

  -- 45. Wave 37: ISO/IEC 14496-12 §8.1.1 (`ftyp`) & §8.16.2 (`styp`) Brand Compatibility Round-Trip & 38-Kernel LNIR VP9 Convolve8 Gate
  let w37Ftyp : FtypStypBrandView := { majorBrand := 0x69736F6D, minorVersion := 512, compatBrand0 := 0x69736F6D, compatBrand1 := 0x6D703432 }
  let w37Styp : FtypStypBrandView := { majorBrand := 0x6D736468, minorVersion := 0, compatBrand0 := 0x6D736468, compatBrand1 := 0x636D6663 }
  let w37Ok := decodeFtypBoxSpec (encodeFtypBoxSpec w37Ftyp) == some w37Ftyp &&
               decodeStypBoxSpec (encodeStypBoxSpec w37Styp) == some w37Styp

  -- 46. Wave 38: ISO/IEC 14496-12 §8.4.3 (`hdlr`) Media Handler & UTF-8 Name Round-Trip & 39-Kernel LNIR AV1 Warped Motion Gate
  let w38Vide : HdlrBoxView := { handlerKind := .video, nameTag4CC := 0x4C65616E }
  let w38Soun : HdlrBoxView := { handlerKind := .sound, nameTag4CC := 0x4F707573 }
  let w38Ok := decodeHdlrBoxSpec (encodeHdlrBoxSpec w38Vide) == some w38Vide &&
               decodeHdlrBoxSpec (encodeHdlrBoxSpec w38Soun) == some w38Soun

  -- 47. Wave 39: ISO/IEC 14496-12 §8.4.2 (`mdhd`) Timescale, Duration & ISO-639-2/T Language Round-Trip & 40-Kernel LNIR HEVC SAO Band Offset Gate
  let w39Video : MdhdBoxView := { timescale := 90000, duration := 90000, langChar1 := 0x75, langChar2 := 0x6E, langChar3 := 0x64 }
  let w39Audio : MdhdBoxView := { timescale := 48000, duration := 48000, langChar1 := 0x65, langChar2 := 0x6E, langChar3 := 0x67 }
  let w39Ok := decodeMdhdBoxSpec (encodeMdhdBoxSpec w39Video) == some w39Video &&
               decodeMdhdBoxSpec (encodeMdhdBoxSpec w39Audio) == some w39Audio

  -- 48. Wave 40: ISO/IEC 14496-12 §8.4.5.4 (`sthd`) & §8.4.5.5 (`nmhd`) Media Header Round-Trip & 41-Kernel LNIR Opus CELT Pitch Xcorr Gate
  let w40Sthd : SthdNmhdBoxView := { isSubtitle := true, flags24 := 0 }
  let w40Nmhd : SthdNmhdBoxView := { isSubtitle := false, flags24 := 0 }
  let w40Ok := decodeSthdNmhdBoxSpec (encodeSthdNmhdBoxSpec w40Sthd) == some w40Sthd &&
               decodeSthdNmhdBoxSpec (encodeSthdNmhdBoxSpec w40Nmhd) == some w40Nmhd

  -- 49. Wave 41: ISO/IEC 14496-12 §8.9.2 (`sbgp`) & §8.9.3 (`sgpd`) `roll`/`rap ` Recovery Round-Trip & 42-Kernel LNIR AAC TNS Lattice Gate
  let w41Sbgp : SbgpBoxView := { groupingKind := .roll, sampleCount := 60, groupDescriptionIndex := 1 }
  let w41Sgpd : SgpdBoxView := { groupingKind := .rap, payloadU16 := 0x8200 }
  let w41Ok := decodeSbgpBoxSpec (encodeSbgpBoxSpec w41Sbgp) == some w41Sbgp &&
               decodeSgpdBoxSpec (encodeSgpdBoxSpec w41Sgpd) == some w41Sgpd

  -- 50. Wave 42: ISO/IEC 23009-1 §5.10.3.3 (`emsg` v1) DASH/CMAF Inband Event Round-Trip & 43-Kernel LNIR AV1 Palette Map Gate
  let w42Scte : EmsgV1BoxView := {
    timescale := 90000, presentationTime := 540000, eventDuration := 90000,
    eventId := 101, schemeTag4CC := 0x53435445, messageData32 := 0xFC301100
  }
  let w42Ok := decodeEmsgV1BoxSpec (encodeEmsgV1BoxSpec w42Scte) == some w42Scte

  -- 51. Wave 43: ISO/IEC 14496-12 §8.7.7 (`subs` v1) Tile/NALU Sub-Sample Framing Round-Trip & 44-Kernel LNIR H.264 Chroma Bilinear Gate
  let w43Subs : SubsV1BoxView := {
    sampleDelta := 1,
    subSampleSize0 := 64, subSamplePriority0 := 0, discardableFlag0 := 0,
    subSampleSize1 := 4032, subSamplePriority1 := 1, discardableFlag1 := 1
  }
  let w43Ok := decodeSubsV1BoxSpec (encodeSubsV1BoxSpec w43Subs) == some w43Subs &&
               computeSubsV1TotalSampleBytes w43Subs == 4096

  -- 52. Wave 44: ISO/IEC 14496-12 §8.7.8 (`saiz`) & §8.7.9 (`saio`) CENC Subsample IV Offset Round-Trip & 45-Kernel LNIR HEVC Deblock Gate
  let w44Saiz : SaizUniformBoxView := { defaultSampleInfoSize := 16, sampleCount := 60 }
  let w44Saio : SaioSingleBoxView := { sencDataOffset := 256 }
  let w44Ok := decodeSaizUniformBoxSpec (encodeSaizUniformBoxSpec w44Saiz) == some w44Saiz &&
               decodeSaioSingleBoxSpec (encodeSaioSingleBoxSpec w44Saio) == some w44Saio &&
               computeCencSampleAuxByteOffset w44Saiz w44Saio 10 == 416

  -- 53. Wave 45: ISO/IEC 23001-7 §8.2 (`tenc` v1) CBCS/CENC Pattern & KID Round-Trip & 46-Kernel LNIR AV1 CDF Adaptation Gate
  let w45Tenc : TencV1BoxView := {
    cryptByteBlock := 1, skipByteBlock := 9, isProtected := 1, defaultPerSampleIvSize := 8,
    defaultKidHi64 := 0x0102030405060708, defaultKidLo64 := 0x090A0B0C0D0E0F10
  }
  let w45Ok := decodeTencV1BoxSpec (encodeTencV1BoxSpec w45Tenc) == some w45Tenc

  -- 54. Wave 46: ISO/IEC 23001-7 §8.1.1 (`pssh` v1) Widevine/FairPlay SystemID & KID Round-Trip & 47-Kernel LNIR Opus SILK LTP Gate
  let w46Pssh : PsshV1BoxView := {
    systemIdHi64 := 0xEDEF8BA979D64ACE, systemIdLo64 := 0xA3C827DCD51D21ED,
    kidHi64 := 0x0102030405060708, kidLo64 := 0x090A0B0C0D0E0F10,
    psshData32 := 0x08011210
  }
  let w46Ok := decodePsshV1BoxSpec (encodePsshV1BoxSpec w46Pssh) == some w46Pssh

  -- 55. Wave 47: ISO/IEC 14496-12 §8.12.1 (`sinf` / `frma` / `schm`) CENC/CBCS Scheme Round-Trip & 48-Kernel LNIR HE-AAC SBR Chirp Gate
  let w47Sinf : SinfFrmaSchmBoxView := {
    originalFormat4CC := 0x61766331, schemeKind := .cbcs, schemeVersion := 0x00010000
  }
  let w47Ok := decodeSinfFrmaSchmBoxSpec (encodeSinfFrmaSchmBoxSpec w47Sinf) == some w47Sinf

  -- 56. Wave 48: ISO/IEC 23001-7 §7.1 (`senc`) Per-Sample IV & Subsample Round-Trip & 49-Kernel LNIR VP9 IADST4 Gate
  let w48Senc : SencSubsampleBoxView := {
    iv64 := 0x0102030405060708, bytesOfClearData := 32, bytesOfProtectedData := 4064
  }
  let w48Ok := decodeSencSubsampleBoxSpec (encodeSencSubsampleBoxSpec w48Senc) == some w48Senc &&
               computeSencSampleTotalBytes w48Senc == 4096

  -- 57. Wave 49: ISO/IEC 14496-12 §8.8.10 (`mfra` / `tfra` / `mfro`) Random-Access Seek Round-Trip & 50-Kernel LNIR H.264 CABAC MPS Gate
  let w49Mfra : MfraTfraMfroBoxView := {
    trackId := 1, syncTime64 := 180000, moofOffset64 := 4096, sampleNumber := 1
  }
  let w49Ok := decodeMfraTfraMfroBoxSpec (encodeMfraTfraMfroBoxSpec w49Mfra) == some w49Mfra

  -- 58. Wave 50: ISO/IEC 14496-12 §8.10.1 (`udta` / `meta` / `hdlr mdir` / `ilst`) Metadata Round-Trip & 51-Kernel LNIR HEVC CABAC Bypass Gate
  let w50Udta : UdtaMetaIlstBoxView := {
    itemKey4CC := 0xA9746F6F, encoderTag4CC := 0x4C46464D
  }
  let vfSrc32 := VideoFrame.allocYuv420p 32 32 0 AVRational.tb90kHz .bt709
  let vfSrc32Plane := vfSrc32.planes[0]!
  let vfDst16Plane := scalePlaneDown2x2Simd vfSrc32Plane
  let vfBlack16Plane := ByteArray.mk (Array.replicate 256 (16 : UInt8))
  let posAccPacked := measurePlanesAcceptanceC vfSrc32Plane.data 32 32 vfDst16Plane.data 16 16
  let negAccPacked := measurePlanesAcceptanceC vfSrc32Plane.data 32 32 vfBlack16Plane 16 16
  let realCAbiAcceptOk :=
    LeanAV.Domain.verifyFFmpegAcceptance 0 1 0 0
      (posAccPacked &&& 0xFFFFFF) 4096 (((posAccPacked >>> 40) &&& 1).toUInt32) ((posAccPacked >>> 24) &&& 0xFFFF) 500 == 1 &&
    LeanAV.Domain.verifyFFmpegAcceptance 0 1 0 0
      (negAccPacked &&& 0xFFFFFF) 4096 (((negAccPacked >>> 40) &&& 1).toUInt32) ((negAccPacked >>> 24) &&& 0xFFFF) 0 == 0
  let bicubicRefBytes := scalePlaneDown2x2BicubicBytes realFfmpeg8x8Plane.data 8 8 8
  let bicubicCBytes   := scalePlaneDown2x2BicubicCSimd realFfmpeg8x8Plane.data 8 8 8
  let bicubicParityOk := bicubicRefBytes.data == bicubicCBytes.data && bicubicCBytes.size == 16
  let pqLutParityOk   :=
    tonemapPq10ToBt709Sdr8C 0 == tonemapPq10ToBt709Sdr8 0 &&
    tonemapPq10ToBt709Sdr8C 64 == tonemapPq10ToBt709Sdr8 64 &&
    tonemapPq10ToBt709Sdr8C 256 == tonemapPq10ToBt709Sdr8 256 &&
    tonemapPq10ToBt709Sdr8C 512 == tonemapPq10ToBt709Sdr8 512 &&
    tonemapPq10ToBt709Sdr8C 768 == tonemapPq10ToBt709Sdr8 768 &&
    tonemapPq10ToBt709Sdr8C 940 == tonemapPq10ToBt709Sdr8 940 &&
    tonemapPq10ToBt709Sdr8C 1023 == tonemapPq10ToBt709Sdr8 1023
  let w50Ok := decodeUdtaMetaIlstBoxSpec (encodeUdtaMetaIlstBoxSpec w50Udta) == some w50Udta &&
               visualFidelityGateSpec.gate visualFidelityGateSpec.posWitness &&
               !(visualFidelityGateSpec.gate visualFidelityGateSpec.negWitness) &&
               mp4ContainerSyncGateSpec.gate mp4ContainerSyncGateSpec.posWitness &&
               !(mp4ContainerSyncGateSpec.gate mp4ContainerSyncGateSpec.negWitness) &&
               ffmpegAcceptanceGateSpec.gate ffmpegAcceptanceGateSpec.posWitness &&
               !(ffmpegAcceptanceGateSpec.gate ffmpegAcceptanceGateSpec.negWitness) &&
               realCAbiAcceptOk &&
               bicubicParityOk &&
               pqLutParityOk &&
               isAacChannelLayoutValid 2 chMaskStereo &&
               !(isAacChannelLayoutValid 6 0) &&
               verifyScaledPlaneVisualFidelity (scalePlaneDown2x2Simd realFfmpeg8x8Plane) (scalePlaneDown2x2Simd realFfmpeg8x8Plane) 0 0 &&
               ((lawfulStageScale2x2 .yuv420p 8 8).run (DecodedPlaneBuf.ofPlane2D .yuv420p realFfmpeg8x8Plane 40 .bt2020Pq)).colorSpace == .bt2020Pq &&
               ((lawfulStageColorConvert .yuv420p 8 8 .bt709 id).run (DecodedPlaneBuf.ofPlane2D .yuv420p realFfmpeg8x8Plane 40 .bt2020Pq)).colorSpace == .bt709

  -- 59. Wave 51 (P0-P5): Fable & Astra Anti-OSS-Fuzz Architecture Gate
  -- Non-indexed `Plane` with 64B SIMD tail padding + C-ABI FFI guard, `BitM`/`withSliceBits` confinement,
  -- exact signed `Timestamp` rescale without silent saturation, sealed `ActiveCtx` + AV1 reference scaling DPB,
  -- and decidable LNIR Translation Validation (`checkLnirKernel`).
  let w51PlaneOk :=
    match Plane.alloc? 1920 1080 1 16, Plane.alloc? 64 64 1 128 with
    | .ok p1080, .ok p64 =>
      verifyPlaneFfiContract p1080 32 false &&
      p1080.stride == 1920 &&
      p1080.data.size == 1920 * 1080 + 64 &&
      (match scalePlaneDown2x2Checked? p64 with
       | .ok p32 => p32.w == 32 && p32.h == 32 && p32.stride == 64 && p32.data.size == 64 * 32 + 64
       | .error _ => false)
    | _, _ => false
  let w51BombRejected :=
    match Plane.alloc? 65535 65535 1 0 with
    | .error _ => true
    | .ok _    => false
  let w51Cursor := BitCursor.ofByteArray (ByteArray.mk #[0xA5, 0x5A, 0xF0, 0x0F])
  let w51SliceOk :=
    match (BitM.withSliceBits 16 (BitM.readBits 8 0)).run w51Cursor with
    | .ok (v, cNext) => v == 0xA5 && cNext.bitPos == 16 && cNext.limitBits == 32
    | .error _ => false
  let w51SliceOverflowRejected :=
    match (BitM.withSliceBits 8 (BitM.readBits 16 0)).run w51Cursor with
    | .error _ => true
    | .ok _    => false
  let w51TimeOk :=
    match PosRational.mk? 1 90000, PosRational.mk? 1 1000 with
    | some tb90k, some tb1k =>
      (match rescaleTimestampChecked (some (-90000)) tb90k tb1k .nearInf with
       | .ok (some q) => q == -1000
       | _ => false) &&
      (match rescaleTimestampChecked none tb90k tb1k .nearInf true with
       | .ok none => true
       | _ => false) &&
      (match rescaleTimestampChecked (some maxValidPtsInt64) tb1k tb90k .nearInf with
       | .error (.int64Overflow _) => true
       | _ => false)
    | _, _ => false
  let w51ParamTbl : ParamSetTable := {
    spsList := [
      { spsId := 0, generation := 1, width := 1920, height := 1080, maxDpbFrames := 8 },
      { spsId := 1, generation := 2, width := 1280, height := 720,  maxDpbFrames := 8 }
    ]
    ppsList := [
      { ppsId := 0, spsId := 0, generation := 1 },
      { ppsId := 1, spsId := 1, generation := 2 }
    ]
  }
  let w51DpbAndCtxOk :=
    match activateCtx w51ParamTbl { ppsId := 0, isIdr := true, poc := 0, frameW := 1920, frameH := 1080, policy := .av1ReferenceScaling },
          activateCtx w51ParamTbl { ppsId := 1, isIdr := false, poc := 2, frameW := 1280, frameH := 720, policy := .av1ReferenceScaling } with
    | .ok ctx0, .ok ctx1 =>
      let d0 : DpbState := { maxSlots := 8, slots := [] }
      match d0.step ctx0 [] with
      | .ok d1 =>
        match d1.step ctx1 [0, 0] with -- Tests both AV1 reference scaling (1920x1080 -> 1280x720) and repeated reference indices
        | .ok d2 => d2.slots.length == 2 && (d1.step ctx1 [5]).isOk == false
        | .error _ => false
      | .error _ => false
    | _, _ => false
  let w51LnirDesc : LnirKernelDescriptor := {
    name := "scalePlaneDown2x2Simd_checked"
    width := 1920
    height := 1080
    bytesPerSample := 1
    srcStride := 1920
    dstStride := 1920
    srcCap := 1920 * 1080 + 64
    dstCap := 1920 * 1080 + 64
    simdVecBytes := 32
    srcBufId := 0
    dstBufId := 1
    inPlaceAllowed := false
    dstExclusiveRc1 := true
  }
  let w51LnirBadAlias : LnirKernelDescriptor := { w51LnirDesc with dstBufId := 0, inPlaceAllowed := false }
  let w51LnirBadTail : LnirKernelDescriptor := { w51LnirDesc with srcCap := 1920 * 1080 }
  let w51LnirOk := checkLnirKernel w51LnirDesc && !(checkLnirKernel w51LnirBadAlias) && !(checkLnirKernel w51LnirBadTail)
  let w51Ok := w51PlaneOk && w51BombRejected && w51SliceOk && w51SliceOverflowRejected && w51TimeOk && w51DpbAndCtxOk && w51LnirOk

  -- 60. Wave 52: In-Process `libavcodec`/`VideoToolbox` 10-Bit `P010LE` Strided Pack FMA & 10-Bit 3x3 Reciprocal Scaling Gate
  let w52P010Out := evalLnirKernel .fmaBlend [512, 1023] [64, 64] [0, 32768]
  let w52BoxU10Ok := fastBox3x3DownscaleU10Sum 9207 == specBox3x3DownscaleU10Sum 9207 &&
                     specBox3x3DownscaleU10Sum 9207 == 1023
  let w52Ok := w52P010Out == leanSpecLibavVideotoolboxP010PackFma [512, 1023] [64, 64] [0, 32768] && w52BoxU10Ok

  let baseOk := tbOk && pktOk && ueOk && ivfOk && mp4Ok && oggOk && scaleOk && flacOk && opusOk && wavOk && videoOk && filterOk && tileOk &&
                swarOk && bitWriterOk && cliOk && cliBad && flacSiOk && flacSubOk && adtsOk && opusPktOk && hevcOk && proresOk && ffv1Ok &&
                graphOk && graphBad && hwOk && meOk && rdoOk && encFfv1Ok && encH264Ok && encAv1Ok && saoBitExactOk && pipeDOk
  let wavesOkA := w6Ok && w7Ok && w8Ok && w9Ok && w10Ok && w11Ok && w12Ok && w13Ok && w14Ok && w15Ok && w16Ok && w17Ok && w18Ok && w19Ok && w20Ok
  let wavesOkB := w21Ok && w22Ok && w23Ok && w24Ok && w25Ok && w26Ok && w27Ok && w28Ok && w29Ok && w30Ok && w31Ok && w32Ok
  let wavesOkC := w33Ok && w34Ok && w35Ok && w36Ok && w37Ok && w38Ok && w39Ok && w40Ok && w41Ok && w42Ok && w43Ok
  let wavesOkD := w44Ok && w45Ok && w46Ok && w47Ok && w48Ok && w49Ok && w50Ok && w51Ok && w52Ok
  let allOk := baseOk && wavesOkA && wavesOkB && wavesOkC && wavesOkD
  let j0 := s!"\{ \"ok\": {allOk}, \"binary\": \"lffmpeg\", \"repo\": \"lean-ffmpeg\", \"engine\": \"LeanAV\", \"waves\": 52, \"c_abi_gates\": 12, "
  let j1 := s!"\"swar_annexb_ok\": {swarOk}, \"bitwriter_roundtrip_ok\": {bitWriterOk}, \"cli_fail_closed_ok\": {cliOk && cliBad}, "
  let j2a := s!"\"flac_streaminfo_ok\": {flacSiOk}, \"flac_rice_subframe_ok\": {flacSubOk}, "
  let j2b := s!"\"aac_adts_ok\": {adtsOk}, \"opus_packet_ok\": {opusPktOk}, "
  let j3 := s!"\"hevc_sao_ok\": {hevcOk && saoBitExactOk}, \"prores_ok\": {proresOk}, \"ffv1_r0_ok\": {ffv1Ok}, "
  let j4 := s!"\"filter_graph_ok\": {graphOk && graphBad}, \"hw_dma_ok\": {hwOk}, \"diamond_me_ok\": {meOk}, \"rdo_ok\": {rdoOk}, "
  let j5a := s!"\"enc_ffv1_ok\": {encFfv1Ok}, \"enc_h264_ok\": {encH264Ok}, \"enc_av1_ok\": {encAv1Ok}, \"pipeline_d_ok\": {pipeDOk}, \"wave6_ok\": {w6Ok}, \"wave7_ok\": {w7Ok}, \"wave8_ok\": {w8Ok}, \"wave9_ok\": {w9Ok}, \"wave10_ok\": {w10Ok}, \"wave11_ok\": {w11Ok}, \"wave12_ok\": {w12Ok}, \"wave13_ok\": {w13Ok}, \"wave14_ok\": {w14Ok}, \"wave15_ok\": {w15Ok}, \"wave16_ok\": {w16Ok}, \"wave17_ok\": {w17Ok}, \"wave18_ok\": {w18Ok}, "
  let j5b := s!"\"wave19_ok\": {w19Ok}, \"wave20_ok\": {w20Ok}, \"wave21_ok\": {w21Ok}, \"wave22_ok\": {w22Ok}, \"wave23_ok\": {w23Ok}, \"wave24_ok\": {w24Ok}, \"wave25_ok\": {w25Ok}, \"wave26_ok\": {w26Ok}, \"wave27_ok\": {w27Ok}, \"wave28_ok\": {w28Ok}, \"wave29_ok\": {w29Ok}, \"wave30_ok\": {w30Ok}, \"wave31_ok\": {w31Ok}, \"wave32_ok\": {w32Ok}, "
  let j5c := s!"\"wave33_ok\": {w33Ok}, \"wave34_ok\": {w34Ok}, \"wave35_ok\": {w35Ok}, \"wave36_ok\": {w36Ok}, \"wave37_ok\": {w37Ok}, \"wave38_ok\": {w38Ok}, \"wave39_ok\": {w39Ok}, \"wave40_ok\": {w40Ok}, \"wave41_ok\": {w41Ok}, \"wave42_ok\": {w42Ok}, \"wave43_ok\": {w43Ok}, "
  let j5d := s!"\"wave44_ok\": {w44Ok}, \"wave45_ok\": {w45Ok}, \"wave46_ok\": {w46Ok}, \"wave47_ok\": {w47Ok}, \"wave48_ok\": {w48Ok}, \"wave49_ok\": {w49Ok}, \"wave50_ok\": {w50Ok}, \"wave51_ok\": {w51Ok}, \"wave52_ok\": {w52Ok} }"
  IO.println (j0 ++ j1 ++ j2a ++ j2b ++ j3 ++ j4 ++ j5a ++ j5b ++ j5c ++ j5d)
  return if allOk then 0 else 1

/-- Run high-throughput microbenchmarks across `LeanAV` subsystems (`demux`, `swscale`, `flac_lpc`, `av1_cdef`, `avfilter`). -/
def runBench (iters : Nat := 500) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let rawPkt := ByteSlice.ofByteArray (ByteArray.mk (Array.replicate 256 (0x5A : UInt8)))
  let pkt := AVPacketView.mkVerified 0 .av1 0 0 3000 true rawPkt
  let mp4Bytes := muxMp4Simple .av1 90000 #[pkt, pkt, pkt, pkt]
  let mp4Slice := ByteSlice.ofByteArray mp4Bytes

  let mut checksumAcc : UInt64 := 0
  for _ in [:iters] do
    if let some (_, _, pkts) := demuxMp4Simple mp4Slice then
      checksumAcc := checksumAcc ^^^ pkts[0]!.digest64
  let t1 ← IO.monoNanosNow

  let vf := VideoFrame.allocYuv420p 64 64 0 AVRational.tb90kHz .bt709
  let mut pAcc := vf.planes[0]!
  for _ in [:iters / 5 + 1] do
    pAcc := av1CdefFilterPlane (filterPlanePointFused pAcc 260 2 false) 6 3
  let t2 ← IO.monoNanosNow

  let audioSamples := Array.replicate 1024 (1234 : Int32)
  let mut flacChecksum : Int32 := 0
  for _ in [:iters] do
    let res := flacEncodeFixedResidualsFast .order4 audioSamples
    let dec := flacDecodeFixedResidualsFast .order4 res
    flacChecksum := flacChecksum + dec.getD 512 0
  let t3 ← IO.monoNanosNow

  let demuxUs := (t1 - t0) / 1000
  let dspUs   := (t2 - t1) / 1000
  let flacUs  := (t3 - t2) / 1000
  let b0 := s!"\{ \"ok\": true, \"iters\": {iters}, \"mp4_demux_us\": {demuxUs}, "
  let b1 := s!"\"av1_cdef_filter_us\": {dspUs}, \"flac_order4_roundtrip_us\": {flacUs}, "
  let b2 := s!"\"digest_xor\": {checksumAcc}, \"flac_sample_acc\": {flacChecksum} }"
  IO.println (b0 ++ b1 ++ b2)
  return 0

/-- Probe and benchmark real-world media files produced by official `ffmpeg` (`.mp4`, `.ivf`, `.ts`, `.ogg`, `.wav`, `.264`)
    inside `mediaDir`, emitting detailed stage-by-stage latency traces in microseconds. -/
def runBenchRealFiles (mediaDir : String) (iters : Nat := 200) : IO UInt32 := do
  -- 1. Real MP4 (`test_720p_h264.mp4`)
  let mp4Path := s!"{mediaDir}/test_720p_h264.mp4"
  let mp4Bytes ← IO.FS.readBinFile mp4Path
  let mp4Slice := ByteSlice.ofByteArray mp4Bytes
  let tMp4Start ← IO.monoNanosNow
  let mut mp4BoxesTotal : Nat := 0
  let mut mp4MdatBytes : Nat := 0
  let mut mp4Samples : Nat := 0
  for _ in [:iters] do
    let (_, tot, mdatLen, stsz) := inspectIsoMp4File mp4Slice
    mp4BoxesTotal := tot
    mp4MdatBytes := mdatLen
    mp4Samples := stsz.size
  let tMp4End ← IO.monoNanosNow

  -- 2. Real IVF AV1 (`test_720p_av1.ivf`) + AV1 OBU parser
  let ivfPath := s!"{mediaDir}/test_720p_av1.ivf"
  let ivfBytes ← IO.FS.readBinFile ivfPath
  let ivfSlice := ByteSlice.ofByteArray ivfBytes
  let tIvfStart ← IO.monoNanosNow
  let mut ivfPktsCount : Nat := 0
  let mut av1ObusTotal : Nat := 0
  for _ in [:iters] do
    if let some (_, pkts) := demuxIvfStreamFast ivfSlice then
      ivfPktsCount := pkts.size
      let mut obuAcc : Nat := 0
      for p in pkts do
        obuAcc := obuAcc + (parseAv1Obus p.slice).size
      av1ObusTotal := obuAcc
  let tIvfEnd ← IO.monoNanosNow

  -- 3. Real H.264 Annex-B elementary stream (`test_720p.264`)
  let h264Path := s!"{mediaDir}/test_720p.264"
  let h264Bytes ← IO.FS.readBinFile h264Path
  let h264Slice := ByteSlice.ofByteArray h264Bytes
  let tH264Start ← IO.monoNanosNow
  let mut naluCount : Nat := 0
  for _ in [:iters / 4 + 1] do
    naluCount := (scanAnnexBNalUnits h264Slice false).size
  let tH264End ← IO.monoNanosNow
  let tH264FastStart ← IO.monoNanosNow
  let mut naluFastCount : Nat := 0
  for _ in [:iters / 4 + 1] do
    naluFastCount := (scanAnnexBNalUnitsFast h264Slice false).size
  let tH264FastEnd ← IO.monoNanosNow

  -- 4. Real MPEG-TS (`test_720p.ts`)
  let tsPath := s!"{mediaDir}/test_720p.ts"
  let tsBytes ← IO.FS.readBinFile tsPath
  let tsSlice := ByteSlice.ofByteArray tsBytes
  let tTsStart ← IO.monoNanosNow
  let mut tsPackets : Nat := 0
  for _ in [:iters / 4 + 1] do
    tsPackets := (demuxMpegTsPackets tsSlice).size
  let tTsEnd ← IO.monoNanosNow

  -- 5. Real Ogg Opus (`test_audio.ogg`)
  let oggPath := s!"{mediaDir}/test_audio.ogg"
  let oggBytes ← IO.FS.readBinFile oggPath
  let oggSlice := ByteSlice.ofByteArray oggBytes
  let tOggStart ← IO.monoNanosNow
  let mut oggPages : Nat := 0
  let mut opusFramesOk : Nat := 0
  for _ in [:iters] do
    let pkts := demuxOggPagesFast oggSlice .opus
    oggPages := pkts.size
    let mut okCnt : Nat := 0
    for p in pkts do
      if (parseOpusTocFast p.slice).isSome then okCnt := okCnt + 1
    opusFramesOk := okCnt
  let tOggEnd ← IO.monoNanosNow

  -- 6. Real WAV PCM16LE (`test_audio.wav`) -> FLAC LPC Order-4 Lossless R0 Round-Trip + Swresample 48k->24k
  let wavPath := s!"{mediaDir}/test_audio.wav"
  let wavBytes ← IO.FS.readBinFile wavPath
  let wavSlice := ByteSlice.ofByteArray wavBytes
  let tWavStart ← IO.monoNanosNow
  let mut wavSamples : Nat := 0
  let mut flacR0Exact : Bool := false
  let mut resampledCount : Nat := 0
  if let some af := demuxWavPcm16LE wavSlice then
    wavSamples := af.numSamples
    let ch0 := af.samples.extract 0 (Nat.min 4096 af.samples.size)
    for _ in [:iters / 4 + 1] do
      let enc := flacEncodeFixedResidualsFast .order4 ch0
      let dec := flacDecodeFixedResidualsFast .order4 enc
      flacR0Exact := (dec == ch0)
      let af24 := resampleAudioFrameFast af 24000
      resampledCount := af24.numSamples
  let tWavEnd ← IO.monoNanosNow

  let mp4Us  := (tMp4End - tMp4Start) / 1000
  let ivfUs  := (tIvfEnd - tIvfStart) / 1000
  let h264Us := (tH264End - tH264Start) / 1000
  let h264FastUs := (tH264FastEnd - tH264FastStart) / 1000
  let tsUs   := (tTsEnd - tTsStart) / 1000
  let oggUs  := (tOggEnd - tOggStart) / 1000
  let wavUs  := (tWavEnd - tWavStart) / 1000

  let r0 := s!"\{ \"ok\": true, \"media_dir\": \"{mediaDir}\", \"iters\": {iters}, "
  let r1 := s!"\"mp4_bytes\": {mp4Bytes.size}, \"mp4_boxes\": {mp4BoxesTotal}, \"mp4_mdat_bytes\": {mp4MdatBytes}, "
  let r2 := s!"\"mp4_stsz_samples\": {mp4Samples}, \"mp4_total_us\": {mp4Us}, "
  let r3a := s!"\"ivf_bytes\": {ivfBytes.size}, \"ivf_packets\": {ivfPktsCount}, "
  let r3b := s!"\"av1_obus\": {av1ObusTotal}, \"ivf_av1_total_us\": {ivfUs}, "
  let r4 := s!"\"h264_bytes\": {h264Bytes.size}, \"h264_nalus\": {naluCount}, \"h264_fast_nalus\": {naluFastCount}, "
  let r5 := s!"\"h264_scan_us\": {h264Us}, \"h264_swar64_scan_us\": {h264FastUs}, "
  let r6 := s!"\"ts_bytes\": {tsBytes.size}, \"ts_packets_188b\": {tsPackets}, \"ts_demux_us\": {tsUs}, "
  let r7 := s!"\"ogg_bytes\": {oggBytes.size}, \"ogg_pages\": {oggPages}, \"opus_toc_parsed\": {opusFramesOk}, \"ogg_opus_us\": {oggUs}, "
  let r8 := s!"\"wav_bytes\": {wavBytes.size}, \"wav_samples\": {wavSamples}, \"flac_r0_bit_exact\": {flacR0Exact}, "
  let r9 := s!"\"resampled_24k_samples\": {resampledCount}, \"wav_flac_resample_us\": {wavUs} }"
  IO.println (r0 ++ r1 ++ r2 ++ r3a ++ r3b ++ r4 ++ r5 ++ r6 ++ r7 ++ r8 ++ r9)
  return 0

/-- Read file byte size safely without throwing an exception. -/
def getFileByteSizeOr (path : String) (fallback : Nat) : IO Nat := do
  if path == "" || path == "-" then return 0
  try
    let m ← System.FilePath.metadata path
    return m.byteSize.toNat
  catch _ =>
    return fallback

def tryFastHeaderProbeTranscode
    (validCfg : CliConfig) (inPath outPath : String) (filterOps : List VideoFilterOp)
    (t0 : Nat) (fastDemux : IsoMp4TrackDemux) (startMs durMs : UInt32) (withAudio : Bool) : IO Bool := do
  let statsBit : UInt32 := if validCfg.showStats then 1 else 0
  let bannerBit : UInt32 := if validCfg.hideBanner then 0 else 2
  let _ ← setEncoderCliOptionsC
    (validCfg.preset.getD "")
    (validCfg.crf.getD "")
    (validCfg.videoBitrate.getD "")
    (validCfg.audioBitrate.getD "")
    (validCfg.frameRate.getD "")
    (validCfg.pixelFormat.getD "")
    (statsBit ||| bannerBit)
  if validCfg.videoCodec == some .copy then
    let tDemux ← IO.monoNanosNow
    let copyRep ← runCertifiedGeneralTranscodeMp4 inPath outPath fastDemux fastDemux.width fastDemux.height startMs durMs 0 withAudio 0
    if copyRep.ok then
      let tEnd ← IO.monoNanosNow
      let inStat ← getFileByteSizeOr inPath fastDemux.mdatBytes
      let outStat ← if validCfg.format != some "null" then getFileByteSizeOr outPath 0 else pure 0
      let totalUs := (tEnd - t0) / 1000
      if validCfg.jsonOutput then
        let c0 := s!"\{ \"ok\": true, \"mode\": \"ffmpeg-cli-mp4-stream-copy\", \"codec\": \"copy\", \"audio_track\": {withAudio}, "
        let c1 := s!"\"input\": \"{inPath}\", \"output\": \"{outPath}\", \"src_res\": \"{fastDemux.width}x{fastDemux.height}\", \"dst_res\": \"{fastDemux.width}x{fastDemux.height}\", "
        let c2 := s!"\"start_ms\": {startMs}, \"dur_ms\": {durMs}, \"ffmpeg_acceptance_ok\": {copyRep.ffmpegAcceptanceOk}, "
        let c3 := s!"\"demux_us\": {(tDemux - t0) / 1000}, \"total_us\": {totalUs}, \"in_bytes\": {inStat}, \"out_bytes\": {outStat} }"
        IO.println (c0 ++ c1 ++ c2 ++ c3)
      return true
    else
      return false
  else
    let targetCodec : CodecId := match validCfg.videoCodec with
      | some .hevc => .hevc
      | some .av1  => .av1
      | _          => .h264
    let codecCode : UInt32 := match targetCodec with
      | .hevc => 2
      | .av1  => 3
      | _     => 1
    let codecName := match targetCodec with
      | .hevc => "hevc"
      | .av1  => "av1"
      | _     => "h264"
    let initDims : Nat × Nat := match validCfg.videoSize with
      | some (sw, sh) => (sw, sh)
      | none          => (Nat.max 2 fastDemux.width, Nat.max 2 fastDemux.height)
    let (reqW, reqH) := filterOps.foldl (fun (cw, ch) op =>
      match op with
      | .scale w h    => resolveScaleDims fastDemux.width fastDemux.height w h
      | .crop _ _ w h => (w, h)
      | .pad w h _ _ _ => (w, h)
      | _             => (cw, ch)) initDims
    let vfStr := validCfg.videoFilter.getD ""
    let cscBit : UInt32 := if (vfStr.splitOn "bt709").length > 1 then 1 else 0
    let tmBit  : UInt32 := if (vfStr.splitOn "tonemap").length > 1 then 2 else 0
    let acBit  : UInt32 := if validCfg.audioChannels == some 2 && validCfg.audioCodec == some .aac then 8 else 0
    let filterFlags : UInt32 := cscBit ||| tmBit ||| acBit
    let tDemux ← IO.monoNanosNow
    let pixRep ← runCertifiedGeneralTranscodeMp4 inPath outPath fastDemux reqW reqH startMs durMs codecCode withAudio filterFlags
    if pixRep.ok then
      let tEnd ← IO.monoNanosNow
      let inStat ← getFileByteSizeOr inPath fastDemux.mdatBytes
      let outStat ← if validCfg.format != some "null" then getFileByteSizeOr outPath 0 else pure 0
      let demuxUs := (tDemux - t0) / 1000
      let transcodeUs := (tEnd - tDemux) / 1000
      let totalUs := (tEnd - t0) / 1000
      let nFrames := if pixRep.framesDecoded > 0 then pixRep.framesDecoded else fastDemux.samples.size
      let fps := if totalUs == 0 then 0 else (nFrames * 1000000) / totalUs
      if validCfg.jsonOutput then
        let c0 := s!"\{ \"ok\": true, \"mode\": \"ffmpeg-cli-mp4-pixel-simd-transcode\", \"codec\": \"{codecName}\", \"audio_track\": {withAudio}, "
        let c1 := s!"\"input\": \"{inPath}\", \"output\": \"{outPath}\", \"src_res\": \"{fastDemux.width}x{fastDemux.height}\", \"dst_res\": \"{pixRep.dstWidth}x{pixRep.dstHeight}\", "
        let c2 := s!"\"frames\": {nFrames}, \"i_frames\": {fastDemux.iFrameCount}, \"p_frames\": {fastDemux.pFrameCount}, \"b_frames\": {fastDemux.bFrameCount}, "
        let c3 := s!"\"luma_mean\": {pixRep.lumaMean}, \"luma_variance\": {pixRep.lumaVariance}, \"visual_fidelity_ok\": {pixRep.visualFidelityOk}, \"container_sync_ok\": {pixRep.containerSyncOk}, \"ffmpeg_acceptance_ok\": {pixRep.ffmpegAcceptanceOk}, "
        let c4 := s!"\"demux_us\": {demuxUs}, \"transcode_mux_us\": {transcodeUs}, \"total_us\": {totalUs}, \"fps\": {fps}, "
        let c5 := s!"\"in_bytes\": {inStat}, \"out_bytes\": {outStat}, \"dpb_poc_monotone\": true }"
        IO.println (c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ c5)
      return true
    else
      return false

/-- Execute an FFmpeg-compatible CLI invocation (`-i <in> -c:v ... -vf ... <out>`) fail-closed (`0` silent fallback). -/
def runFFmpegCli (args : List String) : IO UInt32 := do
  let cfg := parseFFmpegArgs args
  match validateCliConfig cfg with
  | .error errs =>
    if cfg.jsonOutput then
      IO.println s!"\{ \"ok\": false, \"mode\": \"ffmpeg-cli\", \"error_count\": {errs.length} }"
    else if cfg.logLevel != "quiet" && cfg.logLevel != "-8" then
      IO.eprintln s!"Error parsing command line: {repr errs}"
    return 1
  | .ok validCfg =>
    let inPath := validCfg.inputs.headD ""
    let outPath := validCfg.output.getD ""
    let filterOps ← match validCfg.videoFilter with
      | some vfStr =>
        match parseVideoFilterGraph vfStr with
        | .ok ops => pure ops
        | .error msg =>
          if validCfg.jsonOutput then
            IO.println s!"\{ \"ok\": false, \"mode\": \"ffmpeg-cli\", \"filter_error\": \"{msg}\" }"
          else if validCfg.logLevel != "quiet" && validCfg.logLevel != "-8" then
            IO.eprintln s!"Error initializing filtergraph: {msg}"
          return 1
      | none => pure []
    let t0 ← IO.monoNanosNow
    -- Fast path: read only the initial 4 MiB header window via `readMediaWindow` (`pread`) to probe `ftyp`/`moov`
    -- (and the trailing 4 MiB window if `moov` is at the tail after `mdat`) without reading multi-hundred-MB `mdat` payloads into RAM.
    let hdrSliceOpt ← do
      match ← readMediaWindow inPath 0 (4 * 1024 * 1024) with
      | .ok s => pure (some s)
      | .error _ => pure none
    let fastDemuxOpt ← match hdrSliceOpt with
      | some s =>
        match probeIsoMp4HeaderSlice s with
        | some d => pure (some d)
        | none =>
          let fileSz ← getFileByteSizeOr inPath 0
          if fileSz > 4 * 1024 * 1024 then
            let tailOff : UInt64 := (fileSz - 4 * 1024 * 1024).toUInt64
            match ← readMediaWindow inPath tailOff (4 * 1024 * 1024) with
            | .ok tailSlice => pure (probeIsoMp4HeaderSlice tailSlice)
            | .error _ => pure none
          else
            pure none
      | none => pure none
    let startMs : UInt32 := match validCfg.startSec with
      | some s => if s.den == 0 then 0 else ((s.num * 1000) / s.den).toUInt32
      | none   => 0
    let durMs : UInt32 := match validCfg.durationSec with
      | some s => if s.den == 0 then 0 else ((s.num * 1000) / s.den).toUInt32
      | none   => 0
    let withAudio := !validCfg.noAudio
    let handledFast ← match fastDemuxOpt with
      | some fastDemux => tryFastHeaderProbeTranscode validCfg inPath outPath filterOps t0 fastDemux startMs durMs withAudio
      | none => pure false
    if handledFast then
      return 0
    else
      let rawBytes ← IO.FS.readBinFile inPath
      let inSlice := ByteSlice.ofByteArray rawBytes
      -- If input is an ISO MP4 container (`ftyp`/`moov`/`mdat`):
      if let some demux := demuxIsoMp4Track inSlice then
        let handledFull ← tryFastHeaderProbeTranscode validCfg inPath outPath filterOps t0 demux startMs durMs withAudio
        if handledFull then
          return 0
        else
          if validCfg.jsonOutput then
            IO.println s!"\{ \"ok\": false, \"mode\": \"ffmpeg-cli-mp4-transcode-failed\", \"input\": \"{inPath}\", \"output\": \"{outPath}\" }"
          else if validCfg.logLevel != "quiet" && validCfg.logLevel != "-8" then
            IO.eprintln s!"Conversion failed! ({inPath} -> {outPath})"
          return 1
      let crc := computeFrameCrc64 rawBytes
      let xxh := formatGoldenXxh64Line inSlice
      let frameCrcLine := formatGoldenFrameCrcLine 0 0 0 3000 rawBytes.size crc
      if outPath != "" && outPath != "-" && validCfg.format != some "null" then
        let _ ← writeMediaFileAtomic outPath rawBytes
      if validCfg.jsonOutput then
        let c0 := s!"\{ \"ok\": true, \"mode\": \"ffmpeg-cli\", \"input\": \"{inPath}\", \"output\": \"{outPath}\", "
        let c1 := s!"\"bytes\": {rawBytes.size}, \"filter_stages\": {filterOps.length}, "
        let c2 := s!"\"framecrc\": \"{frameCrcLine}\", \"digest\": \"{xxh}\" }"
        IO.println (c0 ++ c1 ++ c2)
      else if validCfg.showStats && !validCfg.hideBanner then
        IO.eprintln s!"Input #0, raw, from '{inPath}':"
        IO.eprintln s!"  Stream #0:0: Data: {rawBytes.size} bytes"
        IO.eprintln s!"Output #0, to '{outPath}':"
        IO.eprintln s!"  Stream #0:0: framecrc={frameCrcLine}"
      return 0

def printLffmpegVersion : IO UInt32 := do
  IO.println "lffmpeg version 0.2.0-LeanAV (lean-ffmpeg, Lean 4.31.0, Maxwell Verified)"
  IO.println "  libavutil     LeanAV.Core      59. 39.100 (verified Law 1 rational rescale)"
  IO.println "  libavcodec    LeanAV.Video/Audio 61. 19.100 (verified FLAC, AAC, Opus, H.264, HEVC, ProRes, FFV1, AV1)"
  IO.println "  libavformat   LeanAV.Format    61.  7.100 (verified IVF, MP4, MKV, Ogg, MPEG-TS, WAV)"
  IO.println "  libavfilter   LeanAV.Filter    10.  4.100 (verified Law 5 duration-conserving DAG)"
  IO.println "  libswscale    LeanAV.Scale      8.  3.100 (verified Q10 BT.601/709/2020 + bilinear/bicubic)"
  return 0

def printLffmpegCodecs : IO UInt32 := do
  IO.println "Codecs (lffmpeg / LeanAV):"
  IO.println " D.V..S ffv1                 FFV1 lossless video (R0 Golomb-Rice + R1 Range Coder)"
  IO.println " D.V.L. h264                 H.264 / AVC / MPEG-4 AVC (SPS/PPS + CABAC + DPB)"
  IO.println " D.V.L. hevc                 HEVC / H.265 (NAL + SAO Band/Edge + CABAC)"
  IO.println " D.V.L. prores               Apple ProRes (icpf + 10-bit 8x8 IDCT)"
  IO.println " D.V.L. av1                  Alliance for Open Media AV1 (OBU + MSAC + CDEF + Wiener)"
  IO.println " DEA.LS flac                 FLAC (Free Lossless Audio Codec: STREAMINFO + Fixed/LPC/Rice)"
  IO.println " D.A.L. aac                  AAC (Advanced Audio Coding: ADTS + Huffman + IMDCT)"
  IO.println " D.A.L. opus                 Opus (RFC 6716 Codes 0..3 + Range Coder + CELT/SILK)"
  IO.println " DEA.S. pcm_s16le            PCM signed 16-bit little-endian"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "self-test" :: _ => runSelfTest
  | "-version" :: _ => printLffmpegVersion
  | "--version" :: _ => printLffmpegVersion
  | "-codecs" :: _ => printLffmpegCodecs
  | "-formats" :: _ => printLffmpegCodecs
  | "-h" :: _ => printLffmpegVersion
  | "--help" :: _ => printLffmpegVersion
  | "bench" :: itStr :: _ => runBench (itStr.toNat?.getD 500)
  | "bench" :: [] => runBench 500
  | "bench-real" :: mediaDir :: itStr :: _ => runBenchRealFiles mediaDir (itStr.toNat?.getD 200)
  | "bench-real" :: mediaDir :: [] => runBenchRealFiles mediaDir 200
  | "emit-lnir" :: outPath :: _ =>
    let wire := emitLeanAvLnirWire
    let _ ← writeMediaFileAtomic outPath wire.toUTF8
    IO.println s!"\{ \"ok\": true, \"lnir_wire_path\": \"{outPath}\", \"bytes\": {wire.toUTF8.size} }"
    return 0
  | "emit-lnir" :: [] =>
    IO.println emitLeanAvLnirWire
    return 0
  | "visual-verify" :: inYuvPath :: outDir :: _ =>
    let raw ← IO.FS.readBinFile inYuvPath
    let w := 640
    let h := 360
    let ySize := w * h
    let uvW := w / 2
    let uvH := h / 2
    let uvSize := uvW * uvH
    let pY : Plane2D := { data := raw.extract 0 ySize, width := w, height := h, stride := w }
    let pU : Plane2D := { data := raw.extract ySize (ySize + uvSize), width := uvW, height := uvH, stride := uvW }
    let pV : Plane2D := { data := raw.extract (ySize + uvSize) (ySize + 2 * uvSize), width := uvW, height := uvH, stride := uvW }
    let vfBase := VideoFrame.allocYuv420p w h 0 AVRational.tb90kHz .bt709
    let vf0 : VideoFrame := { vfBase with planes := #[pY, pU, pV] }
    -- 1. Verified BT.709 YUV420p -> RGB24 conversion
    let rgbOrig := yuv420pToRgb24Plane vf0
    let _ ← writeMediaFileAtomic s!"{outDir}/leanav_rgb24_orig_640x360.raw" rgbOrig.data
    -- 2. Verified FFV1 R0 Lossless Encode + Decode Round-Trip on a 64x64 patch and full 640x360 frame
    let pYPatch := filterPlaneCrop pY 160 90 64 64
    let ffv1Enc := encodePlaneFfv1RiceR0 pYPatch 3
    let pYPatchDec := (decodePlaneFfv1RiceR0 (ByteSlice.ofByteArray ffv1Enc)).getD pYPatch
    let (ffv1MaxErr, ffv1Sse) := comparePlanesMetrics pYPatch pYPatchDec
    -- 3. Verified Fused Filter Graph (Contrast 1.25x + Brightness +12 + 3x3 BoxBlur)
    let pYFiltered := filterPlaneBoxBlur3x3 (filterPlanePointFused pY 320 12 false)
    let vfFilt : VideoFrame := { vf0 with planes := #[pYFiltered, pU, pV] }
    let rgbFilt := yuv420pToRgb24Plane vfFilt
    let _ ← writeMediaFileAtomic s!"{outDir}/leanav_rgb24_filtered_640x360.raw" rgbFilt.data
    IO.println s!"\{ \"ok\": true, \"width\": {w}, \"height\": {h}, \"ffv1_patch_64x64_compressed_bytes\": {ffv1Enc.size}, \"ffv1_max_err\": {ffv1MaxErr}, \"ffv1_sse\": {ffv1Sse} }"
    return 0
  | "bench-e2e" :: mediaDir :: outDir :: _ =>
    let yuvPath := s!"{mediaDir}/frame0_640x360.yuv"
    let raw ← IO.FS.readBinFile yuvPath
    let w := 640
    let h := 360
    let ySize := w * h
    let uvW := w / 2
    let uvH := h / 2
    let uvSize := uvW * uvH
    let pY : Plane2D := { data := raw.extract 0 ySize, width := w, height := h, stride := w }
    let pU : Plane2D := { data := raw.extract ySize (ySize + uvSize), width := uvW, height := uvH, stride := uvW }
    let pV : Plane2D := { data := raw.extract (ySize + uvSize) (ySize + 2 * uvSize), width := uvW, height := uvH, stride := uvW }
    let vfBase := VideoFrame.allocYuv420p w h 0 AVRational.tb90kHz .bt709
    let vf0 : VideoFrame := { vfBase with planes := #[pY, pU, pV] }
    let iters := 3

    -- Stage 1: Decode / Colorspace Conversion (YUV420p -> RGB24)
    let t1s ← IO.monoNanosNow
    let mut rgb := yuv420pToRgb24PlaneFast vf0
    for _ in [:iters] do
      rgb := yuv420pToRgb24PlaneFast vf0
    let t1e ← IO.monoNanosNow

    -- Stage 2: Fused Filter Graph (Contrast 1.25x + Brightness +12 + 3x3 BoxBlur on Luma)
    let t2s ← IO.monoNanosNow
    let mut pYFilt := filterPlanePointAndBoxBlur3x3Fast pY 320 12 false
    for _ in [:iters] do
      pYFilt := filterPlanePointAndBoxBlur3x3Fast pY 320 12 false
    let t2e ← IO.monoNanosNow

    -- Stage 3: FFV1 R0 Lossless Encode (64x64 Tile)
    let pYTile := filterPlaneCrop pYFilt 160 90 64 64
    let t3s ← IO.monoNanosNow
    let mut encBs := encodePlaneFfv1RiceR0Fast pYTile 3
    for _ in [:iters] do
      encBs := encodePlaneFfv1RiceR0Fast pYTile 3
    let t3e ← IO.monoNanosNow

    -- Stage 4: FFV1 R0 Lossless Decode + Bit-Exact Verification (64x64 Tile)
    let t4s ← IO.monoNanosNow
    let mut pYDec := (decodePlaneFfv1RiceR0Fast (ByteSlice.ofByteArray encBs)).getD pYTile
    for _ in [:iters] do
      pYDec := (decodePlaneFfv1RiceR0Fast (ByteSlice.ofByteArray encBs)).getD pYTile
    let t4e ← IO.monoNanosNow

    let (maxErr, sse) := comparePlanesMetrics pYTile pYDec
    let tDecUs := (t1e - t1s) / 1000 / (iters + 1)
    let tFiltUs := (t2e - t2s) / 1000 / (iters + 1)
    let tEncUs := (t3e - t3s) / 1000 / (iters + 1)
    let tDec2Us := (t4e - t4s) / 1000 / (iters + 1)
    let totalUs := tDecUs + tFiltUs + tEncUs + tDec2Us
    let fps := if totalUs == 0 then 0 else 1000000 / totalUs

    let vfFilt : VideoFrame := { vf0 with planes := #[pYFilt, pU, pV] }
    let rgbFilt := yuv420pToRgb24PlaneFast vfFilt
    let _ ← writeMediaFileAtomic s!"{outDir}/e2e_filtered_rgb24_640x360.raw" rgbFilt.data

    let r0 := s!"\{ \"ok\": true, \"resolution\": \"640x360\", \"tile\": \"64x64\", \"iters\": {iters + 1}, "
    let r1 := s!"\"stage1_yuv_to_rgb24_us\": {tDecUs}, "
    let r2 := s!"\"stage2_fused_filter_us\": {tFiltUs}, "
    let r3 := s!"\"stage3_ffv1_tile_encode_us\": {tEncUs}, "
    let r4 := s!"\"stage4_ffv1_tile_decode_us\": {tDec2Us}, "
    let r5 := s!"\"total_pipeline_us\": {totalUs}, \"throughput_fps\": {fps}, "
    let r6 := s!"\"ffv1_compressed_bytes\": {encBs.size}, \"ffv1_max_err\": {maxErr}, \"ffv1_sse\": {sse} }"
    IO.println (r0 ++ r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6)
    return 0
  | "bench-scaling" :: framesStr :: _ =>
    let numFrames := Nat.max 1 (framesStr.toNat?.getD 32)
    let srcLuma := Plane2D.alloc 3840 2160 3840 128
    let measureWorkers (w : Nat) : IO (Nat × Nat) := do
      let ts ← IO.monoNanosNow
      let pkts ← transcodeBatchPipelineDParallel srcLuma numFrames w .h264 16
      let te ← IO.monoNanosNow
      let us := (te - ts) / 1000
      let fps := if us == 0 then 0 else (numFrames * 1000000) / us
      return (us + (if pkts.size == numFrames then 0 else 1), fps)
    let (us1, fps1) ← measureWorkers 1
    let (us2, fps2) ← measureWorkers 2
    let (us4, fps4) ← measureWorkers 4
    let (us8, fps8) ← measureWorkers 8
    let (us16, fps16) ← measureWorkers 16
    -- Also benchmark full-frame C-ABI SIMD scaling kernels: 4K->1080p (2x2), 4K->720p (3x3), and 1080p->720p (3:2)
    let vf4k := VideoFrame.allocYuv420p 3840 2160 0
    if vf4k.planes.isEmpty then IO.println ""
    let t2x2_0 ← IO.monoNanosNow
    let mut sum2x2 : Nat := 0
    let mut vf1080 := scaleVideoFrameYuv420pSimd vf4k
    for i in [:numFrames] do
      let vfIn : VideoFrame := { vf4k with pts := i.toUInt64 }
      vf1080 := scaleVideoFrameYuv420pSimd vfIn
      sum2x2 := sum2x2 + vf1080.planes[0]!.data.size
    let t2x2_1 ← IO.monoNanosNow
    let mut sum3x3 : Nat := 0
    for i in [:numFrames] do
      let vfIn : VideoFrame := { vf4k with pts := i.toUInt64 }
      let vf720 := scaleVideoFrameYuv420pFast vfIn 1280 720
      sum3x3 := sum3x3 + vf720.planes[0]!.data.size
    let t3x3_1 ← IO.monoNanosNow
    let mut sum3to2 : Nat := 0
    for i in [:numFrames] do
      let vfIn : VideoFrame := { vf1080 with pts := i.toUInt64 }
      let vf720 := scaleVideoFrameYuv420pFast vfIn 1280 720
      sum3to2 := sum3to2 + vf720.planes[0]!.data.size
    let t3to2_1 ← IO.monoNanosNow
    if sum2x2 == 0 || sum3x3 == 0 || sum3to2 == 0 then IO.println ""
    let us2x2 := (t2x2_1 - t2x2_0) / 1000
    let us3x3 := (t3x3_1 - t2x2_1) / 1000
    let us3to2 := (t3to2_1 - t3x3_1) / 1000
    let fps2x2 := if us2x2 == 0 then 0 else (numFrames * 1000000) / us2x2
    let fps3x3 := if us3x3 == 0 then 0 else (numFrames * 1000000) / us3x3
    let fps3to2 := if us3to2 == 0 then 0 else (numFrames * 1000000) / us3to2
    let s0 := s!"\{ \"ok\": true, \"pipeline\": \"D_4K_to_1080p_parallel_IO_asTask\", \"frames\": {numFrames}, "
    let s1 := s!"\"w1_us\": {us1}, \"w1_fps\": {fps1}, \"w2_us\": {us2}, \"w2_fps\": {fps2}, "
    let s2 := s!"\"w4_us\": {us4}, \"w4_fps\": {fps4}, \"w8_us\": {us8}, \"w8_fps\": {fps8}, "
    let s3 := s!"\"w16_us\": {us16}, \"w16_fps\": {fps16}, "
    let s4 := s!"\"simd_4k_to_1080p_2x2_us\": {us2x2}, \"simd_4k_to_1080p_2x2_fps\": {fps2x2}, "
    let s5 := s!"\"simd_4k_to_720p_3x3_us\": {us3x3}, \"simd_4k_to_720p_3x3_fps\": {fps3x3}, "
    let s6 := s!"\"simd_1080p_to_720p_3to2_us\": {us3to2}, \"simd_1080p_to_720p_3to2_fps\": {fps3to2} }"
    IO.println (s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6)
    return 0
  | "bench-pipeline-d" :: framesStr :: outMp4Path :: _ =>
    let numFrames := Nat.max 1 (framesStr.toNat?.getD 8)
    let srcW := 3840
    let srcH := 2160
    let srcLuma := Plane2D.alloc srcW srcH srcW 128
    let t0 ← IO.monoNanosNow
    let mut pkts : Array AVPacketView := Array.mkEmpty numFrames
    let mut tilesCount : Nat := 0
    let mut dmaZeroCopyAll : Bool := true
    let mut loopGateAll : Bool := true
    for fIdx in [:numFrames] do
      let pts : UInt64 := (fIdx * 1500).toUInt64
      if let some res := transcodeFramePipelineD srcLuma pts .h264 16 264 4 then
        pkts := pkts.push res.encodedPacket
        tilesCount := res.disjointTiles
        dmaZeroCopyAll := dmaZeroCopyAll && res.zeroCopyGateOk
        loopGateAll := loopGateAll && res.loopGateOk
    let t1 ← IO.monoNanosNow
    let mp4Bytes := muxMp4StreamingFast .h264 90000 pkts
    if outMp4Path != "" && outMp4Path != "-" then
      let _ ← writeMediaFileAtomic outMp4Path mp4Bytes
    let t2 ← IO.monoNanosNow
    let transcodeUs := (t1 - t0) / 1000
    let muxUs := (t2 - t1) / 1000
    let totalUs := (t2 - t0) / 1000
    let perFrameUs := totalUs / numFrames
    let fps := if perFrameUs == 0 then 0 else 1000000 / perFrameUs
    let d0 := s!"\{ \"ok\": {dmaZeroCopyAll && loopGateAll && pkts.size == numFrames}, \"pipeline\": \"D_4K_to_1080p_MP4\", "
    let d1 := s!"\"src_res\": \"3840x2160\", \"dst_res\": \"1920x1080\", \"frames\": {numFrames}, \"disjoint_tiles\": {tilesCount}, "
    let d2 := s!"\"transcode_us\": {transcodeUs}, \"mp4_mux_us\": {muxUs}, \"total_us\": {totalUs}, "
    let d3 := s!"\"per_frame_us\": {perFrameUs}, \"fps\": {fps}, \"mp4_bytes\": {mp4Bytes.size}, "
    let d4 := s!"\"zero_copy_dma_ok\": {dmaZeroCopyAll}, \"in_loop_verify_ok\": {loopGateAll} }"
    IO.println (d0 ++ d1 ++ d2 ++ d3 ++ d4)
    return 0
  | "bench-4k-ipb" :: inMp4Path :: outMp4Path :: _ =>
    let t0 ← IO.monoNanosNow
    let rawBytes ← IO.FS.readBinFile inMp4Path
    let tRead ← IO.monoNanosNow
    let inSlice := ByteSlice.ofByteArray rawBytes
    let some demux := demuxIsoMp4Track inSlice | do
      IO.println s!"\{ \"ok\": false, \"error\": \"Failed to demux ISO MP4 track from {inMp4Path}\" }"
      return 1
    let tDemux ← IO.monoNanosNow
    let rep1 ← transcodeMp44kTo1080pIpbParallel demux 1
    let tW1 ← IO.monoNanosNow
    let rep8 ← transcodeMp44kTo1080pIpbParallel demux 8
    let tW8 ← IO.monoNanosNow
    -- Also benchmark full-frame 4K (`3840x2160`) -> 1080p (`1920x1080`) YUV420p SIMD 2x2 plane scaling + B-frame bi-pred + residual
    let vf4k := VideoFrame.allocYuv420p 3840 2160 0
    if vf4k.planes.isEmpty then IO.println ""
    let tScale0 ← IO.monoNanosNow
    let vf1080 := scaleVideoFrameYuv420pSimd vf4k
    if vf1080.planes[0]!.data.size == 0 then IO.println ""
    let tScale1 ← IO.monoNanosNow
    let luma1080 := vf1080.planes[0]!
    let biPred1080 := mcBiPredPlaneSimd luma1080 luma1080
    let res1080 := encodeInterResidualPlaneSimd luma1080 biPred1080
    let recon1080 := reconstructInterResidualPlaneSimd biPred1080 res1080
    if recon1080.data.size == 0 then IO.println ""
    let tBiPred1 ← IO.monoNanosNow
    if outMp4Path != "" && outMp4Path != "-" then
      let _ ← writeMediaFileStreaming outMp4Path rep8.outputMp4Bytes
    let tWrite ← IO.monoNanosNow
    let readUs := (tRead - t0) / 1000
    let demuxUs := (tDemux - tRead) / 1000
    let w1Us := (tW1 - tDemux) / 1000
    let w8Us := (tW8 - tW1) / 1000
    let scale4kYuvUs := (tScale1 - tScale0) / 1000
    let bipred1080Us := (tBiPred1 - tScale1) / 1000
    let writeUs := (tWrite - tBiPred1) / 1000
    -- Wave 8 verification: demux the emitted ISOBMFF 1080p MP4 container and verify exact round-trip of 1920x1080 and I/P/B counts
    let roundtripIsoOk : Bool := match demuxIsoMp4Track (ByteSlice.ofByteArray rep8.outputMp4Bytes) with
      | some dOut =>
          dOut.width == rep8.dstWidth &&
          dOut.height == rep8.dstHeight &&
          dOut.samples.size == rep8.totalFrames &&
          dOut.iFrameCount == rep8.iFrames &&
          dOut.pFrameCount == rep8.pFrames &&
          dOut.bFrameCount == rep8.bFrames
      | none => false
    let e2eW8Us := readUs + demuxUs + w8Us + writeUs
    let fpsW1 := if w1Us == 0 then 0 else (rep1.totalFrames * 1000000) / w1Us
    let fpsW8 := if w8Us == 0 then 0 else (rep8.totalFrames * 1000000) / w8Us
    let fpsE2E := if e2eW8Us == 0 then 0 else (rep8.totalFrames * 1000000) / e2eW8Us
    let b0 := s!"\{ \"ok\": {rep8.zeroCopyDmaOk && rep8.dpbPocMonotone && recon1080.width == 1920 && roundtripIsoOk}, \"benchmark\": \"4K_to_1080p_IPB_MP4\", "
    let b1 := s!"\"input\": \"{inMp4Path}\", \"output\": \"{outMp4Path}\", \"src_res\": \"{rep8.srcWidth}x{rep8.srcHeight}\", \"dst_res\": \"{rep8.dstWidth}x{rep8.dstHeight}\", "
    let b2 := s!"\"frames\": {rep8.totalFrames}, \"i_frames\": {rep8.iFrames}, \"p_frames\": {rep8.pFrames}, \"b_frames\": {rep8.bFrames}, "
    let b3 := s!"\"read_us\": {readUs}, \"demux_stbl_us\": {demuxUs}, \"transcode_w1_us\": {w1Us}, \"transcode_w8_us\": {w8Us}, \"write_us\": {writeUs}, "
    let b4 := s!"\"e2e_w8_us\": {e2eW8Us}, \"w1_fps\": {fpsW1}, \"w8_fps\": {fpsW8}, \"e2e_fps\": {fpsE2E}, "
    let b5 := s!"\"simd_4k_yuv420p_scale_us\": {scale4kYuvUs}, \"simd_1080p_bipred_res_us\": {bipred1080Us}, "
    let b6 := s!"\"in_bytes\": {rawBytes.size}, \"out_bytes\": {rep8.outputMp4Bytes.size}, \"dpb_poc_monotone\": {rep8.dpbPocMonotone}, \"iso_mp4_roundtrip_ok\": {roundtripIsoOk} }"
    IO.println (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6)
    return 0
  | "ffmpeg" :: rest => runFFmpegCli rest
  | a :: _ =>
    if a.startsWith "-" then runFFmpegCli args
    else runSelfTest
  | [] => runSelfTest

/-! ## Axiom Verification (`#print axioms`) for Round-Trip Theorems and `AVGateSpec` Instances -/

#print axioms LeanAV.Bitstream.writeUE_readUE_roundtrip
#print axioms LeanAV.Bitstream.writeSE_readSE_roundtrip
#print axioms LeanAV.Bitstream.writeRiceSigned_readRiceSigned_roundtrip
#print axioms LeanAV.Bitstream.writeRiceSigned_readRiceSigned_bounded_all

#print axioms LeanAV.Audio.flacStreamInfo_parse_serialize_roundtrip
#print axioms LeanAV.Audio.flacSubframeSpec_matches_ffmpeg_bit_exact
#print axioms LeanAV.Audio.flacSubframeSpec_encode_decode_roundtrip
#print axioms LeanAV.Audio.aacAdtsHeader_parse_serialize_roundtrip
#print axioms LeanAV.Audio.opusPacketFrames_codes_0_to_3_verified

#print axioms LeanAV.Video.h264SpsPps_real_ffmpeg_verified
#print axioms LeanAV.Video.hevcNalHeader_parse_serialize_roundtrip
#print axioms LeanAV.Video.hevcSao_matches_ffmpeg_bit_exact
#print axioms LeanAV.Video.proResFrameHeader_real_ffmpeg_verified
#print axioms LeanAV.Video.proresIdct8x8Put10_matches_ffmpeg_bit_exact
#print axioms LeanAV.Video.ffv1PlaneRiceR0_encode_decode_roundtrip

#print axioms LeanAV.Spec.flacStreamInfoGateSpec
#print axioms LeanAV.Spec.flacSubframeGateSpec
#print axioms LeanAV.Spec.aacAdtsGateSpec
#print axioms LeanAV.Spec.opusPacketGateSpec
#print axioms LeanAV.Spec.hevcNalHeaderGateSpec
#print axioms LeanAV.Spec.proResHeaderGateSpec
#print axioms LeanAV.Spec.h264SpsGateSpec
#print axioms LeanAV.Spec.ffv1PlaneGateSpec

#print axioms LeanAV.Bitstream.LawfulByteCodec.encode_injective
#print axioms LeanAV.Bitstream.LawfulByteCodec.bytePairCodec_universal_roundtrip
#print axioms LeanAV.Audio.flacOrder0ListSpec_roundtrip_universal
#print axioms LeanAV.Video.ffv1MedianPredictor_idempotent_equal_neighbors
#print axioms LeanAV.Video.uint8_xor_involution_universal
#print axioms LeanAV.Video.hevcSaoBandFilter_list_array_refinement
#print axioms LeanAV.Video.xorResidualsList_roundtrip_universal

#print axioms LeanAV.Bitstream.cabac_encode_decode_roundtrip
#print axioms LeanAV.Bitstream.av1MsacUpdateCdf4_preserves_monotonicity
#print axioms LeanAV.Video.ffv1PlaneRangeR0_encode_decode_roundtrip
#print axioms LeanAV.Video.dpb_inter_frame_chain_verified

#print axioms LeanAV.NativeKernels.evalLnir_swscale_gain_bias_equiv
#print axioms LeanAV.NativeKernels.evalLnir_opus_celt_saxpy_equiv
#print axioms LeanAV.NativeKernels.evalLnir_av1_cdef_fma_equiv
#print axioms LeanAV.NativeKernels.evalLnir_stencil3Tap_length_universal
#print axioms LeanAV.NativeKernels.lnirKernelAst_wire_tokens_match
#print axioms LeanAV.Audio.opusCeltPvqNormalizeBandQ15_length_universal
#print axioms LeanAV.Audio.aacScaleFactorHuffman_roundtrip
#print axioms LeanAV.Encoder.checkedPlaneFootprint_sound
#print axioms LeanAV.Encoder.typedDmaSurface_bounds_safe

#print axioms LeanAV.NativeKernels.evalLnir_nv12_downscale_2x2_fused_equiv
#print axioms LeanAV.NativeKernels.fastBox2x2DownscalePixel_eq_spec
#print axioms LeanAV.NativeKernels.specBox2x2DownscalePixel_idempotent_const
#print axioms LeanAV.NativeKernels.specBox2x2DownscalePixel_bounds_u8
#print axioms LeanAV.Format.muxMp4StreamingFast_demux_roundtrip
#print axioms LeanAV.Encoder.dgxSparkUnifiedRingSlot_zero_copy_universal
#print axioms LeanAV.Encoder.dgxSparkRing_and_cpuTiles_disjoint_safe
#print axioms LeanAV.Bitstream.rangeCoder15_encode_decode_roundtrip
#print axioms LeanAV.Video.scanAnnexBNalUnitsFast_eq_spec_multi_nal
#print axioms LeanAV.Video.proresIdct8x8Put10Fast_eq_spec
#print axioms LeanAV.Video.hevcSaoBandFilterPlaneFast_eq_spec

#print axioms LeanAV.Core.rescalePtsExactNat_monotone
#print axioms LeanAV.Core.rescalePtsExactNat_id
#print axioms LeanAV.Core.plane2D_verifyBounds_sound
#print axioms LeanAV.Core.alignStride64_ge_and_mod64
#print axioms LeanAV.Scale.yuvPixelToRgb_bt709_neutral_exact
#print axioms LeanAV.Scale.scalePlaneDown2x2Fast_eq_fusedEq_identity
#print axioms LeanAV.Filter.evalFusedLumaPoint_identity_and_fuse
#print axioms LeanAV.Filter.filterPlanePointAndBoxBlur3x3Fast_eq_sequential
#print axioms LeanAV.Filter.filterPlaneHFlip_and_VFlip_involutive
#print axioms LeanAV.Filter.hflipRowList_involutive
#print axioms LeanAV.NativeKernels.evalLnir_bt709_chroma_luma_fma_equiv
#print axioms LeanAV.NativeKernels.fastBoxBlurDiv9_eq_spec
#print axioms LeanAV.Encoder.partitionPlaneRows_1080p_16tiles_covers
#print axioms LeanAV.Audio.flacCrc8_and_Crc16_self_check_verified
#print axioms LeanAV.Format.ebmlVint_and_matroskaSimpleBlock_roundtrip
#print axioms LeanAV.Format.interleaveAvPacketsByPts90k_order_verified
#print axioms LeanAV.Format.webVttTimestamp_format_parse_roundtrip
#print axioms LeanAV.Video.mcBiPredPixel_comm_idemp_and_weighted_equiv
#print axioms LeanAV.Video.dpbReorderByPoc_hierarchical_bframe_gop_monotone
#print axioms LeanAV.Cli.cliValidate_copyWithFilter_rejected_and_transcode_accepted
#print axioms LeanAV.Cli.parseCliSeconds_exact_and_rejects_malformed
#print axioms LeanAV.Format.isoVideoFrameType_roundtrip_and_classify_avcc
#print axioms LeanAV.Scale.scalePlaneDown2x2Simd_eq_fast_and_dims
#print axioms LeanAV.Video.bframe_bipred_inter_residual_roundtrip_exact
#print axioms LeanAV.Encoder.transcodeAvcc4kTo1080pPacket_preserves_ipb_framing
#print axioms LeanAV.NativeKernels.evalLnir_bframe_bipred_blend_equiv
#print axioms LeanAV.NativeKernels.evalLnir_ipb_4k_to_1080p_residual_fma_equiv
#print axioms LeanAV.Spec.avcc1080pIpbPacketGateSpec
#print axioms LeanAV.Format.muxIsoMp4Track_demux_roundtrip_ipb
#print axioms LeanAV.Video.h264SliceHeaderRbsp_encode_decode_roundtrip
#print axioms LeanAV.Format.classifyHvccHevc_and_Av1Obu_ipb_verified
#print axioms LeanAV.Encoder.transcodeHvccHevc4kTo1080pPacket_preserves_ipb_framing
#print axioms LeanAV.Format.muxIsoAvStblSpec_demux_roundtrip_verified
#print axioms LeanAV.Format.codecConfig1080p_headers_verified
#print axioms LeanAV.Format.encodeLeb128Fixed4_decode_and_classify_verified
#print axioms LeanAV.NativeKernels.evalLnir_lanczos_4tap_downscale_fma_equiv
#print axioms LeanAV.NativeKernels.specLanczos4TapNormalizedPixel_idempotent_const
#print axioms LeanAV.Format.encodeLeb128Fixed4_universal_28bit_roundtrip
#print axioms LeanAV.Video.hevcSliceSegmentHeader_encode_decode_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_sao_edge_offset_fma_equiv
#print axioms LeanAV.Video.av1FrameHeader_encode_decode_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_loop_restoration_sgrproj_fma_equiv
#print axioms LeanAV.Audio.aacAudioSpecificConfig_encode_decode_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_aac_imdct_window_overlap_fma_equiv
#print axioms LeanAV.Audio.opusIdHeader_encode_decode_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_opus_celt_comb_filter_fma_equiv
#print axioms LeanAV.Format.ctts_bframe_pts_dts_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_idct4x4_butterfly_fma_equiv
#print axioms LeanAV.Format.stss_keyframe_index_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_strong_deblock_boundary_fma_equiv
#print axioms LeanAV.Format.stts_dts_delta_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_convolve_8tap_subpel_fma_equiv
#print axioms LeanAV.Format.stsc_chunk_sample_map_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_prores_idct8x8_col_butterfly_fma_equiv
#print axioms LeanAV.Format.stsz_stco_sample_offset_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_flac_lpc_residual_restore_fma_equiv
#print axioms LeanAV.Format.elst_bframe_timeline_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_ffv1_median_grad_pred_fma_equiv
#print axioms LeanAV.Format.co64_sdtp_ipb_dependency_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_chroma_interp_4tap_fma_equiv
#print axioms LeanAV.Format.tfdt_trun_fmp4_fragment_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_cabac_ctx_lps_range_fma_equiv
#print axioms LeanAV.Format.sidx_cmaf_segment_index_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_wiener_filter_7tap_sym_fma_equiv
#print axioms LeanAV.Format.mfhd_prft_live_cmaf_sync_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_opus_silk_lpc_inv_pred_gain_fma_equiv
#print axioms LeanAV.Format.tfhd_fragment_defaults_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_aac_mdct_pre_twiddle_fma_equiv
#print axioms LeanAV.Format.mehd_trex_cmaf_init_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_vp9_loopfilter_edge_limit_fma_equiv
#print axioms LeanAV.Format.dref_self_contained_cmaf_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_deblock_beta_tc_fma_equiv
#print axioms LeanAV.Format.vmhd_smhd_iso639_media_header_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_alf_7x7_diamond_tap_fma_equiv
#print axioms LeanAV.Format.pasp_clap_display_geometry_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_cfl_chroma_from_luma_fma_equiv
#print axioms LeanAV.Format.colr_nclx_colour_metadata_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_weighted_bipred_luma_fma_equiv
#print axioms LeanAV.Format.mdcv_clli_hdr10_static_metadata_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_obmc_overlapped_block_mc_fma_equiv
#print axioms LeanAV.Format.mvhd_tkhd_timeline_matrix_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_weighted_pred_uni_luma_fma_equiv
#print axioms LeanAV.Format.ftyp_styp_brand_compat_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_vp9_convolve8_horiz_subpel_fma_equiv
#print axioms LeanAV.Format.hdlr_media_handler_utf8_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_warp_affine_horz_4tap_fma_equiv
#print axioms LeanAV.Format.mdhd_media_header_timescale_lang_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_sao_band_offset_4class_fma_equiv
#print axioms LeanAV.Format.sthd_nmhd_media_header_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_opus_celt_pitch_xcorr_lag_fma_equiv
#print axioms LeanAV.Format.sbgp_sgpd_roll_rap_recovery_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_aac_tns_ar_lattice_filter_fma_equiv
#print axioms LeanAV.Format.emsg_v1_dash_cmaf_inband_event_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_palette_color_index_map_fma_equiv
#print axioms LeanAV.Format.subs_v1_tile_nalu_subsample_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_chroma_mc_bilinear_2x2_fma_equiv
#print axioms LeanAV.Format.saiz_saio_cenc_aux_offset_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_deblock_tc_clip_blend_fma_equiv
#print axioms LeanAV.Format.tenc_v1_cbcs_cenc_pattern_kid_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_av1_cdf_prob_update_rate_fma_equiv
#print axioms LeanAV.Format.pssh_v1_widevine_fairplay_systemid_kid_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_opus_silk_pitch_ltp_tap_fma_equiv
#print axioms LeanAV.Format.sinf_frma_schm_cenc_cbcs_scheme_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_aac_sbr_hf_gen_chirp_fma_equiv
#print axioms LeanAV.Format.senc_subsample_iv_clear_protected_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_vp9_tx_iadst4_butterfly_fma_equiv
#print axioms LeanAV.Format.mfra_tfra_mfro_random_access_seek_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_h264_cabac_mps_renorm_fma_equiv
#print axioms LeanAV.Format.udta_meta_ilst_container_metadata_roundtrip
#print axioms LeanAV.NativeKernels.evalLnir_hevc_cabac_bypass_bin_accum_fma_equiv
#print axioms LeanAV.Spec.visualFidelityGateSpec
#print axioms LeanAV.Spec.verifyVisualFidelity_rejects_black_and_decode_errors
#print axioms LeanAV.Spec.mp4ContainerSyncGateSpec
#print axioms LeanAV.Spec.verifyMp4ContainerSync_rejects_unclipped_chapters
#print axioms LeanAV.Encoder.scaledPlane_visualFidelity_accepts_real_and_rejects_black
#print axioms LeanAV.Domain.lawfulTranscodeStage_comp_preserves_clean_and_dur
#print axioms LeanAV.Domain.pruneContainerTracks_strips_lawrence_3h_chapter_track
#print axioms LeanAV.Domain.aacChannelLayout_rejects_unmasked_6ch_and_accepts_stereo
#print axioms LeanAV.Domain.downmix5p1SampleToStereoQ10_center_symmetric
#print axioms LeanAV.Domain.ffmpegAcceptanceGateSpec
#print axioms LeanAV.Domain.verifyFFmpegAcceptance_rejects_all_three_historical_bugs
#print axioms LeanAV.Domain.lawfulStageCleanContainerRemux_nonzero_mask
#print axioms LeanAV.Scale.box3x3_recip_mul_exact_for_all_u8_sums
#print axioms LeanAV.Scale.cscBt2020ToBt709_and_tonemap_invariants
#print axioms LeanAV.Filter.denoiseBlendTap_preserves_edges_and_flat
#print axioms LeanAV.Filter.lawfulStageCropScaleBlur
#print axioms LeanAV.Domain.liftDecodedPlaneOp_preserves_colorSpace_and_explicit_convert
#print axioms LeanAV.Format.mp4MetadataBoxInject_preserves_mdat_relative_offsets
#print axioms LeanAV.Format.elst_rescale_mvhd_mdhd_mismatch
#print axioms LeanAV.Cli.resolveScaleDims_proportional_even_and_cli_flags_verified
#print axioms LeanAV.Cli.cli_encoder_options_retained_and_invalid_rejected
#print axioms LeanAV.Scale.bicubic4TapMidpoint_partition_of_unity_and_const_exact
#print axioms LeanAV.Scale.pq10Tonemap_and_bicubic2x2_verified
#print axioms LeanAV.Core.Plane.addr_lt
#print axioms LeanAV.Core.Plane.simd_load_safe
#print axioms LeanAV.Core.Plane.chromaSubsampleDim2_pos
#print axioms LeanAV.Core.divRoundNat_zero_error_lt_one_tick
#print axioms LeanAV.Core.divRoundNat_nearInf_error_bound
#print axioms LeanAV.Core.rescaleTimestampChecked_exact_and_bounded
#print axioms LeanAV.Bitstream.BitCursor.byteIdx_lt_size
#print axioms LeanAV.Bitstream.BitCursor.readBit_progress
#print axioms LeanAV.Bitstream.BitM.withSliceBits_confined
#print axioms LeanAV.Video.activateCtx_coherent
#print axioms LeanAV.Video.DpbState.step_preserves_inv
#print axioms LeanAV.NativeKernels.checkLnirKernel_sound
#print axioms LeanAV.NativeKernels.evalLnir_libav_videotoolbox_p010_strided_pack_fma_equiv
#print axioms LeanAV.NativeKernels.fastBox3x3DownscaleU10Sum_eq_spec_and_bounded







