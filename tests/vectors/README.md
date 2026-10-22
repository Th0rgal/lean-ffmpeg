# LeanAV Real Media Test Vectors & FFmpeg Bit-Exact Oracle Reference

All test vectors in this directory were generated and extracted using the official FFmpeg build from `/var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/FFmpeg` (`ffmpeg version git-2026-10-22-bf0e831`).

## Vector Files

1. `flac_vectors.txt`
   - **T1**: 42-byte `fLaC` + `STREAMINFO` header (`0x664C6143...`) extracted from `artifacts/real_media/t1_sine.flac`.
   - **T2**: Real 64-sample 16-bit FLAC Fixed Order-2 subframe (`stype = 10`, 48 bytes) and LPC Order-8 subframe (`stype = 39`, 75 bytes) with bit-exact PCM16LE output verified against `ffmpeg -i ... -f wav`.

2. `aac_adts_vectors.txt`
   - **T1**: 7-byte AAC ADTS frame header (`fff14c4016dffc`) extracted from `artifacts/real_media/t1_sine.aac`.

3. `opus_vectors.txt`
   - **T1**: Opus TOC and frame-count demux vectors (RFC 6716 Section 3.1–3.2 codes `0..3`, including Code 3 CBR and VBR with padding) extracted from `artifacts/real_media/test_audio.ogg`.

4. `h264_sps_pps_vectors.txt`
   - **T1**: H.264 Annex-B SPS (`nal_unit_type = 7`, 27 bytes) and PPS (`nal_unit_type = 8`, 7 bytes) extracted from `artifacts/real_media/test_720p.264`.

5. `hevc_sao_vectors.txt`
   - **T1**: 2-byte HEVC NAL unit headers (`VPS = 4001`, `SPS = 4201`, `PPS = 4401`, `IDR_W_RADL = 2601`) from `FFmpeg/tests/api/api-hevc-mp4toannexb-test.c`.
   - **T2**: HEVC Sample Adaptive Offset (`SAO`) Band Offset (`BO`) and Edge Offset (`EO` classes `0..3`: 0°, 90°, 135°, 45°) bit-exact reference over the 8x8 real grayscale plane `artifacts/real_media/t1_8x8.gray` vs FFmpeg `libavcodec/h26x/h2656_sao_template.c`.

6. `prores_vectors.txt`
   - **T1**: Apple ProRes frame header (`icpf`, 156 bytes, `64x64`, `chromaFormat = 2`, `qmatFlags = 0x03` luma+chroma matrices) extracted from `artifacts/real_media/t1_64_prores.mov`.
   - **T2**: Apple ProRes 8x8 10-bit integer IDCT (`prores_idct_put_10`) bit-exact reference vs FFmpeg `libavcodec/proresdsp.c` + `libavcodec/simple_idct_template.c`.

7. `ffv1_vectors.txt`
   - **T2**: FFV1 plane R0 lossless median predictor (`mid_pred` / Paeth) + signed Rice-Golomb round-trip and bit-exact verification against `ffmpeg -i artifacts/real_media/t1_16_ffv1.avi -f rawvideo -pix_fmt gray` and `artifacts/real_media/t1_8x8.gray`.
