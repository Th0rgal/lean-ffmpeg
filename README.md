# lean-ffmpeg (`LeanAV`)

`lffmpeg` is a Lean 4 `v4.35.0` command-line tool with an `ffmpeg`-compatible interface. It builds and runs as a standalone binary: codec, container, and filter work that it accepts is done in-process. It does not bundle `ffmpeg` and it does not spawn one.

## Native, in-process

- H.264 High 8-bit 4:2:0 with AAC-LC or Opus in MP4/MOV/MPEG-TS (Baseline/Main/High, CAVLC and CABAC, I/P/B, 8x8 transform, frame crop, explicit and implicit weighted prediction, Q8 bilinear scale, mono/stereo AAC-LC)
- HEVC Main 8-bit 4:2:0 (`-i` / `-c:v hevc` and `hevc-probe`; Annex-B, `hvcC`, MP4/MOV, and MPEG-TS)
- AV1 Main 8-bit 4:2:0 (`-i` / `-c:v av1` and `av1-probe`; OBU, IVF, and MP4/MOV)
- Apple ProRes 422 (`-i` / `-c:v prores` in MP4/MOV)
- Opus audio (`-i` / `-c:a opus` in Ogg/Opus and MP4/MOV)
- MPEG-TS (`-i` / `-f mpegts` PAT/PMT/PES mux and demux) and Ogg (`-i` / `-f ogg` mux and demux)
- FFV1 version 3
- PNG (Zlib/DEFLATE)
- FLAC
- Stream copy for MP4, MOV, MKV, WebM, WAV, FLAC, and IVF
- lavfi sources and filters: `color`, `testsrc`, `nullsrc`, `overlay`, `split`, `hstack`, `vstack`, `sine`, `anullsrc`, `amix`, `amerge`, `asplit`, and `md5` / `framemd5`
- Scale and the `colorspace=bt709` / tonemap path

## Fail-closed

Unsupported input is rejected. It is not silently delegated to another binary. That includes codecs outside the native set (`aac_fixed`, VP9, VVC, and the rest), H.264 / HEVC / AV1 10-bit, 4:4:4, 4:2:2, High-10, RExt, and professional profiles, GPU acceleration (`-hwaccel`, CUDA, VAAPI, VideoToolbox), network and unsafe protocols, and `-filter_complex` graphs the lavfi typechecker rejects. The process exits non-zero, prints a structured diagnostic, and writes no output file.

## What the proofs cover

The Lean kernel check reports `0 sorryAx`; the only axioms are `{propext, Quot.sound, Classical.choice}`. `turbo-lean audit-spec` marks every audited specification `non_vacuous_and_tight` (no vacuous, trivial, or shadowed specs). `SymbolicTV` checks the 46 LNIR kernels for undefined behavior, domain, poison, return, and memory. Differential tests compare byte-exact or bounded-LSB output against a reference `ffmpeg` oracle that is not part of the binary. Counts, per-module tables, and the FATE record are in [`docs/VERIFICATION_APPENDIX.md`](docs/VERIFICATION_APPENDIX.md).

## TCB

The trusted computing base is the Lean 4 runtime, the `lean-sys` POSIX shim, `c/leanav_simd_kernels.c` (FFI and OS glue only; it no longer spawns a child), the 14 unproved LLVM outer shells, and the LLVM 18 backend. There is no `ffmpeg` in the TCB.

## Benchmarks

Published timings are historical and are not a speed claim for this commit. On a Ryzen 9 9950X the archived campaign measured 443.78 ms vs 486.39 ms FFmpeg for 1080p to 540p (1.10×) and 500.16 ms vs 946.64 ms for 540p plus tonemap plus BT.709 (1.89×); other rows in that table were slower. The accepted paired baseline `ae6ed0b` (1080p120 YUV420p to 960×540 lossless H.264) was 10.5057 s vs 10.2235 s FFmpeg 6.1.1, 2.86% slower, with `timing_valid: true`. A later noisy run was rejected because CV exceeded 3%. Methodology and the full table are in [`docs/BENCHMARK_EVIDENCE.md`](docs/BENCHMARK_EVIDENCE.md), [`docs/BOUNDED_BASELINE_20261028.md`](docs/BOUNDED_BASELINE_20261028.md), and [`docs/benchmark-campaign-excerpt.json`](docs/benchmark-campaign-excerpt.json).

## Build

Requires Lean `v4.35.0`, a sibling checkout of [`lean-sys`](https://github.com/Th0rgal/lean-sys) at `077775ba387f1eeb2976cb8763b4633b8d5ce313`, and `clang`. A system `ffmpeg` is used only as an external oracle for `tests/differential`.

```bash
lake build
./scripts/regen_lnir_c_kernels.sh --check-ir
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels
lake env lean scripts/check_axioms.lean
```
