# lean-ffmpeg

`lean-ffmpeg` is a small media-processing experiment with formally specified and verified components inspired by FFmpeg. It is **not** a drop-in replacement for FFmpeg: the current CLI targets a narrow MP4-focused subset. Its intended fail-closed behavior is incomplete; differential testing has found accepted operations that are not honored correctly.

## The idea

FFmpeg is the result of roughly 26 years of development by thousands of people. Its codecs, formats, filters, portability layers, and bug fixes represent an enormous engineering effort; the project has also found more than 1,000 bugs through fuzzing and related testing.

This repository explores the opposite trade-off:

- a much smaller implementation built in about 26 hours;
- executable specifications and formal proofs for important codec, bitstream, pixel, timestamp, and safety properties;
- native C/SIMD kernels behind typed Lean interfaces;
- performance work focused on selected pipelines rather than universal FFmpeg compatibility.

The comparison is about engineering constraints, not replacement claims: FFmpeg wins on breadth and maturity; `lean-ffmpeg` investigates how much correctness and performance can be made explicit and machine-checked in a small system.

## What existed before the FFmpeg-parity hardening

Before the recent CLI compatibility work, the repository had already built most of its core experiment:

- verified AV codec and bitstream components for H.264, HEVC, AV1, FFV1, FLAC, Opus, AAC, and ProRes;
- MP4, IVF, MPEG-TS, Ogg, WAV, and Annex-B parsing experiments;
- formally specified scaling, filtering, color conversion, HDR metadata, timestamps, DPB state, and DMA/FFI boundaries;
- native SIMD paths for selected scaling and video operations;
- an in-process 4K-to-1080p pipeline with parallel workers, H.264/AAC output, and MP4 muxing;
- self-tests, FFmpeg-derived reference vectors, stage benchmarks, and visual verification tools.

The later parity work tightened rejection of unsupported codecs, formats, filters, and options, along with overwrite behavior, JSON escaping, diagnostics, and platform builds. This is ongoing hardening, not a guarantee of CLI parity or complete fail-closed behavior.

## Current CLI

```text
lffmpeg -i INPUT [-c:v h264|hevc|av1|copy] [-c:a aac|copy] [options] OUTPUT.mp4
```

Recognized options include `-y`, `-n`, `-vf`, `-ss`, `-t`, `-f mp4`, `-pix_fmt`, `-preset`, `-crf`, `-b:v`, `-b:a`, `-r`, and `-json`. Recognition does not imply FFmpeg-equivalent semantics; see the known limitations below.

The library contains more codec and filter models than the CLI currently wires to delegated media execution. Formal/library capability and CLI capability are deliberately documented separately.

## Benchmarks

The repository's built-in benchmarks are useful for tracking selected kernels and pipelines, but they are not an apples-to-apples replacement benchmark against FFmpeg. They measure different scopes unless both programs are run on the same input, output, codec settings, thread settings, and verification criteria.

A measured x86 run on the current Linux build produced:

| Benchmark | Result |
| --- | ---: |
| 4K -> 1080p parallel pipeline, 8 frames, 8 workers | 1,721 fps |
| 4K -> 1080p SIMD 2x2 scaling, 8 frames | 618 fps |
| 4K -> 720p scaling, 8 frames | 210 fps |
| 1080p -> 720p scaling, 8 frames | 1,041 fps |
| 4K -> 1080p MP4 pipeline, 8 frames | 166 fps |
| MP4 micro-demux, 100 iterations | 50 us |
| FLAC order-4 round-trip, 100 iterations | 43 us |

These numbers are from the built-in synthetic/in-process benchmarks on one x86 Linux host. They should not be read as FFmpeg speed claims. A direct FFmpeg comparison requires a real FFmpeg binary and matched workloads; neither the system FFmpeg binary nor SSH access to the MacBook Air M2 or DGX Spark was available in the benchmark environment used for this snapshot.

Useful commands:

```sh
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg bench 1000
./.lake/build/bin/lffmpeg bench-scaling 8
./.lake/build/bin/lffmpeg bench-pipeline-d 8 /tmp/lffmpeg.mp4
```

## Known differential-testing limitations

Differential tests against FFmpeg found remaining gaps in delegated execution: some 10-bit color filters can relabel metadata without transforming pixels; edit-list handling can lose encoded frames; `-r` can alter playback duration instead of performing frame-rate conversion; zero or sub-millisecond durations are mishandled; color-matrix metadata can be normalized without converting samples; filter chains are not always applied sequentially; and solid-color inputs can be rejected by the visual-acceptance heuristic. CLI error paths and JSON escaping also need further hardening. These findings are tracked as implementation work rather than hidden behind compatibility claims.

## Verification

The current project includes:

- Lean proofs for the formal specifications;
- native-kernel and C-ABI gates;
- FFmpeg-derived reference vectors;
- fail-closed CLI tests;
- platform build checks for Linux and macOS;
- axiom and `turbo-lean` checks.

The headline is therefore deliberately narrow: `lean-ffmpeg` is a compact, formally checked and optimized experiment over selected media paths, not a claim to reproduce FFmpeg's 26 years of breadth in 26 hours.

## Status

Experimental. Contributions should prefer explicit specifications, proof obligations, deterministic tests, and honest capability boundaries over silent compatibility gaps.
