# lean-ffmpeg (`LeanAV`)

Formally verified **Lean 4** (`v4.35.0`) multimedia pipeline and `ffmpeg`-compatible CLI (`lffmpeg`). It pairs **22 formal Lean 4 modules** (`LeanAV/*.lean`, `40,519` LOC), **21 direct `@[export]` C-ABI entrypoints** (`leanav_lean_*`), **46 compiled `LNIR_WIRE_V1` DSP/stencil/pixel-core kernels** (`c/leanav_lnir_kernels.lnir`: 29 data-parallel SIMD kernels + 17 scalar `@lnir_px_*` pixel cores), and **14 thin 2D strided/reduction/filter/16-bit LLVM 18 outer-loop shells** (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`, deterministically emitted by `scripts/gen_lnir_outer_shells.py` and calling the compiled `@lnir_px_*` cores directly) with a **`1,179`-line** C-ABI/POSIX/SIMD bridge (`c/leanav_simd_kernels.c`), backed by **`0 sorryAx`** and **`0` custom axioms** across **`13,219`** declarations (`scripts/check_axioms.lean`) and **`489 / 489` `non_vacuous_and_tight`** formal specifications audited by [`turbo-lean`](https://github.com/Th0rgal/turbo-lean) (`dc1656dc948f1d7bfc25d165575ae3819a2e8b97`).

`lffmpeg` is currently a **formally gated hybrid multimedia pipeline**, not yet a standalone zero-dependency replacement for `ffmpeg`:
- **Native in-process execution (`independent_verified` & pure Lean/LNIR stages of `translated_partial`)**: CLI parsing and `MediaPlanIR` validation, fail-closed path/protocol security gates, ITU-T H.264 §8.4/§8.7/§8.2.4/§8.2.5 inter prediction (6-tap quarter-pel luma MC, 1/8-pel chroma bilinear MC, explicit/implicit weighted prediction, median/directional MVP, P-Skip, spatial/temporal B-direct, sub-pel diamond ME + RDO), in-loop deblocking (`bS 0..4`), and Decoded Picture Buffer (`pic_order_cnt_type 0/1/2`, RPLM, MMCO `1..6`, sliding-window wraparound, B-pyramid POC bumping, and Annex-B stream simulation), standalone FFV1 version 3 lossless video encode/decode/remux (`yuv420p`, `gray`, `rgb24`, `bgr0`, Golomb-Rice & range coders, context models `0`/`1`, `1..64` slices, CRC-32 `slicecrc`) across Matroska (`.mkv`), QuickTime (`.mov`), AVI (`.avi`), `rawvideo`, `yuv4mpegpipe` (`.y4m`), `md5`, and `framemd5`, standalone lossless PNG + Zlib/DEFLATE (RFC 1950 / RFC 1951) and FLAC (RFC 9639) stream decode/encode (`rawvideo <-> .png`, `.png -> .png`, `.wav` / `u8` / `s16le` / `s24le` / `s32le <-> .flac`, `.flac -> .flac`), and native zero-exec stream copy & trim across MP4/MOV/M4V/M4A, MKV/WebM, WAV, FLAC, and IVF (all with zero `ffmpeg` subprocesses), exact `AVRational` timestamp rescaling, 8-bit and 10-bit (`U16LE`) plane scaling (`1:1` zero-copy identity, `2:1`, `3:1`, `3:2`, and general Q8 bilinear), 64-bit SWAR Annex-B NAL scanning, PQ10/BT.2020 -> BT.709 colorimetry and tonemapping, AV1 CDEF/Wiener and HEVC SAO filtering, Order-4 FLAC LPC prediction/decoding, 16x16 macroblock PSNR/SAD luma acceptance, and ISO BMFF (`moov`, `colr`, `clli`, `mdcv`, `pasp`, `edts`/`elst`), IVF, Matroska (`SimpleBlock`), and 188-byte MPEG-TS container parsing/patching execute in Lean 4 + compiled LNIR/LLVM routines.
- **External `ffmpeg` process delegation (`translated_partial` raw bitstream pipes & `delegated_faithful`)**: Full entropy/transform video/audio codec bitstream decode/encode (`h264`, `hevc`, `av1`, `aac`, etc.) in `translated_partial` pipelines uses ring-buffered POSIX pipes to `ffmpeg` without `/bin/sh`, and general container/filtergraph/muxer workflows in `delegated_faithful` lower through `MediaPlanIR` to structured `fork` + `execvp` calls against a pinned reference `ffmpeg` (`6.1.1`).

---

## Architecture, Execution Tiers & Trusted Computing Base (TCB)

### Qualification Tiers (`MediaPlanIR`)

Every CLI invocation is parsed into [`MediaPlanIR`](LeanAV/PlanIR.lean), checked against a fail-closed security policy (formally proved rejection of network protocols, `/dev/*` device nodes except `/dev/null`, and `..` path traversals), and routed to one of four runtime execution tiers:

| Tier | Execution Mechanism | Scope & Examples |
| :--- | :--- | :--- |
| **`independent_verified`** | Pure Lean 4 + compiled `LNIR_WIRE_V1` kernels with zero `ffmpeg` subprocesses; out-of-domain inputs trigger explicit `fallbackDelegated` | Standalone FFV1 v3 encode/decode/remux (`yuv420p`, `gray`, `rgb24`, `bgr0`, MKV/MOV/AVI/Y4M/`md5`/`framemd5`), standalone PNG + Zlib/DEFLATE (`rawvideo <-> .png`, `.png -> .png`) and FLAC (`.wav` / raw PCM `<-> .flac`, `.flac -> .flac`) lossless codecs, native zero-exec stream copy & trim (`-ss`, `-t`, `-to`, `-map`, `-metadata`) across MP4/MOV/M4V/M4A, MKV/WebM (`SimpleBlock` / `BlockGroup` + cues), WAV, FLAC, and IVF, `2x2` / `3x3` / `3:2` / Q8 bilinear plane scaling, `3x3` box-blur stencil, luma mean/variance reduction, Order-4 FLAC LPC, AV1 CDEF/Wiener, HEVC SAO, 188B MPEG-TS demux, and exact `AVRational` PTS rescaling |
| **`translated_partial`** | Pure Lean 4 + LLVM/SIMD scaling, colorimetry (`PQ10`/`BT.2020` -> `BT.709`), 16x16 luma PSNR/SAD acceptance, and surgical ISO BMFF box patching, paired with ring-buffered POSIX pipe `ffmpeg` raw-frame decode/encode (zero `/bin/sh`) | MP4 transcoding (`h264`, `hevc`, `av1`, `aac`, `-ss`, `-t`, `-vf scale/colorspace=bt709/tonemap`), JSON media probing |
| **`delegated_faithful`** | Validated `MediaPlanIR` lowered to structured `fork` + `execvp` (zero shell interpolation) against reference `ffmpeg` | General muxers/demuxers (`.mkv`, `.webm`, `.mov`, `.wav`, `.flac`, `.ogg`, `.ts`, `.avi`, `.fits`, `.pfm`, `.wbmp`, `hls`, `dash`, `iamf`, `spdif`), `-map`, `-metadata`, `-disposition`, `-bsf`, `-filter_complex` |
| **`unsupported`** | Deterministic fail-closed rejection with structured diagnostics (`stdout` in `-json` mode, `stderr` otherwise) and zero partial output artifacts | Network/unsafe protocols (`http://`, `rtsp://`, `lavfi:`, `concat:`, `/dev/*`, `..`), contradictory codec/filter flags (`-c:v copy -vf ...`) |

### Verification Boundary & Unverified TCB

| Layer | Component | Verification Status |
| :--- | :--- | :--- |
| **Verified Lean 4 Core** | 22 `LeanAV/*.lean` modules (`13,219` declarations) | Kernel-checked under Lean `v4.35.0` (`0 sorryAx`, `0` custom axioms; standard axioms `{propext, Quot.sound, Classical.choice}` only) |
| **Specification Audit** | `489 / 489` `AVGateSpec` & theorem specs | Audited by `turbo-lean@dc1656d` (`audit-spec` v2.1): `489/489 non_vacuous_and_tight`, `0 vacuous`, `0 trivial`, `0 shadowed` |
| **Compiled `LNIR_WIRE_V1` Kernels** | 46 DSP/stencil/pixel-core kernels in `c/leanav_lnir_kernels.lnir` (29 data-parallel SIMD + 17 scalar `@lnir_px_*` cores) | `46/46` pass `lean-native-core validate-tv --samples 64` (`SymbolicTV` UB/domain/poison/return/memory refinement); `verify-certs` passes (`verified: true`, `chainValid: true`, `theoremsValid: true` across all 46 kernels: `37 VerifiedKernelProof`, `8 TranslationValidated`, `1 Tested`) |
| **Unverified TCB (§6.8 Disclosure)** | `c/leanav_simd_kernels.c` (`1,179` lines), 14 thin 2D strided/tiling/narrow-memory (`i8`/`i16` GEP + `zext`/`trunc`) + scalar-accumulator outer LLVM IR shells (`1,454` lines in `c/leanav_lnir_{x86_64,arm64}.ll` generated by `scripts/gen_lnir_outer_shells.py` that delegate all pixel arithmetic to the verified `@lnir_px_*` cores; strided narrow-width loops remain blocked upstream at `turbo-lean@dc1656d`, see [`docs/M1_LNIR_DSP_LIFT_BLOCKER_20261029.md`](docs/M1_LNIR_DSP_LIFT_BLOCKER_20261029.md)), Lean 4 runtime + `lean-sys` POSIX shim (`63` lines), LLVM 18 backend, and external `ffmpeg` (`6.1.1`) when delegated | Zero-drift IR gate (`./scripts/regen_lnir_c_kernels.sh --check-ir`), IR-structural/call-wiring (`tests/test_u16le_kernels_ir.py`, `tests/test_pixel_filters_ir.py`), differential, and runtime (`verify-ffi`, `verify-kernels`) tested, **outer shells not formally proved in Lean** |

---

## Upstream FFmpeg FATE Conformance Evidence (2026-10-29 Wave 2)

Upstream FFmpeg (`bf0e831606938f530326c9679591109407fa8d0d`) defines **`6,133` inventory rows** (`reports/fate-inventory-v3.json`): **`5,721` configured baseline targets** plus **`412` build-disabled rows** (`344` real disabled upstream targets + `68` source-scanner overapproximations), yielding **`6,065` real upstream FATE targets**.

In the Wave 2 sweep (`reports/fate-sweep-wave2-complete-20261029.json`, SHA-256 `43c08c087c812e3a8feac4c3e757c848fceda80c17d1b09e2e6a1f3c23367147`), exact-arm `target_exec.py` substitution replaced only the `ffmpeg` binary with `lffmpeg` (while `LEANAV_FFMPEG_BIN` pointed to each suite's isolated scratch reference `ffmpeg`, and `ffprobe` / C API test binaries ran directly without candidate credit):

| FATE Partition | Targets | Status-Zero | Candidate-CLI Exercised Passes | Non-CLI / Helper Passes (`0` Credit) | Notes |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **Configured baseline (`full_configured_5721`)** | 5,721 | **5,721 / 5,721** | **5,086 / 5,086** | 635 | Includes `221` wrapper/helper rows (`libavformat/tests/seek`, `libswresample/tests/rematrix`, `ffprobe`) kept at `0` candidate credit |
| **Isolated `zlib` suite (`suite_b_zlib_209`)** | 209 | **209 / 209** | **203 / 203** | 6 | PNG/APNG/ZLIB/Matroska-zlib targets |
| **Isolated `--enable-gpl` suite (`suite_c_gpl_57`)** | 57 | **57 / 57** | **53 / 53** | 4 | GPL filter/muxer targets |
| **Isolated external-lib suites (`suite_d_ext_37`)** | 37 | **36 / 37** | **28 / 28** | 8 | `1` non-candidate C API helper failure (`fate-api-astc-profile` in `astcenc 5.4.0`, `lffmpeg` never invoked; fails identically upstream) |
| **x86asm + host-runnable HW helpers** | 6 | **6 / 6** | 0 | 6 | `fate-sws-*-x86`, `fate-av1-levels`, `fate-sws-*-spirv`, `fate-hwcontext-cuda` |
| **Unavailable host hardware / arch** | 35 | Not runnable | — | — | `33` `fate-filter-scale_cuda-*` (no NVIDIA GPU on host; all `33` argvs verified clean via `lffmpeg -dump-plan`) + `2` native `aarch64` (`fate-sws-*-aarch64`) |
| **Disjoint Total (`6,065` real targets)** | **6,065** | **6,029 / 6,030 run** | **5,370 / 5,370 (`0` candidate failures)** | **659** | **Scoped conformance evidence (`global_parity: false`)** |

**Scope limitations on FATE conformance**:
1. Passing FATE targets through `delegated_faithful` or `translated_partial` validates CLI parsing, `MediaPlanIR` lowering, path/option hygiene, and pipeline compatibility—**not** standalone native codec parity.
2. Full-suite (`5,721`-target) kernel eBPF syscall-provenance certification has not yet been executed (`full_fate_syscall_provenance_certified: false`, `global_parity: false`).
3. Repository CI runs the project unit/differential suites (`137` unit suite entries [`137` passed] + `113` differential suite entries [`109` passed, `4` skipped without optional external fixtures] locally; platform-dependent subsets on GitHub-hosted runners), not the multi-gigabyte upstream `fate-suite` corpus.

---

## Performance & Bounded Baselines

Output correctness (`quality_passed`) and timing repeatability (`timing_valid`, requiring paired & per-arm `CV < 3.0%`) are tracked strictly separately. See [`docs/BOUNDED_BASELINE_20261028.md`](docs/BOUNDED_BASELINE_20261028.md) and [`docs/BENCHMARK_EVIDENCE.md`](docs/BENCHMARK_EVIDENCE.md).

### Stage-2 Bounded Paired Baselines (`1080p120` YUV420p -> `960x540` Lossless H.264, Xeon E3-1245 V2)

Workload: 120 frames of `1920x1080` YUV420p scaled to `960x540` H.264 lossless (`-preset veryfast -crf 0`), 2 warmups + 5 alternating pairs, pinned to `cpu0-3` with THP enabled; all 14 outputs per run verified byte-exact (`81,424,133` bytes, SHA-256 `e31886830cff40551868345f60259ffea0ee279b9b2af6515c46198ab06c94de`):

| Candidate | Quality (`14/14` Oracle Byte-Exact) | Candidate Median | FFmpeg 6.1.1 Median | Median Paired Ratio | Candidate / Ref CV | Timing Status |
| :--- | :--- | ---: | ---: | ---: | ---: | :--- |
| **`ae6ed0b` (`paired-baseline-v5-ae6ed0b-thp-a`)** | `quality_passed: true` | `10.5057 s` | `10.2235 s` | `1.028612` (**`+2.86%` slower**) | `1.417%` / `0.382%` | **Accepted (`timing_valid: true`)** |
| **Wave 2 `357e1a4` (`paired-baseline-v5-wave2-357e1a4-thp-a`)** | `quality_passed: true` (+ Stage-1 `17,577` checks) | `10.8803 s` (noisy) | `11.0227 s` (noisy) | `0.995431` *(unvalidated)* | `6.851%` / `6.350%` | **Fail-closed rejected (`timing_valid: false`, `CV > 3%`)** |

In the Wave 2 `357e1a4` run (which added the 64-slot POSIX pipe/pthread ring buffer `execPipeTranscodeU8IO` and `<16 x i32>` AVX2/NEON row accumulators), external sibling-tenant workloads on `cpu4-7` SMT threads caused `CV > 3.0%` mid-run; uncontended `pair-0` observed `10.2768 s` (`lffmpeg`) vs `10.3239 s` (`ffmpeg`), but **no speedup claim is accepted** until a quiet-host rerun passes `CV < 3.0%`.

### Historical Cross-Hardware Campaign Measurements

Recorded in [`docs/benchmark-campaign-excerpt.json`](docs/benchmark-campaign-excerpt.json) from an earlier revision (not a measurement of the current commit; includes decode/encode I/O; **Speedup = FFmpeg time / lffmpeg time**, `< 1.0×` means slower):

| Hardware | Workload | FFmpeg 6.1.1 | lffmpeg | Speedup |
| :--- | :--- | ---: | ---: | ---: |
| **x86 — Ryzen 9 9950X (Zen 5)** | 1080p -> 540p | 486.39 ms | **443.78 ms** | **1.10×** |
| x86 — Ryzen 9 9950X | 1080p -> 480p, Q8 | 478.41 ms | 501.88 ms | 0.95× |
| **x86 — Ryzen 9 9950X** | 540p + tonemap + BT.709 | 946.64 ms | **500.16 ms** | **1.89×** |
| x86 — Ryzen 9 9950X | Stream copy | 38.46 ms | 51.69 ms | 0.74× |
| **DGX Spark — ARM64 CPU** | 1080p -> 540p | 225.77 ms | 309.03 ms | 0.73× |
| DGX Spark — ARM64 CPU | 1080p -> 480p, Q8 | 209.78 ms | 350.85 ms | 0.60× |
| **DGX Spark — ARM64 CPU** | 540p + tonemap + BT.709 | 446.96 ms | **310.62 ms** | **1.44×** |
| DGX Spark — ARM64 CPU | Stream copy | 51.11 ms | 79.16 ms | 0.65× |
| **MacBook Air M2** | Comparative CLI benchmarks | — | — | **Not measured** |

DGX Spark figures above measure the Grace ARM64 CPU path (PTX assembly validation is separate from live GPU dispatch). In-memory native kernel microbenchmarks (excluding codec I/O) are archived in [`docs/BENCHMARK_EVIDENCE.md`](docs/BENCHMARK_EVIDENCE.md).

---

## Declarative Formal Specifications (`AVGateSpec`) & Zero-Trust Audit (`turbo-lean`)

Each safety and conformance gate implements [`AVGateSpec`](LeanAV/Spec.lean), connecting an executable C-ABI gate (`UInt8`) to an independent declarative `Prop` predicate (`sound`, `complete`, `posWitness`, `negWitness`, `nonVacuous`, `tight`).

All **22** `LeanAV/*.lean` modules (**`489 / 489` specifications**) pass `turbo-lean --json audit-spec` (`dc1656d`, v2.1) as `non_vacuous_and_tight` with **`0 vacuous`**, **`0 trivial`**, **`0 shadowed`**, and **`0 sorryAx`** across **`13,219`** kernel-checked declarations (`Format`: 63, `H264InterDeblockDpbProofs`: 61, `Ffv1Proofs`: 60, `NativeKernels`: 59, `Video`: 46, `Audio`: 34, `Encoder`: 30, `Scale`: 28, `Bitstream`: 27, `Spec`: 23, `PlanIR`: 20, `Core`: 11, `Domain`: 8, `Md5`: 7, `Cli`: 6, `Filter`: 6).

---

## Build & Verification

Requires Lean `v4.35.0` ([`lean-toolchain`](lean-toolchain)), sibling checkout [`Th0rgal/lean-sys`](https://github.com/Th0rgal/lean-sys) (`../lean-sys` at `077775ba387f1eeb2976cb8763b4633b8d5ce313`), `clang`, and `ffmpeg` (`>= 6.1`) for differential/delegated tests.

```bash
# 1. Build LeanAV, 46 LNIR kernels + 14 wired 2D/16-bit outer shells, and the 1,179-line C-ABI bridge
lake build

# 2. Run all 53 formal self-test waves, C-ABI gates, compiled LNIR kernel checks, and zero-drift IR check
./scripts/regen_lnir_c_kernels.sh --check-ir
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# 3. Verify 0 sorryAx and 0 custom axioms across all 13,219 LeanAV.* declarations
lake env lean scripts/check_axioms.lean

# 4. Audit all 22 formal modules with turbo-lean (489/489 non_vacuous_and_tight)
for file in LeanAV/*.lean; do turbo-lean --json audit-spec "$file" || exit; done

# 5. Validate the 46 LNIR_WIRE_V1 kernels via SymbolicTV and certificate checking
lean-native-core validate-tv --in c/leanav_lnir_kernels.lnir --out /tmp/lnir_certs.txt --samples 64
lean-native-core verify-certs --in c/leanav_lnir_kernels.lnir --certs /tmp/lnir_certs.txt

# 6. Run unit, IR-structural, and differential test suites
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_*.py"
```

---

## Repository Structure

- [`LeanAV/`](LeanAV/): 22 formal Lean 4 modules (`0 sorryAx`, `13,219` declarations, `489/489` tight specs): `Spec.lean`, `Domain.lean`, `Core.lean`, `Bitstream.lean`, `Format.lean`, `Video.lean`, `Audio.lean`, `Scale.lean`, `Filter.lean`, `Encoder.lean`, `NativeKernels.lean`, `Cli.lean`, `PlanIR.lean`, `Md5.lean`, `Ffv1.lean`, `Ffv1Container.lean`, `Ffv1Pipeline.lean`, `Ffv1Proofs.lean`, `H264InterDeblockDpb.lean`, `H264InterDeblockDpbProofs.lean`, `IO.lean`, `Main.lean`.
- [`c/`](c/):
  - [`c/leanav_simd_kernels.c`](c/leanav_simd_kernels.c) (`1,179` lines): POSIX `fork` + `execvp` delegation shim, `pread`/`pwrite` window I/O shims, 64-slot ring-buffered POSIX pipe/pthread `leanav_c_exec_pipe_transcode_u8` raw-frame bridge, Phase 5 FFI ABI / `__ATOMIC_SEQ_CST` cancellation shims, and zero-copy `lean_sarray_object` wrappers for the compiled LLVM routines.
  - [`c/leanav_lnir_kernels.lnir`](c/leanav_lnir_kernels.lnir), [`c/leanav_lnir_kernels.h`](c/leanav_lnir_kernels.h), [`c/leanav_lnir_x86_64.ll`](c/leanav_lnir_x86_64.ll), [`c/leanav_lnir_arm64.ll`](c/leanav_lnir_arm64.ll): 46 `LNIR_WIRE_V1` DSP/stencil/pixel-core kernels (29 data-parallel SIMD + 17 scalar `@lnir_px_*` cores) + 14 thin 2D strided/reduction/filter/16-bit LLVM 18 outer-loop shells (`x86_64` and `arm64`, wired directly to `@lnir_px_*`) linked into `libleanav_dsp.a`.
- [`tests/`](tests/): Python unit, LLVM IR structural, and differential test suites against `ffmpeg`/`ffprobe` (including portable C-instrumented zero-copy 10-bit identity tests in `tests/differential/test_u16le_identity.py`).
- [`docs/`](docs/): Maxwell parity plan ([`FFMPEG_PARITY_MAXWELL_PLAN.md`](docs/FFMPEG_PARITY_MAXWELL_PLAN.md)), capability registry ([`capability-registry.json`](docs/capability-registry.json)), contracts ([`docs/contracts/`](docs/contracts/)), bounded baseline reports ([`BOUNDED_BASELINE_20261028.md`](docs/BOUNDED_BASELINE_20261028.md), [`BENCHMARK_EVIDENCE.md`](docs/BENCHMARK_EVIDENCE.md)), and closure dossier ([`CAMPAIGN_CLOSURE_DOSSIER.md`](docs/CAMPAIGN_CLOSURE_DOSSIER.md)).
