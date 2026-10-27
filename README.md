# lean-ffmpeg (`LeanAV`)

Formally verified **Lean 4** (`v4.31.0`) multimedia pipeline and `ffmpeg`-compatible CLI (`lffmpeg`). It pairs pure **Lean 4** container/DSP/scaling/transcode pipelines and **16 LeanNative (`LNIR_WIRE_V1`)** DSP/stencil kernels + **14 LLVM 18 2D strided/reduction/filter/16-bit routines** compiled through LLVM 18 (`leanav_lnir_x86_64.ll` and `leanav_lnir_arm64.ll`) and NVIDIA PTX 8.0 (`sm_90`) with a minimal **`621`-line** irreducible C-ABI bridge (`c/leanav_simd_kernels.c`), backed by **`0 sorryAx`** across **`8,887`** declarations (verified under `v4.35.0`) and **`264 / 264` `non_vacuous_and_tight`** formal specifications audited by [`turbo-lean`](https://github.com/Th0rgal/turbo-lean).

10-bit and 8-bit luma acceptance read U16LE and U8 pixels directly from complete planes
across all scaling ratios (`1:1`, `2:1`, `3:1`, and general Q8 bilinear), avoiding
temporary full-frame 8-bit plane allocations. The u8 and u16le kernels share the same block
grid and reductions; each U16LE pixel is decoded as `(value >> 2) & 255` before reference
averaging or Q8 interpolation. Short buffers retain the fast native MSB extraction fallback.
`verify-kernels` checks parity against pure extraction plus acceptance, including odd
sizes, truncated buffers, and the full UInt16 range.


---

## Full upstream FATE campaign

The October 27 campaign pins FFmpeg commit
`bf0e831606938f530326c9679591109407fa8d0d`. Its configured manifest contains
5,721 targets. A broader source inventory retains 6,133 entries, including 68
explicit pixel-format overapproximations; it is **not certified complete**.
The full configured run of `62ba8fd` recorded 4,241 fresh candidate-invoked
passes, 832 failures, 609 rows without candidate execution, and 39 prerequisite
blocks. All 5,721 configured names remain in the denominator; 412 provisional
entries were not enabled. Passing
delegated CLI tests does not establish standalone codec, library/API, checkasm,
or ffprobe parity. No new cross-hardware speedup has been certified.

See [reproducible campaign harnesses](docs/FATE_CAMPAIGN_HARNESSES.md) for inventory,
execution attribution, explicit historical manifests, and paired timing controls.
The [October 27 evidence snapshot](docs/CAMPAIGN_PROGRESS_20261027.md) records
selected correctness waves, measured delegated regressions, and the limited
native oracle/profile observations.
The VVC routing wave `05c1fdc` passed all 61 selected historical failures and
Linux/macOS CI; this bounded delegated result does not update the full-run
counts above. The applicability harness records per-target configuration
observations while retaining the complete provisional inventory.

## Performance across x86, DGX Spark and Apple Silicon

The historical Maxwell campaign reports **1.89× speedup on Ryzen 9 9950X** and
**1.44× on DGX Spark** for its scale + tonemap + BT.709 CLI workload. Other
workloads remain slower. These are recorded campaign measurements, not a fresh
benchmark of the current commit. See [measurement provenance](docs/BENCHMARK_EVIDENCE.md).

### End-to-end CLI: FFmpeg and lffmpeg on the same host

Wall time in milliseconds; lower is better. **Speedup = FFmpeg time / lffmpeg time**;
values below 1 mean lffmpeg is slower. These reported pipeline comparisons include
decode/encode and I/O; they do not establish identical output quality or codec settings.

| Hardware | Workload | FFmpeg 6.1.1 | lffmpeg | Speedup |
| :--- | :--- | ---: | ---: | ---: |
| **x86 — Ryzen 9 9950X (Zen 5)** | 1080p → 540p | 486.39 ms | **443.78 ms** | **1.10×** |
| x86 — Ryzen 9 9950X | 1080p → 480p, Q8 | 478.41 ms | 501.88 ms | 0.95× |
| **x86 — Ryzen 9 9950X** | 540p + tonemap + BT.709 | 946.64 ms | **500.16 ms** | **1.89×** |
| x86 — Ryzen 9 9950X | Stream copy | 38.46 ms | 51.69 ms | 0.74× |
| **DGX Spark — ARM64 CPU** | 1080p → 540p | 225.77 ms | 309.03 ms | 0.73× |
| DGX Spark — ARM64 CPU | 1080p → 480p, Q8 | 209.78 ms | 350.85 ms | 0.60× |
| **DGX Spark — ARM64 CPU** | 540p + tonemap + BT.709 | 446.96 ms | **310.62 ms** | **1.44×** |
| DGX Spark — ARM64 CPU | Stream copy | 51.11 ms | 79.16 ms | 0.65× |
| **MacBook Air M2** | Comparative CLI benchmarks | — | — | **Not measured in the retained evidence** |

DGX Spark timings above use the CPU path, not CUDA kernel execution. PTX assembly
checks are separate from GPU runtime performance. The passing macOS CI validates
its runner; it is **not a MacBook Air M2 benchmark**.

### Native CPU kernels: throughput by architecture

Historical in-memory measurements; these exclude the full FFmpeg CLI workload.
There is no matched FFmpeg kernel baseline in the retained table, so these numbers
must not be used to claim a speedup over an entire FFmpeg transcode.

| Native workload | x86 Xeon E3-1245 V2 | x86 Ryzen 9 9950X | DGX Spark ARM64 CPU | MacBook Air M2 |
| :--- | ---: | ---: | ---: | :--- |
| 4K → 1080p, 2×2 plane scale | 623–693 fps | 1,611–2,128 fps | **2,005–2,469 fps** | Not measured |
| 4K → 720p, 3×3 plane scale | 686–833 fps | 2,140–2,147 fps | **1,547–2,896 fps** | Not measured |
| 1080p → 720p, 3:2 plane scale | 1,243–2,195 fps | **6,617–9,075 fps** | 4,651–6,722 fps | Not measured |
| CDEF filter, 101 × 64×64 planes | 8,561 µs | **1,452 µs** | 4,232 µs | Not measured |
| MP4 demux, 500 iterations | 229 µs | 182 µs | **89 µs** | Not measured |
| Order-4 FLAC LPC round-trip, 500 iterations | 76 µs | **20 µs** | 33 µs | Not measured |

The earlier 234×–1,382× CDEF figures compare against a scalar Lean reference,
not FFmpeg's optimized CDEF implementation. Synthetic Pipeline D throughput is
also excluded from the FFmpeg comparison because its workload differs.

---

## Qualification Tiers (`MediaPlanIR`)

Every CLI request is parsed into a typed intermediate representation (`MediaPlanIR` in [`LeanAV/PlanIR.lean`](LeanAV/PlanIR.lean)), checked against a fail-closed security policy (formally proved rejection of network protocols, `/dev/*` device nodes, and `..` path traversals), and routed to one of four execution tiers:

| Tier | Role | Examples |
| :--- | :--- | :--- |
| **`independent_verified`** | Pure Lean 4 + compiled `LNIR` (`lean-native-core`) kernels verified without FFmpeg dependencies, with explicit fallback (`fallbackDelegated`) | 2x2 / 3x3 / 3:2 / Q8 bilinear plane downscaling (`scale`), 3x3 box-blur stencil, luma mean/variance reduction, Order-4 FLAC LPC predictor/decoder, AV1 CDEF/Wiener filtering, HEVC SAO, native MP4 / IVF / Matroska (`SimpleBlock`) / MPEG-TS (`188B`) demux/mux, exact `AVRational` timestamp rescaling |
| **`translated_partial`** | Pure Lean 4 transcode orchestration (`IO.Process.spawn` without `/bin/sh`) with pure Lean 4 scaling, PQ10/BT.2020 colorimetry, 16x16 macroblock PSNR/SAD acceptance, and ISO BMFF `colr`/`clli`/`mdcv`/`pasp`/`edts` box patching | MP4 transcoding (`h264`, `hevc`, `av1`, `aac`, `-ss`, `-t`, `-vf scale/colorspace=bt709/tonemap`), JSON probing |
| **`delegated_faithful`** | Structured `fork`/`execvp` execution (zero shell interpolation) against reference `ffmpeg` | `.mkv`, `.webm`, `.mov`, `.wav`, `.flac`, `.ogg`, `.ts`, `.avi`, `.ast`, `-map`, `-metadata`, `-disposition`, `-bsf`, `-filter_complex` |
| **`unsupported`** | Deterministic fail-closed rejection with structured diagnostics and zero partial output files | Unsafe protocols (`http://`, `rtsp://`, `pipe:`, `/dev/*`, `..`), invalid flag combinations (`-c:v copy -vf ...`) |

---

## Compatibility: what “100%” covers

**We do not claim to pass 100% of the full FFmpeg test suite.** The historical
FATE result is **129/129 of the reference-passing tests in a selected 187-case
run**. This is useful compatibility evidence, but is neither all 187 cases passing
nor coverage of the full upstream FATE suite. The broader 120-case compatibility
suite still has one recorded mismatch. Full codecs and some CLI operations use
FFmpeg delegation; passing compatibility tests does not imply standalone parity.

| Suite / environment | Result | Scope and limitations |
| :--- | :--- | :--- |
| Local Python suites, 2026-10-27 | **83 passed, 0 skipped** | 30 unit + 53 differential tests; project tests, not upstream FATE |
| Linux CI, `68936da` | **60 passed, 4 skipped** | 30 unit + 34 differential cases counted; skips excluded from passes |
| macOS CI, `68936da` | **43 passed, 6 skipped** | 15 unit + 34 differential cases counted; some IR classes unavailable on this runner |
| CLI self-test / FFI / kernels | **Passed on Linux and macOS** | 53 self-test waves; [CI run](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40462499784) |
| Historical `bench.py` compatibility matrix | **119/120 matched (99.2%)** | 111 byte-exact, 5 lossy-signature matches, 3 both-fail; remaining mismatch not reclassified without evidence |
| Historical `test_diff.py` matrix | **79/79 matched** | Exit codes and ffprobe signatures, not universal bit-exactness |
| Historical selected FATE run | **129/129 reference-passing cases** | Selection: 187 cases; 58 outside this passing subset. Reported 186 matching non-empty outputs is a separate output comparison, not 186 passing tests |

Historical compatibility totals are retained from the campaign dossier; their full
per-case reports and external harnesses are not checked into this repository and
were not reproduced during this documentation update. Current CI does not run the
full upstream FATE suite. See [evidence and gaps](docs/BENCHMARK_EVIDENCE.md).

---

## Declarative Formal Specifications (`AVGateSpec`) & Zero-Trust Audit (`turbo-lean`)

Each safety and conformance gate implements the [`AVGateSpec`](LeanAV/Spec.lean) meta-specification connecting an executable C-ABI gate (`UInt8`) to an independent declarative `Prop` predicate (`sound`, `complete`, `posWitness`, `negWitness`, `nonVacuous`, `tight`).

All **15** `LeanAV/*.lean` modules (**`264 / 264` specifications**) pass `turbo-lean --json audit-spec` as `non_vacuous_and_tight` with **`0 vacuous`**, **`0 trivial`**, **`0 shadowed`**, and **`0 sorryAx`** across **`8,887`** kernel-checked declarations (`Format`: 56, `Video`: 31, `Encoder`: 30, `Scale`: 28, `NativeKernels`: 25, `Spec`: 23, `PlanIR`: 15, `Bitstream`: 13, `Audio`: 12, `Core`: 11, `Domain`: 8, `Cli`: 6, `Filter`: 6).

---

## Build & Verification

```bash
# Build LeanAV, the 16 LLVM-compiled LNIR kernels + 14 2D/stats/filter/16-bit routines, and the 621-line C-ABI bridge (0 sorryAx)
lake build

# Run all 53 formal self-test waves, C-ABI gates, and compiled LNIR kernel checks
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# Verify 0 sorryAx and 0 custom axioms across all 8,887 LeanAV.* declarations
lake env lean scripts/check_axioms.lean

# Audit each formal module (compatible with single-file turbo-lean CLIs)
for file in LeanAV/*.lean; do turbo-lean --json audit-spec "$file" || exit; done

# Validate the 16 LNIR_WIRE_V1 kernels via translation validation and certificate checking
lean-native-core validate-tv --input c/leanav_lnir_kernels.lnir --samples 64
lean-native-core verify-certs --input c/leanav_lnir_kernels.lnir

# Run the Python suites; report executed tests and skips separately
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_*.py"
```

---

## Repository Structure

- [`LeanAV/`](LeanAV/): 15 formal modules (`0 sorryAx`, `264/264` audited specifications): `Spec.lean`, `Domain.lean`, `Core.lean`, `Bitstream.lean`, `Format.lean`, `Video.lean`, `Audio.lean`, `Scale.lean`, `Filter.lean`, `Encoder.lean`, `NativeKernels.lean`, `Cli.lean`, `PlanIR.lean`, `IO.lean`, `Main.lean`. All pixel scaling (`2x2`, `3x3`, `3:2`, `Q8` bilinear), 64-bit SWAR Annex-B start-code scanning (`scanAnnexBNalUnitsFast`, `hasZeroByte64`) and verified `UInt64` SWAR primitives (`swarScale2x2U64`, `swarBiPredAvgU64`, `swarXorResidualU64`), color/tonemap filters (`PQ10 -> BT.709`, `BT.2020 -> BT.709`), B-frame bi-pred / XOR residual DSP, 16x16 macroblock PSNR/SAD acceptance, ISO BMFF 32/64-bit box navigation and `colr`/`clli`/`mdcv`/`pasp`/`edts` patching, `avcC`/`hvcC`/`av1C` pure colorimetry probing, and `IO.Process.spawn` transcode orchestration are defined in pure Lean 4.
- [`c/`](c/):
  - [`c/leanav_simd_kernels.c`](c/leanav_simd_kernels.c): Minimal **`621`-line** irreducible C-ABI bridge (reduced by **84.6%** from `4,022` lines after migrating all DSP, scaling, ISO BMFF container probing/patching, and transcode orchestration to pure Lean 4 and `LNIR_WIRE_V1`):
    1. POSIX `fork` + `execvp` delegation shim (`leanav_c_exec_delegated_ffmpeg`),
    2. Phase 5 FFI ABI contract & `__ATOMIC_SEQ_CST` cancellation shims (`leanav_c_verify_plane_ffi_contract`, `leanav_c_ffi_abi_version`, `leanav_c_ffi_cancel_gate`, `leanav_c_ffi_probe_mp4_contract`), and
    3. Zero-copy `ByteArray` (`lean_sarray_object` / `lean_sarray_cptr`) bridge to the 16 compiled `LNIR_WIRE_V1` LLVM IR kernels and 7 vectorized 2D strided/reduction runtime routines (`leanav_c_exec_lnir_unary_ba`, `leanav_c_exec_lnir_binary_ba`, `leanav_c_exec_lnir_ternary_ba`, `leanav_c_exec_lnir_scale2d_ba` dispatching `kernel_id` `0..4` including `@lean_native_stencil2d_box3x3_u8` at `kernel_id = 4`, fused 3-plane YUV420p `leanav_c_exec_lnir_scale2d_yuv420p_ba`, `leanav_c_exec_lnir_cdef_ba`, and `leanav_c_exec_lnir_luma_stats_ba`).
  - [`c/leanav_lnir_kernels.lnir`](c/leanav_lnir_kernels.lnir), [`c/leanav_lnir_kernels.h`](c/leanav_lnir_kernels.h), [`c/leanav_lnir_x86_64.ll`](c/leanav_lnir_x86_64.ll), [`c/leanav_lnir_arm64.ll`](c/leanav_lnir_arm64.ll): 16 distinct `LNIR_WIRE_V1` DSP/stencil kernels + 7 vectorized 2D strided/reduction routines validated (`validate-tv` + `verify-certs`) and lowered to LLVM 18 IR (`x86_64` AVX2 and `arm64` NEON) and NVIDIA PTX 8.0 (`sm_90`) by `lean-native-core`, compiled and linked into `libleanav_dsp.a`.
- [`tests/`](tests/): Python unit and differential tests (execution counts and skips listed above) against `ffmpeg`/`ffprobe`.
- [`docs/`](docs/): Maxwell parity plan ([`FFMPEG_PARITY_MAXWELL_PLAN.md`](docs/FFMPEG_PARITY_MAXWELL_PLAN.md)), capability registry ([`capability-registry.json`](docs/capability-registry.json)), contracts ([`docs/contracts/`](docs/contracts/)), and closure dossier ([`CAMPAIGN_CLOSURE_DOSSIER.md`](docs/CAMPAIGN_CLOSURE_DOSSIER.md)).

The 10-bit identity gate is checked in both the frame scaler and the transcode
loop. Exact-size frames reuse the source buffer; padded scaler inputs are trimmed
to the packed YUV420 footprint. Compiled unit and differential tests check pointer
reuse, all UInt16 bit patterns, native-call counts, raw pipeline bytes, metrics,
resize fallbacks, truncated input, and encoder failure:

```bash
python3 -m unittest discover -s tests/differential -p "test_u16le_identity.py" -v
```


Validation provenance: the green Linux and macOS CI at `68936da` uses Lean
4.31.0 and audits **8,993 declarations with zero sorryAx/custom axioms**. The
historical local Lean 4.35.0 report counts 8,887. These counts depend on the
toolchain. The identity test now uses portable C instrumentation; neither its
pointer-reuse checks nor its native-call positive control is skipped to make
macOS pass.
