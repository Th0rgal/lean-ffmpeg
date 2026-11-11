# Verification appendix

Measured on `campaign/p1-1-hdr-highbitdepth-20261106` under Lean `v4.35.0` and `turbo-lean@dc1656dc948f1d7bfc25d165575ae3819a2e8b97` (`audit-spec` v2.1).

## Kernel check

`LEAN_PATH='.lake/build/lib/lean:../lean-sys/.lake/build/lib/lean' lean scripts/check_axioms.lean`:

```
Verified 24984 LeanAV declarations (0 sorryAx, 0 custom axioms).
```

38 `LeanAV/*.lean` modules, 99,805 lines. Axiom allowlist: `{propext, Quot.sound, Classical.choice}`.

## Tight specifications

`turbo-lean --json audit-spec` on every `LeanAV/*.lean`: **890/890** `non_vacuous_and_tight`, 0 vacuous, 0 trivial, 0 shadowed.

| Module | Specs |
| :--- | ---: |
| `AacLcProofs` | 84 |
| `H264IntraTransformProofs` | 82 |
| `H264InterDeblockDpbProofs` | 79 |
| `Format` | 70 |
| `Ffv1Proofs` | 60 |
| `NativeKernels` | 59 |
| `Video` | 47 |
| `LavfiGraphProofs` | 40 |
| `Encoder` | 37 |
| `Audio` | 35 |
| `H264EntropyProofs` | 35 |
| `Scale` | 34 |
| `Av1MainProofs` | 33 |
| `H264SyntaxProofs` | 32 |
| `HevcMainProofs` | 31 |
| `Bitstream` | 27 |
| `Spec` | 23 |
| `PlanIR` | 22 |
| `Core` | 14 |
| `Domain` | 9 |
| `InprocTranscode` | 8 |
| `Cli` | 7 |
| `Filter` | 7 |
| `Md5` | 7 |
| `LavfiGraph` | 6 |
| `UnifiedPipeline` | 2 |

The other 12 modules (`AacLc`, `Av1Main`, `Ffv1`, `Ffv1Container`, `Ffv1Pipeline`, `H264Entropy`, `H264InterDeblockDpb`, `H264IntraTransform`, `H264Syntax`, `HevcMain`, `IO`, `Main`) audit as zero specs.

## LNIR

46 `LNIR_WIRE_V1` kernels (`37 VerifiedKernelProof`, `8 TranslationValidated`, `1 Tested`) plus 14 unproved LLVM 18 outer shells. `c/leanav_simd_kernels.c` is 672 lines of FFI and OS glue (window I/O, ABI, cancellation, `lean_sarray_object` wrappers) and does not spawn a process.

## Historical FATE record

These numbers are from the Wave 2 sweep (`reports/fate-sweep-wave2-complete-20261029.json`, SHA-256 `43c08c087c812e3a8feac4c3e757c848fceda80c17d1b09e2e6a1f3c23367147`) on an older hybrid binary that could still delegate. They are not a measurement of the zero-delegation tree.

| Suite | Targets | Passed | Exact | Notes |
| :--- | ---: | ---: | ---: | :--- |
| Isolated external-lib (`suite_d_ext_37`) | 37 | 36/37 | 28/28 | 8 skipped; 1 non-candidate C API helper failure (`fate-api-astc-profile`) |
| Unavailable host hardware / arch | 35 | not runnable | — | 33 `fate-filter-scale_cuda-*` (no NVIDIA GPU) + 2 native `aarch64` |

Passing a delegated FATE target on that older binary checked CLI parsing and plan lowering, not standalone codec parity. This branch rejects those routes instead of spawning `ffmpeg`.
