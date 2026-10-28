# `AGENTS.md` - Operational & Architectural Guide (`lean-ffmpeg` / `LeanAV`)

## 1. Architecture Overview

`lean-ffmpeg` (`LeanAV`) is a formally verified Lean 4 (`v4.35.0`) multimedia pipeline and `ffmpeg`-compatible CLI (`lffmpeg`), pairing:
1. **15 Formal Lean 4 Modules (`LeanAV/*.lean`)**:
   - **`8,897` declarations** (verified under `v4.35.0`) verified with **`0 sorryAx`** and **`0` custom axioms** (`scripts/check_axioms.lean`).
   - **`264 / 264` `non_vacuous_and_tight` specifications** audited by `turbo-lean --json audit-spec` (`0 vacuous`, `0 trivial`, `0 shadowed`): `Format` (56), `Video` (31), `Encoder` (30), `Scale` (28), `NativeKernels` (25), `Spec` (23), `PlanIR` (15), `Bitstream` (13), `Audio` (12), `Core` (11), `Domain` (8), `Cli` (6), `Filter` (6).
   - All plane scaling (`2x2`, `3x3`, `3:2`, `Q8` bilinear, 16-bit LE), 64-bit SWAR Annex-B start-code scanning (`scanAnnexBNalUnitsFast`, `hasZeroByte64`) and verified `UInt64` SWAR primitives (`swarScale2x2U64`, `swarBiPredAvgU64`, `swarXorResidualU64`), color/tonemap filters (`PQ10 -> BT.709`, `BT.2020 -> BT.709`), B-frame bi-pred / XOR residual DSP, 16x16 macroblock PSNR/SAD acceptance (`@lean_native_luma_acceptance_16x16_u8`, `@lean_native_luma_acceptance_16x16_u16le`), ISO BMFF 32/64-bit box navigation, surgical trailing-`moov` `pwrite` patching (`locateMp4TrailingMoovWindowIO` + `writeMp4WindowIO`), `colr`/`clli`/`mdcv`/`pasp`/`edts` patching, `avcC`/`hvcC`/`av1C` pure colorimetry probing, and `IO.Process.spawn` transcode orchestration are defined in pure Lean 4.
2. **21 Direct Lean 4 `@[export]` C-ABI Entrypoints (`leanav_lean_*`)**:
   - Decision gates, ISO BMFF header/handler/colorimetry classifiers, edit-list (`elst`) timestamp rescaling, bitrate and muxing-overhead estimators, luma mean/variance and PSNR acceptance packers, plane FFI contract checks, and PQ10/BT.2020 color-space helpers live in pure Lean 4 (`LeanAV/Format.lean`, `LeanAV/Scale.lean`, `LeanAV/PlanIR.lean`, `LeanAV/Encoder.lean`) and are exported to C without shadow re-implementations.
3. **16 Compiled `LNIR_WIRE_V1` Kernels & `623`-Line Irreducible C-ABI Bridge (`c/libleanav_dsp.a`)**:
   - `c/leanav_lnir_kernels.lnir` is validated via `lean-native-core validate-tv` (`64` samples) and `lean-native-core verify-certs`, lowered to LLVM 18 IR (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`) and NVIDIA PTX 8.0 (`sm_90`), and linked with `c/leanav_simd_kernels.c` (`623` lines containing only the POSIX `fork`+`execvp` shim, `pread`/`pwrite` window I/O shims, Phase 5 FFI ABI / `__ATOMIC_SEQ_CST` shims, and zero-copy `lean_sarray_object` bridge for the 16 compiled LNIR kernels and 14 vectorized 2D strided/reduction/filter/16-bit runtime routines, including fused 3-plane YUV420p `leanav_c_exec_lnir_scale2d_yuv420p_ba` and 16-bit LE `leanav_c_exec_lnir_scale2d_yuv420p10le_ba`, 4x-vectorized `@lean_native_swscale_bilinear_q8_u8` and `@lean_native_swscale_bilinear_q8_u16le`, `@lean_native_apply_filters_yuv420p_u8` with `lean_is_exclusive` in-place reuse, `@lean_native_luma_stats_u8` and `@lean_native_luma_stats_u16le` with both `step == 1` and `step == 16` SIMD loops, `@lean_native_extract_u16le_msb8`, and the shared u8/u16le `@lean_native_luma_acceptance_16x16_*` kernels).

---

## 2. Engineering & Verification Rules

1. **Zero `sorryAx` & Zero Custom Axioms**:
   Every declaration in `LeanAV.*` must depend only on standard Lean axioms (`{propext, Quot.sound, Classical.choice}`). Run `lake env lean scripts/check_axioms.lean` after any Lean edit.
2. **Simple, Non-Vacuous Specifications (`AVGateSpec`)**:
   Keep Layer-II theorems short ($\le 3$ lines where possible) and verify all 15 modules pass `turbo-lean --json audit-spec` with `0` vacuous, `0` trivial, and `0` shadowed specs.
3. **Zero Model-Code Gap Across the FFI Boundary**:
   Keep `c/leanav_simd_kernels.c` strictly limited to irreducible C-ABI / OS / `lean_sarray_object` glue. All arithmetic, DSP, container parsing/patching, and pipeline orchestration belong in pure Lean 4 or `LNIR_WIRE_V1`.
4. **Documentation Sync**:
   Whenever declaration counts (`scripts/check_axioms.lean`) or audited specification counts (`turbo-lean --json audit-spec`) change, update `README.md`, `AGENTS.md`, and `docs/CAMPAIGN_CLOSURE_DOSSIER.md` in the same commit.

---

## 3. Standard Verification Checklist

```bash
# 1. Build LeanAV, the 16 LLVM-compiled LNIR kernels, and the 623-line C-ABI bridge
lake build

# 2. Run all 53 self-test waves, FFI ABI checks, and compiled LNIR kernel checks
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# 3. Verify 0 sorryAx and 0 custom axioms across all 8,897 LeanAV.* declarations
lake env lean scripts/check_axioms.lean

# 4. Audit all 15 formal modules in parallel with turbo-lean (264/264 non_vacuous_and_tight)
for file in LeanAV/*.lean; do turbo-lean --json audit-spec "$file" || exit; done

# 5. Run Python tests; executed counts depend on platform and available dependencies
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_*.py"
```


Validation provenance: Wave 14 CI (`b2867db`, run `40436255776`) used Lean 4.31.0
and audited 8,993 declarations with no sorryAx/custom axioms; the historical local Lean 4.35.0
report counted 8,887. That Linux run executed 30 unit tests and 34 differential tests
(4 skipped). macOS failed the identity test setup because its linker does not
support GNU `--wrap`; the test now compiles the production C bridge with a renamed
scaler entrypoint and a counting wrapper on both platforms. No test is skipped to
work around that failure. Historical benchmark and suite totals below are not
claims that every case ran on the current CI runner.

The MPEG options audit on 2026-10-27 under Lean v4.35.0 counted 8,897 declarations
with zero sorryAx/custom axioms; all 264 specifications remained tight.
