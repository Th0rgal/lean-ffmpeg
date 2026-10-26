# `AGENTS.md` - Operational & Architectural Guide (`lean-ffmpeg` / `LeanAV`)

## 1. Architecture Overview

`lean-ffmpeg` (`LeanAV`) is a formally verified Lean 4 (`v4.31.0`) multimedia pipeline and `ffmpeg`-compatible CLI (`lffmpeg`), pairing:
1. **15 Formal Lean 4 Modules (`LeanAV/*.lean`)**:
   - **`8,165` declarations** verified with **`0 sorryAx`** and **`0` custom axioms** (`scripts/check_axioms.lean`).
   - **`209 / 209` `non_vacuous_and_tight` specifications** audited by `turbo-lean --json audit-spec` (`0 vacuous`, `0 trivial`, `0 shadowed`): `Format` (48), `Video` (27), `Spec` (23), `NativeKernels` (21), `Bitstream` (13), `PlanIR` (13), `Scale` (13), `Audio` (12), `Core` (11), `Encoder` (9), `Domain` (8), `Cli` (6), `Filter` (5).
2. **21 Direct Lean 4 `@[export]` C-ABI Entrypoints (`leanav_lean_*`)**:
   - Decision gates, ISO BMFF header/handler/colorimetry classifiers, edit-list (`elst`) timestamp rescaling, bitrate and muxing-overhead estimators, luma mean/variance and PSNR acceptance packers, plane FFI contract checks, and PQ10/BT.2020 color-space helpers live in pure Lean 4 (`LeanAV/Format.lean`, `LeanAV/Scale.lean`, `LeanAV/PlanIR.lean`, `LeanAV/Encoder.lean`) and are called directly from C without shadow re-implementations.
3. **12 Compiled `LNIR_WIRE_V1` Kernels & C-ABI SIMD Bridge (`c/libleanav_dsp.a`)**:
   - `c/leanav_lnir_kernels.lnir` is validated via `lean-native-core validate-tv` (`64` samples) and `lean-native-core verify-certs`, lowered to LLVM 18 IR (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`), and linked with `c/leanav_simd_kernels.c` (`AVX2` / `SSE4.2` / `NEON` plane kernels, unified 32/64-bit ISO BMFF box walker + top-level `moov` seeker, and shell-free `execvp` delegation).

---

## 2. Engineering & Verification Rules

1. **Zero `sorryAx` & Zero Custom Axioms**:
   Every declaration in `LeanAV.*` must depend only on standard Lean axioms (`{propext, Quot.sound, Classical.choice}`). Run `lake env lean scripts/check_axioms.lean` after any Lean edit.
2. **Simple, Non-Vacuous Specifications (`AVGateSpec`)**:
   Keep Layer-II theorems short ($\le 3$ lines where possible) and verify all 15 modules pass `turbo-lean --json audit-spec` with `0` vacuous, `0` trivial, and `0` shadowed specs.
3. **Zero Model-Code Gap Across the FFI Boundary**:
   Pure arithmetic, classification, and validation logic belongs in Lean 4 and is exposed to C via `@[export leanav_lean_*]` with concrete regression vectors in `LeanAV.Format.format_ffi_export_vectors_verified` / `LeanAV/Main.lean`.
4. **Documentation Sync**:
   Whenever declaration counts (`scripts/check_axioms.lean`) or audited specification counts (`turbo-lean --json audit-spec`) change, update `README.md`, `AGENTS.md`, and `docs/CAMPAIGN_CLOSURE_DOSSIER.md` in the same commit.

---

## 3. Standard Verification Checklist

```bash
# 1. Build LeanAV, C-ABI SIMD kernels, and the 12 LLVM-compiled LNIR kernels
lake build

# 2. Run all 53 self-test waves, FFI ABI checks, and compiled LNIR kernel checks
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# 3. Verify 0 sorryAx and 0 custom axioms across all 8,165 LeanAV.* declarations
lake env lean scripts/check_axioms.lean

# 4. Audit all 15 formal modules with turbo-lean (209/209 non_vacuous_and_tight)
for f in LeanAV/*.lean; do turbo-lean --json audit-spec "$f"; done

# 5. Run the 59 Python unit and differential tests (15 unit + 44 differential)
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_*.py"
```
