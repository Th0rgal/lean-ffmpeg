# M1: LNIR Lift of the 14 Unverified DSP Routines — Result and Blocker (2026-10-29)

Base: `campaign/wave2-complete-20261029` @ `367be0820eeb708f637cb48ea5f0bdee2f08da55`.
Pins: Lean `v4.35.0`, `lean-sys@077775b`, `turbo-lean@dc1656d`
(`lean-native-core` sha256 `7c873444804589b086ad419d83fb4de1e6926e6e1aa653dceaaeec84c8831db9`).

## What was lifted (Option B)

The per-pixel arithmetic cores of the 14 hand-written LLVM routines were moved into
`LNIR_WIRE_V1`. `c/leanav_lnir_kernels.lnir` grows from 16 to **28** declarations
(decls 17-28 in `LeanAV/NativeKernels.lean`):

| Decl | Kernel | Arithmetic core of |
|---|---|---|
| 17 | `extract_u16le_msb8_simd` | `@lean_native_extract_u16le_msb8` |
| 18 | `luma_stats_moments_simd` | `@lean_native_luma_stats_{u8,u16le}` (sum / sum²) |
| 19 | `luma_stats_pack_simd` | luma-stats mean/variance packing |
| 20 | `luma_acceptance_accum_simd` | `@lean_native_luma_acceptance_16x16_*` per-pixel SAD/black/ref moments |
| 21 | `luma_acceptance_gate_simd` | acceptance threshold gate |
| 22 | `bilinear_q8_blend_simd` | `@lean_native_swscale_bilinear_q8_*` horizontal blend |
| 23 | `bilinear_q8_pack_simd` | bilinear vertical blend + rounding |
| 24 | `bilinear_q8_clamp10_simd` | 10-bit output clamp |
| 25 | `av1_cdef_tap_simd` | AV1 CDEF constrain tap |
| 26 | `down2x2_fused_eq_simd` | fused 2x2 downscale + contrast (`eq`) |
| 27 | `down2x2_fused_brightness_simd` | fused brightness + signed byte clamp |
| 28 | `yuv420p_studio_range_simd` | luma/chroma studio-range clamp |

Each kernel body is produced by `mkLnirPixelCoreDecl name params k`, which splices
`k.toWireTokens` for the typed `LnirKernelAst` constructor `k`. The wire therefore
matches the AST that `evalLnirKernel` interprets **by construction**; the emitted
module is byte-identical to the one validated below.

Evidence (pinned toolchain):

- `lean-native-core validate-tv --samples 64`: **28/28** pass.
- `lean-native-core verify-certs`: `verified: true`, all `chainValid`/`theoremsValid`;
  `20 VerifiedKernelProof`, `7 TranslationValidated`, `1 Tested`. The single `Tested`
  decl is the pre-existing `flac_lpc_autocorr_dot_simd`; the checked-in base module
  also yields overall `Tested` under this pin, so this is not a regression.
- `lffmpeg verify-kernels`: `verifyCompiledPixelCoreSuiteC` runs the 12 new compiled
  symbols from `libleanav_dsp.a` over adversarial lanes (sign boundaries, `x>>>63`
  negatives, zero divisors, clamp edges) and checks them bit-for-bit against `evalLnirKernel`.
- `lffmpeg self-test` wave 14 pins the decl count to 28 and checks hand-computed vectors.
- `turbo-lean audit-spec`: 278/278 `non_vacuous_and_tight` (NativeKernels 25 → 37).

### Wire defect found while lifting

The first hand-written wire for decls 20 (`luma_acceptance_accum`) and 25 (`av1_cdef_tap`) passed
`validate-tv` 28/28 but **disagreed with `evalLnirKernel` at runtime** (e.g.
`luma_acceptance_accum` returned `[-255, -1, …]`, and `av1_cdef_tap` lost the tap sign).
`evalLnirKernel` was unchanged, and its expected values were identical before and after
the fix, so the defect was in the hand-written wire tokens and not in the LLVM backend.
Regenerating both bodies from a single generator, which uses the `S_sel`/`B_le`
absolute-difference idiom, fixed them. `mkLnirPixelCoreDecl` now removes this class
of drift. `validate-tv` compares LNIR with its own lowering, not with `LeanAV`
semantics, so it cannot catch a wire that is well-formed but wrong. The runtime cross-check against
`evalLnirKernel` is required and is now in CI via `verify-kernels`.

## What could not be lifted (blocker)

The **outer loops** of the 14 routines are still unverified LLVM templates
(`turbo-lean` `Backend/LLVM.lean` `emitRuntimeAndCAbiHelpers`, lines ~1233-1819; checked in
as the helper prefix of `c/leanav_lnir_{x86_64,arm64}.ll`). This covers 2D strides, row
pointers, `u8`/`u16le` loads and stores, horizontal reductions, and 16x16 tiling. Lifting
them is infeasible at the pinned `turbo-lean@dc1656d`, for three reasons:

1. **Memory lowering is i64-only.** `IR/Codec.lean` accepts `T_rawPtr T_i8`/`T_i16`, but the
   LLVM raw load/store lowering (`Backend/LLVM.lean` ~812/1075) always emits `i64` GEPs and loads.
   A `u8` plane would be read 8 bytes per pixel.
2. **`emitParForLoop` ignores the element type** (`_elemTy`, `Backend/LLVM.lean:928`): every
   `C_par` input and output is an `i64` `lean_sarray_object` lane.
3. **Semantics are `Array UInt64`** (`Semantics/Eval.lean` sarray ~303). There is no
   narrow-width array model, so `SymbolicTV` has nothing to refine `u8`/`u16le` stride
   accesses against. Reductions across lanes (`C_par` is element-wise only) and strided
   2D indexing likewise have no validated lowering.

Consequences:

- The acceptance criterion "no unverified DSP routine remains" is **partially closed
  (M1-A2, 2026-10-30)**: all per-pixel arithmetic has been removed from the 14 outer
  routines and wired via direct LLVM `call i64 @lnir_px_*` calls to **17 compiled scalar
  `LNIR_WIRE_V1` pixel-core declarations** (decls 30–46 in `LeanAV/NativeKernels.lean`,
  plus SIMD decl 29 `bt2020_to_bt709_uv_simd`, bringing `c/leanav_lnir_kernels.lnir` to
  **46/46** `SymbolicTV`-validated and `verify-certs`-certified declarations and
  `turbo-lean audit-spec` to **300/300** `non_vacuous_and_tight` specs across **9,065**
  Lean declarations).
- **§6.8 Explicit TCB Disclosure**: the 14 thin outer shells (`1,454` lines in
  `c/leanav_lnir_{x86_64,arm64}.ll`, deterministically emitted by
  `scripts/gen_lnir_outer_shells.py` and checked for zero drift by
  `./scripts/regen_lnir_c_kernels.sh --check-ir`) remain in the unverified TCB solely for
  2D row-stride/coordinate loops, narrow `i8`/`i16` GEP + `zext`/`trunc` loads and stores,
  16x16 macroblock tiling, and scalar loop-carried accumulators (`sum`, `sumSq`, `maxSad`,
  `totalSse`). Every pixel-level formula executes inside a verified `@lnir_px_*` core,
  verified structurally and at runtime by `tests/test_u16le_kernels_ir.py`,
  `tests/test_pixel_filters_ir.py`, and `lffmpeg verify-kernels`.

## Required upstream work (turbo-lean / lean-native-core)

1. Width-aware `T_rawPtr`/`T_sarray` lowering (`i8`/`i16` GEP, `zext`/`trunc`) with matching
   `Semantics` (byte-array model) and `SymbolicTV` memory refinement.
2. A strided 2D `C_par` form (row stride, width, height) or verified `C_for` with
   `rawLoad`/`rawStore` at narrow widths.
3. A validated reduction combinator (associative `add` fold) for luma stats and acceptance.

Once these exist, each template can be re-expressed as a loop nest over the decl-17..28 cores
and removed from `emitRuntimeAndCAbiHelpers`.
