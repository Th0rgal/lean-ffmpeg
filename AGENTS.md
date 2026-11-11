# `AGENTS.md` - Operational & Architectural Guide (`lean-ffmpeg` / `LeanAV`)

## 1. Architecture Overview

`lean-ffmpeg` (`LeanAV`) is a formally verified Lean 4 (`v4.35.0`) multimedia pipeline and `ffmpeg`-compatible CLI (`lffmpeg`). The binary is standalone: every accepted route runs in-process, and anything outside that set fails closed. There is no child process and no external `ffmpeg` / `ffprobe` override environment variable.

1. **38 Formal Lean 4 Modules (`LeanAV/*.lean`, `99,526` LOC)**:
   - **`24,968` declarations** (verified under `v4.35.0`) with **`0 sorryAx`** and **`0` custom axioms** (`scripts/check_axioms.lean`).
   - **`890 / 890` `non_vacuous_and_tight` specifications** audited by `turbo-lean --json audit-spec` (`dc1656dc948f1d7bfc25d165575ae3819a2e8b97`, v2.1; `0 vacuous`, `0 trivial`, `0 shadowed`): `AacLcProofs` (84), `H264IntraTransformProofs` (82), `H264InterDeblockDpbProofs` (79), `Format` (70), `Ffv1Proofs` (60), `NativeKernels` (59), `Video` (47), `LavfiGraphProofs` (40), `Encoder` (37), `Audio` (35), `H264EntropyProofs` (35), `Scale` (34), `Av1MainProofs` (33), `H264SyntaxProofs` (32), `HevcMainProofs` (31), `Bitstream` (27), `Spec` (23), `PlanIR` (22), `Core` (14), `Domain` (9), `InprocTranscode` (8), `Cli` (7), `Filter` (7), `Md5` (7), `LavfiGraph` (6), `UnifiedPipeline` (2) (plus the 12 implementation/orchestration modules `AacLc`, `Av1Main`, `Ffv1`, `Ffv1Container`, `Ffv1Pipeline`, `H264Entropy`, `H264InterDeblockDpb`, `H264IntraTransform`, `H264Syntax`, `HevcMain`, `IO`, and `Main`).
   - Native routes, all with zero subprocesses: unified multi-stream `-i ... -c:v/-c:a` demux -> `LavfiGraph` -> encode -> mux pipeline (`unified_media_pipeline` in `LeanAV/UnifiedPipeline.lean`), FFV1 v3, PNG + Zlib/DEFLATE, FLAC, H.264/AVC syntax + CAVLC/CABAC + intra/inter/deblock/DPB (including High / High 10 / High 4:2:2 / High 4:4:4 Predictive 8/10/12-bit, custom 4x4/8x8 scaling matrices, and `qp=0` lossless), AAC-LC, Opus (`Ogg/Opus` and `MP4/MOV`, RFC 6716 CELT FB silence `0xFF 0xFE` with fail-closed rejection of compressed non-silent packets pending P1.2), Apple ProRes 422 (`apcn` in `MP4/MOV`), MPEG-TS (`PAT/PMT/PES`), HEVC Main / Main 10 / RExt 8/10/12-bit 4:2:0/4:2:2/4:4:4 (`-i` / `-c:v hevc` and `hevc-probe`, plus HDR10 `mdcv`/`clli` SEI & Dolby Vision `UNSPEC62` RPU passthrough), AV1 Main / High / Professional 8/10/12-bit 4:2:0/4:2:2/4:4:4 with film-grain synthesis (`-i` / `-c:v av1` and `av1-probe`, plus ITU-T T.35 Dolby Vision EMDF RPU passthrough), lavfi DAG (`color`, `testsrc`, `nullsrc`, `overlay`, `split`, `hstack`, `vstack`, `sine`, `anullsrc`, `amix`, `amerge`, `asplit`, `md5`, `framemd5`), and stream copy for MP4/MOV/MKV/WebM/WAV/FLAC/IVF. High-bit-depth pixel formats (`yuv420p10le`, `p010le`, `yuv422p10le`, `yuv444p10le`, `yuv420p12le`, `yuv422p12le`, `yuv444p12le`, `gbrp10le`, `rgba64le`), Bayer/Floyd-Steinberg dithering, scale, and BT.2020 PQ/HLG `colorspace=bt709` / tonemap stay in-process. Out-of-scope codecs, profiles, GPU, network protocols, and rejected filter graphs are `BackendTier.unsupported` (`delegatedContainer := false`, `fallbackAllowed := false`) and exit non-zero with no output file. CLI classification lives in `LeanAV/PlanIR.lean`, `LeanAV/UnifiedPipeline.lean`, and `LeanAV/Main.lean`.
2. **21 Direct Lean 4 `@[export]` C-ABI Entrypoints (`leanav_lean_*`)**:
   - Decision gates, ISO BMFF header/handler/colorimetry classifiers, edit-list (`elst`) timestamp rescaling, bitrate and muxing-overhead estimators, luma mean/variance and PSNR acceptance packers, plane FFI contract checks, and PQ10/BT.2020 color-space helpers live in pure Lean 4 (`LeanAV/Format.lean`, `LeanAV/Scale.lean`, `LeanAV/PlanIR.lean`, `LeanAV/Encoder.lean`) and are exported to C without shadow re-implementations.
3. **46 Compiled `LNIR_WIRE_V1` Kernels, 14 Thin Outer Shells & `672`-Line C-ABI Bridge (`c/libleanav_dsp.a`)**:
   - `c/leanav_lnir_kernels.lnir` is validated via `lean-native-core validate-tv` (`46/46` `SymbolicTV`, `64` samples) and `lean-native-core verify-certs` (`verified: true`, `chainValid: true`, `theoremsValid: true` across all 46 kernels: `37 VerifiedKernelProof`, `8 TranslationValidated`, `1 Tested`), lowered to LLVM 18 IR (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`), spliced deterministically by `scripts/gen_lnir_outer_shells.py` (`./scripts/regen_lnir_c_kernels.sh --check-ir` enforces zero drift), and linked with `c/leanav_simd_kernels.c` (`672` lines: `pread`/`pwrite` window I/O, FFI ABI / `__ATOMIC_SEQ_CST` cancellation, and zero-copy `lean_sarray_object` wrappers for the 46 compiled LNIR kernels and 14 thin outer shells). The file does not spawn a process. Pixel arithmetic stays in the `@lnir_px_*` cores (`leanav_c_exec_lnir_scale2d_yuv420p_ba`, `leanav_c_exec_lnir_scale2d_yuv420p10le_ba`, `@lean_native_swscale_bilinear_q8_u8`, `@lean_native_swscale_bilinear_q8_u16le`, `@lean_native_apply_filters_yuv420p_u8`, `@lean_native_luma_stats_u8`, `@lean_native_luma_stats_u16le`, `@lean_native_extract_u16le_msb8`, `@lean_native_luma_acceptance_16x16_*`).

---

## 2. Engineering & Verification Rules

1. **Zero `sorryAx` & Zero Custom Axioms**:
   Every declaration in `LeanAV.*` must depend only on standard Lean axioms (`{propext, Quot.sound, Classical.choice}`). Run `LEAN_PATH='.lake/build/lib/lean:../lean-sys/.lake/build/lib/lean' lean scripts/check_axioms.lean` after any Lean edit.
2. **Simple, Non-Vacuous Specifications (`AVGateSpec`)**:
   Keep Layer-II theorems short ($\le 3$ lines where possible) and verify all 38 modules pass `turbo-lean --json audit-spec` with `0` vacuous, `0` trivial, and `0` shadowed specs (`890/890` `non_vacuous_and_tight`).
3. **Zero Model-Code Gap Across the FFI Boundary**:
   Keep `c/leanav_simd_kernels.c` strictly limited to irreducible C-ABI / OS / `lean_sarray_object` glue. All arithmetic, DSP, container parsing/patching, and pipeline orchestration belong in pure Lean 4 or `LNIR_WIRE_V1`. Do not reintroduce a process spawn.
4. **Documentation Sync**:
   Whenever declaration counts (`scripts/check_axioms.lean`) or audited specification counts (`turbo-lean --json audit-spec`) change, update `AGENTS.md`, `docs/VERIFICATION_APPENDIX.md`, `docs/CAMPAIGN_CLOSURE_DOSSIER.md`, and the greps in `.github/workflows/ci.yml` in the same commit.

---

## 3. Standard Verification Checklist

```bash
# 1. Build LeanAV, the 46 LLVM-compiled LNIR kernels + 14 wired outer shells, and the 672-line C-ABI bridge
export LEAN_PATH='.lake/build/lib/lean:../lean-sys/.lake/build/lib/lean'
python3 scripts/build_turbo.py
./scripts/regen_lnir_c_kernels.sh --check-ir

# 2. Run self-test waves, FFI ABI checks, and compiled LNIR kernel checks
./.lake/build/bin/lffmpeg self-test
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# 3. Verify 0 sorryAx and 0 custom axioms across all 24,968 LeanAV.* declarations
lean scripts/check_axioms.lean

# 4. Audit all 38 formal modules with turbo-lean (890/890 non_vacuous_and_tight)
for file in LeanAV/*.lean; do turbo-lean --json audit-spec "$file" || exit; done

# 5. Standalone suite (no ffmpeg on PATH), then differential oracles
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
The M3-D post-deletion measurement counted 22,820 declarations and 807/807 tight specs;
the P1.0 unified-pipeline measurement counted 23,201 declarations and 812/812 tight specs;
the current P1.1 HDR/high-bit-depth measurement is 24,968 declarations and 890/890 tight specs
(see `docs/VERIFICATION_APPENDIX.md`).
