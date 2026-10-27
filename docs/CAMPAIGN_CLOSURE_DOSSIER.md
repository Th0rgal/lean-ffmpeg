# Campaign Closure Dossier: FFmpeg Parity & Maxwell Qualification (`lean-ffmpeg`)

## W11-W14 direct all-ratio U8/U16LE acceptance, 10-bit identity zero-copy, dual-step luma stats, surgical trailing-moov, SIMD 3x3 & 3:2 U16LE, 16-lane down2x2_fused_eq, disabled-plane filter skip, and 8-lane box3x3 & AV1 CDEF validation

The direct U16LE and U8 acceptance paths support `1:1`, `2:1`, `3:1`, and general Q8
bilinear geometries (`lumaAcceptanceAllRatiosGateSpec`), using a shared u8/u16le LLVM
emitter and `extractU16LeMsb8Fast` fallback. Wave 12 adds zero-copy 10-bit 1:1 identity
frame reuse (`yuv420p10leIdentityZeroCopyGateSpec`), vectorized `step == 1` and
`step == 16` luma statistics (`lumaStatsStepSelectionGateSpec`), and surgical
trailing-`moov` `pwrite` patching (`surgicalMoovTailPatchGateSpec`). Wave 13 adds
4-lane `<4 x i32>` SIMD 3x3 U16LE downscaling (`b3vec`) with exact `/ 9` (`udiv`)
across the full `0..65535` `UInt16` range (`u16leDownscale3x3VecGateSpec`),
disabled-plane zero-copy skip (`%src == %dst`) and `memcpy` (`%src != %dst`) in
`@lean_native_apply_filters_yuv420p_u8` (`yuv420pFilterPlaneSkipGateSpec`), single-FD
`readMp4MoovWindowIO`, and an 8-lane `<8 x i16>/<8 x i32>` SIMD interior loop in
`@lean_native_stencil2d_box3x3_u8` (`box3x3StencilInteriorVecGateSpec`). Wave 14 adds
all-ratio (`1:1`, `2:1`, `3:1`, and general Q8 bilinear) 16x16 luma acceptance in
`@lean_native_luma_acceptance_16x16_u8` and `@lean_native_luma_acceptance_16x16_u16le`,
16-lane `<16 x i8>` SIMD non-identity EQ in `@lean_native_swscale_down2x2_fused_eq_u8` +
paired `3:2` Q8 fastpath in `@lean_native_swscale_bilinear_q8_u16le` (`down2x2FusedEqVecGateSpec`),
and an 8-lane `<8 x i32>` SIMD interior loop with `shift & 31` normalization in
`@lean_native_av1_cdef_filter_u8` (`av1CdefInteriorVecGateSpec`). Local
validation under Lean v4.35.0 passed all 53 self-test waves, `verify-ffi`,
`verify-kernels`, and the axiom audit: **8,887 declarations, zero sorryAx/custom axioms**.
The current spec audit is **264/264 non_vacuous_and_tight, zero shadowed** (`Format`: 56,
`Video`: 31, `Encoder`: 30, `Scale`: 28, `NativeKernels`: 25, `Spec`: 23, `PlanIR`: 15,
`Bitstream`: 13, `Audio`: 12, `Core`: 11, `Domain`: 8, `Cli`: 6, `Filter`: 6). The bridge
has 625 lines and links 14 runtime routines. Python validation passed 30 unit/IR tests and
53 differential tests (83/83 total). Both generated target kernels (`c/leanav_lnir_x86_64.ll`
and `c/leanav_lnir_arm64.ll`) compile with zero warnings under `clang-18 -O3 -Werror`.

The earlier campaign results below describe their original revisions.


This dossier collects the deliverables, contracts, formal proofs, differential test suites, and qualification/rollback policies required by [`docs/FFMPEG_PARITY_MAXWELL_PLAN.md`](FFMPEG_PARITY_MAXWELL_PLAN.md) (Sections 10 and 11).

---

## 1. Qualification Taxonomy & Support Tiers (Section 1)

Every capability in the registry and in [`LeanAV.PlanIR.BackendTier`](../LeanAV/PlanIR.lean) is classified into exactly one of seven tiers:
1. **`independent_verified`**: Implemented in Lean 4 / `LNIR_WIRE_V1` / C-ABI SIMD without FFmpeg dependencies, formally proved (`0 sorryAx`, `0` warnings under `turbo-lean --json audit-spec`), and differentially validated with explicit fallback (`KernelExecutionResult.fallbackDelegated`).
2. **`independent_tested`**: Independently implemented and validated against the differential oracle and adversarial corpus.
3. **`delegated_faithful`**: Lowered through [`MediaPlanIR`](../LeanAV/PlanIR.lean) and executed via structured delegation (`fork` + `execvp` without shell interpolation via [`leanav_c_exec_delegated_ffmpeg`](../c/leanav_simd_kernels.c) or linked `libav*`) with differential parity.
4. **`translated_partial`**: MP4 transcode pipeline (`h264`, `hevc`, `av1`, `scale`, `colorspace=bt709`, `tonemap`, `-ss`, `-t`) gated by visual fidelity and container synchronization checks.
5. **`approximate`**: Behavior bounded by explicit numerical tolerances (PSNR / luma / duration).
6. **`unsupported`**: Rejected fail-closed (non-zero exit code, structured diagnostic on `stdout` in `-json` mode or `stderr` outside `-json` mode, zero residual partial output files).
7. **`untested`**: Inventoried under `declared_ffmpeg_capabilities` (`inventory_only: true`) and never claimed as supported.

---

## 2. Phase-by-Phase Summary (Phase 0 to Phase 7)

### Phase 0 (Wave A): Governance, Capability Registry & Pinned Reference
- **Pinned reference FFmpeg binary**: `6.1.1-3ubuntu5` (`/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg` and `ffprobe`, SHA-256 digests recorded).
- **Generator & Registry**: [`scripts/generate_capability_registry.py`](../scripts/generate_capability_registry.py) and [`docs/capability-registry.json`](capability-registry.json) strictly separating `declared_ffmpeg_capabilities` (`inventory_only: true`, 14 complete domains) from `tested_lean_ffmpeg_capabilities`.
- **Contracts**:
  - [`docs/contracts/platform-qualification.json`](contracts/platform-qualification.json) (`linux-x86_64`: `tested_local`; `macos-arm64`, `linux-arm64`, `windows-x86_64`: `untested`).
  - [`docs/contracts/quorum-wave-a.json`](contracts/quorum-wave-a.json) (external multi-model review completed at the end of the campaign).

### Phase 1 (Wave A): Bounded Differential Harness & CLI Routing
- **Harness**: [`tests/differential/runner.py`](../tests/differential/runner.py) with isolated working directories, wall-clock/CPU/memory/output bounds, process-group cleanup, rational `ffprobe` normalization, packet/frame probes, and decoded stream probes.
- **CLI Routing & Error Hygiene**: [`LeanAV/Cli.lean`](../LeanAV/Cli.lean) and [`LeanAV/Main.lean`](../LeanAV/Main.lean) guaranteeing:
  - Exactly one JSON object on `stdout` and `stderr == ""` when `-json` / `--json` is passed (on both success and failure, including during H.264/HEVC/AV1 transcoding).
  - Full suppression of banners and stats on `stderr` for `-v quiet|panic|fatal|error|warning|-8|0|8|16|24`.
  - Automatic `unlink` cleanup of any partial output file on remux or transcode failure over truncated or corrupt media.

### Phase 2 (Waves B & C): Core Invariants (Timebases, Seek, VFR/B-frames, Color, Audio, Determinism)
- **Contract**: [`docs/contracts/timing-seek.json`](contracts/timing-seek.json).
- **Differential tests**: [`tests/differential/test_phase2.py`](../tests/differential/test_phase2.py) verifying:
  - Fail-closed rejection of missing inputs with zero residual artifacts.
  - Colorimetry metadata (`bt709`, `tv`), 10-bit `yuv444p10le`, VFR streams with B-frames (`nb_frames = 20`, 29 decoded frames), exact audio sample counts (`48000 Hz`, `duration_ts = 96000`), and bit-exact reproducibility (identical SHA-256 across repeated runs).

### Phase 3 (Wave D): Typed Intermediate Representation (`MediaPlanIR`)
- **Contract**: [`docs/contracts/phase3-ir-schema.json`](contracts/phase3-ir-schema.json).
- **Implementation**: [`LeanAV/PlanIR.lean`](../LeanAV/PlanIR.lean) (`MediaPlanIR`, `parseArgsToPlanIR`, `planIRToCliArgs`, `validatePlanIR`, `serializePlanIRJson`).
- **CLI Inspection**: `lffmpeg plan <args>` and `lffmpeg -dump-plan <args>`.
- **Proved Theorems (`0 sorryAx`)**:
  - `LeanAV.PlanIR.streamMapSpec_parse_format_roundtrip`
  - `LeanAV.PlanIR.planIR_cli_roundtrip_verified`
  - `LeanAV.PlanIR.validatePlanIR_sound_and_rejects_unsafe`

### Phase 4 (Waves E & F): General Delegated Compatibility & Protocol Security Gate
- **Contract**: [`docs/contracts/phase4-delegated-coverage.json`](contracts/phase4-delegated-coverage.json).
- **Coverage**: Containers `mp4`, `matroska` (`.mkv`), `webm`, `wav`, `flac`, `ogg`, `mpegts` (`.ts`), `ivf`, `adts` (`.aac`), `framecrc`, `md5`, `null`; flags `-map`, `-metadata`, `-map_metadata`, `-map_chapters`, `-c:s` / `-scodec`, `-sn`, `-bsf:v`, `-bsf:a`.
- **Security (Section 8)**: `LeanAV.PlanIR.isSafeLocalMediaPath` and theorem `LeanAV.PlanIR.protocolSecurityPolicy_accepts_local_and_rejects_network_device_traversal` rejecting `http://`, `https://`, `rtsp://`, `rtmp://`, `tcp://`, `udp://`, `lavfi:`, `concat:`, `/dev/*`, and `..`.

### Phase 5 (Wave G): Pinned C-ABI FFI Facade, Memory Ownership & Cancellation
- **Contract**: [`docs/contracts/phase5-ffi-abi-boundary.json`](contracts/phase5-ffi-abi-boundary.json).
- **Direct Lean 4 `@[export]` & C-ABI Implementation**:
  - `leanav_c_ffi_abi_version` (`0x00010005`, forwarded to `@[export leanav_lean_ffi_abi_version]` in [`LeanAV/PlanIR.lean`](../LeanAV/PlanIR.lean))
  - `leanav_c_ffi_probe_mp4_contract` (pure Lean 4 bounded MP4 box probe `ffiProbeMp4ContractPure` via `@[export leanav_lean_ffi_probe_mp4_contract]` with a borrowed `b_lean_obj_arg` C-ABI shim preserving caller reference counts)
  - `leanav_c_ffi_cancel_gate` (`__ATOMIC_SEQ_CST` fence in C followed by `@[export leanav_lean_ffi_cancel_gate]` / `specFfiCancelGate` with zero model-code gap)
  - `leanav_c_verify_plane_ffi_contract` (64-byte stride alignment + 64-byte tail SIMD padding, delegated directly to `@[export leanav_lean_verify_plane_ffi_contract]` in [`LeanAV/Encoder.lean`](../LeanAV/Encoder.lean))
  - 14 additional ISO BMFF / transcode / quality-acceptance / handler-classification C-ABI exports in [`LeanAV/Format.lean`](../LeanAV/Format.lean) (`leanav_lean_rescale_elst_entry_u64`, `leanav_lean_select_iso_header_timescale_u32`, `leanav_lean_select_iso_header_duration_u64`, `leanav_lean_compute_bitrate_kbps_u64`, `leanav_lean_classify_colr_nclx_u32`, `leanav_lean_classify_dar_u32`, `leanav_lean_classify_avc_level_u32`, `leanav_lean_compute_output_frame_limit_u64`, `leanav_lean_classify_luma_psnr_x10_u64`, `leanav_lean_pack_acceptance_metrics_u64`, `leanav_lean_pack_transcode_report_u64`, `leanav_lean_compute_luma_mean_var_packed_u64`, `leanav_lean_compute_muxing_overhead_micro_pct_u64`, `leanav_lean_classify_mp4_handler_type_u32`) and 3 scaling/tonemap exports in [`LeanAV/Scale.lean`](../LeanAV/Scale.lean) (`leanav_lean_csc_chroma_bt2020_to_bt709_u16`, `leanav_lean_bilinear_tab_entry_q8`, `leanav_lean_tonemap_pq10_to_bt709_u8`)
  - Pure Lean 4 and `LNIR_WIRE_V1` replacements for all non-irreducible C kernels (`scalePlaneDown2x2CSimd`, `scalePlaneDown2x2FusedEqCSimd`, `scalePlaneDown3x3CSimd`, `scalePlaneDown3to2CSimd`, `mcBiPredBytesSimd`, `xorResidualBytesSimd`, `setEncoderCliOptionsC`, `getLastAcceptanceMetricsC`, `measurePlanesAcceptanceC`, and `transcodeMp4GeneralVerifiedC`), reducing [`c/leanav_simd_kernels.c`](../c/leanav_simd_kernels.c) from `4,022` lines to **`383` lines** of irreducible C-ABI / POSIX `fork`+`execvp` / zero-copy `lean_sarray_object` glue.
- **CLI Verification**: `lffmpeg verify-ffi`.

### Phase 6 (Wave H): Independent Verified Kernels & Compiled `LNIR_WIRE_V1` Suite
- **Contract**: [`docs/contracts/phase6-independent-kernels.json`](contracts/phase6-independent-kernels.json).
- **Qualified Independent Kernels (`independent_verified`)**:
  1. `LeanAV.PlanIR.rescalePtsIndependentOrFallback` (exact rational timestamp conversion with explicit out-of-domain fallback).
  2. `LeanAV.PlanIR.scalePlane2x2IndependentOrFallback` (verified 2x2 downscaler with bounds and parity guards).
  3. `LeanAV.PlanIR.demuxIvfIndependentOrFallback`, `LeanAV.PlanIR.demuxMatroskaIndependentOrFallback`, and `LeanAV.PlanIR.demuxMpegTsIndependentOrFallback` (IVF, Matroska `SimpleBlock`, and 188-byte MPEG-TS container demuxers with explicit out-of-domain fallback).
  4. **16 Compiled `LNIR_WIRE_V1` DSP & Stencil Kernels** in [`LeanAV/NativeKernels.lean`](../LeanAV/NativeKernels.lean) (`swscale_luma_gain_bias_simd`, `flac_lpc_autocorr_dot_simd`, `opus_celt_pvq_mix_saxpy_gpu`, `av1_wiener_3tap_sym_gpu`, `av1_cdef_fma_blend_gpu`, `h264_idct_tuple_accum_sroa`, `bframe_bipred_blend_gpu`, `hevc_sao_band_offset_add_gpu`, `aac_imdct_window_mul_gpu`, `prores_qscale_map_simd`, `boxblur_div9_recip_shift_simd`, `pq10_studio_clamp_select_simd`, `swscale_down2x2_box_simd`, `swscale_down3x3_box_simd`, `swscale_down3to2_bilinear_simd`, `av1_cdef_dir_filter_simd`), validated with `lean-native-core validate-tv` (`16/16`, 64 samples) and `lean-native-core verify-certs` (`16/16 VerifiedKernelProof`), lowered to LLVM 18 IR (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`, including 7 vectorized 2D strided/reduction runtime routines) and NVIDIA PTX 8.0 (`sm_90`), linked into `libleanav_dsp.a`, and verified at runtime against `evalLnirKernel`.
- **Completeness & Fallback Theorem**: `LeanAV.PlanIR.independentKernel_fallback_complete_and_sound`.
- **CLI Verification**: `lffmpeg verify-kernels`.

### Phase 7: Progressive Promotion, Rollback & Closure
- **Contract**: [`docs/contracts/phase7-promotion-and-rollback.json`](contracts/phase7-promotion-and-rollback.json).
- **Rollback Policy**: Any differential regression, FFI invariant violation, or out-of-domain input triggers `KernelExecutionResult.fallbackDelegated` to `BackendTier.delegatedFaithful` or immediate demotion in the capability registry.

---

## 3. External Quorum Reviews & Final Validation (`APPROVED`)

### 3.1 Wave A Quorum (Claude Fable 5.1, GPT-6 Astra, Gemini 4 Argon)
Executed via Orb MCP on `nippur`:
- **Claude Fable 5.1** (`claudecode`, `claude-fable-5-1`), Mission `20e7bae7-a9ed-412d-9314-624296673d97`
- **GPT-6 Astra** (`codex`, `gpt-6-astra`), Mission `667e0fbb-daed-40f3-a989-876e75778181`
- **Gemini 4 Argon** (`antigravity`, `gemini-4-argon`), Mission `912bb20d-d926-484b-b6e9-f761aa4c61df`

All parity, security, universal theorem (`∀`), and architectural deduplication items raised by the three reviewers were remediated and covered by regression tests in [`tests/differential/test_phase3_to_7.py`](../tests/differential/test_phase3_to_7.py).

### 3.2 Final `turbo-lean` (`689d906`) + Built-In `LeanNative` & Multi-Hardware Closure Quorum
Executed across `nippur` (Intel Xeon E3-1245 V2), **Zen 5 Boat VM** (`AMD Ryzen 9 9950X`, Mission `465214a1-db78-4351-b9e6-7680c3ac3bd6`), and **DGX Spark** (`spark-de79`, Grace ARM64 + Blackwell GB10 `sm_90`, Missions `977f8684-fbb2-451e-95df-4243b1f7a73a` and `13515315-3d63-414d-98c0-a8da6e6dd270`) after integrating unified `turbo-lean` (`689d906` with built-in `LeanNative` LLVM 18 + PTX 8.0 `sm_90` codegen, parallel multi-file `audit_spec_files`, and Blake3 content-addressed per-file spec-audit cache achieving `2.23 ms` warm audit across all 15 modules), verifying **`8,734` declarations** (`8,734` under `v4.35.0`, `8,821` under `v4.31.0`, `0 sorryAx`, `0` custom axioms) via `scripts/check_axioms.lean`, auditing all 15 `LeanAV/*.lean` modules (**`252 / 252` `non_vacuous_and_tight`**), migrating all non-irreducible C routines to pure Lean 4 + `LNIR_WIRE_V1`, keeping `c/leanav_simd_kernels.c` at **`585` lines** of irreducible C glue (including fused 3-plane YUV420p `leanav_c_exec_lnir_scale2d_yuv420p_ba` and 16-bit LE `leanav_c_exec_lnir_scale2d_yuv420p10le_ba`, 4x-vectorized `@lean_native_swscale_bilinear_q8_u8` and `@lean_native_swscale_bilinear_q8_u16le`, `@lean_native_apply_filters_yuv420p_u8` with `lean_is_exclusive` in-place reuse, `@lean_native_luma_stats_u16le`, `@lean_native_extract_u16le_msb8`, and `@lean_native_luma_acceptance_16x16_u8`), and linking the 16 compiled `LNIR_WIRE_V1` kernels and 13 vectorized 2D strided/reduction/filter/16-bit runtime routines into `libleanav_dsp.a`:
- **GPT-6 Astra** (`codex`, `gpt-6-astra`), Missions `2d44b8ec-e74d-47a0-bd65-7b2c8401fc9f` and `68a2250e-a517-4179-a28a-827975d1a3b2` (`VERDICT: APPROVED`), plus Wave 4 audit Mission `09eac971-7ae9-414f-a48c-37f8aa773d1f` (initial `REJECTED` audit identifying PTX GF(2) `.clmul64` lowering, universal SWAR byte-lane quantification, and `v4.31.0` `.olean` alignment, all remediated in `eea4446`, `7304087`, and `2eebfb6`).
- **Claude Fable 5.1** (`claudecode`, `claude-fable-5-1`), Missions `2078cb13-feb4-46f7-93c1-e2a7c0f98717`, `13f1481c-e838-445c-8042-710a25fbb30c`, and `7adc1208-b806-44e4-8300-7221019f90f3` (initial audit `REJECTED` on doc sync `7304087`, final `VERDICT: APPROVED` on `2eebfb6` after independent verification of all build, spec audit, axiom, LNIR, PTX GF(2) emulation, and end-to-end transcode gates).

---

## 4. Differential & FATE Verification Summary (`448` Tests)

| Verification Suite | Scope | Before (`v0.2.0-quorum`) | Current Verified State | Verifiable Details |
| :--- | :--- | :---: | :---: | :--- |
| **Suite #0 (`tests/`)** | **79 Python unit & differential tests** + C-ABI / LNIR self-tests | `58 / 59` (`98.3%`) | **`79 / 79` (`100%`)** | `26/26` unit + `53/53` differential + `53/53` `self-test` waves + `16/16` compiled LNIR kernels |
| **Suite #1 (`bench.py`)** | **120 cases**: containers, `-map`, metadata, chapters, dispositions, BSFs, subtitles, multi-input & timeline | `78 / 120` (`65.0%`) | **`119 / 120` (`99.2%`)** | `111` bit-exact `MATCH` + `5 MATCH(lossy)` + `3 MATCH(both-fail)` |
| **Suite #2 (`test_diff.py`)** | **79 cases**: video/audio codecs, `-vf` / `-af`, `pix_fmt`, rate control (`-crf`, `-b:v`, `-qp`) & time trimming | `41 / 79` (`51.9%`) | **`79 / 79` (`100%`)** | `79/79` identical exit codes, `79/79` identical `ffprobe` signatures (`0 DIFF`) |
| **Suite #3 (`fate-run.sh`)** | **187 official FFmpeg FATE tests** (`fate-lavf-*` + `fate-ffmpeg-*`) | `0 / 187` FATE pass (`187/187` CLI rejections) | **`129 / 129` FATE pass (`100%`)**<br>**`186 / 186` identical outputs** | `100%` of the `129` FATE tests passed by `ffmpeg 6.1.1` pass under `lffmpeg`, `0/187` CLI rejections, `186/186` bit-identical non-empty outputs |
