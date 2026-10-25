# Campaign Closure Dossier: FFmpeg Parity & Maxwell Qualification (`lean-ffmpeg`)

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
  - `leanav_c_ffi_abi_version` (`0x00010005`, exported directly from Lean 4 in [`LeanAV/PlanIR.lean`](../LeanAV/PlanIR.lean))
  - `leanav_c_ffi_probe_mp4_contract` (pure Lean 4 bounded MP4 box probe `ffiProbeMp4ContractPure` exported directly to C-ABI)
  - `leanav_c_ffi_cancel_gate` (exported directly from Lean 4 `specFfiCancelGate` with zero model-code gap)
  - `leanav_c_verify_plane_ffi_contract` (64-byte stride alignment + 64-byte tail SIMD padding)
  - `leanav_c_mc_bipred_plane` and `leanav_c_xor_residual_plane` wired as `@[extern]` in [`LeanAV/Video.lean`](../LeanAV/Video.lean)
- **CLI Verification**: `lffmpeg verify-ffi`.

### Phase 6 (Wave H): Independent Verified Kernels & Compiled `LNIR_WIRE_V1` Suite
- **Contract**: [`docs/contracts/phase6-independent-kernels.json`](contracts/phase6-independent-kernels.json).
- **Qualified Independent Kernels (`independent_verified`)**:
  1. `LeanAV.PlanIR.rescalePtsIndependentOrFallback` (exact rational timestamp conversion with explicit out-of-domain fallback).
  2. `LeanAV.PlanIR.scalePlane2x2IndependentOrFallback` (verified 2x2 downscaler with bounds and parity guards).
  3. `LeanAV.PlanIR.demuxIvfIndependentOrFallback` (IVF container demuxer with 64-bit per-packet integrity check).
  4. **12 Compiled `LNIR_WIRE_V1` DSP Kernels** in [`LeanAV/NativeKernels.lean`](../LeanAV/NativeKernels.lean) (`swscale_luma_gain_bias_simd`, `flac_lpc_autocorr_dot_simd`, `opus_celt_pvq_mix_saxpy_gpu`, `av1_wiener_3tap_sym_gpu`, `av1_cdef_fma_blend_gpu`, `h264_idct_tuple_accum_sroa`, `bframe_bipred_blend_gpu`, `hevc_sao_band_offset_add_gpu`, `aac_imdct_window_mul_gpu`, `prores_qscale_map_simd`, `boxblur_div9_recip_shift_simd`, `pq10_studio_clamp_select_simd`), validated with `turbo-lean native-validate-tv` (`12/12`, 64 samples) and `turbo-lean native-verify-certs` (`12/12 VerifiedKernelProof`), lowered to LLVM 18 IR (`c/leanav_lnir_x86_64.ll` and `c/leanav_lnir_arm64.ll`), linked into `libleanav_dsp.a`, and verified at runtime against `evalLnirKernel`.
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

### 3.2 Final `turbo-lean` (`23e426f`) + `lean-native-core` Closure Quorum
Executed on `nippur` after integrating `turbo-lean` (`23e426f`), fixing the 3+ binder sampler in `gpu_fastcheck.rs`, fixing `scripts/check_axioms.lean` (`8,112` declarations verified), consolidating the 15 `LeanAV/*.lean` modules (`205 / 205` `non_vacuous_and_tight`), moving the C-ABI gates and MP4 header probe to direct Lean 4 `@[export]` functions, adding zero-copy `ByteArray` (`lean_sarray_object`) LNIR execution, and linking the 12 compiled `LNIR_WIRE_V1` kernels into `libleanav_dsp.a`:
- **GPT-6 Astra** (`codex`, `gpt-6-astra`), Mission `8a3a02ee-9f9a-46d3-a987-c8dfea825322`: **`VERDICT: APPROVED`** (zero blocking issues).
- **Claude Fable 5.1** (`claudecode`, `claude-fable-5-1`), Mission `3820c481-cc12-4e40-aa3b-719294176f73`: **`Verdict: APPROVED`** (zero blocking issues after independent verification of all build, spec audit, axiom, LNIR, and differential gates).

---

## 4. Differential & FATE Verification Summary (`445` Tests)

| Verification Suite | Scope | Before (`v0.2.0-quorum`) | Current Verified State | Verifiable Details |
| :--- | :--- | :---: | :---: | :--- |
| **Suite #0 (`tests/`)** | **59 Python unit & differential tests** + C-ABI / LNIR self-tests | `58 / 59` (`98.3%`) | **`59 / 59` (`100%`)** | `15/15` unit + `44/44` differential + `53/53` `self-test` waves + `12/12` compiled LNIR kernels |
| **Suite #1 (`bench.py`)** | **120 cases**: containers, `-map`, metadata, chapters, dispositions, BSFs, subtitles, multi-input & timeline | `78 / 120` (`65.0%`) | **`119 / 120` (`99.2%`)** | `111` bit-exact `MATCH` + `5 MATCH(lossy)` + `3 MATCH(both-fail)` |
| **Suite #2 (`test_diff.py`)** | **79 cases**: video/audio codecs, `-vf` / `-af`, `pix_fmt`, rate control (`-crf`, `-b:v`, `-qp`) & time trimming | `41 / 79` (`51.9%`) | **`79 / 79` (`100%`)** | `79/79` identical exit codes, `79/79` identical `ffprobe` signatures (`0 DIFF`) |
| **Suite #3 (`fate-run.sh`)** | **187 official FFmpeg FATE tests** (`fate-lavf-*` + `fate-ffmpeg-*`) | `0 / 187` FATE pass (`187/187` CLI rejections) | **`129 / 129` FATE pass (`100%`)**<br>**`186 / 186` identical outputs** | `100%` of the `129` FATE tests passed by `ffmpeg 6.1.1` pass under `lffmpeg`, `0/187` CLI rejections, `186/186` bit-identical non-empty outputs |
