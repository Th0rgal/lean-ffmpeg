# M3-D Integration Contract (2026-11-04)

- **Coordinator**: `89faa3dd-0ec6-43f3-85f5-f6e58fe29836` (`opencode` + `builtin/smart`)
- **Base**: `741fb1d0c4d71a27a2bdc4759dc354aefa09a675` (`campaign/m2-complete-20261031`)
- **Branch**: `campaign/m3-d-zero-exec-20261104` (new). Never push `main`. Never force-push. Never `--amend` a pushed commit. Never `[skip ci]`.
- **GPG**: `30EAE29B6766A7A70A4DEB4BF480B9A3F84BE648` (`Thomas Marchand (agent) <agent@thomas.md>`). Every commit `git commit -S`.
- **Tips to integrate (all independent `ACCEPT`, GitHub `verified: true`)**:
  - M3-A HEVC Main: `7beef63e9370bddb2f01f3187c4a9fe3bdb975a1` (`campaign/m3-a-hevc-main-20261102`, CI `41547094723`)
  - M3-B AV1 Main: `c944e1dc56f8ee5b70a96eb557182e2683c5173f` (`campaign/m3-b-av1-main-20261102`, CI `41878300506`)
  - M3-C lavfi DAG: `644b0056defbaf4a3d36fb28adf14a20b16c42e6` (`campaign/m3-c-lavfi-dag-20261102`, CI `41486474839`)
- **Pins**: Lean `v4.35.0`, `lean-sys@077775ba387f1eeb2976cb8763b4633b8d5ce313`, `turbo-lean@dc1656dc948f1d7bfc25d165575ae3819a2e8b97` built from source. Axiom allowlist only `{propext, Classical.choice, Quot.sound}`.

## Merge shape (verified via `gh api` compare)

Each tip vs `741fb1d` touches exactly the six shared files plus its exclusive modules. Exclusive files do not overlap, so check them out from the tip. Shared files must be merged by hand.

| Tip | Exclusive files (take whole) | Shared deltas |
| :--- | :--- | :--- |
| M3-A `7beef63` | `LeanAV/HevcMain.lean` (+7762), `LeanAV/HevcMainProofs.lean` (+539), `tests/differential/test_hevc_main.py` (+220) | `ci.yml` +3/−3, `AGENTS.md` +7/−7, `LeanAV.lean` +2, `Main.lean` +84/−3, `README.md` +8/−8, dossier +17 |
| M3-B `c944e1d` | `LeanAV/Av1Main.lean` (+14566), `LeanAV/Av1MainProofs.lean` (+504), `tests/differential/test_av1_main.py` (+1107) | `ci.yml` +3/−3, `AGENTS.md` +7/−7, `LeanAV.lean` +2, `Main.lean` +92/−3, `README.md` +8/−8, dossier +23 |
| M3-C `644b005` | `LeanAV/LavfiGraph.lean` (+1914), `LeanAV/LavfiGraphProofs.lean` (+762), `tests/differential/test_lavfi_graph.py` (+200) | `ci.yml` +3/−3, `AGENTS.md` +7/−7, `LeanAV.lean` +2, `Main.lean` +588/−13, `README.md` +10/−10, dossier +20 |

`LeanAV/Format.lean` is untouched on all three tips. Do not edit it.

### Shared-file numbers (do not copy any one tip's grep)

| Track | decls | tight specs | new proof-module specs | self-test waves |
| :--- | :--- | :--- | :--- | :--- |
| base `741fb1d` | 17478 | 717/717 | — | 54 |
| M3-A | 19449 | 740/740 | `HevcMainProofs` 23 | 55 |
| M3-B | 19925 | 743/743 | `Av1MainProofs` 26 | 55 |
| M3-C | 18429 | 758/758 | `LavfiGraphProofs` 36, `LavfiGraph` 5 | 55 |

After the three-way merge, **recompute** declaration count, `turbo-lean` tight-spec count, LOC, and self-test wave count. Expected ballpark before M3-D deletions: decls `17478 + (19449-17478) + (19925-17478) + (18429-17478) = 22847`, specs `717 + 23 + 26 + 41 = 807`. Deleting delegation will move both numbers; CI greps must match the post-deletion measurement, on both Linux and macOS jobs.

`LeanAV.lean` just gains six imports (order: Hevc, Av1, Lavfi, each module then its proofs, after `InprocTranscode`).

## Delegation that M3-D must delete (still live on base `741fb1d`)

Zero-exec means the finished `lffmpeg` binary contains **no** `fork`, `execvp`, `execve`, `posix_spawn`, or `IO.Process.spawn` of `ffmpeg`/`ffprobe`. `strace -f -e trace=execve` with `PATH=/nonexistent` and `LEANAV_FFMPEG_BIN=/nonexistent` must report `execve == 1` (the `lffmpeg` process itself) on the standalone matrix, including the HEVC/AV1/lavfi CLIs.

Delete or rewrite all of:

1. `LeanAV/PlanIR.lean`: Delete `buildDelegatedFfmpegArgv` (~L2126), `@[extern "leanav_c_exec_delegated_ffmpeg"] opaque ffiExecDelegatedFfmpegC` (~L2296), and `BackendTier.delegatedFaithful` / `"delegated_faithful"` (reclassify out-of-scope routes to `BackendTier.unsupported` / `"unsupported"`, `delegatedContainer := false`, `fallbackAllowed := false` so `plan` / `-dump-plan` honestly states that out-of-scope codecs/containers/options fail closed rather than delegating). **Keep** `leanav_lean_ffi_abi_version`, `leanav_lean_ffi_cancel_gate`, `leanav_lean_ffi_probe_mp4_contract` and the matching `leanav_c_ffi_*` opaques.
2. `LeanAV/Main.lean`: `tier := .delegatedFaithful` (~L1432); `runDelegatedLosslessFallback` (~L1653, calls `buildDelegatedFfmpegArgv` + `ffiExecDelegatedFfmpegC`); JSON mode `ffmpeg-cli-delegated-faithful` (~L1668); every `.fallbackDelegated` branch (~L1709, L1791, L1940, L1956); the second `ffiExecDelegatedFfmpegC` (~L1986). **Keep** the native paths: `tryFastHeaderProbeTranscode`, `readMp4MoovWindowIO`, `probeIsoMp4HeaderSlice`, `runtimeVideoFilterSupported` (scale / `colorspace=bt709` / tonemap), `runInprocH264TranscodeCli`, `runNativeStreamCopy`. Where a native path used to fall back to ffmpeg, **fail closed** with a structured diagnostic and a non-zero exit (no partial output). The fast-header probe may still report `ffmpeg-cli-mp4-transcode-failed` when demux succeeds and the in-process transcode does not (~L2150–2180); it must not spawn.
3. `LeanAV/Encoder.lean`: `resolveToolExecPathIO` (~L1646), `resolveFfmpegBinIO` (`LEANAV_FFMPEG_BIN`, hardcoded `/tmp/opencode/ffmpeg-runtime-full/...`) (~L1655), `resolveFfprobeBinIO` (`LEANAV_FFPROBE_BIN`) (~L1665), `ffmpegSpawnEnvIO` (~L1675), `probeInputHdrColorspaceFallbackIO` / `probeInputFpsRationalFallbackIO` / `probeInputHdrAndFpsIO` (`IO.Process.output` on ffprobe, ~L1784–1897), `opaque execPipeTranscodeU8IO` (~L1971, used ~L2355), `closeChildStdinAndWait` (~L2150), and the spawn inside `transcodeMp4GeneralVerifiedIO` (~L2188, `resolveFfmpegBinIO` ~L2201). Replace the ffprobe color/fps fallback with the pure-Lean `avcC`/`hvcC`/`av1C` probe already in `Format.lean` / `Encoder.lean`, or fail closed. Update `combinedProbeFallbackGateSpec` so it no longer describes an ffprobe process budget.
4. `c/leanav_simd_kernels.c`: argv builder (~L825–838); `leanav_spawn_dec_child` (~L840) and `leanav_spawn_enc_child` (~L870) (`pipe`/`fork`/`execvp`/`_exit(127)`); `leanav_c_exec_delegated_ffmpeg` (~L186–188 and ~L844–892). Delete the pipe-transcode pthread bridge only if nothing else calls it after `execPipeTranscodeU8IO` is gone. **Keep** `pread`/`pwrite` window I/O, the FFI ABI / cancel gate, and the `lean_sarray_object` LNIR wrappers. After the edit, `grep -nE 'fork|execvp|execve|posix_spawn'` on `c/*.c` must be empty.
5. Tests. Two groups, do not confuse them.

   **Group A — the binary used to spawn `ffmpeg`/`ffprobe`. These must change, because after this branch that spawn does not exist.** Every former `delegated_faithful` and `translated_partial` subprocess execution (the block in `runFFmpegCli` at `Main.lean:2068–2128`, the introspection fallback at `Main.lean:1986`, `transcodeMp4GeneralVerifiedIO`, and the three `IO.Process.output` ffprobe probes) now **fail closed**: non-zero exit, structured JSON naming the unsupported codec/container/filter, no output file, and no `execve` of anything but `lffmpeg` itself. `PlanIR` classifies those out-of-scope inputs as `"unsupported"` (`delegated_container: false`, `fallback_allowed: false`). `scripts/check_mpeg_options.lean` must check option parsing + fail-closed `"unsupported"` classification only, never execution.

   **Group B — routing tests that previously checked `delegated_faithful` classification and invoked a stub `ffmpeg`.** Update their plan assertions from `"delegated_faithful"` to `"unsupported"` (`delegated_container == False`) while **keeping** their option-grammar / parse-field assertions (e.g., `mpegOptions`, `bsf`, `exportSideData`, `outputTsOffset`, `iamf`, `vvc`, `wavelet`), and update execution assertions to expect fail-closed non-zero exit with zero stub invocations (`not self.log.exists()`) and zero output file. Known members: `tests/test_{aac_fixed,bsf,export_side_data,extended_pixel_format,iamf,image_output,mpeg_options,output_ts_offset,spdif,vvc,wavelet}_routing.py`, `tests/test_inproc_transcode_routing.py`, `tests/differential/test_{delegated_diagnostics,decoder_options,pixel_formats,semiplanar_444,streamhash,ogg_serial_offset,phase3_to_7,native_remux,native_ffv1,lossless_codecs,aac_lc,combined_probe}.py`. Read each one; preserve every positive native assertion and convert every delegated expectation to fail-closed + zero-exec.

   `tests/differential/test_u16le_identity.py`: `u16le_identity.lean` called `transcodeMp4GeneralVerifiedIO` / `execPipeTranscodeU8IO`. Once `execPipeTranscodeU8IO` and `leanav_c_exec_pipe_transcode_u8` are deleted, update `u16le_identity.lean` + `test_u16le_identity.py` to test the pure in-process 10-bit LNIR scaling & luma-stats C-ABI wrappers (`leanav_c_exec_lnir_scale2d_yuv420p10le_ba`, `leanav_c_exec_lnir_luma_stats_u16le_ba`, `leanav_c_exec_lnir_extract_u16le_msb8_ba`) directly with the C interposition counter (`u16le_identity_counter.c`), with zero `ffmpeg` subprocess stubs.

   `tests/differential/test_phase2.py` and `test_phase3_to_7.py` skip unless `/tmp/opencode/ffmpeg-runtime-full/bin/{ffmpeg,ffprobe}` exist. Do not vendor that tree. Point `REFERENCE`/`FFPROBE` at `shutil.which` and `skipUnless` the oracle; the candidate assertions that no longer hold because the path now fail-closes must be rewritten, not skipped.
6. `.github/workflows/ci.yml`: drop `libavformat-dev libavcodec-dev libswresample-dev libavutil-dev` (`lake build` never links libav; keep `clang` and `strace`). Run `lake build`, `self-test`, `verify-ffi`, `verify-kernels`, `check_axioms`, and a dedicated **Zero-FFmpeg Standalone Suite** step with `PATH=/usr/bin:/bin` (or `ffmpeg`/`ffprobe` hidden/absent) + `strace -f -e trace=execve` (`execve == 1` across remux, FFV1, PNG, FLAC, H.264+AAC MP4, HEVC, AV1, lavfi, and fail-closed rejections) BEFORE installing or exposing reference `ffmpeg`/`ffprobe` purely as external test oracles for the differential parity suite (`tests/differential`), where `lffmpeg` itself continues to run under `ISO_ENV` (`PATH=/nonexistent`).

## CLI wiring to preserve from each tip (all three land in `LeanAV/Main.lean`)

The three `Main.lean` diffs are small and disjoint. Apply all three, then delete the spawn.

- **M3-A** adds `open LeanAV.HevcMain` / `HevcMainProofs`; a `m3aHevcMainOk` self-test conjunct (so `baseOk` gains `&& m3aHevcMainOk` and the JSON gains `"m3a_hevc_main_ok"`); CLI arms `hevc-probe`, `hevc-decode-raw`, `hevc-encode-raw` (encode takes `qp`, `fmt` ∈ {`annexb`,`mp4`,`hvcc`}, `log2Ctb`, `tilesCol`, `tilesRow`); and 30 `#print axioms LeanAV.HevcMainProofs.*` lines.
- **M3-B** adds `open LeanAV.Av1Main` / `Av1MainProofs`; `m3bAv1MainOk` (round-trips a 32×32 mid-grey frame at qidx 0); CLI arms `av1-probe`, `av1-decode-raw`, `av1-encode-raw` (`qidx`, `fmt` ∈ {`obu`,`ivf`,`mp4`,`auto`}, `tilesCol`, `tilesRow`, using `av1TileLog2`); and 34 `#print axioms LeanAV.Av1MainProofs.*` lines. Note `encodeAv1FromYuv420p` takes `(qidx, fmt, tileColsLog2, tileRowsLog2)` — the CLI wrapper does the `av1TileLog2 1` conversion. Do not change that signature.
- **M3-C** adds `open LeanAV.LavfiGraph` / `LavfiGraphProofs`; `m3cLavfiOk` (ten gate specs plus one video DAG, one `amix`, and a cycle rejected at typecheck); the whole lavfi planner (`lavfiSupportedFilterNames` is 31 names, `scanRawLavfiCli`, `assembleRawLavfiGraphSpec`, `inprocLavfiDagCandidateArgs`, `promoteLavfiDagPlanArgs`, `refinePlanWithInputWithArgs`, `executeLavfiSpec`, `runInprocLavfiDagCli`, `runLavfiProbeCli`, `runLavfiRunCli`); CLI arms `lavfi-probe` and `lavfi-run`; the `runFFmpegCli` call becomes `refinePlanWithInputWithArgs plan0 args` with a dispatch arm for `inproc_lavfi_dag` directly after the H.264 arm; and 11 `#print axioms`.

All three bump the self-test JSON `"waves": 54` to `55` and add their own conjunct to `baseOk` and `j5e`. The merged self-test has **one** `"waves"` field (keep `55` unless you add a wave) and a `baseOk` / `j5e` that carries all three conjuncts: `m3aHevcMainOk`, `m3bAv1MainOk`, `m3cLavfiOk`.

## What stays native (do not regress)

- **H.264 + AAC-LC MP4** (`runInprocH264TranscodeCli` / `runInprocTranscodeWithProbeStatsIO`): 8-bit 4:2:0 Baseline/Main/High, CAVLC and CABAC, I/P/B, 8x8 transform, frame crop, explicit and implicit weighted prediction, Q8 bilinear scale, mono/stereo AAC-LC, bounded packet ring, synthetic ISO-BMFF mux.
- **HEVC Main 8-bit 4:2:0** via the existing raw CLI already on the M3-A tip: `hevc-decode-raw`, `hevc-encode-raw`, `hevc-probe`. Wire them from `Main.lean` exactly as M3-A does. Entry points to call (do not reimplement): `decodeHevcToYuv420p`, `probeHevcStreamJson`, `encodeHevcFromYuv420p`, `initHevcEncoder`, `encodeHevcNals`, `buildHvccRecord`, `buildHevcMp4`. `hevcMain8BitScopeSafe` stays the scope gate. 10-bit, 4:4:4, 4:2:2, non-Main, and odd dimensions stay fail-closed.
- **AV1 Main 8-bit 4:2:0** via `av1-decode-raw`, `av1-encode-raw`, `av1-probe` as wired on the M3-B tip. Entry points: `decodeAv1ToYuv420p`, `probeAv1StreamJson`, `encodeAv1FromYuv420p`, `av1MuxIsoMp4Track`, `av1ParseAv1C`, `av1BuildAv1C`, `av1DemuxIsoMp4Av1Samples`. Preserve the fail-closed policy exactly:
  - Do **not** reject a sequence header because `seq.filmGrainPresent` / `film_grain_params_present` is set when `apply_grain=0`.
  - Reject only when a frame carries `apply_grain=1`.
  - Fail closed on inter prediction when `hdr.width0 != rSlot.w || hdr.height != rSlot.h`.
  - 10-bit, 4:4:4, 4:2:2, non-Main, mono, and reserved-bit `av1C` stay fail-closed.
  - `moof`/`mvex` fragmented MP4 may stay a clean non-zero exit.
  - **Darwin**: never run a live `libsvtav1` encode (Mach semaphore deadlock). The v10 test file gates that off `__APPLE__` and instead decodes the embedded SVT-AV1 superres, scaled-inter, and rav1e 4-byte `av1C` fixtures (`box_sz == 12`, six mutations). Keep `run()` `timeout=60` and the live `librav1e` case at `duration=0.08`.
- **lavfi** (`inproc_lavfi_dag`) as wired on the M3-C tip: `parseFilterGraph`, `typecheckFilterGraph`, `executeTypedFilterGraph`, sources `color`/`testsrc`/`nullsrc`/`sine`/`anullsrc`, multi-pad `split`/`asplit`/`overlay`/`hstack`/`vstack`/`amix`/`amerge`, and the raw/`md5`/`framemd5`/`.mp4`/`.mkv`/`.avi`/`.wav`/`.flac`/`.png` muxers (`muxLavfiMp4Bytes`, `muxLavfiFfv1Bytes`, `muxLavfiMd5Bytes`). Cycles and ill-typed links fail closed. `maxLavfiVideoFrames = 300`, `maxLavfiAudioSamples = 480000`.
- **Lossless**: FFV1 v3, PNG + Zlib/DEFLATE, FLAC. Native `-c copy` remux for MP4/MOV/M4V/M4A, MKV/WebM, WAV, FLAC, IVF. CLI introspection (`-version`, `-formats`, `-codecs`, `-filters`, `-h`, …) with no subprocess.
- **LNIR**: 46 `LNIR_WIRE_V1` kernels + 14 outer shells. Do not touch `c/leanav_lnir_*.ll` or `scripts/gen_lnir_outer_shells.py`.

## Unsupported = fail closed, not delegated

Anything not in the native set above exits non-zero with a structured diagnostic (`stdout` when `-json`, else `stderr`) and writes no output file:

- codecs outside the native set (`aac_fixed`, `prores`, `vp9`, `opus`, `vvc`, …)
- H.264 / HEVC / AV1 10-bit, 4:4:4, 4:2:2, High-10, RExt, professional profiles
- GPU (`-hwaccel`, `cuda`, `vaapi`, `videotoolbox`)
- network and unsafe protocols (`http://`, `rtsp://`, `concat:`, `/dev/*`, `..`)
- `-filter_complex` graphs the lavfi typechecker rejects

There is no `delegated_faithful` tier and no `LEANAV_FFMPEG_BIN` / `LEANAV_FFPROBE_BIN` after this branch. Remove both env vars from docs and tests.

## README (user directive 2026-11-03)

Rewrite `README.md` as a short human overview, not the current metric wall:

1. What `lffmpeg` is (one paragraph): Lean 4 `v4.35.0` `ffmpeg`-compatible CLI, standalone, no bundled `ffmpeg`.
2. **Native, in-process** — a flat list of codecs, containers, bit depths, and filters that actually run: H.264 High 8-bit 4:2:0 + AAC-LC MP4; HEVC Main 8-bit 4:2:0; AV1 Main 8-bit 4:2:0; FFV1 v3; PNG; FLAC; stream copy for MP4/MOV/MKV/WebM/WAV/FLAC/IVF; lavfi sources and the filters named above; scale and the `colorspace=bt709` / tonemap path.
3. **Fail-closed** — the unsupported list above. Say explicitly that unsupported input is rejected, not silently delegated.
4. **What the proofs cover** — three sentences: Lean kernel check (`0 sorryAx`, axioms `{propext, Quot.sound, Classical.choice}` only), `turbo-lean audit-spec` (`non_vacuous_and_tight`, no vacuous/trivial/shadowed), and `SymbolicTV` on the 46 LNIR kernels (UB/domain/poison/return/memory). Then one sentence on what differential tests add (byte-exact or bounded-LSB comparison against a reference `ffmpeg` oracle, which is **not** part of the binary).
5. **TCB** — name it, do not bury it: Lean 4 runtime, `lean-sys` POSIX shim, `c/leanav_simd_kernels.c` (FFI/OS glue only, after the spawn deletion), the 14 unproved LLVM outer shells, the LLVM 18 backend. No `ffmpeg` in the TCB.
6. **Benchmarks** — a short summary of the numbers already measured in the current README (do not invent new timings). Point at `docs/` for the methodology.
7. Move the declaration tables, FATE/audit tables, and the per-module spec counts to `docs/` (a new `docs/VERIFICATION_APPENDIX.md` is fine). `AGENTS.md` keeps the exact measured counts because CI and reviewers read it.

`docs/CAMPAIGN_CLOSURE_DOSSIER.md`: append one M3-D paragraph. Do not rewrite M1/M2/M3-A/B/C entries.

## Gates before you push

1. `lake build`
2. `lffmpeg self-test`, `verify-ffi`, `verify-kernels`
3. `lake env lean scripts/check_axioms.lean` — `0 sorryAx`, `0` custom axioms
4. `turbo-lean --json audit-spec` on every `LeanAV/*.lean` (build turbo-lean from the pinned commit)
5. `python3 -m unittest discover -s tests -p "test_*.py"` with `ffmpeg`/`ffprobe` hidden from `PATH`, PLUS a new dedicated `tests/test_zero_delegation_cert.py` verifying zero symbol references to `fork`/`execvp`/`execve`/`posix_spawn` in `.lake/build/bin/lffmpeg` (`nm -u`) and `strace -f -e trace=execve` (`execve == 1`, Linux) across the full standalone matrix (introspection, remux, FFV1, PNG, FLAC, H.264+AAC MP4, HEVC, AV1, lavfi, and fail-closed unsupported cases), PLUS `python3 -m unittest discover -s tests/differential -p "test_*.py"` (where external `ffmpeg`/`ffprobe` act strictly as test-harness reference oracles and `lffmpeg` runs with `PATH=/nonexistent`).
6. `strace -f -e trace=execve` on the HEVC, AV1, lavfi, H.264 in-proc, and remux CLIs: `execve == 1`
7. `grep -nE 'fork\(|execvp|execve|posix_spawn|IO\.Process\.(spawn|output)|LEANAV_FFMPEG_BIN|LEANAV_FFPROBE_BIN|ffiExecDelegatedFfmpegC|execPipeTranscodeU8IO|delegatedFaithful|delegated_faithful' -- LeanAV c scripts tests .github` returns nothing (test files may mention the strings only inside a negative assertion that they are absent)
8. Both CI jobs green. Update the decl and spec greps to the measured values.

## Do not

- Do not push or merge to `main`. The coordinator does that, and only after a fresh `writer=false` review returns `Verdict: ACCEPT`.
- Do not run `maxwell`.
- Do not edit frozen receipts, `paired-baseline-*`, `epoll29-*`, or `integration/lean-ffmpeg-wave2-complete`.
- Do not resume any earlier mission. This branch starts from `741fb1d` plus the three tips.
- Do not "fix" the AV1 Darwin `libsvtav1` deadlock by running the encoder anyway. Keep the skip and the embedded fixtures.
