# Maxwell Plan for Measured and Verifiable FFmpeg Compatibility

## 0. Mandate

Goal: evolve `lean-ffmpeg` from an MP4 prototype into a typed, portable, and progressively verifiable multimedia layer that delegates faithfully where needed and replaces FFmpeg components selectively where formally proved and benchmarked.

The project does not claim blanket 1:1 superiority everywhere. Every capability requires a versioned contract, an oracle, formal proofs or differential tests, measured metrics, and an explicit backend qualification decision.

Baseline references:

- repository: `lean-ffmpeg`;
- initial commit: `386c07663a214aba2fbbf563abb561a08ddc8d52`;
- Lean toolchain: `leanprover/lean4:v4.31.0`;
- `lean-sys` pinned to commit `9a3fda9180d8e9a2e429ca38046b74467f68866b`;
- `turbo-lean` (including built-in `LeanNative` / `lean-native-core`) pinned to commit `23e426fa99438c81d34e3167a955dbe3958a060d`;
- reference FFmpeg pinned in the generated capability registry with binary SHA-256, build configuration, and shared library metadata;
- Maxwell governor: `https://github.com/Th0rgal/maxwell`.

## 1. Success Contracts

A capability enters the contractual scope only when qualified by build, platform, and backend tier:

- `independent_verified`: independent implementation formally verified and differentially compared;
- `independent_tested`: independent implementation tested against the differential oracle but not yet fully proved;
- `delegated_faithful`: structured delegation to the pinned reference FFmpeg build;
- `translated_partial`: partial translation with explicit domain boundaries;
- `approximate`: bounded semantic equivalence within documented numerical tolerances;
- `unsupported`: explicit fail-closed rejection before execution;
- `untested`: inventoried only, never claimed as supported.

Evaluation axes are tracked separately:

1. CLI compatibility and diagnostics;
2. container, codec, filter, and I/O coverage;
3. media fidelity, timestamps, and metadata;
4. throughput, memory footprint, latency, and energy;
5. security, robustness, and resource bounds;
6. cross-platform portability and determinism;
7. verifiability and trusted computing base (TCB) size;
8. licensing and redistributability.

## 2. Mandatory Maxwell Loop

Each workstream follows the loop:

```text
Conjecture -> Specification -> Certification -> telemetry -> priors -> next wave
```

### Conjecture

Generate short competing hypotheses covering architecture, bug reduction, test corpus, IR design, or kernel optimization. Each branch carries:

- stable `branch_id`;
- `race_group`;
- prior probability `p`;
- `impact`;
- `effort_p50` and `effort_p90` in tokens;
- falsifiable hypothesis;
- mechanical oracle;
- abandonment condition.

Any branch with `effort_p50 > 6000` is recursively decomposed before certification. Each leaf task targets a single module, theorem family, or self-contained test harness.

### Specification

Formalize the target contract and its counterexamples:

- normalized inputs and outputs;
- reference FFmpeg behavior;
- equivalence class;
- domain bounds and non-goals;
- negative mutants;
- performance and fidelity metrics;
- specification hash.

Every formal module must pass `turbo-lean --json audit-spec` with zero vacuous, trivial, or shadowed specifications, paired with negative mutants confirming that the test suite catches regressions.

### Certification

A branch is accepted only after passing:

- `lake build` and `turbo-lean --json audit-spec`;
- `lake env lean scripts/check_axioms.lean` (`0 sorryAx`, `0` custom axioms);
- `turbo-lean native-validate-tv` and `turbo-lean native-verify-certs` for `LNIR_WIRE_V1` kernels;
- differential tests against the pinned FFmpeg build;
- adversarial corpus and boundary checks for native FFI surfaces;
- output, error, resource, and determinism checks;
- multi-model quorum review for architectural or contractual gates.

### Maxwell Governance

Use Maxwell to:

- rank candidate branches by probability, impact, and effort;
- launch at least one falsification probe per wave;
- cancel sibling branches in a race group once a winner is certified or falsified;
- prune stagnant or over-budget branches;
- record controller-verified outcomes (`VALIDATED`, `FALSIFIED`, `PRUNED`, `BLOCKED`, or `FALSE_GOAL`);
- audit campaign telemetry after each wave with `audit-campaign --fix`.

Workers do not self-report their own priors or costs.

## 3. Multi-Model Validation Quorums

External models provide independent adversarial review; they never replace mechanical oracles.

### Standard Quorum

For major decisions, consult Fable, Astra, and Gemini with an immutable review packet: git diff, formal specification, test outputs, benchmark metrics, and concrete audit questions.

A decision passes when:

- at least 2 of 3 reviews converge;
- no review identifies an unresolved contradiction with the specification;
- all mechanical oracles and test suites pass;
- dissenting points are tracked as explicit follow-up risks or experiments.

### Reinforced Quorum

Mandatory for:

- changes to public semantics or historical compatibility;
- CLI vs FFI vs independent kernel routing changes;
- adding network protocols, device inputs, or hardware accelerators;
- changes to the trusted computing base;
- licensing or redistribution changes;
- promoting an independent backend as the default implementation;
- removing a fallback path;
- claiming performance or security superiority.

Threshold: 3 convergent reviews, or 2 convergent reviews paired with a discriminating experiment that resolves the disagreement. Persistent divergence blocks promotion and opens a dedicated Maxwell branch.

### Review Format

Each consultation answers six questions separately:

1. Is the specification non-vacuous and falsifiable?
2. Do the proofs and tests measure the intended contract?
3. What risks are still missing?
4. Which architecture is recommended and why?
5. What minimal experiment could falsify this recommendation?
6. Is the promotion verdict `approve`, `approve_with_limits`, or `reject`?

## 4. Phases and Gates

### Phase 0: Scope Freeze and Baseline

Deliverables: generated capability registry, pinned FFmpeg reference build, environment manifest, platform qualification matrix, equivalence classes, and historical quirk policy.

Gate: no capability claimed without an executable test; reproducible baseline on Linux x86-64 first, with macOS ARM64, Linux ARM64, and Windows x86-64 tracked explicitly before cross-platform promotion.

### Phase 1: Differential Harness

Build the runner capturing argv, file hashes, environment, stdout/stderr, exit code, output artifacts, `ffprobe` JSON, packets, frames, samples, timestamps, metadata, and resource usage.

Compare exit status, error hygiene, streams, frames, samples, duration, timestamps, side data, visual/audio quality, file size, wall time, memory, and determinism.

Gate: never rely on "output file exists" alone; every observed discrepancy becomes a minimized regression test.

### Phase 2: Core Media Invariants

Cover timebases, PTS/DTS, edit lists, `-r`, `-ss`, `-t`, sub-millisecond durations, negative timestamps, color/range/matrix metadata, bit depth/chroma subsampling, filter chains, audio sample counts, `-v quiet`, `-json`, and missing-file error paths.

Gate: zero critical divergence on the regression corpus, with a preserved counterexample for every fix.

### Phase 3: Stream, Graph, and Timeline IR (`MediaPlanIR`)

Replace flat CLI parsing with a typed intermediate representation covering inputs, outputs, stream selectors, maps, filter graphs, timeline bounds, metadata, bitstream filters, and backend routing policy.

Gate: JSON-serializable and inspectable plan (`lffmpeg plan`), fail-closed pre-execution validation, verified CLI/IR round-trip, and preservation of all existing MP4 workflows.

### Phase 4: General Delegated Compatibility

Add support across waves for containers, codecs, filters, `-map`, multi-input/output, subtitles, metadata, chapters, dispositions, bitstream filters, protocols, and diagnostics.

Each integration is tagged `delegated_faithful`, `translated_partial`, or `approximate`.

Gate: domain coverage measured, malformed inputs rejected cleanly, unsafe paths blocked fail-closed, no flag silently ignored.

### Phase 5: Pinned C-ABI FFI Facade

Cover probing, packet/frame views, remuxing, plane alignment/padding contracts, and atomic cancellation through a compact, ABI-pinned C facade with explicit memory ownership.

Gate: memory ownership checks, cancellation gate verification, multi-worker concurrency tests, ABI version check (`0x00010005`), and zero regression against the CLI backend.

### Phase 6: Independent Verified Kernels

Target bounded components with clear mathematical specifications: timestamp rescaling (`AVRational`), 2x2/3:2 spatial scaling, container parsers/demuxers (IVF/MP4), lossless audio prediction (FLAC LPC), and `LNIR_WIRE_V1` DSP kernels compiled via `lean-native-core`.

Gate: independent declarative specification (`AVGateSpec`), formal proof (`0 sorryAx`, `turbo-lean audit-spec`), translation validation (`native-validate-tv`), certificate verification (`native-verify-certs`), differential oracle check, benchmark measurement, and explicit fallback (`fallbackDelegated`).

### Phase 7: Progressive Promotion and Rollback

An independent kernel becomes the default tier only when its coverage, fidelity, error handling, security, performance, portability, and rollback policy are documented and verified.

Gate: multi-model quorum approval and published per-capability benchmarks.

## 5. Mandatory Test Corpus

The test corpus covers:

- SD through 4K resolutions, CFR/VFR, B-frames, negative timestamps, and short/long durations;
- mono and stereo audio, 44.1/48 kHz sample rates, priming, and silence;
- 8/10/12/16-bit depth, 4:2:0/4:2:2/4:4:4 chroma subsampling, SDR/HDR10/HLG metadata;
- rotation, SAR/DAR, chapters, dispositions, and stream side data;
- fragmented MP4 (`moof`/`trun`) and non-seekable streams;
- truncated headers, corrupt payloads, and invalid CLI flag mutations.

Every reduced bug case is kept as a permanent regression test.

## 6. Security, Licensing, and Platform Policy

Execution uses structured `argv` (`fork` + `execvp`) with zero shell interpolation, isolated temporary directories, bounded CPU/memory/file/wall-clock limits, a strict local-file protocol allowlist (`isSafeLocalMediaPath`), and explicit path traversal rejection.

Platform status is tracked in [`docs/contracts/platform-qualification.json`](contracts/platform-qualification.json) across Linux x86-64, macOS ARM64, Linux ARM64, and Windows x86-64.

## 7. Persistent Repository Artifacts

Maintain in version control:

- this plan ([`docs/FFMPEG_PARITY_MAXWELL_PLAN.md`](FFMPEG_PARITY_MAXWELL_PLAN.md));
- the generated capability registry ([`docs/capability-registry.json`](capability-registry.json)) and its generator ([`scripts/generate_capability_registry.py`](../scripts/generate_capability_registry.py));
- formal specifications, `LNIR_WIRE_V1` artifacts, and negative mutants;
- minimized media fixtures and test vectors ([`tests/`](../tests/));
- stage contracts ([`docs/contracts/`](contracts/));
- quorum records and campaign closure dossier ([`docs/CAMPAIGN_CLOSURE_DOSSIER.md`](CAMPAIGN_CLOSURE_DOSSIER.md)).
