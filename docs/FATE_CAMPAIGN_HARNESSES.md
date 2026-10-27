# Reproducing campaign evidence

These tools preserve failures and unavailable cases. They do not certify full
FFmpeg compatibility or a faster independent implementation.

## Upstream scope and inventory

The October 27, 2026 campaign uses FFmpeg commit
`bf0e831606938f530326c9679591109407fa8d0d` and 2,631 hashed sample files.
Generate the configured target list from an explicitly configured upstream build,
then expand the source inventory:

```sh
make --no-print-directory -s -C /path/to/FFmpeg fate-list SAMPLES=/path/to/fate-suite > configured.txt
python3 scripts/fate_inventory.py --ffmpeg-root /path/to/FFmpeg \
  --configured-list configured.txt --output inventory.json
```

GNU make expands generated names and conditional groups. The output retains
disabled cases and hashes transitive make inputs. Hypothetical feature unions
are source cases, not proof that all combinations can be built or executed.
Architecture, endian, unstable and large-test variants remain explicit.

The retained inventory has 6,133 entries: 6,065 marked upstream source cases and
68 pixel-descriptor overapproximations. Its 5,721 configured entries exactly
match the configured list. Independent review leaves `full_manifest_certified`
false because executable applicability and conditional completeness are not
fully established. Never replace this scope with a successful subset.

## Attributing execution

`scripts/fate_target_exec.py` replaces only the exact pinned FFmpeg executable
with the candidate. All other tools run unchanged and are traced as reference
helpers. Set three absolute paths:

```sh
export FATE_REFERENCE_FFMPEG=/path/to/FFmpeg/ffmpeg
export FATE_CANDIDATE=/path/to/lffmpeg
export FATE_EXEC_TRACE=/path/to/fresh-exec.jsonl
make -C /path/to/FFmpeg fate SAMPLES=/path/to/fate-suite \
  TARGET_EXEC="python3 /path/to/lean-ffmpeg/scripts/fate_target_exec.py"
```

For per-target attribution, include an additional makefile **after** the upstream
Makefile containing `$(FATE): export FATE_CASE_NAME = $@`. The JSONL trace records
target, executable, argv, PID, working directory and timestamp. A trace records
an invocation attempt; combine it with fresh successful FATE reports and binary
hashes before crediting a pass. Preserve reports before subsequent runs and use
unique output paths. `fate-hwdevice` must be handled explicitly when it appears
in `fate-list` but is excluded from the default `fate` aggregate.

The retained full baseline has 4,650 fresh both-zero reports (including unchanged
reference helpers), 1,031 candidate failures, 39 stale/unavailable entries, and
one reference-only hardware helper. Another 412 provisional entries are not
enabled. These are baseline counts, not a current full-suite success claim.
Later selected correctness waves do not silently update that denominator.
Delegating CLI work to FFmpeg does not demonstrate candidate library/API,
checkasm, ffprobe, or standalone codec implementations.

## Historical manifests

`scripts/historical_compat.py` requires an explicit JSON manifest, available
media, and separate reference/candidate commands. Run `--help` for arguments.
Both commands must succeed and produce matching nonempty bytes; requested probe
checks must also succeed. Both-fail and matching metadata over corrupt content
do not pass. The historical 119/120 and 79-case definitions remain unrecovered;
this tool does not invent replacement cases or counts.

## Paired timing diagnostics

`scripts/paired_benchmark.py` supports a deliberately bounded manifest schema.
Inputs must be self-contained NUT or WAV files with an explicit `input_format`;
the harness forces that demuxer before `-i`. Playlists and auxiliary inputs are
unsupported. Every command explicitly selects `-c copy` after the input, before
any optional lossless per-stream codec overrides. Implicit encoders are rejected.
It pins executable, manifest and input SHA-256s; enforces Linux CPU affinity and
decoder, encoder and filter thread counts; runs at least two warmups per side
and five alternating AB/BA pairs; and retains raw times, medians and sample CV.
Both timed commands finish before probing or decoding either output.

Every case requires decoded stream byte hashes plus matching duration, frame
count and stream properties. Exact mode also compares encoded bytes. Missing
metadata, failed commands, unsupported inputs, unavailable affinity and CV above
3% prevent valid timing. The gain threshold is `max(1%, 2*maxCV)` with per-case
regression checks. Use a unique output filename for every run.

Backend declarations are not verified implementation evidence. The harness
always leaves `independent_implementation_speedup_eligible`,
`benchmark_gates_passed`, and `optimization_accepted` false. Its FFmpeg-against-
itself smoke validates plumbing only. A promotion still requires an independent
oracle, measured Amdahl profile, frozen reviewed tools, proof/test gates, and
actual hardware evidence. macOS CI does not establish MacBook Air M2 timing.

## Harness tests

```sh
python3 -m unittest discover -s tests -p 'test_fate_*.py'
python3 -m unittest discover -s tests -p 'test_historical_compat.py'
python3 -m unittest discover -s tests -p 'test_paired_benchmark.py'
```

Controls include generated/disabled cases, transitive-input mutations, precise
executable replacement, both-fail, missing/empty/corrupt output, probe failures,
invalid manifests, insufficient samples, and pair ordering. These checks are
harness validation, not FFmpeg feature coverage.
