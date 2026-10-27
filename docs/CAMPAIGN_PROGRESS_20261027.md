# October 27 campaign evidence snapshot

This snapshot reports completed observations from the continuing campaign. It is
not a full-FFmpeg, standalone-codec, performance, or cross-hardware certificate.
The correctness and harness work live on separate campaign branches.

## Configured FATE run

Upstream FFmpeg is pinned to `bf0e831606938f530326c9679591109407fa8d0d`.
The complete configured attempt used candidate `62ba8fd`:

| Classification | Targets |
|---|---:|
| Fresh candidate-invoked pass | 4,241 |
| Candidate failure | 832 |
| Candidate not exercised (reference helpers/source checks) | 609 |
| Prerequisite blocked, no fresh report | 39 |
| Configured total | 5,721 |

The provisional inventory retains 6,133 entries: 6,065 source cases and 68
pixel-format overapproximations. There are 412 not-enabled entries. Configuration,
architecture/endian and generated/disabled completeness remain unresolved. Helper
success does not certify candidate library/API, checkasm, or ffprobe behavior.

The signed `62ba8fd` pixel-format wave passed all 231 selected reference/candidate
targets, fixing 195 prior candidate failures. The signed `c7bd145` decoder-option
wave (`flags2`, `downmix`, `dtshd`) passed all 52 selected reference/candidate
targets with candidate invocation traces. Its local checks passed 53 self-test
waves, FFI/kernels, 30 unit tests, 65 differential tests, 8,887 declarations with
zero forbidden axioms, and 264 tight specifications. Linux/macOS CI run
[40475884934](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40475884934)
passed. These selections do not replace the full denominator or update the
frozen full-run counts by arithmetic.

The signed `a504de1` pixel-alias wave retained all 50 selected targets:
reference 50 passed, candidate 44 passed and six remained blocked by
`-wavelet_type`. Linux/macOS CI run
[40481681577](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40481681577)
passed. The signed `05c1fdc` VVC routing wave then passed all 61 selected
historical failures with fresh reference/candidate reports, exact argv
attribution, and unchanged source/media/binary pins. Local validation passed
39 unit tests, 74 differential tests, 53 self-test waves, FFI/kernels, the
8,887-declaration axiom audit, and 264 tight specifications. Independent review
passed 279 receipt checks. Linux/macOS CI run
[40486081911](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40486081911)
passed. VVC support here is delegated CLI routing, not a standalone codec.

## Delegated x86 diagnostic

One predeclared attempt compared `c7bd145` against an assembly-enabled build of
the pinned FFmpeg source. It used CPU affinity 2, one thread, two warmups, five
alternating AB/BA pairs, forced lossless media, and decoded/probe/encoded quality
checks. All quality comparisons passed.

| Workload | Candidate median slowdown | Candidate CV |
|---|---:|---:|
| 720p FFV1 | 15.33% | 0.697% |
| 720p to 360p FFV1 | 38.82% | 1.786% |

Both cases materially regressed. `timing_valid`, `benchmark_gates_passed`, and
`optimization_accepted` remained false. No favorable retry was selected. This
measured end-to-end delegated CLI slowdown; it is not an independent native implementation
comparison. No current DGX Spark or verified MacBook Air M2 measurement exists.

## Exact-fixture native oracle and exploratory profile

A separate untimed probe used immutable candidate `c7bd145` and pinned FFmpeg
6.1.1/x264 runtime artifacts. This runtime is distinct from the upstream FATE
build. Its self-contained MP4 contains 12 lossless 128×96 yuv420p BT.709 frames at
12 fps. The candidate selected `translated_partial` and scaled to 64×48. Two
FFmpeg children decoded and encoded the frames; their argv contained no scale
filter. Source dispatch supports native rounded 2×2 reduction.

All 55,296 decoded bytes matched both FFmpeg `area` output and an independent
scalar `(a+b+c+d+2)//4` oracle. Frame timestamps, duration, stream/color metadata,
and encoded MP4 bytes also matched for this fixture. Independent review checked
219 runtime pins, 43 artifact hashes, source snapshots, complete sample
containment, and recomputed every scalar output byte.

A separate isolated build added parent-stage timing spans without changing the
transform algorithm. One instrumented run and one immutable-candidate run under
`strace` preserved the same output oracle and child argv. Independent review
verified hashes, spans, thread creation, exec and wait records. SIGCHLD supplied
coarse child CPU totals; `perf` was unavailable. The traces are perturbed by
instrumentation, Python shims, and ptrace. Parent waits overlap child work, and
runtime initialization lies outside the instrumented main span. No causal Amdahl
fractions or speed conclusion follow.

The fixture does not cover arbitrary scale ratios, bit depths, HDR, audio, or
metadata. There is no dynamic kernel-entry trace, measured instrumentation
overhead, complete runtime module closure, representative steady-state profile,
or frozen settings-equivalence benchmark contract. Optimization workers remain
gated. The profiling source and binary are diagnostic artifacts, not production
changes.

Campaign receipts are retained privately beside `CONTRACT.md` in the authorized
campaign workspace. Historical 119/120 and 79-case definitions/media remain
unrecovered; their historical summaries are not fresh certificates.
