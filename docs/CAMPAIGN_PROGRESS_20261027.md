# October 27 campaign evidence snapshot

This snapshot reports completed observations from the continuing campaign. It is
not a full-FFmpeg, standalone-codec, performance, or cross-hardware certificate.
The correctness and harness work live on separate campaign branches.

## Configured FATE run

Upstream FFmpeg is pinned to `bf0e831606938f530326c9679591109407fa8d0d`.
The latest complete configured attempt used candidate `8806be9` in two isolated
execution trees with private Git contexts, separate generated outputs, typed
executable and recipe START/END traces, complete before/after tree inventories,
and sample/provenance boundary checks. The reference arm returned zero for all
5,721 targets. Candidate results were:

| Classification | Targets |
|---|---:|
| Fresh candidate-invoked CLI pass | 4,407 |
| Candidate failure | 646 |
| Prerequisite blocked, no fresh report | 72 |
| Candidate unexercised | 215 |
| Helper/text status zero, no candidate credit | 380 |
| Source-only status zero, no candidate credit | 1 |
| Configured total | 5,721 |
| Not enabled in this configuration | 412 |
| Retained inventory total | 6,133 |

The 68 pixel-format overapproximations are included in the 412 not-enabled rows.
The independent terminal auditor accepted evidence consistency; the full attempt
correctly exited nonzero because FATE failures remain. It verified the retained
rows, raw reports, trace pairing, 142 frozen artifact pins, 128 candidate
provenance pins, 2,631 sample files, Git contexts and generated deltas. Receipt
SHA-256: `9d32b5920034734480cbabb76b432c8f8359240bab5e56f2d781d1e3f04e2182`.

This is not a complete upstream manifest, library/API, checkasm, ffprobe, or
standalone-codec certificate. Per-open/descendant input closure and fresh
provenance for every cached build input remain unproved. Helper and source-check
success receives no candidate CLI credit.

The earlier shared-scratch diagnostic had 4,404 CLI passes, 669 candidate
failures, 39 prerequisite blocks and 609 no-credit rows. Row-by-row comparison
found 15 prior failures now passing and 33 newly prerequisite-blocked rows,
including 12 prior CLI passes. All previous 39 blocks remain; no prior CLI pass
became a direct candidate failure. Fresh generator failures and missing candidate
fixtures are observed. Different fixture preparation prevents attributing these
changes solely to the AAC code change; discarded generator stderr and missing
per-open provenance limit root-cause claims.

A separate actual `--enable-gpl` configuration and upstream Make target list
contains 5,778 members: 57 additions (53 FFmpeg CLI, four ffprobe), no removals or
unknown rows. All 6,133 inventory rows remain; 355 are disabled in that alternate
configuration, including all 68 overapproximations. The probe reused a pinned
pixel-format list. Configuration membership alone does not establish build,
fixture, sample or runtime coverage.

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

The signed wavelet-routing commit `e9b2205` passed its six selected FATE targets
and Linux/macOS CI. The signed AAC decoder-routing commit `8806be9` added only
`aac_fixed` to the delegated codec list and eight portable routing/security tests.
Its 17-target gate retains 15 fresh candidate-invoked passes and two failures:
`fate-ffmpeg-streamloop-transcode-av` (`-stream_loop`) and
`fate-filter-meta-4560-rotate0` (`-display_rotation:v:0`). The latter fails before
its second-stage AAC invocation. Existing upstream AAC comparison tolerances are
unchanged; passing this gate is not a byte-exact or native AAC claim. Local
validation passed build, 53 self-test waves, FFI/kernels, 54 unit tests, 74
differential tests, 8,887 declarations with zero forbidden axioms and 264 tight
specifications. Linux/macOS CI run
[40505766049](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40505766049)
passed for `8806be9`.

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

A subsequent fixed overhead qualification compared the same original and
instrumented binaries without tracing during measured runs. It used two
route/quality qualifications, two warmups per binary, and five alternating
paired trials on four distinct allowed physical cores. All 16 outputs matched
the scalar oracle, frozen metadata/timestamps and encoded bytes. Original median
was 276.30 ms (CV 0.40%); instrumented median was 278.50 ms (CV 1.17%), or 0.80%
aggregate overhead. Individual paired overheads ranged from 0.49% to 2.80%.

The instrumented parent timeline conserves outer wall duration. Clock epoch
alignment is unproved, so startup and exit share an undivided residual rather
than invented separate intervals. Median native-transform occupancy was about
0.017% (48.45 microseconds total), under-resolved by the predeclared sensitivity
check. Parent waits overlap child work; these are occupancy observations, not
exclusive CPU or causal Amdahl fractions. The first attempt stopped at its first
qualification because strace elided argv; no measured trials ran. A second
prepared version was rejected during review for misclassifying the loader cache.
Both are retained; one corrected fixed attempt completed without extra trials.

The fixture does not cover arbitrary scale ratios, bit depths, HDR, audio, or
metadata. A representative workload, concurrency-aware causal profile and frozen
settings-equivalent candidate-versus-FFmpeg benchmark remain missing.
Optimization workers remain gated. The profiling source and binary are diagnostic
artifacts, not production changes; this overhead comparison is not a speedup.

Campaign receipts are retained privately beside `CONTRACT.md` in the authorized
campaign workspace. Historical 119/120 and 79-case definitions/media remain
unrecovered; their historical summaries are not fresh certificates.
