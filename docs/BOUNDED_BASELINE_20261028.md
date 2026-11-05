# Accepted bounded baselines — 28 October 2026

## Compiler-integrated candidate `ae6ed0b`

An independently accepted run now measures the frozen compiler-integrated
candidate `ae6ed0bde09f9d6832f582ffbf7f4e71a2abf33f` against the pinned FFmpeg
6.1.1 runtime on nippur (Intel Xeon E3-1245 V2, affinity CPUs 0–3, shared host).
This is the exact 120-frame 1920×1080 YUV420P → 960×540 H.264 lossless workload
(`-preset veryfast -crf 0`), not a claim about arbitrary H.264 transcodes.

| Measurement | Result |
| --- | ---: |
| Candidate median wall time | 10.505727 s |
| FFmpeg median wall time | 10.223550 s |
| Median of paired candidate/reference ratios | 1.0286119133 |
| Paired slowdown | **2.861%** |
| Candidate / reference CV | 1.4173% / 0.3818% |
| Paired-ratio CV | 1.4321% |
| Measured pairs | 5; candidate slower in all five |

The paired ratio is the median of five per-pair ratios, not the ratio of the two
median times. Two warmups per arm preceded five alternating pairs; there was one
run and no retry. All fourteen 81,424,133-byte outputs matched the frozen oracle
byte for byte. The 28 before/after observations retained the same THP setting,
CPU affinity, model and governor configuration. Timing includes process launch,
wait and lifecycle receipt overhead; no overhead was subtracted. Shared-host
measurements do not establish physical isolation or absence of systematic bias.

Independent terminal review passed 941 checks, including all output bytes,
452 runtime pins, 38 guarded artifacts and independently recomputed statistics.
Evidence under `baseline-preparation/1080p120-v1/paired-baseline-v5-ae6ed0b-thp-a/`:

| Artifact | SHA256 |
| --- | --- |
| `result.json` | `f2f0e2557848b678eb70271f92f66e32e49ee5f1e86ce5b4ff38ce2aea0e68fa` |
| `independent-terminal-acceptance.json` | `6407039dd256633aa310e92d28852d173cc3232b2252ccd2c7ee89a284cc7523` |
| `run-end.json` | `415b29ea209d2c72402c725d34f37a87bb931a0d9f98c2fdbe4084f72ec9820a` |

The raw result intentionally retains `bounded_baseline_accepted: false` pending
review; the separate immutable terminal acceptance records the final accepted
verdict. This measurement does not cover later PFM/BSF/IAMF corrections, other
workloads or hardware. Full FATE provenance remains incomplete, and no
optimization or universal speedup is accepted.

## Earlier candidate

This historical measurement qualifies the frozen `lffmpeg-mpeg-options` candidate,
not the current integration or IAMF candidate. It is an instrumented measurement
on a shared host, without proof of physical isolation.

The workload is exactly 120 frames of 1920×1080 YUV420P scaled to 960×540.
There were two warmups per arm and five alternating measured pairs. All fourteen
outputs passed the workload quality checks. The median paired candidate/reference
wall-time ratio was **1.032490**, meaning **3.249% slower** for this workload.
Candidate, reference and paired-ratio coefficients of variation were respectively
0.804744%, 0.265003% and 0.602041%.

The independent verdict was `ACCEPTED_BOUNDED_SHARED_HOST_BASELINE`.
The earlier v4 run remains rejected: it stopped during warmup with zero measured
pairs. Output correctness, timing validity and performance improvement are separate
checks; a slower measurement can be valid.

Evidence is retained in the campaign workspace under
`baseline-preparation/1080p120-v1/paired-baseline-v5-parent-a/`:

| Artifact | SHA256 |
| --- | --- |
| `result.json` | `b2f0d946f9edaec7e315e37c064fc353bbc57b492d1b512514b915af21df8111` |
| `activation.json` | `4617b374c10e59c57a1b6035bc1c0d36772a64095710c1cac08722243c993415` |
| `run-end.json` | `582144e508e575d77b95a39863c3c96326f547c14af12b1362b1206ab1cd8cf1` |

These hashes bind the retained artifacts; they do not substitute for publishing
all raw measurements. This result does not qualify the current compiler integration,
all FATE tests, other workloads, DGX Spark, or MacBook Air M2. No optimization is
accepted on its basis alone.
