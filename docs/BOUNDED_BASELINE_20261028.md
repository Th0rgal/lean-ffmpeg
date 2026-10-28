# Accepted bounded baseline — 28 October 2026

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
