# Integrated conformance candidate — 28 October 2026

This candidate combines the published VVC, aac_fixed, wavelet, MPEG, SPDIF,
Ogg serial-offset and HDCD diagnostic corrections. It adds delegated routing
for 68 upstream pixel formats and `export_side_data`, including stream
specifiers. Native pixel formats remain unchanged; unsupported layouts are
processed by the selected FFmpeg backend.

The compiler integration uses turbo-lean commit
`533aa4975a15d45cae7b23463b6cc75d3ca40315` and Lean 4.35.0.
Regenerated LLVM has the same 58 x86 and 71 ARM function bodies as the prior
integration; ordering, formatting and the x86 vendor triple differ. No CPU
speed improvement is established by this regeneration.

## Local validation

- Build: 53 jobs; self-test: 53 waves; FFI and kernel checks pass.
- Axiom audit: 8,897 declarations, zero sorryAx/custom axioms.
- Specifications: 264/264 tight. Existing style warnings remain recorded.
- Unit tests: 98 distinct tests covered with no skips. The initial full run
  passed 96/96; after adding two edge tests, the changed side-data module was
  rerun in full and passed 14/14. This is composite evidence, not one 98-test run.
- Differential suite: 81/81 executed, no skips or failures.
- Real-media comparisons: 68 output pixel conversions and eight pp7/spp
  side-data variants; all 76 produced nonempty byte-identical outputs against
  the frozen upstream GPL build. All 16 framecrc outputs contain five frames.
  Independent review accepted this scoped evidence.

The source fixture bytes are pinned, but these 76 comparisons do not certify
complete fixture-generator/runtime provenance or add global FATE credits.
Input-format permutations and the entire stream-specifier grammar are not
claimed from this output-focused check. Tests using mock backends establish
argument routing and safety, not codec semantics.

## Full-suite denominator and performance limits

The retained campaign inventory contains 6,133 rows: 6,065 upstream cases and
68 retained overapproximations. Of these, 5,721 were configured and 412 disabled.
The reference passed the configured set. A fresh complete candidate run with
process/file provenance is still required; passing project tests is not 100%
FFmpeg parity. Helpers executed from upstream do not establish candidate API
or library compatibility.

A separate prospective x86 baseline for the **older frozen
`lffmpeg-mpeg-options` candidate** was independently accepted: two warmups per
arm and five alternating pairs, all 14 outputs identical. Median instrumented
wall times were 10.539735 s (candidate) and 10.220533 s (FFmpeg), with CVs
0.804744% and 0.265003%. The median paired ratio was 1.032490: candidate
**3.249% slower**. Measurement includes lifecycle journaling; shared-host
systematic contention is not excluded. This is neither a timing result for
this integrated candidate nor evidence of a gain from the compiler update.

The previous rejected v4 attempt remains rejected with zero measured pairs.
No DGX Spark or MacBook Air M2 measurement was added by this integration.
