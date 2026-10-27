# Benchmark evidence and limits

The retained cross-hardware figures are campaign measurements recorded in
the mission journal `maxwell_overnight_campaign_log.md` (Wave 9, W9-B4).
The exact relevant journal row is preserved in
[benchmark-campaign-excerpt.json](benchmark-campaign-excerpt.json). Native-kernel
figures were already recorded in the pre-update README; their individual raw
trial samples were not recovered. The older Wave 7 receipt at
`artifacts/traces/wave7_benchmark_receipt.json` describes a different workload
and is not the source of the paired CLI table. They cover nippur/x86, a Zen 5
Boat VM, and DGX Spark ARM64. No retained receipt contains a MacBook Air M2
benchmark, so the README marks that column as unmeasured.

The CLI comparison table uses paired measurements reported by the campaign. The
native-kernel table measures in-memory routines and is not an end-to-end FFmpeg
comparison. PTX assembly on DGX Spark does not prove live CUDA dispatch.

Compatibility claims are scoped carefully:

- current CI at commit `68936da` is green on Linux and macOS;
- local project tests reported 30 unit plus 53 differential passes;
- historical matrices report 119/120, 79/79, and 129/129 of the specified subsets;
- none of these is a claim that the complete upstream FFmpeg/FATE suite passes.

The 129/129 historical FATE claim comes from
[CAMPAIGN_CLOSURE_DOSSIER.md](CAMPAIGN_CLOSURE_DOSSIER.md), section 4. The external
`bench.py` and `test_diff.py` harnesses and complete paired FATE reports were not
recovered in the current workspace inspection. A remaining `shortest.rep` in the
sibling FFmpeg tree is an isolated failed test record, not the full campaign
result. It cannot establish either full coverage or the cause of the 120th
compatibility mismatch. The README therefore labels these totals historical and
does not claim their fresh reproduction.

Current CI evidence:
[Linux and macOS run 40462499784](https://github.com/Th0rgal/lean-ffmpeg/actions/runs/40462499784),
commit `68936da3998bdc943a5bc9dd0ddb56fa5d571be6`:

| Runner | Unit tests counted / skipped | Differential counted / skipped | Passed |
| :--- | ---: | ---: | ---: |
| Linux | 30 / 0 | 34 / 4 | 60 |
| macOS | 15 / 2 | 34 / 4 | 43 |

Both runners pass build, self-test, FFI, kernels and axiom audit. The local
83-test result was obtained with additional media dependencies and Lean 4.35.0;
the CI uses Lean 4.31.0. Skips and unavailable test classes are not passing tests.
