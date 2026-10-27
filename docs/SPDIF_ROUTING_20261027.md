# SPDIF14 independent terminal acceptance

Frozen auditor accepted terminal evidence consistency. Reference: 14 raw-status-zero rows. Candidate: 11 CLI credits and 3 retained failures. Harness/live/frozen-artifact integrity checks passed; selected FATE success remains false.

All 6,133 inventory rows are retained: 5,721 configured (14 selected and 5,707 unselected), plus 412 disabled. The 68 overapproximation rows remain a subset of disabled.

| Target | Reference raw status | Candidate raw status | Stage exits (candidate) | Candidate CLI credit |
|---|---:|---:|---|---|
| fate-spdif-aac-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-ac3-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-dca-core-bswap | 0 | 1 | [1] | no |
| fate-spdif-dca-core-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-dca-master | 0 | 1 | [1] | no |
| fate-spdif-dca-master-core | 0 | 1 | [1] | no |
| fate-spdif-dca-master-core-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-eac3 | 0 | 0 | [0] | yes |
| fate-spdif-eac3-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-mlp | 0 | 0 | [0] | yes |
| fate-spdif-mp2-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-mp3-remux | 0 | 0 | [0, 0] | yes |
| fate-spdif-truehd | 0 | 0 | [0] | yes |
| fate-spdif-truehd-branch-padding | 0 | 0 | [0] | yes |

The three failures retain exact co-blockers: `dca-core-bswap` rejects `-spdif_flags +be`; `dca-master` rejects `-dtshd_rate 192000`; `dca-master-core` rejects `-dtshd_rate 96000`. Each candidate command ran and returned nonzero; none is waived.

The frozen auditor verified 106 source/dependency pins, 10 distinct external media files, 14 golden files, exact recipes and stage argv, seven two-stage remux cases and seven one-stage MD5 cases. Every selected candidate row invoked the frozen candidate. Each arm removed exactly 50 vsynth PGMs plus `tests/test_copy.ffmeta`; inputs outside that set may be reused. No per-file input-open closure is claimed.

Pre-START anchors were captured 17232426501 ns before reference START. Full quality/provenance, source/Git identity, sample trees, complete before/after inventories, and alias-contract checks passed. Original failed quality receipts are retained.

No global, full-suite, native, library/API, or oracle promotion.

Terminal audit SHA256: `8bb52d898abfdf71a7b8a647517f90d97ac0d0b60c36c41f41a333b430803a18`
Terminal receipt SHA256: `5ba03a6b1c0cfa44b28cae64f039a2a55e47078d57609d06e32e7235c0b023e5`
Pre-START anchors SHA256: `4f9e0c30c818ffeb913853492da94b2bcffb81d1ade80ffa5874f1107b361f62`

## Implementation and project validation

The only production change adds the exact `spdif` token to
`LeanAV.Cli.supportedFormat`. Explicit input/output formats use the existing
delegated path. Ten portable routing tests check argument order and bytes,
backend exit codes, native-path controls, malformed formats and unsafe paths.
Native codecs, PlanIR, the FFI and security policy are unchanged.

Local validation under Lean 4.35.0 passed 74 unit tests, 74 differential tests
with zero skips, 53 self-test waves, FFI/kernel checks, the axiom audit
(8,897 declarations; zero forbidden axioms), and 264 tight specifications.
The first differential attempt ran only 55 tests with four skipped classes due
to two absent ignored fixtures. Restoring their pinned bytes exposed three H.264
failures with a minimal backend lacking libx264. Both the prior and new frozen
candidates failed those three tests with that backend and passed them with the
full runtime. The corrected 74-test run passed with the explicit full runtime;
earlier failed receipts remain preserved. Upstream FATE used its original pinned
reference configuration throughout.

FFmpeg source: `bf0e831606938f530326c9679591109407fa8d0d`.
Frozen candidate SHA256:
`fb9e1fc7e327d751ef6ab70ec2a2ec90ecce5c3617ed2513c56a8270b2f12592`.
Composite project-quality SHA256:
`a43f224ceba6853a983e94940407f586b246c46198e5d6d7ebe2cddbe59a0459`.
Candidate provenance SHA256:
`247679d38a9f4dda2032f04ac8af2776b803fd0806f1502603098bca337f110f`.

This wave supplies no new performance measurements or speedup claim.
