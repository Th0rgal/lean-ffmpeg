# IAMF routing qualification — 28 October 2026

The CLI previously rejected IAMF format, stream-group and stream-ID arguments
used by upstream recipes. This correction accepts the explicit `iamf` format and
`.iamf` suffix, `-streamid`, `-stream_group`, `-use_stream_ids_as_track_ids`,
`-/stream_group` and `-/filter_complex`. Input group maps are sent to the delegated
backend, including semantic validation of group IDs and selector tails.

The original argument order and bytes reach the backend. File-valued arguments
must satisfy the existing local-path policy. This checks filenames; it does not
confine references inside graph files or resolve symlinks. The implementation
adds no blanket unknown-option passthrough and no native IAMF codec.

## Executed original recipes

Reference source: `bf0e831606938f530326c9679591109407fa8d0d`.
Each listed recipe ran encode, decode and probe phases for both arms. All
**14/14 paired recipes** matched the frozen upstream expected output (encoded
file MD5 and size, decoded frame CRC and probe output), with byte-identical paired
media. All **84 process receipts** reported success. Twenty-eight invocations
were upstream `ffprobe` helpers, not candidate implementation coverage.

- `fate-iamf-5_1-copy`
- `fate-iamf-5_1_4`
- `fate-iamf-7_1_4`
- `fate-iamf-9_1_6`
- `fate-iamf-ambisonic_1`
- `fate-iamf-ambisonic_1-projection`
- `fate-iamf-ambisonic_1-projection-copy`
- `fate-iamf-ambisonic_3-copy`
- `fate-iamf-stereo`
- `fate-mov-mp4-iamf-5_1_4`
- `fate-mov-mp4-iamf-7_1_4-video-last`
- `fate-mov-mp4-iamf-ambisonic_1`
- `fate-mov-mp4-iamf-stereo`
- `fate-mov-mp4-iamf-stereo-id-collision`

Parent review independently checked 722 assertions over actual command arrays,
terminal receipts, output bytes, recipe reconstruction and 89 pinned inputs.
The recipe runner was also checked with 97 synthetic controls and 20 checks of
actual runner execution, including failure propagation and full attempt counts.

## Project qualification

The build, 53 self-test waves, FFI and kernel checks passed. The axiom audit
reported 8,899 declarations with no forbidden axioms; all 264 specifications
remained tight. Unit tests passed 118/118 with no skips. Differential tests passed 81/81 with no skips.

The initial unit attempt retained one obsolete expectation that safe
`-/filter_complex` remained unsupported. It was replaced with exact delegated
argument checks plus rejection of traversal and remote graph filenames. The
initial failed receipt and interrupted retry logs remain preserved.

## Evidence and scope

Campaign artifacts are retained under `campaign-ffmpeg-20261027/parent-audit/`:

| Artifact | SHA256 |
| --- | --- |
| `iamf-routing-independent-review-r2.json` | `90f43044c108543188f8a55795a5dd419c33c406eddd2d2eb94bcfd9997ceee4` |
| `iamf-routing-media-plan.json` | `3dc1349492355331f059c4e4324900d908b084a16d04b150fd923723c66ff90f` |
| `iamf-routing-media-a/result.json` | `afc4b469ae0d16eb645be6c9402761f493fff0c909b788643f52f79958dcb48c` |
| `iamf-media-parent-raw-acceptance.json` | `6b205cfeb307a4ed0027de62780c910d3418996a7ed25bcb757b4353cc5ce18f` |
| `iamf-unit-r3.json` | `057cb6e490fe103b2a58627f90ea1359087e0349b902467bba70f1e81c07f006` |
| `iamf-differential-r3.json` | `c78fd47218d14c4670ec1b23aa8c1422049e2ba64fea664ed9cb08bed43f7dac` |

This is scoped compatibility evidence. The frozen full-suite candidate has not
been replaced, full FATE totals are unchanged, and no performance result or
main-branch promotion is implied.
