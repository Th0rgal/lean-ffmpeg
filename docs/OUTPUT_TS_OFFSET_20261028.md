# Signed output timestamp offset routing — 28 October 2026

The CLI now recognizes the exact `-output_ts_offset` option and consumes its
signed duration argument. Previously the upstream Matroska regression recipe's
`-output_ts_offset -60ms` produced two parser errors; positive values and zero
also failed because the option was absent from the delegated-option registry.
The original full argv now passes plan validation with zero errors.

The correction reuses the existing signed-duration validation for `-itsoffset`
and `-sseof`. It retains the original argument spelling and order and delegates
execution to FFmpeg. Unknown option spellings, malformed durations and unsafe
media paths remain rejected. This bounded parser grammar is not a claim of
complete equivalence to every upstream duration spelling; the backend retains
final numeric-range and semantic validation.

## Qualification

On the isolated candidate based on `81f58a3`, the build (53 jobs), 53 self-test
waves, FFI/kernel checks and all proof checks passed. Counts remain **8,899
LeanAV declarations with zero sorryAx/custom axioms and 264/264 tight specs**.
Python qualification passed **136/136 unit tests, 81/81 differential tests and
7/7 focused routing tests**, with zero skips. Focused tests use a recording fake
backend and cover exact argv, signed time units, repeated options, backend
status/diagnostics, malformed values and unchanged security checks.

An initial test incorrectly assumed the existing MP4 copy plan was native.
Comparison with the frozen base showed both versions delegated that plan. The
test now checks the existing translated H.264 scaling plan instead. The initial
failure and comparison evidence remain retained in the campaign audit; no
production code changed after the successful build/proof checks.

The local terminal review passed 266 checks, including preservation of the
frozen base tree/cache/binary; independent parent review passed 251 checks.
Executable SHA256:
`3d5239f11ac7a1277177df9c717786665a4ab55e115bde4023246ae86fee2151`.

## Scope

No fresh upstream Matroska media recipe has been executed for this correction.
The selected encode/decode validation is prepared but awaits the reviewed
runtime/provenance protocol. These project checks earn no upstream FATE credit,
full-suite parity claim, native codec claim or performance result.
