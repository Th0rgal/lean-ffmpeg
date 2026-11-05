# BSF parsing and delegated routing — 28 October 2026

The CLI now handles the outer bitstream-filter list using the frozen upstream
FFmpeg token grammar instead of splitting every comma. Escaped or single-quoted
commas inside `setts` expressions remain inside their stage. Original arguments
are passed unchanged to FFmpeg; this adds no native codec or bitstream-filter
implementation.

The supported-name gate also recognizes `trim`, `jpegapp`, `apv_metadata`,
`dv_error_marker`, and `remove_extra`. FITS/WBMP support from the preceding
`7e800f3` change is retained. No additional codec options, protocols or filesystem
permissions are accepted by this change.

## Grammar and verification scope

The lexer follows upstream `av_get_token` and `av_bsf_list_parse_str`, including
protected trailing whitespace, one escaping layer, literal backslashes inside
single quotes, unmatched single quotes and one terminal comma. Empty first or
interior stages fail name validation. Filter names follow `av_strtok` semantics
for leading `=` characters and remain case-sensitive. Option values and media
semantics are validated by the delegated backend, whose error status and
diagnostics remain observable.

The frozen source is FFmpeg `bf0e831606938f530326c9679591109407fa8d0d`.
A test-only oracle linked against its pinned `libavutil.a` directly calls
`av_get_token` and `av_strtok`. **8,909 deterministic cases** produced identical
decoded tokens and name-gate results when compared with the production Lean
functions. This is bounded differential evidence, not a universal equivalence
proof or a media benchmark. The corpus contains NUL-free argument strings; the
existing execution-hygiene gate rejects embedded NUL characters.

The portable routing suite passes **11/11 test methods**, including 64 executable
pure-function assertions, 32 lexical edge cases and ten raw escaped expressions
from completed failing FATE invocations. It checks original argv bytes, input and
output option positions, aliases, unknown-name rejection, backend failures and
unchanged path/protocol policy. Its backend shim does not process media.

The complete project suites pass **117/117 unit tests** and **81/81 differential
tests**, with zero failures, errors or skips. Native self-test, FFI and kernel
checks also pass. These are project checks, not the upstream FATE denominator.
The existing VVC regression now accepts one terminal comma and still rejects
a double terminal comma, matching the frozen upstream grammar.

The axiom audit remains **8,897 declarations with zero forbidden axioms**;
**264/264 specifications** remain tight. Existing style warnings are retained.
These declaration/specification counts do not establish that every FFmpeg
behavior is implemented or formally proved.

## Remaining work

The retained failure snapshot contains 62 BSF-related failed targets: 52 with
missing names, one with escaped-comma tokenization alone, and nine with both.
A separate replay of all 62 captured FFmpeg invocations against the frozen
upstream binary produced **56 successful pairs with byte-identical media or
framecrc output**. The six independent blockers below remained. The replay
retained all arguments except relocated file-output paths and checked 25 pinned
files before and after execution. An independently reviewed harness passed
74 bounded controls. This is scoped real-media evidence; it does not rerun the
complete FATE recipes or change the historical full-run denominator.

Six targets also have independent blockers: two JPEG APP negative tests need
`-xerror`, two APV tests need the APV codec and format, and two trim flush tests
need `-stream_loop`. These options remain unsupported. Unrelated `source` and
`sink` filters remain outside the allowlist. The pre-existing
`remove_extradata` spelling is not rewritten to `remove_extra`; backend rejection
of that old spelling remains unchanged.

No full-suite parity or performance improvement is claimed.
