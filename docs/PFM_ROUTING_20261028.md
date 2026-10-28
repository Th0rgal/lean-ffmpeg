# PFM output routing — 28 October 2026

Outputs ending in `.pfm` now select the delegated `image2` route. Previously the
CLI rejected this suffix before FFmpeg could encode the image. The change adds
one suffix to the existing inference table; it does not implement a PFM codec.
Explicit formats retain precedence, `-f pfm` remains invalid, and original argv,
backend exit status and path-security checks remain unchanged.

The frozen FFmpeg source is `bf0e831606938f530326c9679591109407fa8d0d`.
Its `libavformat/img2.c` maps PFM to this extension and `img2enc.c` lists it under
`image2`. The affected recipes are `fate-lavf-gbrpf32be.pfm`,
`fate-lavf-gbrpf32le.pfm`, `fate-lavf-grayf32be.pfm` and
`fate-lavf-grayf32le.pfm`.

Validation used each original encode and decode command with only output paths
relocated into fresh directories. Both arms read the same 50 original PGM
fixtures. All four pairs produced 13 images each: all 52 corresponding outputs
were byte-identical. For each arm, image 02 MD5 and size plus decoded CRC also
matched the frozen upstream reference text. Sixteen subprocesses returned zero;
pinned binaries, runtime files, fixtures and references were unchanged.

Project checks: 108/108 unit tests and 81/81 differential tests, with no skips;
53 self-test waves, FFI and native-kernel checks; 8,897 declarations with no
forbidden axioms; 264/264 tight specifications. Existing specification style
warnings are retained. The 10 image-routing test methods reproduce 13 rejected
subcases on the previous binary and pass on the corrected binary.

The media comparison replays the original recipe checks outside the full FATE
runner. It does not update the global FATE pass count, prove native codec parity,
or establish a performance improvement. Full inventory/provenance closure,
current-candidate timing and final integration remain separate campaign gates.
