# EF Delegated End-to-End Plan (`lean-ffmpeg` / `LeanAV`)

Date: 2026-11-11. Base `main` @ `3f9055cfab9ef1ed2730cd34026c949a91e8af8a`.
P1.1 branch `origin/campaign/p1-1-hdr-highbitdepth-20261106` @ `61aa07be8ea5622a77ecde0b8c3858b199a5e0d1`
(contract `docs/contracts/p1-1-hdr-highbitdepth.json`). Pins: Lean `v4.35.0`,
`lean-sys@077775ba387f1eeb2976cb8763b4633b8d5ce313`,
`turbo-lean@dc1656dc948f1d7bfc25d165575ae3819a2e8b97`.

This plan is the frozen execution contract for one coordinator goal. Workers
implement. The coordinator reviews only specs, receipts, and differential
evidence. Proof bodies are never re-read by the coordinator; `turbo-lean` is
the proof oracle.

## 0. Cost model (binding)

1. **Writers** are Ethereum Foundation models only, in this order:
   `ethereumfoundation/glm-5.3` (primary),
   `ethereumfoundation/deepseek-v4.1-flash` (second writer family when a
   wave needs two writers), `ethereumfoundation/qwen3.8-27b` (fallback).
   Backend `opencode`, `model_effort=high`. Do not use Anthropic, OpenAI,
   Gemini, Grok, Kimi, MiniMax, Mistral, or Spark models for writing **or**
   review.
2. **No second reviewer.** There is no `consult_model` quorum, no
   `writer=false` reviewer mission, and no extra model family "just to check".
   The coordinator is the only reviewer.
3. **Coordinator review is mechanical.** Accept or reject from the packet in
   §4. Do not open `*Proofs.lean` except to confirm a named spec exists and
   matches the one-line contract. Do not re-derive proofs. Do not rewrite
   worker code. A rejected wave is one retask with the failing command and
   the spec id; a second failure on the same shared premise stops that
   capability as `BLOCKED` (explicit fail-closed) instead of a third attempt.
4. **One writer per wave, sequential waves.** No parallel writers on the same
   branch. One managed VM at a time (`auto-managed:boost:boost-32vcpu-96gb`
   or `auto-managed:large` if Boost is saturated). Destroy it when the wave
   receipt is pushed. Reuse snapshot `turbo-lean-d-warm`
   (`orb-snap-assistant-turbo-lean-d-warm-mwtb`) when the tool accepts a
   project snapshot; otherwise `managed_from_snapshot=light`.
5. **Push every accepted commit** to `origin` on
   `campaign/ef-e2e-20261111` before the next wave. Signed commits (`-S`),
   never amend, never force-push, never `[skip ci]`. Never invoke `lake`.

## 1. Done line

The campaign is done when all of the following are true on one pushed HEAD:

1. P1.1 (HDR / high bit depth / 4:2:2 / 4:4:4 / film grain / DoVi passthrough)
   is merged from `61aa07be` with docs and CI counters updated, and
   `tests/differential/test_p1_1_e2e_pipeline.py` is zero-skip green.
2. Every capability in §3 is either `independent_verified` (spec + proof
   oracle + differential) or an explicit `unsupported` fail-closed route
   (non-zero exit, zero output bytes). No silent delegation, no
   `ffmpeg`/`ffprobe` subprocess (`execve == 1` under `strace -f -e trace=execve`).
3. `scripts/check_axioms.lean` reports `0 sorryAx` and `0` custom axioms.
4. `turbo-lean --json audit-spec` on every `LeanAV/*.lean` reports `0`
   vacuous, `0` trivial, `0` shadowed, and the new spec count is written
   into `docs/ef-e2e/RECEIPTS.md`.
5. `./scripts/bench_e2e.py` has run on the worker VM and written
   `docs/ef-e2e/bench-<sha>.json`: encode+decode wall time and peak RSS for
   the §5 ladder versus the pinned system `ffmpeg`, three trials, median.
   No speedup claim without that file. A slower-but-correct native route
   still counts as done if the JSON exists and the spec packet passes.
6. `README.md`, `AGENTS.md`, `docs/VERIFICATION_APPENDIX.md`, and
   `docs/CAMPAIGN_CLOSURE_DOSSIER.md` match the new counters in the same
   commit as the code.

Out of scope, fail-closed, not a campaign failure: network protocols,
hardware decode/encode, GPU/CUDA, and any codec marked `unsupported` in §3
after a `BLOCKED` stop. The 14 LNIR outer shells stay in the TCB until
`lean-native-core` grows narrow `i8`/`i16` loads, strided 2D `C_par`, and a
reduction combinator (`docs/M1_LNIR_DSP_LIFT_BLOCKER_20261029.md`). Do not
fork `turbo-lean` to remove them.

## 2. Global invariants (every wave)

- Build: `LEAN_PATH=.lake/build/lib/lean:../lean-sys/.lake/build/lib/lean`
  `python3 scripts/build_turbo.py` (or `--direct-lean`). `TURBO_LEAN_EMIT_C=1`
  when C is emitted.
- Specs stay `AVGateSpec` (or the existing Layer-I shape in `LeanAV/Spec.lean`):
  `sound`, `complete`, `posWitness`, `negWitness`, `nonVacuous`, `tight`.
  One new behavior = one named spec whose `negWitness` is a one-byte or
  one-field mutant a reviewer can see without reading the proof.
- New codec/container code lands in existing `LeanAV/*.lean` modules. Do not
  break public declarations imported across modules (the P1.1 contract lists
  them). Preserve canonical raw layouts from
  `docs/contracts/p1-1-hdr-highbitdepth.json`.
- Differential oracles compare against the system `ffmpeg`/`ffprobe` already
  on the worker. Tests fail, not skip, when the oracle is missing a needed
  encoder; record `SKIP_REASON` only when the binary lacks the encoder, and
  treat that capability as `unsupported` in the packet.
- Each wave commit message starts with `feat(ef-e2e):` or `fix(ef-e2e):` and
  lists spec ids.

## 3. Waves (sequential)

Branch: `campaign/ef-e2e-20261111` from `main`. One worker prompt per wave,
pointing at this file and the wave id. The worker pushes the branch and
stops. The coordinator runs §4 before the next wave.

### W0 — Land P1.1

Merge `origin/campaign/p1-1-hdr-highbitdepth-20261106` (`61aa07be`) into the
campaign branch. Fix conflicts only. Update `README.md` so it no longer
describes an 8-bit 4:2:0 ceiling. Run the full §4 packet plus
`tests/differential/test_p1_1_e2e_pipeline.py`. No new features.

### W1 — Opus (P1.2)

Replace the CELT FB silence stub (`0xFF 0xFE`) with a real RFC 6716 decode
and encode for SILK/CELT/hybrid at 8–48 kHz, mono/stereo, in `LeanAV/Audio.lean`,
Ogg and MP4/MOV. Specs: packet header parse roundtrip; silence frame still
decodes to zeros; a one-bit header mutant is rejected; TOC mode/bandwidth
config is complete for the supported modes. Unsupported modes fail closed.
Differential: `ffmpeg -c:a libopus` vs `lffmpeg` on sine, impulse, and
silence, sample-exact for the lossless/SILK-narrow cases the spec names,
bounded PSNR where the spec says lossy.

### W2 — Decode/encode parity ladder

For each row, extend the existing native decoder/encoder. Do not add a
second implementation beside a working one.

| Id | Route | Oracle |
| --- | --- | --- |
| W2a | H.264 High 8/10/4:2:2/4:4:4 decode+encode already on P1.1: lock e2e via UnifiedPipeline, not raw helpers | `libx264` |
| W2b | HEVC Main/Main10/RExt e2e (`-c:v hevc` + `-pix_fmt`) | `libx265` |
| W2c | AV1 Main/Main10/High/Professional + film grain e2e | `libaom-av1` |
| W2d | VP9 profile 0 8-bit 4:2:0 and profile 2 10-bit 4:2:0 in WebM/MKV and IVF | `libvpx-vp9` |
| W2e | VP8 in WebM | `libvpx` |
| W2f | MJPEG decode+encode in AVI/MOV | `mjpeg` |
| W2g | MPEG-4 ASP (no GMC) in AVI/MP4 | `mpeg4` |

Each row: one `AVGateSpec` for admission (reject the next profile/bit depth),
one roundtrip spec (decode(encode(x)) = x on the lossless or qp0 subset),
and a differential test file `tests/differential/test_ef_<id>.py` with no
skips when the oracle encoder exists. Anything not in this table stays
fail-closed.

### W3 — Containers and CLI surface

Wire the W2 routes through `LeanAV/UnifiedPipeline.lean` and `LeanAV/Main.lean`
for MP4, MOV, MKV/WebM, MPEG-TS, AVI, Ogg, IVF, WAV, FLAC. `-c copy` must
preserve the packet bytes the demuxer already accepts. CLI flags already
parsed in `PlanIR.lean` must either work or fail closed with the same
non-zero class as today. Spec: a declared `-c copy` of an accepted codec
is byte-identical on the elementary stream; an unknown `-c` writes no file.

### W4 — Audio remainder

Native decode+encode, or explicit fail-closed, for:

- MP3 (MPEG-1/2 Layer III) in MP3/MP4/MKV
- AAC-LC already on `main`: extend to HE-AAC/PS only if W4's first packet
  is green; otherwise fail closed (do not half-implement SBR)
- PCM `s16le`/`s32le`/`f32le` in WAV/MOV
- Vorbis in Ogg (decode; encode if the spec roundtrip is cheap, else
  fail-closed encode)

Specs: header admission + one negWitness mutant + sample roundtrip on PCM;
lossy codecs follow the W1 PSNR pattern.

### W5 — End-to-end performance

No new codecs. Add `scripts/bench_e2e.py` (Python, no new deps) that:

1. Builds via `scripts/build_turbo.py` if `lffmpeg` is missing.
2. Runs the ladder below, 3 trials, median wall time and peak RSS
   (`/usr/bin/time -v` or `/proc/self/status` sampler).
3. Writes `docs/ef-e2e/bench-<sha>.json` with fields
   `{sha, route, ffmpeg_s, lffmpeg_s, ratio, rss_ffmpeg_kib, rss_lffmpeg_kib}`.

Ladder (64×64 or 160×120, ≤ 30 frames, so a wave finishes on one VM):

- `scale=w*2:h*2` flags=`bilinear` on `yuv420p` and `yuv420p10le`
- H.264 High qp 23 encode of `testsrc`
- HEVC Main qp 23 encode of `testsrc`
- Opus 96k encode of `sine` 5 s
- `-c copy` remux MP4 → MKV of the H.264 fixture

Hot pixel loops that `bench_e2e.py` shows at `ratio > 3` versus `ffmpeg`
may be moved into an existing `LNIR_WIRE_V1` kernel **only** by reusing
`mkLnirPixelCoreDecl` / the current emit path. Do not hand-write LLVM
outer shells. If the ratio stays above 3 after one kernel attempt, record
it in the JSON and stop. Correctness gates of §4 stay mandatory; a
regression in `audit-spec` or axioms rejects the wave even if the bench
improved.

## 4. Review packet (the only thing the coordinator reads)

The worker appends one block to `docs/ef-e2e/RECEIPTS.md` and pushes:

```text
wave: W?
sha: <full>
specs:
  - name: <theorem>
    file: LeanAV/<File>.lean
    pos: <literal witness>
    neg: <literal mutant>
    audit: non_vacuous_and_tight
axioms: sorryAx=0 custom=0 decls=<n>
audit_spec: vacuous=0 trivial=0 shadowed=0 tight=<n>
tests:
  - cmd: python3 -m unittest tests/differential/test_ef_<id>.py
    result: OK
execve: 1
bench: docs/ef-e2e/bench-<sha>.json   # W5 only
```

Coordinator checks, in order, and stops at the first failure:

1. `git fetch` and `git rev-parse` equals the packet `sha`.
2. `git diff <prev>..<sha> -- '**/*Proofs.lean'` is not reviewed line by
   line. Instead confirm each packet spec name exists
   (`git grep -n theorem.<name> <sha> -- LeanAV`).
3. Re-run on a clean managed VM, or accept the worker log only if the
   coordinator personally re-runs, the four commands:
   `python3 scripts/build_turbo.py`,
   `lean scripts/check_axioms.lean`,
   `for f in LeanAV/*.lean; do turbo-lean --json audit-spec "$f" || exit 1; done`,
   and the packet's unittest lines.
4. `neg` in the packet is a real input the new test asserts is rejected
   (grep the test name in the diff). If the mutant is not in a test, reject.
5. Diff does not add `sorry`, `sorryAx`, `axiom`, `unsafe`, `IO.Process`, or
   `execve`/`fork`/`execvp` strings. `git grep` is the check.
6. For W5, open only the JSON and confirm `sha` matches and every ladder
   route has three numeric fields.

Accept = one line in `docs/ef-e2e/RECEIPTS.md`: `ACCEPT <wave> <sha>`.
Reject = do not ACCEPT; retask once with the failing check number.

## 5. Coordinator operating rules

- Mission prompts name this file, the wave id, and the base sha. They do
  not paste code.
- `estimated_disk_gib` ≥ 40. `managed_ttl_minutes` 180, extended only while
  a build is running.
- Poll with `get_mission_health`. Do not pull full event traces.
- After ACCEPT, `destroy_managed_machine` the wave VM.
- Stop the campaign and report to the user on: axiom escape, a second
  failed retask, or a bench JSON that cannot be reproduced. Do not open a
  new model family to "unblock" a wave.
