# EF E2E campaign receipts (`lean-ffmpeg` / `LeanAV`)

One block per wave, appended by the wave worker, per
`docs/EF_DELEGATED_E2E_PLAN.md` §4. The coordinator accepts or rejects from
these blocks only.

```text
wave: W0
sha: 3949bf86918c04d89ff551d4253b8801c8812a06
base: 4624a5e46b1d51d13dd4e7264a8bbd2b4f2f9cc1 (campaign/ef-e2e-20261111)
merged: origin/campaign/p1-1-hdr-highbitdepth-20261106 @ 61aa07be8ea5622a77ecde0b8c3858b199a5e0d1 (clean merge, conflicts: none)
docs: README.md updated to P1.1 capability set (10/12-bit 4:2:0/4:2:2/4:4:4,
      yuv420p10le/p010le/yuv422p10le/yuv444p10le/yuv420p12le/yuv422p12le/
      yuv444p12le/gbrp10le/rgba64le, Bayer/Floyd-Steinberg dithering, PQ/HLG
      tonemap, H.264 High 10/4:2:2/4:4:4, HEVC Main 10 + RExt, AV1 Main 10/
      High/Professional + film-grain synthesis, HDR10 mdcv/clli + Dolby Vision
      dvcC/dvvC/RPU passthrough); EF_DELEGATED_E2E_PLAN.md kept intact.
specs:
  - name: av1SupportedSeqSpec_iff
    file: LeanAV/Av1MainProofs.lean
    pos: { profile := 2, hbd := 2, monochrome := false, ssHor := 1, ssVer := 0 }  (AV1 Professional 12-bit 4:2:2 admitted)
    neg: { profile := 0, hbd := 2, monochrome := false, ssHor := 1, ssVer := 1 }  (Main profile with 12-bit rejected)
    audit: non_vacuous_and_tight
  - name: av1FilmGrainBoundsSpec_iff
    file: LeanAV/Av1MainProofs.lean
    pos: (1, 3, 3, 3, 14)   (grain_seed 1, ar_coeff_lag 3, ar_coeff_shift 3, grain_scale_shift 3, num_y_points 14)
    neg: (65536, 0, 0, 0, 0)   (grain_seed out of 16-bit range rejected)
    audit: non_vacuous_and_tight
  - name: hevcPixFmtPairSpec_iff
    file: LeanAV/HevcMainProofs.lean
    pos: (10, 2)   (HEVC Main 4:2:2 10-bit, RExt, admitted)
    neg: (10, 0)   (10-bit monochrome rejected)
    audit: non_vacuous_and_tight
  - name: hevcMain10OrRextSpsSpec_iff
    file: LeanAV/HevcMainProofs.lean
    pos: SPS { profileIdc := 4, chromaFormatIdc := 2, bitDepth := 12, bitDepthChroma := 12, width := 64, height := 48 }   (RExt Main 4:2:2 12-bit admitted)
    neg: SPS { profileIdc := 2, chromaFormatIdc := 3, bitDepth := 10, bitDepthChroma := 10 }   (Main 10 profile claiming 4:4:4 rejected)
    audit: non_vacuous_and_tight
  - name: h264HighTierSpsProfileValidSpec_iff
    file: LeanAV/H264SyntaxProofs.lean
    pos: { profileIdc := 244, chromaFormatIdc := 3, separateColourPlaneFlag := true, bitDepthLumaMinus8 := 4, bitDepthChromaMinus8 := 4, qpprimeYZeroTransformBypass := true }
    neg: { profileIdc := 100, chromaFormatIdc := 1, bitDepthLumaMinus8 := 2 }  (High claiming 12-bit luma without High 10 profile rejected)
    audit: non_vacuous_and_tight
  - name: ditherOutputGateSpec
    file: LeanAV/Scale.lean
    pos: (10, 8, 255)   (10->8-bit dithered sample at 8-bit max)
    neg: (10, 8, 256)   (one-past-max dithered sample rejected)
    audit: non_vacuous_and_tight
  - name: hdrTransferGateSpec
    file: LeanAV/Scale.lean
    pos: (1023, 65536)   (PQ 10-bit code 1023 -> Q16 65536)
    neg: (1024, 65536)   (PQ code > 1023 rejected)
    audit: non_vacuous_and_tight
  - name: tonemapFrameGateSpec_iff
    file: LeanAV/Filter.lean
    pos: (bt2020ncl 2x2 yuv420p src, "hable", filterVideoTonemap src "hable")  (bt709 3-plane conserved output)
    neg: (bt2020ncl 2x2 yuv420p src, "hable", src)  (unconverted src frame rejected: colorMatrix != bt709)
    audit: non_vacuous_and_tight
  - name: colorspaceFrameGateSpec_iff
    file: LeanAV/LavfiGraphProofs.lean
    pos: (bt2020ncl 2x2 yuv420p src, "bt709", filterVideoColorspace src "bt709")
    neg: (bt2020ncl 2x2 yuv420p src, "bt709", src)  (identity mutant rejected)
    audit: non_vacuous_and_tight
  - name: p11UnifiedHdrGateSpec_iff
    file: LeanAV/UnifiedPipeline.lean
    pos: (16, 16, 10, 1)   (even 16x16 10-bit 4:2:0 raw frame admitted)
    neg: (15, 16, 10, 1)   (odd width rejected)
    audit: non_vacuous_and_tight
  - name: p11SampleEntryDepthGateSpec
    file: LeanAV/Format.lean
    pos: { fourcc := "hvc1", depth := 10 }   (10-bit HEVC visual sample entry admitted)
    neg: { fourcc := "mp4a", depth := 10 }   (audio sample entry claiming visual depth rejected)
    audit: non_vacuous_and_tight
  - name: p11CrossContainerGateSpec
    file: LeanAV/Format.lean
    pos: (.mp4, .mkv)   (HDR/DoVi cross-container remux admitted)
    neg: (.mp4, .mp4)   (same-family cross-remux rejected — asserted in test_p1_1_hdr_dovi_containers.py `cross-remux mp4 mp4`)
    audit: non_vacuous_and_tight
  - name: p11_hdr_dovi_container_roundtrip
    file: LeanAV/Format.lean
    pos: colr nclx {9, 16, 9, false} + mdcv {10000000, 50} + clli {1000, 400} MP4 box encode/decode roundtrip (decide-proved)
    neg: `-color_trc not_a_trc` CLI plan mutant (rejected, error_count > 0, test_p1_1_hdr_dovi_containers.py)
    audit: non_vacuous_and_tight (p11 gate specs above; roundtrip theorem is decide-proved)
  - name: p11_rpu_and_obu_roundtrip
    file: LeanAV/Format.lean
    pos: hevcRpuNalHeaderOk 0x7C 0x01 ∧ av1T35DoviOk [0x2A, 9, 0x04, 0xB5, 0x00, 0x3B, 0x00, 0x00, 0x08, 0x00, 0x19] ∧ EMDF pack/unpack roundtrip (decide-proved)
    neg: corrupted RPU mutant `rpuHex.take 103 ++ [0x00, 0x80]` fails `hevcRpuPayloadOk (0x19 :: badRpu)` (CRC32 mismatch; asserted in test_p1_1_hdr_dovi_containers.py Lean driver)
    audit: non_vacuous_and_tight (p11 gate specs above; roundtrip theorem is decide-proved)
  - name: p11_mkv_hdr_and_dovi_roundtrip
    file: LeanAV/Format.lean
    pos: MKV Colour {9, 16, 9, 1000, 400} + dvcC/dvvC block-add roundtrip for doviProfile5/8 (decide-proved)
    neg: mkv PCM audio cross-remux mutant (rejected non-zero, test_p1_1_e2e_pipeline.py)
    audit: non_vacuous_and_tight (p11 gate specs above; roundtrip theorem is decide-proved)
axioms: sorryAx=0 custom=0 decls=24990
audit_spec: vacuous=0 trivial=0 shadowed=0 tight=890
tests:
  - cmd: python3 scripts/build_turbo.py
    result: OK (built .lake/build/bin/lffmpeg, LEAN_PATH=.lake/build/lib/lean:../lean-sys/.lake/build/lib/lean, TURBO_LEAN_EMIT_C=1, turbo-lean @ dc1656dc948f1d7bfc25d165575ae3819a2e8b97)
  - cmd: ./scripts/regen_lnir_c_kernels.sh --check-ir
    result: OK (46 LNIR decls + 14 outer shells byte-identical)
  - cmd: ./.lake/build/bin/lffmpeg self-test
    result: OK (55 waves, c_abi_gates 15, all *_ok true)
  - cmd: ./.lake/build/bin/lffmpeg verify-ffi
    result: OK (abi_version 0x00010005)
  - cmd: ./.lake/build/bin/lffmpeg verify-kernels
    result: OK (12 compiled kernels + u16le acceptance)
  - cmd: lean scripts/check_axioms.lean
    result: OK (Verified 24990 LeanAV declarations, 0 sorryAx, 0 custom axioms)
  - cmd: for f in LeanAV/*.lean; do turbo-lean --json audit-spec "$f"; done
    result: OK (38 modules, 890/890 non_vacuous_and_tight, 0 vacuous, 0 trivial, 0 shadowed)
  - cmd: python3 -m unittest tests/differential/test_p1_1_e2e_pipeline.py
    result: OK (Ran 7 tests, zero skips; e2e HDR10/DoVi/10-12-bit ladder incl. -vf negate on yuv420p10le fail-closed)
  - cmd: python3 -m unittest tests/differential/test_p1_1_pixfmt_hdr.py tests/differential/test_p1_1_hdr_dovi_containers.py
    result: OK (Ran 13 tests, zero skips; oracle: reference ffmpeg n8.1 static build, same as .github/workflows/ci.yml; system 6.1.1 lacks AV1 ITU-T T.35 DoVi probe support)
execve: 1
```

W0 worker notes (not part of the §4 template):

- Verification ran on the merged tree at `3949bf8` (campaign branch head after
  the W0 push); the packet commit adds only this file.
- `strace -f -e trace=execve ./.lake/build/bin/lffmpeg self-test` shows
  exactly one `execve` (the `lffmpeg` invocation itself); zero child spawns.
- P1.1 branch pin `61aa07be` merged exactly as frozen in the plan; the later
  `3632c2f` tip pushed after freeze is out of W0 scope.
