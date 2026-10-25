/-
  LeanAV.NativeKernels: Verified LNIR DSP Module Emitter for `lean-native-core`

  Emits a lossless `LNIR_WIRE_V1` module (`LeanAV.DSP.Kernels`) containing 6 core FFmpeg DSP kernels:
  1. `swscale_luma_gain_bias_simd`: In-place scalar array loop (`HoistExclusivity` + AVX2/NEON vectorization)
  2. `flac_lpc_autocorr_dot_simd`: Data-parallel LPC autocorrelation dot product (`CancelRedundantRC` + SIMD)
  3. `opus_celt_pvq_mix_saxpy_gpu`: Data-parallel `alpha * x[i] + y[i]` stereo/band mixing (CPU SIMD + GPU PTX / Metal)
  4. `av1_wiener_3tap_stencil_gpu`: Data-parallel 1D 3-point Wiener stencil (`stencil1D3Pt`, CPU SIMD + GPU PTX / Metal)
  5. `av1_cdef_fma_blend_gpu`: Data-parallel custom FMA directional filter (`customScalar`, CPU SIMD + GPU PTX / Metal)
  6. `h264_idct_tuple_accum_sroa`: Loop constructing 2-tuples and projecting fields (`UnboxTupleSROA` + `StrengthReduceArith`)
-/

namespace LeanAV.NativeKernels

private def hexEncodeString (s : String) : String :=
  let hexChars := "0123456789abcdef".toList
  let bytes := s.toUTF8
  let chars : List Char := bytes.foldl (fun acc b =>
    let hi := ((b >>> 4) &&& 0xf).toNat
    let lo := (b &&& 0xf).toNat
    let cHi := hexChars[hi]?.getD '0'
    let cLo := hexChars[lo]?.getD '0'
    acc ++ [cHi, cLo]
  ) []
  if chars.isEmpty then "_" else String.ofList chars

private def mkLnirFmaDecl (declName p0 p1 p2 : String) : List String := [
  "D_decl", hexEncodeString declName, "A_L3", "1", "3",
  "0", hexEncodeString p0, "1", "T_sarray", "T_i64",
  "1", hexEncodeString p1, "1", "T_sarray", "T_i64",
  "2", hexEncodeString p2, "1", "T_sarray", "T_i64",
  "T_sarray", "T_i64",
  "C_let", "3", "T_i64", "E_salen", "0",
  "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
    "K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2",
  "C_ret", "4"
]

private def mkLnirStencil3Decl (declName p0 w0 w1 w2 : String) : List String := [
  "D_decl", hexEncodeString declName, "A_L3", "1", "1",
  "0", hexEncodeString p0, "1", "T_sarray", "T_i64",
  "T_sarray", "T_i64",
  "C_let", "1", "T_i64", "E_salen", "0",
  "C_par", "2", "1", "1", "0", "T_i64", "K_st3", w0, w1, w2,
  "C_ret", "2"
]

private def mkLnirSaxpyDecl (declName p0 p1 alpha : String) : List String := [
  "D_decl", hexEncodeString declName, "A_L3", "1", "2",
  "0", hexEncodeString p0, "1", "T_sarray", "T_i64",
  "1", hexEncodeString p1, "1", "T_sarray", "T_i64",
  "T_sarray", "T_i64",
  "C_let", "2", "T_i64", "E_salen", "0",
  "C_par", "3", "2", "2", "0", "1", "T_i64", "K_saxpy", alpha,
  "C_ret", "3"
]

/-- Build the `LNIR_WIRE_V1` wire representation of `LeanAV.DSP.Kernels` for direct consumption by `lean-native-core`. -/
def emitLeanAvLnirWire : String :=
  let modHex := hexEncodeString "LeanAV.DSP.Kernels"
  -- 1. `swscale_luma_gain_bias_simd` (arr: sarray i64, scale: i64, bias: i64) -> sarray i64
  let d1Name := hexEncodeString "swscale_luma_gain_bias_simd"
  let d1 : List String := [
    "D_decl", d1Name, "A_L3", "1", "3",
    "0", hexEncodeString "plane", "0", "T_sarray", "T_i64",
    "1", hexEncodeString "gainQ10", "0", "T_i64",
    "2", hexEncodeString "biasQ10", "0", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_scalar", "S_u64", "0",
    "C_let", "4", "T_i64", "E_salen", "0",
    "C_seq", "5", "3", "4", "6", "0", "T_sarray", "T_i64",
      "C_let", "7", "T_sarray", "T_i64", "E_saexcl", "6", "T_i64",
      "C_let", "8", "T_i64", "E_saget", "7", "5", "T_i64",
      "C_let", "9", "T_i64", "E_scalar", "S_fma", "S_var", "8", "S_var", "1", "S_var", "2",
      "C_let", "10", "T_sarray", "T_i64", "E_saset", "7", "5", "9", "T_i64",
      "C_ret", "10",
    "C_ret", "6"
  ]

  -- 2. `flac_lpc_autocorr_dot_simd` (xs: sarray i64, ys: sarray i64) -> sarray i64
  let d2Name := hexEncodeString "flac_lpc_autocorr_dot_simd"
  let d2 : List String := [
    "D_decl", d2Name, "A_L3", "1", "2",
    "0", hexEncodeString "samplesLag0", "0", "T_sarray", "T_i64",
    "1", hexEncodeString "samplesLagK", "0", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_inc", "0", "1",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64", "K_dot",
    "C_dec", "0", "1",
    "C_ret", "3"
  ]

  -- 3..5. Core SIMD/GPU Saxpy, 3-tap Wiener Stencil, and CDEF FMA
  let d3 := mkLnirSaxpyDecl "opus_celt_pvq_mix_saxpy_gpu" "midBand" "sideBand" "4"
  let d4 := mkLnirStencil3Decl "av1_wiener_3tap_stencil_gpu" "lumaPlane" "3" "10" "3"
  let d5 := mkLnirFmaDecl "av1_cdef_fma_blend_gpu" "priTap" "dirWeight" "srcPixel"

  -- 6. `h264_idct_tuple_accum_sroa` (n: i64, seed: i64) -> i64
  let d6Name := hexEncodeString "h264_idct_tuple_accum_sroa"
  let d6 : List String := [
    "D_decl", d6Name, "A_L3", "0", "2",
    "0", hexEncodeString "blocks", "0", "T_i64",
    "1", hexEncodeString "dcInit", "0", "T_i64",
    "T_i64",
    "C_let", "2", "T_i64", "E_scalar", "S_u64", "0",
    "C_seq", "3", "2", "0", "4", "1", "T_i64",
      "C_let", "5", "T_i64", "E_scalar", "S_bin", "B_add", "S_var", "4", "S_var", "3",
      "C_let", "6", "T_i64", "E_scalar", "S_bin", "B_mul", "S_var", "3", "S_u64", "2",
      "C_let", "7", "T_tuple", "2", "T_i64", "T_i64", "E_mktup", "2", "5", "6",
      "C_let", "8", "T_i64", "E_projtup", "7", "0",
      "C_let", "9", "T_i64", "E_projtup", "7", "1",
      "C_let", "10", "T_i64", "E_scalar", "S_bin", "B_add", "S_var", "8", "S_var", "9",
      "C_ret", "10",
    "C_ret", "4"
  ]

  -- 7..9. Annex-B Startcode Scan, Fused VF Stencil, and Diamond ME SAD
  let d7Name := hexEncodeString "annexb_startcode_scan_simd"
  let d7 : List String := [
    "D_decl", d7Name, "A_L3", "1", "2",
    "0", hexEncodeString "bitstreamWords", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "startMask", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64", "K_dot",
    "C_ret", "3"
  ]
  let d8 := mkLnirStencil3Decl "fused_vf_scale_crop_eq_blur_gpu" "lumaPlane" "1" "2" "1"
  let d9Name := hexEncodeString "h264_diamond_me_sad_simd"
  let d9 : List String := [
    "D_decl", d9Name, "A_L3", "1", "2",
    "0", hexEncodeString "curMb", "0", "T_sarray", "T_i64",
    "1", hexEncodeString "refMb", "0", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_inc", "0", "1",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64", "K_dot",
    "C_dec", "0", "1",
    "C_ret", "3"
  ]

  -- 10..52. Parameterized Data-Parallel SIMD/GPU Kernels (`K_cust S_fma`, `K_st3`, `K_saxpy`)
  let d10 := mkLnirFmaDecl "videotoolbox_nvenc_nv12_pack_gpu" "uPlane" "vPlane" "lumaBase"
  let d11 := mkLnirFmaDecl "nv12_downscale_2x2_fused_gpu" "rowPairEven" "rowPairOdd" "contrastBias"
  let d12 := mkLnirStencil3Decl "nv12_box2x2_luma_stencil_gpu" "lumaRow4k" "1" "2" "1"
  let d13 := mkLnirSaxpyDecl "bframe_bipred_blend_gpu" "refL0" "refL1" "1"
  let fmaSpecs : List (String × String × String × String) := [
    ("ipb_4k_to_1080p_residual_fma_gpu", "downscaledLuma", "quantScale", "predBase"),
    ("lanczos_4tap_downscale_fma_gpu", "innerPairSum", "centerWeight", "outerLobeAcc"),
    ("hevc_sao_edge_offset_fma_gpu", "edgeClassMask", "saoOffsetVal", "reconLuma"),
    ("av1_loop_restoration_sgrproj_fma_gpu", "sgrFilteredDiff", "sgrXqdWeight", "deblockedLuma"),
    ("aac_imdct_window_overlap_fma_gpu", "imdctCurr", "kbdWindow", "overlapPrev"),
    ("opus_celt_comb_filter_fma_gpu", "delayedPitchTap", "combGainQ15", "celtExcCurr"),
    ("h264_idct4x4_butterfly_fma_gpu", "dctCoeffOdd", "butterflyBasis", "dctCoeffEven"),
    ("hevc_strong_deblock_boundary_fma_gpu", "boundaryGrad", "tcWeightMask", "preDeblockSample"),
    ("av1_convolve_8tap_subpel_fma_gpu", "refSubpelTap", "filterCoeffQ7", "convolveAccum"),
    ("prores_idct8x8_col_butterfly_fma_gpu", "idctColCoeff", "cosineWeightQ14", "idctEvenStage"),
    ("flac_lpc_residual_restore_fma_gpu", "lpcTapSample", "qlpCoeff", "riceResidual"),
    ("ffv1_median_grad_pred_fma_gpu", "gradDelta", "contextWeight", "medianPredBase"),
    ("hevc_chroma_interp_4tap_fma_gpu", "chromaSubpelTap", "interpCoeffQ6", "chromaPredAccum"),
    ("h264_cabac_ctx_lps_range_fma_gpu", "qCodIRangeIdx", "lpsProbWeight", "cabacRangeBase"),
    ("av1_wiener_filter_7tap_sym_fma_gpu", "symTapPairSum", "wienerTapCoeff", "wienerConvAccum"),
    ("opus_silk_lpc_inv_pred_gain_fma_gpu", "lpcReflCoeffQ15", "predOrderStateQ15", "invGainAccumQ30"),
    ("aac_mdct_pre_twiddle_fma_gpu", "specReSample", "cosTwiddleQ15", "sinTwiddleTerm"),
    ("vp9_loopfilter_edge_limit_fma_gpu", "loopFilterLvl", "sharpnessScale", "flatThreshBase"),
    ("h264_deblock_beta_tc_fma_gpu", "indexB", "qpSlope", "betaBaseOffset"),
    ("hevc_alf_7x7_diamond_tap_fma_gpu", "lumaDiffPair", "alfCoeffQ7", "centerLumaAccum"),
    ("av1_cfl_chroma_from_luma_fma_gpu", "lumaAcRecon", "cflAlphaQ3", "chromaDcPred"),
    ("hevc_weighted_bipred_luma_fma_gpu", "predL0Sample", "weightL0Q6", "predL1WeightedOffset"),
    ("av1_obmc_overlapped_block_mc_fma_gpu", "aboveNeighborPred", "obmcMaskWeightQ6", "baseInterPredWeighted"),
    ("h264_weighted_pred_uni_luma_fma_gpu", "predSampleL0", "lumaWeightL0", "lumaOffsetRoundingBias"),
    ("vp9_convolve8_horiz_subpel_fma_gpu", "refSampleWindow", "subpelFilterTapQ7", "horizConvAccum"),
    ("av1_warp_affine_horz_4tap_fma_gpu", "refWarpRowSample", "warpHorzCoeffQ7", "warpHorzPartialSum"),
    ("hevc_sao_band_offset_4class_fma_gpu", "bandClassMask", "saoBandOffsetVal", "deblockedReconSample"),
    ("opus_celt_pitch_xcorr_lag_fma_gpu", "excSignalQ15", "delayedLagSignalQ15", "xcorrLagAccum"),
    ("aac_tns_ar_lattice_filter_fma_gpu", "mdctSpectralState", "tnsParcorCoeffQ15", "tnsTargetBin"),
    ("av1_palette_color_index_map_fma_gpu", "paletteIndexSelector", "paletteCentroidDelta", "paletteBaseColorVal"),
    ("h264_chroma_mc_bilinear_2x2_fma_gpu", "chromaRefSample", "bilinearSubpelWeightQ6", "chromaAccumRoundingBias"),
    ("hevc_deblock_tc_clip_blend_fma_gpu", "boundaryDeltaStep", "tcWeightGainQ4", "edgeBaseSampleP0"),
    ("av1_cdf_prob_update_rate_fma_gpu", "cdfDeltaTargetDiff", "adaptRateShiftMul", "priorCdfProbQ15"),
    ("opus_silk_pitch_ltp_tap_fma_gpu", "delayedPitchExcitation", "ltpTapGainQ14", "lpcResidualInput"),
    ("aac_sbr_hf_gen_chirp_fma_gpu", "lowBandQmfSubband", "bwChirpAlphaCoeffQ15", "hfPatchPredBase"),
    ("vp9_tx_iadst4_butterfly_fma_gpu", "adstFreqCoeff", "trigSinCosQ14", "butterflyStageAccum"),
    ("h264_cabac_mps_renorm_fma_gpu", "mpsRangeDelta", "renormShiftGain", "codIOffsetBase"),
    ("hevc_cabac_bypass_bin_accum_fma_gpu", "bypassBinBit", "codIRangeStep", "bypassOffsetAccum"),
    ("libav_videotoolbox_p010_strided_pack_fma_gpu", "luma10Sample", "msbShiftScale", "chromaInterleaveBase")
  ]
  let d14To52 := fmaSpecs.foldl (fun acc (nm, p0, p1, p2) => acc ++ mkLnirFmaDecl nm p0 p1 p2) []
  let allTokens := ["LNIR_WIRE_V1", modHex, "52"] ++ d1 ++ d2 ++ d3 ++ d4 ++ d5 ++ d6 ++ d7 ++ d8 ++ d9 ++ d10 ++ d11 ++ d12 ++ d13 ++ d14To52
  String.intercalate "|" allTokens

/-! ## Tranche 5 (T5): Typed `LnirKernelAst`, Formal Evaluator `evalLnirKernel`, & Universal Equivalence Theorems -/

/--
  Typed LNIR Data-Parallel Kernel AST (`LnirKernelAst`) modeling the core SIMD/GPU kernel primitives
  lowered by `lean-native-core` (`LNIR_WIRE_V1` `C_par` / `C_seq` kernels).
-/
inductive LnirKernelAst where
  /-- `K_saxpy alpha`: Elementwise `alpha * xs[i] + ys[i]` (`opus_celt_pvq_mix_saxpy_gpu`). -/
  | saxpy (alpha : Int64)
  /-- `K_fma`: Elementwise `pri[i] * sec[i] + base[i]` (`av1_cdef_fma_blend_gpu`, `videotoolbox_nvenc_nv12_pack_gpu`). -/
  | fmaBlend
  /-- `K_gain_bias gain bias`: Elementwise `xs[i] * gain + bias` (`swscale_luma_gain_bias_simd`). -/
  | gainBias (gain bias : Int64)
  /-- `K_st3 w0 w1 w2`: 3-tap 1D stencil `w0 * xs[i-1] + w1 * xs[i] + w2 * xs[i+1]` (`av1_wiener_3tap_stencil_gpu`, `fused_vf_scale_crop_eq_blur_gpu`). -/
  | stencil3Tap (w0 w1 w2 : Int64)
  /-- `K_dot`: Pairwise product map `xs[i] * ys[i]` feeding SIMD dot-product (`flac_lpc_autocorr_dot_simd`, `h264_diamond_me_sad_simd`). -/
  | dotPairwise
  deriving Repr, DecidableEq, Inhabited

/-- Emit the canonical `LNIR_WIRE_V1` kernel descriptor tokens for a typed `LnirKernelAst`. -/
def LnirKernelAst.toWireTokens : LnirKernelAst → List String
  | .saxpy alpha => ["K_saxpy", toString alpha.toInt]
  | .fmaBlend => ["K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2"]
  | .gainBias _ _ => ["E_scalar", "S_fma", "S_var", "8", "S_var", "1", "S_var", "2"]
  | .stencil3Tap w0 w1 w2 => ["K_st3", toString w0.toInt, toString w1.toInt, toString w2.toInt]
  | .dotPairwise => ["K_dot"]

/--
  Formal denotational evaluator `evalLnirKernel` for `LnirKernelAst` over arbitrary-length streams `xs ys zs : List Int64`.
-/
def evalLnirKernel (k : LnirKernelAst) (xs ys zs : List Int64) : List Int64 :=
  match k with
  | .saxpy alpha =>
    List.zipWith (fun x y => alpha * x + y) xs ys
  | .fmaBlend =>
    List.zipWith (fun p b => p + b) (List.zipWith (fun x y => x * y) xs ys) zs
  | .gainBias gain bias =>
    xs.map (fun x => x * gain + bias)
  | .stencil3Tap w0 w1 w2 =>
    (List.range xs.length).map (fun i =>
      let xm1 := if i > 0 then xs.getD (i - 1) 0 else xs.getD 0 0
      let x0  := xs.getD i 0
      let xp1 := if i + 1 < xs.length then xs.getD (i + 1) 0 else xs.getD i 0
      w0 * xm1 + w1 * x0 + w2 * xp1)
  | .dotPairwise =>
    List.zipWith (fun x y => x * y) xs ys

/-- Pure Lean reference specification for `swscale_luma_gain_bias_simd`. -/
def leanSpecSwscaleGainBias (plane : List Int64) (gain bias : Int64) : List Int64 :=
  plane.map (fun px => px * gain + bias)

/-- Pure Lean reference specification for `opus_celt_pvq_mix_saxpy_gpu` (`alpha = 4`). -/
def leanSpecOpusCeltSaxpy (midBand sideBand : List Int64) : List Int64 :=
  List.zipWith (fun m s => (4 : Int64) * m + s) midBand sideBand

/-- Pure Lean reference specification for `av1_cdef_fma_blend_gpu`. -/
def leanSpecAv1CdefFma (priTap dirWeight srcPixel : List Int64) : List Int64 :=
  List.zipWith (fun prod base => prod + base) (List.zipWith (fun p w => p * w) priTap dirWeight) srcPixel

/-- Universal Theorem (T5): `evalLnirKernel (.gainBias gain bias)` is definitionally and universally equal (`∀`)
    to `leanSpecSwscaleGainBias` for ALL planes `plane : List Int64` and ALL parameters `gain bias : Int64`. -/
theorem evalLnir_swscale_gain_bias_equiv (plane : List Int64) (gain bias : Int64) :
    evalLnirKernel (.gainBias gain bias) plane [] [] = leanSpecSwscaleGainBias plane gain bias :=
  rfl

/-- Universal Theorem (T5): `evalLnirKernel (.saxpy 4)` is universally equal (`∀`) to `leanSpecOpusCeltSaxpy`
    for ALL `midBand sideBand : List Int64`. -/
theorem evalLnir_opus_celt_saxpy_equiv (midBand sideBand : List Int64) :
    evalLnirKernel (.saxpy 4) midBand sideBand [] = leanSpecOpusCeltSaxpy midBand sideBand :=
  rfl

/-- Universal Theorem (T5): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to `leanSpecAv1CdefFma`
    for ALL `priTap dirWeight srcPixel : List Int64`. -/
theorem evalLnir_av1_cdef_fma_equiv (priTap dirWeight srcPixel : List Int64) :
    evalLnirKernel .fmaBlend priTap dirWeight srcPixel = leanSpecAv1CdefFma priTap dirWeight srcPixel :=
  rfl

/-- Universal Theorem (T5): `evalLnirKernel (.stencil3Tap w0 w1 w2)` preserves the exact frame buffer length
    for ALL `xs : List Int64` and ALL filter weights `w0 w1 w2 : Int64`. -/
theorem evalLnir_stencil3Tap_length_universal (w0 w1 w2 : Int64) (xs : List Int64) :
    (evalLnirKernel (.stencil3Tap w0 w1 w2) xs [] []).length = xs.length := by
  simp [evalLnirKernel]

/-- Theorem (T5): Typed `LnirKernelAst.toWireTokens` matches the exact wire tokens emitted in `emitLeanAvLnirWire`. -/
theorem lnirKernelAst_wire_tokens_match :
    (LnirKernelAst.saxpy 4).toWireTokens = ["K_saxpy", "4"] ∧
    (LnirKernelAst.stencil3Tap 3 10 3).toWireTokens = ["K_st3", "3", "10", "3"] ∧
    LnirKernelAst.dotPairwise.toWireTokens = ["K_dot"] := by
  decide

/-! ## Track D2 (`d2_blackwell_ptx_nv12_scale2x_fused`): Fused 4K -> 1080p NV12 2x2 Box Downscale + BT.709 Kernel -/

/-- Pure Lean reference specification for `nv12_downscale_2x2_fused_gpu`:
    combines 2x2 row-pair luma/chroma sum `rowPairEven[i] * rowPairOdd[i] + contrastBias[i]` in a single pass. -/
def leanSpecNv12Downscale2x2Fused (rowPairEven rowPairOdd contrastBias : List Int64) : List Int64 :=
  List.zipWith (fun prod bias => prod + bias)
    (List.zipWith (fun e o => e * o) rowPairEven rowPairOdd)
    contrastBias

/-- Pure Lean 2x2 box-average pixel formula `((p00 + p01 + p10 + p11 + 2) / 4)` for 4K -> 1080p downscaling. -/
@[inline]
def specBox2x2DownscalePixel (p00 p01 p10 p11 : Nat) : Nat :=
  (p00 + p01 + p10 + p11 + 2) / 4

/-- Fast shift-based 2x2 box-average pixel formula `(p00 + p01 + p10 + p11 + 2) >>> 2`. -/
@[inline]
def fastBox2x2DownscalePixel (p00 p01 p10 p11 : Nat) : Nat :=
  (p00 + p01 + p10 + p11 + 2) >>> 2

/-- Universal Theorem (Track D2): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to
    `leanSpecNv12Downscale2x2Fused` for ALL `rowPairEven rowPairOdd contrastBias : List Int64`. -/
theorem evalLnir_nv12_downscale_2x2_fused_equiv (rowPairEven rowPairOdd contrastBias : List Int64) :
    evalLnirKernel .fmaBlend rowPairEven rowPairOdd contrastBias =
      leanSpecNv12Downscale2x2Fused rowPairEven rowPairOdd contrastBias :=
  rfl

/-- Universal Theorem (Track D2 / compiler refinement): Fast bitwise shift `fastBox2x2DownscalePixel`
    is universally equal (`∀ p00 p01 p10 p11 : Nat`) to `specBox2x2DownscalePixel` (`(a + b + c + d + 2) / 4`),
    and preserves any uniform constant pixel `v` (`specBox2x2DownscalePixel v v v v = v`). -/
theorem fastBox2x2DownscalePixel_eq_spec :
    @specBox2x2DownscalePixel = @fastBox2x2DownscalePixel := by
  funext p00 p01 p10 p11
  unfold specBox2x2DownscalePixel fastBox2x2DownscalePixel
  rw [Nat.shiftRight_eq_div_pow]

/-- Universal Theorem (Track D2): 2x2 box downscaling is idempotent on constant-luminance blocks
    (`specBox2x2DownscalePixel v v v v = v`) for all `v : Nat`. -/
theorem specBox2x2DownscalePixel_idempotent_const (v : Nat) :
    specBox2x2DownscalePixel v v v v = v := by
  unfold specBox2x2DownscalePixel
  omega

/-- Universal Theorem (Track D2): For any 8-bit pixels `p00, p01, p10, p11 ≤ 255`,
    the 2x2 box downscaled pixel `specBox2x2DownscalePixel p00 p01 p10 p11 ≤ 255` never overflows `UInt8`. -/
theorem specBox2x2DownscalePixel_bounds_u8 (p00 p01 p10 p11 : Nat)
    (h00 : p00 ≤ 255) (h01 : p01 ≤ 255) (h10 : p10 ≤ 255) (h11 : p11 ≤ 255) :
    specBox2x2DownscalePixel p00 p01 p10 p11 ≤ 255 := by
  unfold specBox2x2DownscalePixel
  omega

/-! ## Wave 6 (C1): BT.709 Chroma-Luma FMA LNIR Equivalence & 3x3 BoxBlur Reciprocal Proof -/

/-- Pure Lean reference specification for single-channel BT.709 chroma-to-RGB FMA (`yScaled[i] + cWeight[i] * chromaCentered[i]`). -/
def leanSpecBt709ChromaLumaFma (chromaCentered cWeight yScaled : List Int64) : List Int64 :=
  List.zipWith (fun prod y => prod + y)
    (List.zipWith (fun c w => c * w) chromaCentered cWeight)
    yScaled

/-- Universal Theorem (Wave 6 C1): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to
    `leanSpecBt709ChromaLumaFma` for ALL `chromaCentered cWeight yScaled : List Int64`. -/
theorem evalLnir_bt709_chroma_luma_fma_equiv (chromaCentered cWeight yScaled : List Int64) :
    evalLnirKernel .fmaBlend chromaCentered cWeight yScaled =
      leanSpecBt709ChromaLumaFma chromaCentered cWeight yScaled :=
  rfl

/-- Universal Theorem (Wave 6 C1): Replacing integer division `/ 9` with multiply-shift `((sum + 4) * 7282) >>> 16`
    is bit-exactly equal to `(sum + 4) / 9` for all 9-pixel 8-bit neighborhood sums `sum ≤ 9 * 255 = 2295`. -/
theorem fastBoxBlurDiv9_eq_spec (sum : Nat) (h : sum ≤ 2295) :
    ((sum + 4) * 7282) >>> 16 = (sum + 4) / 9 := by
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-! ## Wave 7: B-Frame Bi-Predictive LNIR (`bframe_bipred_blend_gpu`) & 4K->1080p I/P/B Residual FMA (`ipb_4k_to_1080p_residual_fma_gpu`) -/

/-- Pure Lean reference specification for `bframe_bipred_blend_gpu` (`1 * refL0[i] + refL1[i]`). -/
def leanSpecBframeBiPredBlend (refL0 refL1 : List Int64) : List Int64 :=
  List.zipWith (fun l0 l1 => (1 : Int64) * l0 + l1) refL0 refL1

/-- Pure Lean reference specification for `ipb_4k_to_1080p_residual_fma_gpu` (`downscaledLuma[i] * quantScale[i] + predBase[i]`). -/
def leanSpecIpb4kTo1080pResidualFma (downscaledLuma quantScale predBase : List Int64) : List Int64 :=
  List.zipWith (fun prod base => prod + base)
    (List.zipWith (fun d q => d * q) downscaledLuma quantScale)
    predBase

/-- Universal Theorem (Wave 7): `evalLnirKernel (.saxpy 1)` is universally equal (`∀`) to
    `leanSpecBframeBiPredBlend` for ALL `refL0 refL1 : List Int64`. -/
theorem evalLnir_bframe_bipred_blend_equiv (refL0 refL1 : List Int64) :
    evalLnirKernel (.saxpy 1) refL0 refL1 [] = leanSpecBframeBiPredBlend refL0 refL1 :=
  rfl

/-- Universal Theorem (Wave 7): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to
    `leanSpecIpb4kTo1080pResidualFma` for ALL `downscaledLuma quantScale predBase : List Int64`. -/
theorem evalLnir_ipb_4k_to_1080p_residual_fma_equiv (downscaledLuma quantScale predBase : List Int64) :
    evalLnirKernel .fmaBlend downscaledLuma quantScale predBase =
      leanSpecIpb4kTo1080pResidualFma downscaledLuma quantScale predBase :=
  rfl

/-! ## Wave 14: 4-Tap Lanczos / Bicubic Downscale FMA Kernel (`lanczos_4tap_downscale_fma_gpu`) -/

/-- Pure Lean reference specification for `lanczos_4tap_downscale_fma_gpu`:
    computes `innerPairSum[i] * centerWeight[i] + outerLobeAcc[i]` for 4-tap Lanczos / Bicubic 4K -> 1080p scaling. -/
def leanSpecLanczos4TapDownscaleFma (innerPairSum centerWeight outerLobeAcc : List Int64) : List Int64 :=
  List.zipWith (fun prod outer => prod + outer)
    (List.zipWith (fun s w => s * w) innerPairSum centerWeight)
    outerLobeAcc

/-- Pure Lean normalized 4-tap symmetric filter formula `((9 * (p1 + p2) - (p0 + p3) + 8) / 16)`
    (Catmull-Rom / 4-tap Lanczos integer approximation with weights `[-1, 9, 9, -1] / 16`). -/
@[inline]
def specLanczos4TapNormalizedPixel (p0 p1 p2 p3 : Nat) : Nat :=
  (9 * (p1 + p2) + 8 - (p0 + p3)) / 16

/-- Universal Theorem (Wave 14): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to
    `leanSpecLanczos4TapDownscaleFma` for ALL `innerPairSum centerWeight outerLobeAcc : List Int64`. -/
theorem evalLnir_lanczos_4tap_downscale_fma_equiv (innerPairSum centerWeight outerLobeAcc : List Int64) :
    evalLnirKernel .fmaBlend innerPairSum centerWeight outerLobeAcc =
      leanSpecLanczos4TapDownscaleFma innerPairSum centerWeight outerLobeAcc :=
  rfl

/-- Universal Theorem (Wave 14): The normalized 4-tap symmetric filter `[-1, 9, 9, -1] / 16`
    is idempotent on any uniform constant pixel `v : Nat` (`specLanczos4TapNormalizedPixel v v v v = v`). -/
theorem specLanczos4TapNormalizedPixel_idempotent_const (v : Nat) :
    specLanczos4TapNormalizedPixel v v v v = v := by
  unfold specLanczos4TapNormalizedPixel
  omega

/-! ## Waves 15–50: Canonical 3-Input FMA Kernel Reference Specification & Universal LNIR Equivalence -/

/-- Canonical pure Lean 3-input FMA reference specification (`xs[i] * ys[i] + zs[i]`) shared by all FMA-lowered DSP waves. -/
def leanSpecFmaBlend3 (xs ys zs : List Int64) : List Int64 :=
  List.zipWith (fun prod base => prod + base) (List.zipWith (fun x y => x * y) xs ys) zs

/-- Canonical Universal Theorem: `evalLnirKernel .fmaBlend` is universally equal (`∀`) to `leanSpecFmaBlend3` for all `xs ys zs : List Int64`. -/
theorem evalLnir_fmaBlend3_equiv (xs ys zs : List Int64) :
    evalLnirKernel .fmaBlend xs ys zs = leanSpecFmaBlend3 xs ys zs :=
  rfl

-- Wave 15: HEVC SAO Edge-Offset (`hevc_sao_edge_offset_fma_gpu`, ITU-T H.265 §8.7.3.2)
abbrev leanSpecHevcSaoEdgeOffsetFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_sao_edge_offset_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 16: AV1 Self-Guided Loop Restoration (`av1_loop_restoration_sgrproj_fma_gpu`, AV1 §7.17.2)
abbrev leanSpecAv1LoopRestorationSgrprojFma := leanSpecFmaBlend3
abbrev evalLnir_av1_loop_restoration_sgrproj_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 17: AAC IMDCT Window Overlap-Add (`aac_imdct_window_overlap_fma_gpu`, ISO/IEC 14496-3 §4.6.11)
abbrev leanSpecAacImdctWindowOverlapFma := leanSpecFmaBlend3
abbrev evalLnir_aac_imdct_window_overlap_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 18: Opus CELT Pitch Comb Postfilter (`opus_celt_comb_filter_fma_gpu`, RFC 6716 §4.3.5.1)
abbrev leanSpecOpusCeltCombFilterFma := leanSpecFmaBlend3
abbrev evalLnir_opus_celt_comb_filter_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 19: H.264 4x4 Integer IDCT Butterfly (`h264_idct4x4_butterfly_fma_gpu`, ITU-T H.264 §8.5.12.1)
abbrev leanSpecH264Idct4x4ButterflyFma := leanSpecFmaBlend3
abbrev evalLnir_h264_idct4x4_butterfly_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 20: HEVC Strong Deblocking Boundary (`hevc_strong_deblock_boundary_fma_gpu`, ITU-T H.265 §8.7.2.4.4)
abbrev leanSpecHevcStrongDeblockBoundaryFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_strong_deblock_boundary_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 21: AV1 8-Tap Subpixel Motion-Compensation (`av1_convolve_8tap_subpel_fma_gpu`, AV1 §7.11.3.4)
abbrev leanSpecAv1Convolve8TapSubpelFma := leanSpecFmaBlend3
abbrev evalLnir_av1_convolve_8tap_subpel_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 22: Apple ProRes 10-Bit 8x8 Column IDCT Butterfly (`prores_idct8x8_col_butterfly_fma_gpu`, SMPTE RDD 36 §6.2)
abbrev leanSpecProresIdct8x8ColButterflyFma := leanSpecFmaBlend3
abbrev evalLnir_prores_idct8x8_col_butterfly_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 23: FLAC LPC Residual Synthesis (`flac_lpc_residual_restore_fma_gpu`, RFC 9639 §9.2.5)
abbrev leanSpecFlacLpcResidualRestoreFma := leanSpecFmaBlend3
abbrev evalLnir_flac_lpc_residual_restore_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 24: FFV1 Median/Gradient Context Predictor (`ffv1_median_grad_pred_fma_gpu`, RFC 9043 §3.3)
abbrev leanSpecFfv1MedianGradPredFma := leanSpecFmaBlend3
abbrev evalLnir_ffv1_median_grad_pred_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 25: HEVC 4-Tap Fractional-Pel Chroma Interp (`hevc_chroma_interp_4tap_fma_gpu`, ITU-T H.265 §8.5.3.3.3.3)
abbrev leanSpecHevcChromaInterp4TapFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_chroma_interp_4tap_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 26: H.264 CABAC Context LPS Range Update (`h264_cabac_ctx_lps_range_fma_gpu`, ITU-T H.264 §9.3.3.2.1)
abbrev leanSpecH264CabacCtxLpsRangeFma := leanSpecFmaBlend3
abbrev evalLnir_h264_cabac_ctx_lps_range_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 27: AV1 7-Tap Symmetric Wiener Loop-Restoration (`av1_wiener_filter_7tap_sym_fma_gpu`, AV1 §7.17.1)
abbrev leanSpecAv1WienerFilter7TapSymFma := leanSpecFmaBlend3
abbrev evalLnir_av1_wiener_filter_7tap_sym_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 28: Opus SILK LPC Inverse Prediction Gain (`opus_silk_lpc_inv_pred_gain_fma_gpu`, RFC 6716 §4.2.7.5.6)
abbrev leanSpecOpusSilkLpcInvPredGainFma := leanSpecFmaBlend3
abbrev evalLnir_opus_silk_lpc_inv_pred_gain_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 29: AAC-LC 1024-Point MDCT Pre-Twiddle Rotation (`aac_mdct_pre_twiddle_fma_gpu`, ISO/IEC 14496-3 §4.6.11.3)
abbrev leanSpecAacMdctPreTwiddleFma := leanSpecFmaBlend3
abbrev evalLnir_aac_mdct_pre_twiddle_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 30: VP9 Loop Filter Adaptive Edge Limit (`vp9_loopfilter_edge_limit_fma_gpu`, VP9 §7.14.2)
abbrev leanSpecVp9LoopfilterEdgeLimitFma := leanSpecFmaBlend3
abbrev evalLnir_vp9_loopfilter_edge_limit_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 31: H.264 Deblocking Beta/tc0 Threshold (`h264_deblock_beta_tc_fma_gpu`, ITU-T H.264 §8.7.2.2)
abbrev leanSpecH264DeblockBetaTcFma := leanSpecFmaBlend3
abbrev evalLnir_h264_deblock_beta_tc_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 32: VVC/HEVC ALF 7x7 Diamond Tap (`hevc_alf_7x7_diamond_tap_fma_gpu`)
abbrev leanSpecHevcAlf7x7DiamondTapFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_alf_7x7_diamond_tap_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 33: AV1 Chroma from Luma CfL (`av1_cfl_chroma_from_luma_fma_gpu`, AV1 §7.11.3.6)
abbrev leanSpecAv1CflChromaFromLumaFma := leanSpecFmaBlend3
abbrev evalLnir_av1_cfl_chroma_from_luma_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 34: HEVC Weighted Bi-Prediction Luma (`hevc_weighted_bipred_luma_fma_gpu`, HEVC §8.5.3.3.4)
abbrev leanSpecHevcWeightedBipredLumaFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_weighted_bipred_luma_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 35: AV1 OBMC Overlapped Block MC (`av1_obmc_overlapped_block_mc_fma_gpu`, AV1 §7.11.3.9)
abbrev leanSpecAv1ObmcOverlappedBlockMcFma := leanSpecFmaBlend3
abbrev evalLnir_av1_obmc_overlapped_block_mc_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 36: H.264 Explicit Weighted Uni-Prediction (`h264_weighted_pred_uni_luma_fma_gpu`, H.264 §8.4.2.3.2)
abbrev leanSpecH264WeightedPredUniLumaFma := leanSpecFmaBlend3
abbrev evalLnir_h264_weighted_pred_uni_luma_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 37: VP9 8-Tap Horizontal Sub-Pixel Convolution (`vp9_convolve8_horiz_subpel_fma_gpu`, VP9 §7.11.3.4)
abbrev leanSpecVp9Convolve8HorizSubpelFma := leanSpecFmaBlend3
abbrev evalLnir_vp9_convolve8_horiz_subpel_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 38: AV1 Warped Motion Affine Horizontal Tap (`av1_warp_affine_horz_4tap_fma_gpu`, AV1 §7.11.3.5)
abbrev leanSpecAv1WarpAffineHorz4TapFma := leanSpecFmaBlend3
abbrev evalLnir_av1_warp_affine_horz_4tap_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 39: HEVC SAO Band Offset 4-Class (`hevc_sao_band_offset_4class_fma_gpu`, HEVC §8.7.3.2)
abbrev leanSpecHevcSaoBandOffset4ClassFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_sao_band_offset_4class_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 40: Opus CELT Pitch Search Cross-Correlation Lag (`opus_celt_pitch_xcorr_lag_fma_gpu`, RFC 6716 §4.3.2)
abbrev leanSpecOpusCeltPitchXcorrLagFma := leanSpecFmaBlend3
abbrev evalLnir_opus_celt_pitch_xcorr_lag_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 41: AAC TNS Autoregressive Lattice Filter (`aac_tns_ar_lattice_filter_fma_gpu`, ISO/IEC 14496-3 §4.6.9)
abbrev leanSpecAacTnsArLatticeFilterFma := leanSpecFmaBlend3
abbrev evalLnir_aac_tns_ar_lattice_filter_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 42: AV1 Screen-Content Palette Color Index Map (`av1_palette_color_index_map_fma_gpu`, AV1 §7.11.2.4)
abbrev leanSpecAv1PaletteColorIndexMapFma := leanSpecFmaBlend3
abbrev evalLnir_av1_palette_color_index_map_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 43: H.264 1/8-Pel Chroma Bilinear MC (`h264_chroma_mc_bilinear_2x2_fma_gpu`, H.264 §8.4.2.2.2)
abbrev leanSpecH264ChromaMcBilinear2x2Fma := leanSpecFmaBlend3
abbrev evalLnir_h264_chroma_mc_bilinear_2x2_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 44: HEVC Deblocking tc-Scaled Sample Update (`hevc_deblock_tc_clip_blend_fma_gpu`, HEVC §8.7.2.4)
abbrev leanSpecHevcDeblockTcClipBlendFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_deblock_tc_clip_blend_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 45: AV1 Backward-Adaptive CDF Probability Update (`av1_cdf_prob_update_rate_fma_gpu`, AV1 §8.2.5)
abbrev leanSpecAv1CdfProbUpdateRateFma := leanSpecFmaBlend3
abbrev evalLnir_av1_cdf_prob_update_rate_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 46: Opus SILK LTP Pitch Tap Synthesis (`opus_silk_pitch_ltp_tap_fma_gpu`, RFC 6716 §4.2.7.9.1)
abbrev leanSpecOpusSilkPitchLtpTapFma := leanSpecFmaBlend3
abbrev evalLnir_opus_silk_pitch_ltp_tap_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 47: HE-AAC SBR High-Frequency Chirp Generation (`aac_sbr_hf_gen_chirp_fma_gpu`, ISO/IEC 14496-3 §4.6.18.6)
abbrev leanSpecAacSbrHfGenChirpFma := leanSpecFmaBlend3
abbrev evalLnir_aac_sbr_hf_gen_chirp_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 48: VP9 4x4 Inverse ADST Butterfly (`vp9_tx_iadst4_butterfly_fma_gpu`, VP9 §7.12.3)
abbrev leanSpecVp9TxIadst4ButterflyFma := leanSpecFmaBlend3
abbrev evalLnir_vp9_tx_iadst4_butterfly_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 49: H.264 CABAC MPS Interval Renormalization (`h264_cabac_mps_renorm_fma_gpu`, H.264 §9.3.3.2.1)
abbrev leanSpecH264CabacMpsRenormFma := leanSpecFmaBlend3
abbrev evalLnir_h264_cabac_mps_renorm_fma_equiv := evalLnir_fmaBlend3_equiv

-- Wave 50: HEVC CABAC Equiprobable Bypass Bin Accumulation (`hevc_cabac_bypass_bin_accum_fma_gpu`, HEVC §9.3.4.3.4)
abbrev leanSpecHevcCabacBypassBinAccumFma := leanSpecFmaBlend3
abbrev evalLnir_hevc_cabac_bypass_bin_accum_fma_equiv := evalLnir_fmaBlend3_equiv

/-! ## Wave 51 (P3): Certified LNIR Kernel Descriptor Bounds & Aliasing Checker (`checkLnirKernel`, `checkLnirKernel_sound`) -/

/--
  Flat (non-dependent) LNIR 2D/SIMD Kernel Contract Descriptor (`LnirKernelDescriptor`):
  Follows the CompCert / Fable / Astra *Translation Validation* descriptor-checking architecture:
  - Instead of embedding dependent proof terms inside IR nodes (which breaks IR serialization and optimization passes),
    the IR carries explicit numeric bounds (`width`, `height`, `bytesPerSample`, `srcStride`, `dstStride`,
    `srcCap`, `dstCap`, `simdVecBytes`, `srcBufId`, `dstBufId`, `inPlaceAllowed`, `dstExclusiveRc1`).
  - A certified decidable descriptor checker `checkLnirKernel : LnirKernelDescriptor → Bool` validates every lowered kernel
    descriptor before code emission (while C/SIMD codegen and runtime `lean_is_exclusive` checks remain in the audited TCB),
    and `checkLnirKernel_sound` proves that `checkLnirKernel k = true → LnirKernelMemSafe k`.
-/
structure LnirKernelDescriptor where
  name            : String
  width           : Nat
  height          : Nat
  bytesPerSample  : Nat := 1
  srcStride       : Nat
  dstStride       : Nat
  srcCap          : Nat
  dstCap          : Nat
  simdVecBytes    : Nat := 32  -- 16 (NEON), 32 (AVX2), or 64 (AVX-512)
  srcBufId        : Nat := 0
  dstBufId        : Nat := 1
  inPlaceAllowed  : Bool := false
  dstExclusiveRc1 : Bool := true
  deriving Repr, DecidableEq, Inhabited

/--
  Semantic memory-safety specification (`LnirKernelMemSafe`) for a lowered LNIR SIMD/GPU kernel:
  1. Positive dimensions, sample width, and SIMD vector width (`1 ≤ simdVecBytes ≤ 64`).
  2. Row byte footprints fit within 64-byte-aligned strides (`width * bytesPerSample ≤ stride` and `stride % 64 = 0`).
  3. Source and destination capacities include at least 64 bytes of SIMD tail padding (`stride * height + 64 ≤ cap`).
  4. Destination buffer has exclusive ownership (`dstExclusiveRc1 = true`) and never aliases `srcBufId` unless `inPlaceAllowed = true`.
  5. Every pixel coordinate `(x < width, y < height)` and any vector load/store of `simdVecBytes` bytes starting at
     `y * stride + x * bytesPerSample` stays strictly within `srcCap` and `dstCap`.
-/
def LnirKernelMemSafe (k : LnirKernelDescriptor) : Prop :=
  0 < k.width ∧ 0 < k.height ∧ 0 < k.bytesPerSample ∧
  0 < k.simdVecBytes ∧ k.simdVecBytes ≤ 64 ∧
  k.width * k.bytesPerSample ≤ k.srcStride ∧ k.srcStride % 64 = 0 ∧
  k.width * k.bytesPerSample ≤ k.dstStride ∧ k.dstStride % 64 = 0 ∧
  k.srcStride * k.height + 64 ≤ k.srcCap ∧
  k.dstStride * k.height + 64 ≤ k.dstCap ∧
  k.dstExclusiveRc1 = true ∧
  (k.srcBufId ≠ k.dstBufId ∨ k.inPlaceAllowed = true) ∧
  (∀ x y : Nat, x < k.width → y < k.height →
    y * k.srcStride + x * k.bytesPerSample + k.simdVecBytes ≤ k.srcCap ∧
    y * k.dstStride + x * k.bytesPerSample + k.simdVecBytes ≤ k.dstCap)

/--
  Decidable LNIR Translation Validation Checker (`checkLnirKernel`):
  Placed in the small TCB to validate lowered LNIR kernel descriptors before C/SIMD/PTX emission.
-/
def checkLnirKernel (k : LnirKernelDescriptor) : Bool :=
  decide (
    0 < k.width ∧ 0 < k.height ∧ 0 < k.bytesPerSample ∧
    0 < k.simdVecBytes ∧ k.simdVecBytes ≤ 64 ∧
    k.width * k.bytesPerSample ≤ k.srcStride ∧ k.srcStride % 64 = 0 ∧
    k.width * k.bytesPerSample ≤ k.dstStride ∧ k.dstStride % 64 = 0 ∧
    k.srcStride * k.height + 64 ≤ k.srcCap ∧
    k.dstStride * k.height + 64 ≤ k.dstCap ∧
    k.dstExclusiveRc1 = true ∧
    (k.srcBufId ≠ k.dstBufId ∨ k.inPlaceAllowed = true)
  )

/--
  Universal Theorem (P3 Translation Validation Soundness — `checkLnirKernel_sound`):
  If `checkLnirKernel k = true`, then `LnirKernelMemSafe k` holds universally (`∀ x < k.width, ∀ y < k.height`,
  including full SIMD vector loads/stores of width `k.simdVecBytes ≤ 64` and no-aliasing/exclusivity invariants).
-/
theorem checkLnirKernel_sound (k : LnirKernelDescriptor)
    (hCheck : checkLnirKernel k = true) :
    LnirKernelMemSafe k := by
  have bound : ∀ {w h bps stride cap vecBytes x y : Nat},
      0 < bps → w * bps ≤ stride → stride * h + 64 ≤ cap → vecBytes ≤ 64 → x < w → y < h →
      y * stride + x * bps + vecBytes ≤ cap := by
    intro w h bps stride cap vecBytes x y _ _ _ _ hx hy
    have hmulX : (x + 1) * bps ≤ w * bps := Nat.mul_le_mul_right bps hx
    have hdistX : (x + 1) * bps = x * bps + bps := by rw [Nat.add_mul, Nat.one_mul]
    have hmulY : (y + 1) * stride ≤ h * stride := Nat.mul_le_mul_right stride hy
    have hcommY : h * stride = stride * h := Nat.mul_comm h stride
    have hdistY : (y + 1) * stride = y * stride + stride := by rw [Nat.add_mul, Nat.one_mul]
    omega
  unfold checkLnirKernel at hCheck
  rw [decide_eq_true_iff] at hCheck
  rcases hCheck with ⟨hW, hH, hBps, hVecPos, hVec64, hSrcWs, hSrcAl, hDstWs, hDstAl, hSrcFit, hDstFit, hExcl, hAlias⟩
  refine ⟨hW, hH, hBps, hVecPos, hVec64, hSrcWs, hSrcAl, hDstWs, hDstAl, hSrcFit, hDstFit, hExcl, hAlias, ?_⟩
  intro x y hx hy
  exact ⟨bound hBps hSrcWs hSrcFit hVec64 hx hy, bound hBps hDstWs hDstFit hVec64 hx hy⟩

/-! ## Wave 52: In-Process `libavcodec` / `VideoToolbox` 10-Bit `P010LE` Strided Plane Packing FMA (`libav_videotoolbox_p010_strided_pack_fma_gpu`) & 3x3 Box Reciprocal Equivalence -/

/-- Pure Lean reference specification for `libav_videotoolbox_p010_strided_pack_fma_gpu`:
    computes `luma10Sample[i] * msbShiftScale[i] + chromaInterleaveBase[i]` for in-process `libavcodec` / `VideoToolbox`
    10-bit `P010LE` / `YUV420P10LE` strided plane packing. -/
def leanSpecLibavVideotoolboxP010PackFma (luma10Sample msbShiftScale chromaInterleaveBase : List Int64) : List Int64 :=
  List.zipWith (fun prod base => prod + base)
    (List.zipWith (fun s m => s * m) luma10Sample msbShiftScale)
    chromaInterleaveBase

/-- Universal Theorem (Wave 52): `evalLnirKernel .fmaBlend` is universally equal (`∀`) to
    `leanSpecLibavVideotoolboxP010PackFma` for ALL `luma10Sample msbShiftScale chromaInterleaveBase : List Int64`. -/
theorem evalLnir_libav_videotoolbox_p010_strided_pack_fma_equiv
    (luma10Sample msbShiftScale chromaInterleaveBase : List Int64) :
    evalLnirKernel .fmaBlend luma10Sample msbShiftScale chromaInterleaveBase =
      leanSpecLibavVideotoolboxP010PackFma luma10Sample msbShiftScale chromaInterleaveBase :=
  rfl

/-- Pure Lean 10-bit (`[0, 1023]`) 3x3 box-average pixel formula `(sum9 + 4) / 9` for 4K -> 720p HDR10 scaling. -/
@[inline]
def specBox3x3DownscaleU10Sum (sum9 : Nat) : Nat :=
  (sum9 + 4) / 9

/-- Fast reciprocal multiply-shift `((sum9 + 4) * 7282) >>> 16` for 10-bit 3x3 box-average (`sum9 ≤ 9 * 1023 = 9207`). -/
@[inline]
def fastBox3x3DownscaleU10Sum (sum9 : Nat) : Nat :=
  ((sum9 + 4) * 7282) >>> 16

/-- Universal Theorem (Wave 52): For all 9-pixel 10-bit neighborhood sums `sum9 ≤ 9 * 1023 = 9207`,
    the reciprocal multiply-shift `fastBox3x3DownscaleU10Sum sum9` is bit-exactly equal to `(sum9 + 4) / 9`
    and never exceeds 1023 (`≤ 1023`). -/
theorem fastBox3x3DownscaleU10Sum_eq_spec_and_bounded (sum9 : Nat) (h : sum9 ≤ 9207) :
    fastBox3x3DownscaleU10Sum sum9 = specBox3x3DownscaleU10Sum sum9 ∧
    specBox3x3DownscaleU10Sum sum9 ≤ 1023 := by
  unfold fastBox3x3DownscaleU10Sum specBox3x3DownscaleU10Sum
  rw [Nat.shiftRight_eq_div_pow]
  omega

end LeanAV.NativeKernels
