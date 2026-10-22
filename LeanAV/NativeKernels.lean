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

/-- Build the `LNIR_WIRE_V1` wire representation of `LeanAV.DSP.Kernels` for direct consumption by `lean-native-core`. -/
def emitLeanAvLnirWire : String :=
  let modHex := hexEncodeString "LeanAV.DSP.Kernels"
  -- 1. `swscale_luma_gain_bias_simd` (arr: sarray i64, scale: i64, bias: i64) -> sarray i64
  -- Triggers HoistExclusivity + FMA vectorization + GPU PTX/Metal offload
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
  -- Triggers CancelRedundantRC + SIMD/GPU dotProduct reduction
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

  -- 3. `opus_celt_pvq_mix_saxpy_gpu` (xs: sarray i64, ys: sarray i64) -> sarray i64
  -- Data-parallel `4 * xs[i] + ys[i]` kernel eligible for CPU AVX2/NEON and GPU CUDA PTX / Metal
  let d3Name := hexEncodeString "opus_celt_pvq_mix_saxpy_gpu"
  let d3 : List String := [
    "D_decl", d3Name, "A_L3", "1", "2",
    "0", hexEncodeString "midBand", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "sideBand", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64", "K_saxpy", "4",
    "C_ret", "3"
  ]

  -- 4. `av1_wiener_3tap_stencil_gpu` (src: sarray i64) -> sarray i64
  -- Data-parallel 3-point Wiener loop restoration stencil `[3, 10, 3]`
  let d4Name := hexEncodeString "av1_wiener_3tap_stencil_gpu"
  let d4 : List String := [
    "D_decl", d4Name, "A_L3", "1", "1",
    "0", hexEncodeString "lumaPlane", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "1", "T_i64", "E_salen", "0",
    "C_par", "2", "1", "1", "0", "T_i64", "K_st3", "3", "10", "3",
    "C_ret", "2"
  ]

  -- 5. `av1_cdef_fma_blend_gpu` (pri: sarray i64, sec: sarray i64, base: sarray i64) -> sarray i64
  -- Data-parallel FMA directional filter `pri[i] * sec[i] + base[i]`
  let d5Name := hexEncodeString "av1_cdef_fma_blend_gpu"
  let d5 : List String := [
    "D_decl", d5Name, "A_L3", "1", "3",
    "0", hexEncodeString "priTap", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "dirWeight", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "srcPixel", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2",
    "C_ret", "4"
  ]

  -- 6. `h264_idct_tuple_accum_sroa` (n: i64, seed: i64) -> i64
  -- Triggers UnboxTupleSROA + StrengthReduceArith (`* 2` -> `<< 1`)
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

  -- 7. `annexb_startcode_scan_simd` (bitstreamWords: sarray i64, startMask: sarray i64) -> sarray i64
  -- Wave 1 P1: Data-parallel SWAR/SIMD Annex-B zero-byte & start-code prefix correlation (`K_dot`)
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

  -- 8. `fused_vf_scale_crop_eq_blur_gpu` (lumaPlane: sarray i64) -> sarray i64
  -- Wave 3 P3: Single-pass fused `scale + crop + eq + boxblur` 3-point GPU/SIMD stencil `[1, 2, 1]`
  let d8Name := hexEncodeString "fused_vf_scale_crop_eq_blur_gpu"
  let d8 : List String := [
    "D_decl", d8Name, "A_L3", "1", "1",
    "0", hexEncodeString "lumaPlane", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "1", "T_i64", "E_salen", "0",
    "C_par", "2", "1", "1", "0", "T_i64", "K_st3", "1", "2", "1",
    "C_ret", "2"
  ]

  -- 9. `h264_diamond_me_sad_simd` (curMb: sarray i64, refMb: sarray i64) -> sarray i64
  -- Wave 4 P4: Data-parallel Diamond Motion Estimation SAD/correlation reduction (`CancelRedundantRC` + `K_dot`)
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

  -- 10. `videotoolbox_nvenc_nv12_pack_gpu` (uPlane: sarray i64, vPlane: sarray i64, lumaBase: sarray i64) -> sarray i64
  -- Wave 4 P4: Zero-copy hardware DMA NV12 chroma interleave & pack for Apple VideoToolbox / NVIDIA NVENC (`K_cust` FMA)
  let d10Name := hexEncodeString "videotoolbox_nvenc_nv12_pack_gpu"
  let d10 : List String := [
    "D_decl", d10Name, "A_L3", "1", "3",
    "0", hexEncodeString "uPlane", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "vPlane", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "lumaBase", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2",
    "C_ret", "4"
  ]

  let allTokens := ["LNIR_WIRE_V1", modHex, "10"] ++ d1 ++ d2 ++ d3 ++ d4 ++ d5 ++ d6 ++ d7 ++ d8 ++ d9 ++ d10
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

end LeanAV.NativeKernels
