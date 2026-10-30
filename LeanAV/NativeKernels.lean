/-
  LeanAV.NativeKernels: Verified LNIR DSP Module Emitter & C-ABI Bridge for `lean-native-core`

  Emits a lossless `LNIR_WIRE_V1` module (`LeanAV.DSP.Kernels`) containing 46 genuinely distinct
  FFmpeg DSP and scalar pixel-core kernels compiled by `lean-native-core` into `libleanav_dsp.a`:
  1.  `swscale_luma_gain_bias_simd`: In-place scalar array loop (`HoistExclusivity` + `S_fma`)
  2.  `flac_lpc_autocorr_dot_simd`: Data-parallel LPC autocorrelation product (`CancelRedundantRC` + `K_dot`)
  3.  `opus_celt_pvq_mix_saxpy_gpu`: Data-parallel `4 * mid[i] + side[i]` stereo mixing (`K_saxpy 4`)
  4.  `av1_wiener_3tap_sym_gpu`: Data-parallel 3-tap symmetric Wiener filter `3 * l[i] + 10 * c[i] + 3 * r[i]`
  5.  `av1_cdef_fma_blend_gpu`: Data-parallel 3-input directional filter `pri[i] * w[i] + src[i]` (`S_fma`)
  6.  `h264_idct_tuple_accum_sroa`: Scalar loop constructing 2-tuples and projecting fields (`UnboxTupleSROA`)
  7.  `bframe_bipred_blend_gpu`: Data-parallel `1 * refL0[i] + refL1[i]` bi-predictive blend (`K_saxpy 1`)
  8.  `hevc_sao_band_offset_add_gpu`: Data-parallel `recon[i] + offset[i]` SAO band offset (`K_za`)
  9.  `aac_imdct_window_mul_gpu`: Data-parallel `mdct[i] * window[i]` KBD windowing (`K_zm`)
  10. `prores_qscale_map_simd`: Data-parallel `coeff[i] * 16 + 8` affine dequantization (`K_msa 16 8`)
  11. `boxblur_div9_recip_shift_simd`: Data-parallel reciprocal multiply-shift `((sum9[i] + 4) * 7282) >>> 16`
  12. `pq10_studio_clamp_select_simd`: Data-parallel branchless `S_sel` clamp to 10-bit studio range `[64, 940]`
  13. `swscale_down2x2_box_simd`: Data-parallel 4-input 2x2 rounded box downscale `(p00 + p01 + p10 + p11 + 2) >>> 2`
  14. `swscale_down3x3_box_simd`: Data-parallel 3x3 reciprocal multiply-shift downscale `((row0 + row1 + row2 + 4) * 7282) >>> 16`
  15. `swscale_down3to2_bilinear_simd`: Data-parallel 3:2 bilinear downscale `(p00 + p01 + p10 + p11 + 2) >>> 2`
  16. `av1_cdef_dir_filter_simd`: Data-parallel AV1 CDEF directional tap blend `(center * 8 + tapPos * 4 + tapNeg * 4 + 8) >>> 4`
  17-29. Data-parallel SIMD per-pixel arithmetic cores (`extract_u16le_msb8_simd` .. `bt2020_to_bt709_uv_simd`)
  30-46. Scalar `LNIR_WIRE_V1` pixel cores (`lnir_px_*`) called directly by the 14 outer 2D/strided LLVM shells
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

private def mkLnirSaxpyDecl (declName p0 p1 alpha : String) : List String := [
  "D_decl", hexEncodeString declName, "A_L3", "1", "2",
  "0", hexEncodeString p0, "1", "T_sarray", "T_i64",
  "1", hexEncodeString p1, "1", "T_sarray", "T_i64",
  "T_sarray", "T_i64",
  "C_let", "2", "T_i64", "E_salen", "0",
  "C_par", "3", "2", "2", "0", "1", "T_i64", "K_saxpy", alpha,
  "C_ret", "3"
]

/--
  Typed LNIR Data-Parallel Kernel AST (`LnirKernelAst`) modeling all distinct SIMD/GPU kernel primitives
  in `LeanAV.DSP.Kernels` lowered by `lean-native-core`.
-/
inductive LnirKernelAst where
  /-- `swscale_luma_gain_bias_simd`: Elementwise `xs[i] * gain + bias`. -/
  | gainBias (gain bias : Int64)
  /-- `flac_lpc_autocorr_dot_simd` (`K_dot`): Pairwise product map `xs[i] * ys[i]`. -/
  | dotPairwise
  /-- `opus_celt_pvq_mix_saxpy_gpu` / `bframe_bipred_blend_gpu` (`K_saxpy alpha`): `alpha * xs[i] + ys[i]`. -/
  | saxpy (alpha : Int64)
  /-- `av1_wiener_3tap_sym_gpu`: 3-tap symmetric Wiener filter `3 * xs[i] + 10 * ys[i] + 3 * zs[i]`. -/
  | wiener3TapSym
  /-- `av1_cdef_fma_blend_gpu`: 3-input FMA `xs[i] * ys[i] + zs[i]`. -/
  | fmaBlend
  /-- `hevc_sao_band_offset_add_gpu` (`K_za`): Elementwise `xs[i] + ys[i]`. -/
  | zipAdd
  /-- `aac_imdct_window_mul_gpu` (`K_zm`): Elementwise `xs[i] * ys[i]`. -/
  | zipMul
  /-- `prores_qscale_map_simd` (`K_msa scale bias`): Elementwise `xs[i] * scale + bias`. -/
  | mapScaleAdd (scale bias : Int64)
  /-- `boxblur_div9_recip_shift_simd`: Elementwise unsigned reciprocal shift `((xs[i] + 4) * 7282) >>> 16`. -/
  | boxBlurDiv9Recip
  /-- `pq10_studio_clamp_select_simd`: Branchless `S_sel` clamp to 10-bit studio range `[64, 940]`. -/
  | pq10StudioClamp
  /-- `swscale_down2x2_box_simd`: Pairwise 2x2 box downscale `(xs[i] + ys[i] + 2) >>> 2`. -/
  | down2x2Box
  /-- `swscale_down3x3_box_simd`: 3-row 3x3 box downscale `((xs[i] + ys[i] + zs[i] + 4) * 7282) >>> 16`. -/
  | down3x3Box
  /-- `swscale_down3to2_bilinear_simd`: 3:2 bilinear row blend `((xs[i] * 2 + ys[i] + 4) * 7282) >>> 16`. -/
  | down3to2Bilinear
  /-- `av1_cdef_dir_filter_simd`: AV1 CDEF directional tap blend `xs[i] + ((ys[i] + zs[i] + 2) >>> 2)`. -/
  | av1CdefDirFilter
  /-- `extract_u16le_msb8_simd`: extract the scaled most-significant byte. -/
  | extractU16LeMsb8
  /-- `luma_stats_moments_simd`: pack one sample and its square. -/
  | lumaStatsMoments
  /-- `luma_stats_pack_simd`: derive packed mean/variance from moments and count. -/
  | lumaStatsPack
  /-- `luma_acceptance_accum_simd`: pack SAD, black/reference sums, and SSE. -/
  | lumaAcceptanceAccum
  /-- `luma_acceptance_gate_simd`: block-level brightness/SAD acceptance decision. -/
  | lumaAcceptanceGate
  /-- `bilinear_q8_blend_simd`: fixed-point horizontal blend. -/
  | bilinearQ8Blend
  /-- `bilinear_q8_pack_simd`: vertical blend and one final rounding. -/
  | bilinearQ8Pack
  /-- `bilinear_q8_clamp10_simd`: unsigned clamp to ten-bit range. -/
  | bilinearQ8Clamp10
  /-- `av1_cdef_tap_simd`: one constrained directional tap with packed `(damping <<< 32) | priStr`. -/
  | av1CdefTap
  /-- `down2x2_fused_eq_simd`: box average and unclamped signed Q8 contrast centered at 128. -/
  | down2x2FusedEq
  /-- `down2x2_fused_brightness_simd`: signed 32-bit brightness offset and byte saturation. -/
  | down2x2FusedBrightness
  /-- `yuv420p_studio_range_simd`: luma/chroma studio-range saturation. -/
  | yuv420pStudioRange
  /-- `bt2020_to_bt709_uv_simd`: packed Q10 BT.2020-to-BT.709 chroma matrix `(outV <<< 8) | outU`. -/
  | bt2020ToBt709Uv
  deriving Repr, DecidableEq, Inhabited

/-- Emit the canonical `LNIR_WIRE_V1` kernel descriptor tokens for a typed `LnirKernelAst`. -/
def LnirKernelAst.toWireTokens : LnirKernelAst → List String
  | .gainBias _ _ => ["E_scalar", "S_fma", "S_var", "8", "S_var", "1", "S_var", "2"]
  | .dotPairwise => ["K_dot"]
  | .saxpy alpha => ["K_saxpy", toString alpha.toInt]
  | .wiener3TapSym => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_add",
        "S_bin", "B_add",
          "S_bin", "B_mul", "S_var", "0", "S_u64", "3",
          "S_bin", "B_mul", "S_var", "1", "S_u64", "10",
        "S_bin", "B_mul", "S_var", "2", "S_u64", "3"
    ]
  | .fmaBlend => ["K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2"]
  | .zipAdd => ["K_za"]
  | .zipMul => ["K_zm"]
  | .mapScaleAdd s b => ["K_msa", toString s.toInt, toString b.toInt]
  | .boxBlurDiv9Recip => [
      "K_cust", "10", "1", "0",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add", "S_var", "0", "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16"
    ]
  | .pq10StudioClamp => [
      "K_cust", "10", "1", "0",
      "S_sel",
        "S_bin", "B_lt", "S_var", "0", "S_u64", "64",
        "S_u64", "64",
        "S_sel",
          "S_bin", "B_lt", "S_u64", "940", "S_var", "0",
          "S_u64", "940",
          "S_var", "0"
    ]
  | .down2x2Box => [
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_shr",
        "S_bin", "B_add",
          "S_bin", "B_add", "S_var", "0", "S_var", "1",
          "S_u64", "2",
        "S_u64", "2"
    ]
  | .down3x3Box => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add",
            "S_bin", "B_add",
              "S_bin", "B_add", "S_var", "0", "S_var", "1",
              "S_var", "2",
            "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16"
    ]
  | .down3to2Bilinear => [
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add",
            "S_bin", "B_add",
              "S_bin", "B_mul", "S_var", "0", "S_u64", "2",
              "S_var", "1",
            "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16"
    ]
  | .av1CdefDirFilter => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_add",
        "S_var", "0",
        "S_bin", "B_shr",
          "S_bin", "B_add",
            "S_bin", "B_add", "S_var", "1", "S_var", "2",
            "S_u64", "2",
          "S_u64", "2"
    ]
  | .extractU16LeMsb8 => [
      "K_cust", "10", "1", "0",
      "S_bin", "B_bitAnd", "S_bin", "B_shr", "S_var", "0", "S_u64", "2", "S_u64", "255"
    ]
  | .lumaStatsMoments => [
      "K_cust", "10", "1", "0",
      "S_bin", "B_bitOr",
        "S_bin", "B_shl", "S_bin", "B_mul", "S_var", "0", "S_var", "0", "S_u64", "32",
        "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295"
    ]
  | .lumaStatsPack => [
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_bitOr",
        "S_bin", "B_shl",
          "S_sel",
            "S_bin", "B_lt",
              "S_bin", "B_mul",
                "S_bin", "B_div", "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295", "S_var", "1",
                "S_bin", "B_div", "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295", "S_var", "1",
              "S_bin", "B_div", "S_bin", "B_shr", "S_var", "0", "S_u64", "32", "S_var", "1",
            "S_bin", "B_sub",
              "S_bin", "B_div", "S_bin", "B_shr", "S_var", "0", "S_u64", "32", "S_var", "1",
              "S_bin", "B_mul",
                "S_bin", "B_div", "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295", "S_var", "1",
                "S_bin", "B_div", "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295", "S_var", "1",
            "S_u64", "0",
          "S_u64", "32",
        "S_bin", "B_bitAnd",
          "S_bin", "B_div", "S_bin", "B_bitAnd", "S_var", "0", "S_u64", "4294967295", "S_var", "1",
          "S_u64", "4294967295"
    ]
  | .lumaAcceptanceAccum => [
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_bitOr", "S_bin", "B_bitOr", "S_bin", "B_bitOr", "S_sel", "S_bin", "B_le", "S_var", "1", "S_var",
      "0", "S_bin", "B_sub", "S_var", "0", "S_var", "1", "S_bin", "B_sub", "S_var", "1", "S_var",
      "0", "S_bin", "B_shl", "S_sel", "S_bin", "B_le", "S_u64", "16", "S_var", "0", "S_bin", "B_sub",
      "S_var", "0", "S_u64", "16", "S_bin", "B_sub", "S_u64", "16", "S_var", "0", "S_u64", "16",
      "S_bin", "B_shl", "S_var", "0", "S_u64", "32", "S_bin", "B_shl", "S_bin", "B_mul", "S_sel", "S_bin",
      "B_le", "S_var", "1", "S_var", "0", "S_bin", "B_sub", "S_var", "0", "S_var", "1", "S_bin",
      "B_sub", "S_var", "1", "S_var", "0", "S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0",
      "S_bin", "B_sub", "S_var", "0", "S_var", "1", "S_bin", "B_sub", "S_var", "1", "S_var", "0",
      "S_u64", "48"
    ]
  | .lumaAcceptanceGate => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_sel", "S_bin", "B_le", "S_u64", "6144", "S_var", "2",
        "S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0", "S_u64", "0", "S_u64", "1",
        "S_u64", "1"
    ]
  | .bilinearQ8Blend => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_add",
        "S_bin", "B_mul", "S_var", "0", "S_bin", "B_sub", "S_u64", "256", "S_var", "2",
        "S_bin", "B_mul", "S_var", "1", "S_var", "2"
    ]
  | .bilinearQ8Pack => [
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_shr",
        "S_bin", "B_add",
          "S_bin", "B_add",
            "S_bin", "B_mul", "S_var", "0", "S_bin", "B_sub", "S_u64", "256", "S_var", "2",
            "S_bin", "B_mul", "S_var", "1", "S_var", "2",
          "S_u64", "32768",
        "S_u64", "16"
    ]
  | .bilinearQ8Clamp10 => [
      "K_cust", "10", "1", "0",
      "S_sel", "S_bin", "B_lt", "S_u64", "1023", "S_var", "0", "S_u64", "1023", "S_var", "0"
    ]
  | .av1CdefTap =>
      let str := ["S_bin", "B_bitAnd", "S_var", "2", "S_u64", "2147483647"]
      let d32 := ["S_bin", "B_shr", "S_var", "2", "S_u64", "32"]
      let sh := ["S_bin", "B_bitAnd",
        "S_sel", "S_bin", "B_lt", "S_u64", "0", ] ++ d32 ++ d32 ++ ["S_u64", "1", "S_u64", "31"]
      let ad := ["S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0",
        "S_bin", "B_sub", "S_var", "0", "S_var", "1",
        "S_bin", "B_sub", "S_var", "1", "S_var", "0"]
      let q := ["S_bin", "B_shr"] ++ ad ++ sh
      let diff := ["S_bin", "B_sub"] ++ str ++ q
      let mag := ["S_sel", "S_bin", "B_le"] ++ str ++ q ++ ["S_u64", "0",
        "S_sel", "S_bin", "B_le"] ++ ad ++ diff ++ ad ++ diff
      ["K_cust", "10", "3", "0", "1", "2",
       "S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0"] ++ mag ++
      ["S_bin", "B_sub", "S_u64", "0"] ++ mag
  | .down2x2FusedEq =>
      let avg := ["S_bin", "B_shr", "S_bin", "B_add",
        "S_bin", "B_add", "S_var", "0", "S_var", "1", "S_u64", "2", "S_u64", "2"]
      let cent := ["S_bin", "B_sub"] ++ avg ++ ["S_u64", "128"]
      let prod32 := ["S_bin", "B_sar", "S_bin", "B_shl", "S_bin", "B_add",
        "S_bin", "B_mul"] ++ cent ++ ["S_var", "2", "S_u64", "128", "S_u64", "32", "S_u64", "32"]
      ["K_cust", "10", "3", "0", "1", "2",
       "S_bin", "B_add", "S_bin", "B_sar"] ++ prod32 ++ ["S_u64", "8", "S_u64", "128"]
  | .down2x2FusedBrightness =>
      let sum32 := ["S_bin", "B_sar", "S_bin", "B_shl",
        "S_bin", "B_add", "S_var", "0", "S_var", "1", "S_u64", "32", "S_u64", "32"]
      ["K_cust", "10", "2", "0", "1",
       "S_sel", "S_bin", "B_le"] ++ sum32 ++ ["S_u64", "255"] ++ sum32 ++
      ["S_sel", "S_bin", "B_shr"] ++ sum32 ++ ["S_u64", "63", "S_u64", "0", "S_u64", "255"]
  | .yuv420pStudioRange => [
      "K_cust", "10", "2", "0", "1",
      "S_sel", "S_bin", "B_bitAnd", "S_var", "1", "S_u64", "1",
        "S_sel", "S_bin", "B_lt", "S_var", "0", "S_u64", "16", "S_u64", "16",
          "S_sel", "S_bin", "B_lt", "S_u64", "240", "S_var", "0", "S_u64", "240", "S_var", "0",
        "S_sel", "S_bin", "B_lt", "S_var", "0", "S_u64", "16", "S_u64", "16",
          "S_sel", "S_bin", "B_lt", "S_u64", "235", "S_var", "0", "S_u64", "235", "S_var", "0"
    ]
  | .bt2020ToBt709Uv =>
      let cb := ["S_bin", "B_sub", "S_var", "0", "S_u64", "128"]
      let cr := ["S_bin", "B_sub", "S_var", "1", "S_u64", "128"]
      let uRaw := ["S_bin", "B_add", "S_bin", "B_sar", "S_bin", "B_add", "S_bin", "B_add",
        "S_bin", "B_mul"] ++ cb ++ ["S_u64", "1004",
        "S_bin", "B_mul"] ++ cr ++ ["S_u64", "18446744073709551542",
        "S_u64", "512", "S_u64", "10", "S_u64", "128"]
      let vRaw := ["S_bin", "B_add", "S_bin", "B_sar", "S_bin", "B_add", "S_bin", "B_add",
        "S_bin", "B_mul"] ++ cb ++ ["S_u64", "18446744073709551574",
        "S_bin", "B_mul"] ++ cr ++ ["S_u64", "986",
        "S_u64", "512", "S_u64", "10", "S_u64", "128"]
      let clamp (e : List String) :=
        ["S_sel", "S_bin", "B_le"] ++ e ++ ["S_u64", "255"] ++ e ++
        ["S_sel", "S_bin", "B_shr"] ++ e ++ ["S_u64", "63", "S_u64", "0", "S_u64", "255"]
      ["K_cust", "10", "2", "0", "1",
       "S_bin", "B_bitOr", "S_bin", "B_shl"] ++ clamp vRaw ++ ["S_u64", "8"] ++ clamp uRaw

/-- Build an `A_L3` data-parallel `LNIR_WIRE_V1` declaration whose `C_par` kernel body is exactly
    `k.toWireTokens`, so the emitted wire and the typed `LnirKernelAst` coincide by construction. -/
private def mkLnirPixelCoreDecl (declName : String) (params : List String) (k : LnirKernelAst) : List String :=
  let n := params.length
  let paramToks := (params.zipIdx).flatMap fun (nm, i) =>
    [toString i, hexEncodeString nm, "1", "T_sarray", "T_i64"]
  ["D_decl", hexEncodeString declName, "A_L3", "1", toString n] ++ paramToks ++
  ["T_sarray", "T_i64", "C_let", toString n, "T_i64", "E_salen", "0",
   "C_par", toString (n + 1), toString n, toString n] ++ (List.range n).map toString ++
  ["T_i64"] ++ k.toWireTokens ++ ["C_ret", toString (n + 1)]

private def mkLnirBinaryParDecl (declName p0 p1 kTok : String) : List String := [
  "D_decl", hexEncodeString declName, "A_L3", "1", "2",
  "0", hexEncodeString p0, "1", "T_sarray", "T_i64",
  "1", hexEncodeString p1, "1", "T_sarray", "T_i64",
  "T_sarray", "T_i64",
  "C_let", "2", "T_i64", "E_salen", "0",
  "C_par", "3", "2", "2", "0", "1", "T_i64", kTok,
  "C_ret", "3"
]

/-- Build the `LNIR_WIRE_V1` wire representation of `LeanAV.DSP.Kernels` (12 distinct DSP kernels)
    for direct consumption, translation validation, superoptimization, and static library compilation
    by `lean-native-core`. -/
def emitLeanAvLnirWire : String :=
  let modHex := hexEncodeString "LeanAV.DSP.Kernels"
  -- 1. `swscale_luma_gain_bias_simd` (plane: sarray i64, gainQ10: i64, biasQ10: i64) -> sarray i64
  let d1 : List String := [
    "D_decl", hexEncodeString "swscale_luma_gain_bias_simd", "A_L3", "1", "3",
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

  -- 2. `flac_lpc_autocorr_dot_simd` (samplesLag0: sarray i64, samplesLagK: sarray i64) -> sarray i64
  let d2 : List String := [
    "D_decl", hexEncodeString "flac_lpc_autocorr_dot_simd", "A_L3", "1", "2",
    "0", hexEncodeString "samplesLag0", "0", "T_sarray", "T_i64",
    "1", hexEncodeString "samplesLagK", "0", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_inc", "0", "1",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64", "K_dot",
    "C_dec", "0", "1",
    "C_ret", "3"
  ]

  -- 3. `opus_celt_pvq_mix_saxpy_gpu` (midBand: sarray i64, sideBand: sarray i64) -> sarray i64
  let d3 := mkLnirSaxpyDecl "opus_celt_pvq_mix_saxpy_gpu" "midBand" "sideBand" "4"

  -- 4. `av1_wiener_3tap_sym_gpu` (tapLeft: sarray i64, tapCenter: sarray i64, tapRight: sarray i64) -> sarray i64
  --    Computes `3 * tapLeft[i] + 10 * tapCenter[i] + 3 * tapRight[i]`
  let d4 : List String := [
    "D_decl", hexEncodeString "av1_wiener_3tap_sym_gpu", "A_L3", "1", "3",
    "0", hexEncodeString "tapLeft", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "tapCenter", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "tapRight", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_add",
        "S_bin", "B_add",
          "S_bin", "B_mul", "S_var", "0", "S_u64", "3",
          "S_bin", "B_mul", "S_var", "1", "S_u64", "10",
        "S_bin", "B_mul", "S_var", "2", "S_u64", "3",
    "C_ret", "4"
  ]

  -- 5. `av1_cdef_fma_blend_gpu` (priTap: sarray i64, dirWeight: sarray i64, srcPixel: sarray i64) -> sarray i64
  let d5 : List String := [
    "D_decl", hexEncodeString "av1_cdef_fma_blend_gpu", "A_L3", "1", "3",
    "0", hexEncodeString "priTap", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "dirWeight", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "srcPixel", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2", "S_fma", "S_var", "0", "S_var", "1", "S_var", "2",
    "C_ret", "4"
  ]

  -- 6. `h264_idct_tuple_accum_sroa` (blocks: i64, dcInit: i64) -> i64
  let d6 : List String := [
    "D_decl", hexEncodeString "h264_idct_tuple_accum_sroa", "A_L3", "0", "2",
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

  -- 7. `bframe_bipred_blend_gpu` (refL0: sarray i64, refL1: sarray i64) -> sarray i64
  let d7 := mkLnirSaxpyDecl "bframe_bipred_blend_gpu" "refL0" "refL1" "1"

  -- 8. `hevc_sao_band_offset_add_gpu` (reconSample: sarray i64, bandOffset: sarray i64) -> sarray i64
  let d8 := mkLnirBinaryParDecl "hevc_sao_band_offset_add_gpu" "reconSample" "bandOffset" "K_za"

  -- 9. `aac_imdct_window_mul_gpu` (mdctSpec: sarray i64, kbdWindow: sarray i64) -> sarray i64
  let d9 := mkLnirBinaryParDecl "aac_imdct_window_mul_gpu" "mdctSpec" "kbdWindow" "K_zm"

  -- 10. `prores_qscale_map_simd` (dctCoeff: sarray i64) -> sarray i64
  let d10 : List String := [
    "D_decl", hexEncodeString "prores_qscale_map_simd", "A_L3", "1", "1",
    "0", hexEncodeString "dctCoeff", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "1", "T_i64", "E_salen", "0",
    "C_par", "2", "1", "1", "0", "T_i64", "K_msa", "16", "8",
    "C_ret", "2"
  ]

  -- 11. `boxblur_div9_recip_shift_simd` (sum9Plane: sarray i64) -> sarray i64
  --     Computes `((sum9Plane[i] + 4) * 7282) >>> 16`
  let d11 : List String := [
    "D_decl", hexEncodeString "boxblur_div9_recip_shift_simd", "A_L3", "1", "1",
    "0", hexEncodeString "sum9Plane", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "1", "T_i64", "E_salen", "0",
    "C_par", "2", "1", "1", "0", "T_i64",
      "K_cust", "10", "1", "0",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add", "S_var", "0", "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16",
    "C_ret", "2"
  ]

  -- 12. `pq10_studio_clamp_select_simd` (luma10Plane: sarray i64) -> sarray i64
  --     Computes branchless `if x < 64 then 64 else if 940 < x then 940 else x`
  let d12 : List String := [
    "D_decl", hexEncodeString "pq10_studio_clamp_select_simd", "A_L3", "1", "1",
    "0", hexEncodeString "luma10Plane", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "1", "T_i64", "E_salen", "0",
    "C_par", "2", "1", "1", "0", "T_i64",
      "K_cust", "10", "1", "0",
      "S_sel",
        "S_bin", "B_lt", "S_var", "0", "S_u64", "64",
        "S_u64", "64",
        "S_sel",
          "S_bin", "B_lt", "S_u64", "940", "S_var", "0",
          "S_u64", "940",
          "S_var", "0",
    "C_ret", "2"
  ]

  -- 13. `swscale_down2x2_box_simd` (row0PairSum: sarray i64, row1PairSum: sarray i64) -> sarray i64
  --     Computes `(row0PairSum[i] + row1PairSum[i] + 2) >>> 2`
  let d13 : List String := [
    "D_decl", hexEncodeString "swscale_down2x2_box_simd", "A_L3", "1", "2",
    "0", hexEncodeString "row0PairSum", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "row1PairSum", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64",
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_shr",
        "S_bin", "B_add",
          "S_bin", "B_add", "S_var", "0", "S_var", "1",
          "S_u64", "2",
        "S_u64", "2",
    "C_ret", "3"
  ]

  -- 14. `swscale_down3x3_box_simd` (row0TriSum: sarray i64, row1TriSum: sarray i64, row2TriSum: sarray i64) -> sarray i64
  --     Computes `(((row0TriSum[i] + row1TriSum[i] + row2TriSum[i]) + 4) * 7282) >>> 16`
  let d14 : List String := [
    "D_decl", hexEncodeString "swscale_down3x3_box_simd", "A_L3", "1", "3",
    "0", hexEncodeString "row0TriSum", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "row1TriSum", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "row2TriSum", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add",
            "S_bin", "B_add",
              "S_bin", "B_add", "S_var", "0", "S_var", "1",
              "S_var", "2",
            "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16",
    "C_ret", "4"
  ]

  -- 15. `swscale_down3to2_bilinear_simd` (rowAHoriz: sarray i64, rowBHoriz: sarray i64) -> sarray i64
  --     Computes `(((rowAHoriz[i] * 2 + rowBHoriz[i]) + 4) * 7282) >>> 16`
  let d15 : List String := [
    "D_decl", hexEncodeString "swscale_down3to2_bilinear_simd", "A_L3", "1", "2",
    "0", hexEncodeString "rowAHoriz", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "rowBHoriz", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "2", "T_i64", "E_salen", "0",
    "C_par", "3", "2", "2", "0", "1", "T_i64",
      "K_cust", "10", "2", "0", "1",
      "S_bin", "B_shr",
        "S_bin", "B_mul",
          "S_bin", "B_add",
            "S_bin", "B_add",
              "S_bin", "B_mul", "S_var", "0", "S_u64", "2",
              "S_var", "1",
            "S_u64", "4",
          "S_u64", "7282",
        "S_u64", "16",
    "C_ret", "3"
  ]

  -- 16. `av1_cdef_dir_filter_simd` (centerPx: sarray i64, tapPosSum: sarray i64, tapNegSum: sarray i64) -> sarray i64
  --     Computes `centerPx[i] + ((tapPosSum[i] + tapNegSum[i] + 2) >>> 2)`
  let d16 : List String := [
    "D_decl", hexEncodeString "av1_cdef_dir_filter_simd", "A_L3", "1", "3",
    "0", hexEncodeString "centerPx", "1", "T_sarray", "T_i64",
    "1", hexEncodeString "tapPosSum", "1", "T_sarray", "T_i64",
    "2", hexEncodeString "tapNegSum", "1", "T_sarray", "T_i64",
    "T_sarray", "T_i64",
    "C_let", "3", "T_i64", "E_salen", "0",
    "C_par", "4", "3", "3", "0", "1", "2", "T_i64",
      "K_cust", "10", "3", "0", "1", "2",
      "S_bin", "B_add",
        "S_var", "0",
        "S_bin", "B_shr",
          "S_bin", "B_add",
            "S_bin", "B_add", "S_var", "1", "S_var", "2",
            "S_u64", "2",
          "S_u64", "2",
    "C_ret", "4"
  ]

  -- 17. `extract_u16le_msb8_simd`: `(sample >>> 2) & 255`, including 16-bit samples.
  let d17 := mkLnirPixelCoreDecl "extract_u16le_msb8_simd" ["samples"] .extractU16LeMsb8

  -- 18. `luma_stats_moments_simd`: packed `(sumSq[47:16] | sum)` for one sample.
  let d18 := mkLnirPixelCoreDecl "luma_stats_moments_simd" ["samples"] .lumaStatsMoments

  -- 19. `luma_stats_pack_simd`: `(variance <<< 32) | mean` from packed moments and count.
  let d19 := mkLnirPixelCoreDecl "luma_stats_pack_simd" ["moments", "counts"] .lumaStatsPack

  -- 20. `luma_acceptance_accum_simd`: packed `(sad | blackSum<<16 | refSum<<32 | sse<<48)`.
  let d20 := mkLnirPixelCoreDecl "luma_acceptance_accum_simd" ["source", "reconstructed"] .lumaAcceptanceAccum

  -- 21. `luma_acceptance_gate_simd`: reject non-flat, sufficiently bright bad blocks.
  let d21 := mkLnirPixelCoreDecl "luma_acceptance_gate_simd" ["sad", "blackSum", "refSum"] .lumaAcceptanceGate

  -- 22. `bilinear_q8_blend_simd`: four weighted pixels, fixed-point horizontal fraction.
  let d22 := mkLnirPixelCoreDecl "bilinear_q8_blend_simd" ["p00", "p01", "fx"] .bilinearQ8Blend

  -- 23. `bilinear_q8_pack_simd`: weighted top/bottom rows, rounded once at 16 bits.
  let d23 := mkLnirPixelCoreDecl "bilinear_q8_pack_simd" ["top", "bottom", "fy"] .bilinearQ8Pack

  -- 24. `bilinear_q8_clamp10_simd`: clamp the rounded sample to `[0, 1023]`.
  let d24 := mkLnirPixelCoreDecl "bilinear_q8_clamp10_simd" ["sample"] .bilinearQ8Clamp10

  -- 25. `av1_cdef_tap_simd`: constrained signed difference with packed `(damping <<< 32) | priStr`.
  let d25 := mkLnirPixelCoreDecl "av1_cdef_tap_simd" ["neighbor", "center", "strengthDamp"] .av1CdefTap

  -- 26. `down2x2_fused_eq_simd`: rounded 2x2 average and unclamped signed Q8 EQ centered at 128.
  let d26 := mkLnirPixelCoreDecl "down2x2_fused_eq_simd" ["row0PairSum", "row1PairSum", "contrastQ8"] .down2x2FusedEq

  -- 27. `down2x2_fused_brightness_simd`: add signed 32-bit brightness and clamp to a byte.
  let d27 := mkLnirPixelCoreDecl "down2x2_fused_brightness_simd" ["contrastCentered", "brightness"] .down2x2FusedBrightness

  -- 28. `yuv420p_studio_range_simd`: independently clamp one Y/U/V sample.
  let d28 := mkLnirPixelCoreDecl "yuv420p_studio_range_simd" ["sample", "isChroma"] .yuv420pStudioRange

  -- 28b. `bt2020_to_bt709_uv_simd`: Q10 BT.2020-to-BT.709 `(1004, -74, -42, 986)` chroma matrix.
  let d28b := mkLnirPixelCoreDecl "bt2020_to_bt709_uv_simd" ["uPlane", "vPlane"] .bt2020ToBt709Uv

  let mkScalarDecl (declName : String) (params : List String)
      (lets : List (List String)) (retVar : Nat) : List String :=
    let n := params.length
    let pToks := (params.zipIdx).flatMap fun (nm, i) =>
      [toString i, hexEncodeString nm, "0", "T_i64"]
    let lToks := (lets.zipIdx).flatMap fun (rhs, j) =>
      ["C_let", toString (n + j), "T_i64", "E_scalar"] ++ rhs
    ["D_decl", hexEncodeString declName, "A_L3", "0", toString n] ++ pToks ++
      ["T_i64"] ++ lToks ++ ["C_ret", toString retVar]

  -- 29-45. Scalar `LNIR_WIRE_V1` pixel cores wired directly by the 14 outer LLVM shells.
  let d29 := mkScalarDecl "lnir_px_down2x2" ["sum4"]
    [["S_bin", "B_shr", "S_bin", "B_add", "S_var", "0", "S_u64", "2", "S_u64", "2"]] 1
  let d30 := mkScalarDecl "lnir_px_down2x2_fused_eq_u8" ["sum4", "contrastQ8", "brightness"] [
    ["S_bin", "B_shr", "S_bin", "B_add", "S_var", "0", "S_u64", "2", "S_u64", "2"],
    ["S_bin", "B_sub", "S_var", "3", "S_u64", "128"],
    ["S_bin", "B_sar", "S_bin", "B_shl", "S_bin", "B_add",
      "S_bin", "B_mul", "S_var", "4", "S_var", "1", "S_u64", "128", "S_u64", "32", "S_u64", "32"],
    ["S_bin", "B_sar", "S_var", "5", "S_u64", "8"],
    ["S_bin", "B_sar", "S_bin", "B_shl", "S_bin", "B_add",
      "S_bin", "B_add", "S_var", "6", "S_u64", "128", "S_var", "2", "S_u64", "32", "S_u64", "32"],
    ["S_sel", "S_bin", "B_le", "S_var", "7", "S_u64", "255", "S_var", "7",
      "S_sel", "S_bin", "B_shr", "S_var", "7", "S_u64", "63", "S_u64", "0", "S_u64", "255"]
  ] 8
  let d31 := mkScalarDecl "lnir_px_down3x3_u8" ["sum9"] [
    ["S_bin", "B_shr", "S_bin", "B_mul",
      "S_bin", "B_add", "S_var", "0", "S_u64", "4", "S_u64", "7282", "S_u64", "16"]
  ] 1
  let d32 := mkScalarDecl "lnir_px_down3x3_u16" ["sum9"] [
    ["S_bin", "B_div", "S_bin", "B_add", "S_var", "0", "S_u64", "4", "S_u64", "9"]
  ] 1
  let d33 := mkScalarDecl "lnir_px_down3to2_u8" ["p00", "p01", "p10", "p11", "oddX", "oddY"] [
    ["S_sel", "S_bin", "B_bitAnd", "S_var", "4", "S_u64", "1",
      "S_bin", "B_add", "S_var", "0", "S_bin", "B_shl", "S_var", "1", "S_u64", "1",
      "S_bin", "B_add", "S_bin", "B_shl", "S_var", "0", "S_u64", "1", "S_var", "1"],
    ["S_sel", "S_bin", "B_bitAnd", "S_var", "4", "S_u64", "1",
      "S_bin", "B_add", "S_var", "2", "S_bin", "B_shl", "S_var", "3", "S_u64", "1",
      "S_bin", "B_add", "S_bin", "B_shl", "S_var", "2", "S_u64", "1", "S_var", "3"],
    ["S_sel", "S_bin", "B_bitAnd", "S_var", "5", "S_u64", "1",
      "S_bin", "B_add", "S_var", "6", "S_bin", "B_shl", "S_var", "7", "S_u64", "1",
      "S_bin", "B_add", "S_bin", "B_shl", "S_var", "6", "S_u64", "1", "S_var", "7"],
    ["S_bin", "B_shr", "S_bin", "B_mul",
      "S_bin", "B_add", "S_var", "8", "S_u64", "4", "S_u64", "7282", "S_u64", "16"]
  ] 9
  let d34 := mkScalarDecl "lnir_px_down3to2_u16_clamp10" ["colA", "colB"] [
    ["S_bin", "B_shr", "S_bin", "B_add",
      "S_bin", "B_add", "S_var", "0", "S_var", "1", "S_u64", "2", "S_u64", "2"],
    ["S_sel", "S_bin", "B_lt", "S_u64", "1023", "S_var", "2", "S_u64", "1023", "S_var", "2"]
  ] 3
  let d35 := mkScalarDecl "lnir_px_av1_cdef_tap" ["neighbor", "center", "priStr", "damping"] [
    ["S_bin", "B_bitAnd", "S_var", "2", "S_u64", "2147483647"],
    ["S_bin", "B_bitAnd", "S_var", "3", "S_u64", "4294967295"],
    ["S_bin", "B_bitAnd",
      "S_sel", "S_bin", "B_lt", "S_u64", "0", "S_var", "5", "S_var", "5", "S_u64", "1",
      "S_u64", "31"],
    ["S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0",
      "S_bin", "B_sub", "S_var", "0", "S_var", "1",
      "S_bin", "B_sub", "S_var", "1", "S_var", "0"],
    ["S_bin", "B_shr", "S_var", "7", "S_var", "6"],
    ["S_sel", "S_bin", "B_le", "S_var", "4", "S_var", "8", "S_u64", "0",
      "S_sel", "S_bin", "B_le", "S_var", "7", "S_bin", "B_sub", "S_var", "4", "S_var", "8",
        "S_var", "7", "S_bin", "B_sub", "S_var", "4", "S_var", "8"],
    ["S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0",
      "S_var", "9", "S_bin", "B_sub", "S_u64", "0", "S_var", "9"]
  ] 10
  let d36 := mkScalarDecl "lnir_px_av1_cdef_filter4_u8" ["px", "c0", "c1", "c2", "c3"] [
    ["S_bin", "B_add",
      "S_bin", "B_add", "S_var", "1", "S_var", "2",
      "S_bin", "B_add", "S_var", "3", "S_var", "4"],
    ["S_bin", "B_sar", "S_bin", "B_add", "S_var", "5", "S_u64", "2", "S_u64", "2"],
    ["S_bin", "B_add", "S_var", "0", "S_var", "6"],
    ["S_sel", "S_bin", "B_le", "S_var", "7", "S_u64", "255", "S_var", "7",
      "S_sel", "S_bin", "B_shr", "S_var", "7", "S_u64", "63", "S_u64", "0", "S_u64", "255"]
  ] 8
  let d37 := mkScalarDecl "lnir_px_bilinear_q8" ["p00", "p01", "p10", "p11", "fx", "fy"] [
    ["S_bin", "B_sub", "S_u64", "256", "S_var", "4"],
    ["S_bin", "B_sub", "S_u64", "256", "S_var", "5"],
    ["S_bin", "B_add",
      "S_bin", "B_mul", "S_var", "0", "S_var", "6",
      "S_bin", "B_mul", "S_var", "1", "S_var", "4"],
    ["S_bin", "B_add",
      "S_bin", "B_mul", "S_var", "2", "S_var", "6",
      "S_bin", "B_mul", "S_var", "3", "S_var", "4"],
    ["S_bin", "B_shr",
      "S_bin", "B_add",
        "S_bin", "B_add",
          "S_bin", "B_mul", "S_var", "8", "S_var", "7",
          "S_bin", "B_mul", "S_var", "9", "S_var", "5",
        "S_u64", "32768",
      "S_u64", "16"]
  ] 10
  let d38 := mkScalarDecl "lnir_px_bilinear_q8_clamp10" ["p00", "p01", "p10", "p11", "fx", "fy"] [
    ["S_bin", "B_sub", "S_u64", "256", "S_var", "4"],
    ["S_bin", "B_sub", "S_u64", "256", "S_var", "5"],
    ["S_bin", "B_add",
      "S_bin", "B_mul", "S_var", "0", "S_var", "6",
      "S_bin", "B_mul", "S_var", "1", "S_var", "4"],
    ["S_bin", "B_add",
      "S_bin", "B_mul", "S_var", "2", "S_var", "6",
      "S_bin", "B_mul", "S_var", "3", "S_var", "4"],
    ["S_bin", "B_shr",
      "S_bin", "B_add",
        "S_bin", "B_add",
          "S_bin", "B_mul", "S_var", "8", "S_var", "7",
          "S_bin", "B_mul", "S_var", "9", "S_var", "5",
        "S_u64", "32768",
      "S_u64", "16"],
    ["S_sel", "S_bin", "B_lt", "S_u64", "1023", "S_var", "10", "S_u64", "1023", "S_var", "10"]
  ] 11
  let d39 := mkScalarDecl "lnir_px_extract_u16le_msb8" ["sample"] [
    ["S_bin", "B_bitAnd", "S_bin", "B_shr", "S_var", "0", "S_u64", "2", "S_u64", "255"]
  ] 1
  let d40 := mkScalarDecl "lnir_px_u16le_to_u10" ["sample"] [
    ["S_bin", "B_shr", "S_var", "0", "S_u64", "2"]
  ] 1
  let d41 := mkScalarDecl "lnir_px_luma_stats_pack" ["sum", "sumSq", "count"] [
    ["S_bin", "B_div", "S_var", "0", "S_var", "2"],
    ["S_bin", "B_div", "S_var", "1", "S_var", "2"],
    ["S_bin", "B_mul", "S_var", "3", "S_var", "3"],
    ["S_sel", "S_bin", "B_lt", "S_var", "5", "S_var", "4",
      "S_bin", "B_sub", "S_var", "4", "S_var", "5", "S_u64", "0"],
    ["S_bin", "B_bitOr",
      "S_bin", "B_shl", "S_var", "6", "S_u64", "32",
      "S_bin", "B_bitAnd", "S_var", "3", "S_u64", "4294967295"]
  ] 7
  let d42 := mkScalarDecl "lnir_px_luma_acceptance_accum" ["refPx", "dstPx"] [
    ["S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0",
      "S_bin", "B_sub", "S_var", "0", "S_var", "1",
      "S_bin", "B_sub", "S_var", "1", "S_var", "0"],
    ["S_sel", "S_bin", "B_le", "S_u64", "16", "S_var", "0",
      "S_bin", "B_sub", "S_var", "0", "S_u64", "16",
      "S_bin", "B_sub", "S_u64", "16", "S_var", "0"],
    ["S_bin", "B_mul", "S_var", "2", "S_var", "2"],
    ["S_bin", "B_bitOr",
      "S_bin", "B_bitOr",
        "S_bin", "B_bitOr", "S_var", "2", "S_bin", "B_shl", "S_var", "3", "S_u64", "16",
        "S_bin", "B_shl", "S_var", "0", "S_u64", "32",
      "S_bin", "B_shl", "S_var", "4", "S_u64", "48"]
  ] 5
  let d43 := mkScalarDecl "lnir_px_luma_acceptance_gate" ["sad", "blackSum", "refSum", "oldOk"] [
    ["S_sel", "S_bin", "B_le", "S_u64", "6144", "S_var", "2",
      "S_sel", "S_bin", "B_le", "S_var", "1", "S_var", "0", "S_u64", "0", "S_var", "3",
      "S_var", "3"]
  ] 4
  let d44 := mkScalarDecl "lnir_px_y_studio_clamp_u8" ["y"] [
    ["S_sel", "S_bin", "B_lt", "S_var", "0", "S_u64", "16", "S_u64", "16",
      "S_sel", "S_bin", "B_lt", "S_u64", "235", "S_var", "0", "S_u64", "235", "S_var", "0"]
  ] 1
  let d45 := mkScalarDecl "lnir_px_bt2020_to_bt709_uv_u8" ["uPx", "vPx"] [
    ["S_bin", "B_sub", "S_var", "0", "S_u64", "128"],
    ["S_bin", "B_sub", "S_var", "1", "S_u64", "128"],
    ["S_bin", "B_add",
      "S_bin", "B_sar",
        "S_bin", "B_add",
          "S_bin", "B_add",
            "S_bin", "B_mul", "S_var", "2", "S_u64", "1004",
            "S_bin", "B_mul", "S_var", "3", "S_u64", "18446744073709551542",
          "S_u64", "512",
        "S_u64", "10",
      "S_u64", "128"],
    ["S_bin", "B_add",
      "S_bin", "B_sar",
        "S_bin", "B_add",
          "S_bin", "B_add",
            "S_bin", "B_mul", "S_var", "2", "S_u64", "18446744073709551574",
            "S_bin", "B_mul", "S_var", "3", "S_u64", "986",
          "S_u64", "512",
        "S_u64", "10",
      "S_u64", "128"],
    ["S_sel", "S_bin", "B_le", "S_var", "4", "S_u64", "255", "S_var", "4",
      "S_sel", "S_bin", "B_shr", "S_var", "4", "S_u64", "63", "S_u64", "0", "S_u64", "255"],
    ["S_sel", "S_bin", "B_le", "S_var", "5", "S_u64", "255", "S_var", "5",
      "S_sel", "S_bin", "B_shr", "S_var", "5", "S_u64", "63", "S_u64", "0", "S_u64", "255"],
    ["S_bin", "B_bitOr", "S_bin", "B_shl", "S_var", "7", "S_u64", "8", "S_var", "6"]
  ] 8

  let declList := [
    d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d28b,
    d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41,
    d42, d43, d44, d45
  ]
  let declTokens := declList.flatten
  let allTokens := ["LNIR_WIRE_V1", modHex, "46"] ++ declTokens
  String.intercalate "|" allTokens

/-! ## Typed `LnirKernelAst`, Formal Evaluator `evalLnirKernel`, & Universal Equivalence Theorems -/

/-- Single-element unsigned reciprocal shift `((x.toUInt64 + 4) * 7282) >>> 16` for `boxblur_div9_recip_shift_simd`. -/
@[inline]
def evalBoxBlurDiv9RecipElem (x : Int64) : Int64 :=
  (((x.toUInt64 + 4) * 7282) >>> 16).toInt64

/-- Single-element branchless clamp `if u < 64 then 64 else if 940 < u then 940 else u` for `pq10_studio_clamp_select_simd`. -/
@[inline]
def evalPq10StudioClampElem (x : Int64) : Int64 :=
  let u := x.toUInt64
  (if u < 64 then (64 : UInt64) else if 940 < u then (940 : UInt64) else u).toInt64

/-- Single-element 2x2 box reduction `((r0.toUInt64 + r1.toUInt64 + 2) >>> 2)` for `swscale_down2x2_box_simd`. -/
@[inline]
def evalDown2x2BoxElem (r0 r1 : Int64) : Int64 :=
  ((r0.toUInt64 + r1.toUInt64 + 2) >>> 2).toInt64

/-- Single-element 3x3 box reduction `(((r0.toUInt64 + r1.toUInt64 + r2.toUInt64 + 4) * 7282) >>> 16)` for `swscale_down3x3_box_simd`. -/
@[inline]
def evalDown3x3BoxElem (r0 r1 r2 : Int64) : Int64 :=
  (((r0.toUInt64 + r1.toUInt64 + r2.toUInt64 + 4) * 7282) >>> 16).toInt64

/-- Single-element 3:2 bilinear reduction `(((rA.toUInt64 * 2 + rB.toUInt64 + 4) * 7282) >>> 16)` for `swscale_down3to2_bilinear_simd`. -/
@[inline]
def evalDown3to2BilinearElem (rA rB : Int64) : Int64 :=
  (((rA.toUInt64 * 2 + rB.toUInt64 + 4) * 7282) >>> 16).toInt64

/-- Single-element AV1 CDEF directional blend `(c + ((tPos + tNeg + 2) >>> 2))`
    for `av1_cdef_dir_filter_simd`. -/
@[inline]
def evalAv1CdefDirFilterElem (c tPos tNeg : Int64) : Int64 :=
  (c.toUInt64 + ((tPos.toUInt64 + tNeg.toUInt64 + 2) >>> 2)).toInt64

def evalExtractU16LeMsb8Elem (sample : Int64) : Int64 :=
  ((sample.toUInt64 >>> 2) &&& 255).toInt64

def evalLumaStatsMomentsElem (sample : Int64) : Int64 :=
  let u := sample.toUInt64
  ((u * u <<< 32) ||| (u &&& 0xFFFFFFFF)).toInt64

def evalLumaStatsPackElem (moments count : Int64) : Int64 :=
  let u := moments.toUInt64
  let mean := (u &&& 0xFFFFFFFF) / count.toUInt64
  let meanSq := (u >>> 32) / count.toUInt64
  let variance := if mean * mean < meanSq then meanSq - mean * mean else 0
  ((variance <<< 32) ||| (mean &&& 0xFFFFFFFF)).toInt64

def evalLumaAcceptanceAccumElem (src dst : Int64) : Int64 :=
  let s := src.toUInt64
  let d := dst.toUInt64
  let ad := if d ≤ s then s - d else d - s
  let black := if 16 ≤ s then s - 16 else 16 - s
  (ad ||| (black <<< 16) ||| (s <<< 32) ||| ((ad * ad) <<< 48)).toInt64

def evalLumaAcceptanceGateElem (sad blackSum refSum : Int64) : Int64 :=
  if 6144 ≤ refSum.toUInt64 then
    if blackSum.toUInt64 ≤ sad.toUInt64 then 0 else 1
  else 1

def evalBilinearQ8BlendElem (p00 p01 fx : Int64) : Int64 :=
  (p00.toUInt64 * (256 - fx.toUInt64) + p01.toUInt64 * fx.toUInt64).toInt64

def evalBilinearQ8PackElem (top bottom fy : Int64) : Int64 :=
  ((top.toUInt64 * (256 - fy.toUInt64) + bottom.toUInt64 * fy.toUInt64 + 32768) >>> 16).toInt64

def evalBilinearQ8Clamp10Elem (sample : Int64) : Int64 :=
  (if 1023 < sample.toUInt64 then 1023 else sample.toUInt64).toInt64

def evalAv1CdefTapElem (neighbor center strengthDamp : Int64) : Int64 :=
  let n := neighbor.toUInt64
  let c := center.toUInt64
  let raw := strengthDamp.toUInt64
  let str := raw &&& 2147483647
  let d32 := raw >>> 32
  let sh := (if 0 < d32 then d32 else 1) &&& 31
  let ad := if c ≤ n then n - c else c - n
  let q := ad >>> sh
  let mag := if str ≤ q then 0 else if ad ≤ str - q then ad else str - q
  (if c ≤ n then mag else 0 - mag).toInt64

/-- Signed saturation of a two's-complement `UInt64` value to `[0, 255]`. -/
def clampByteU64 (x : UInt64) : UInt64 :=
  if x ≤ 255 then x else if x >>> 63 != 0 then 0 else 255

/-- Sign-extend the low 32 bits of a `UInt64` using arithmetic shift right (`B_sar (B_shl x 32) 32`). -/
@[inline]
def sext32U64 (x : UInt64) : UInt64 :=
  ((x <<< 32).toInt64 >>> 32).toUInt64

def evalDown2x2FusedEqElem (r0 r1 contrastQ8 : Int64) : Int64 :=
  let average := (r0.toUInt64 + r1.toUInt64 + 2) >>> 2
  let prod32 := sext32U64 ((average - 128) * contrastQ8.toUInt64 + 128)
  ((prod32.toInt64 >>> 8).toUInt64 + 128).toInt64

def evalDown2x2FusedBrightnessElem (centered brightness : Int64) : Int64 :=
  let sum32 := sext32U64 (centered.toUInt64 + brightness.toUInt64)
  (clampByteU64 sum32).toInt64

def evalYuv420pStudioRangeElem (sample isChroma : Int64) : Int64 :=
  let u := sample.toUInt64
  let upper : UInt64 := if isChroma.toUInt64 &&& 1 = 0 then 235 else 240
  (if u < 16 then 16 else if upper < u then upper else u).toInt64

def evalBt2020ToBt709UvElem (uPx vPx : Int64) : Int64 :=
  let cb := uPx.toUInt64 - 128
  let cr := vPx.toUInt64 - 128
  let neg74 : UInt64 := 18446744073709551542
  let neg42 : UInt64 := 18446744073709551574
  let uRaw := ((cb * 1004 + cr * neg74 + 512).toInt64 >>> 10).toUInt64 + 128
  let vRaw := ((cb * neg42 + cr * 986 + 512).toInt64 >>> 10).toUInt64 + 128
  let uOut := clampByteU64 uRaw
  let vOut := clampByteU64 vRaw
  ((vOut <<< 8) ||| uOut).toInt64

/--
  Formal denotational evaluator `evalLnirKernel` for `LnirKernelAst` over arbitrary-length streams `xs ys zs : List Int64`.
-/
def evalLnirKernel (k : LnirKernelAst) (xs ys zs : List Int64) : List Int64 :=
  match k with
  | .gainBias gain bias =>
    xs.map (fun x => x * gain + bias)
  | .dotPairwise =>
    List.zipWith (fun x y => x * y) xs ys
  | .saxpy alpha =>
    List.zipWith (fun x y => alpha * x + y) xs ys
  | .wiener3TapSym =>
    List.zipWith (fun s r => s + r * 3)
      (List.zipWith (fun l c => l * 3 + c * 10) xs ys)
      zs
  | .fmaBlend =>
    List.zipWith (fun p b => p + b) (List.zipWith (fun x y => x * y) xs ys) zs
  | .zipAdd =>
    List.zipWith (fun x y => x + y) xs ys
  | .zipMul =>
    List.zipWith (fun x y => x * y) xs ys
  | .mapScaleAdd scale bias =>
    xs.map (fun x => x * scale + bias)
  | .boxBlurDiv9Recip =>
    xs.map evalBoxBlurDiv9RecipElem
  | .pq10StudioClamp =>
    xs.map evalPq10StudioClampElem
  | .down2x2Box =>
    List.zipWith evalDown2x2BoxElem xs ys
  | .down3x3Box =>
    List.zipWith (fun p z => evalDown3x3BoxElem p.1 p.2 z) (List.zip xs ys) zs
  | .down3to2Bilinear =>
    List.zipWith evalDown3to2BilinearElem xs ys
  | .av1CdefDirFilter =>
    List.zipWith (fun p z => evalAv1CdefDirFilterElem p.1 p.2 z) (List.zip xs ys) zs
  | .extractU16LeMsb8 => xs.map evalExtractU16LeMsb8Elem
  | .lumaStatsMoments => xs.map evalLumaStatsMomentsElem
  | .lumaStatsPack => List.zipWith evalLumaStatsPackElem xs ys
  | .lumaAcceptanceAccum => List.zipWith evalLumaAcceptanceAccumElem xs ys
  | .lumaAcceptanceGate => List.zipWith (fun p z => evalLumaAcceptanceGateElem p.1 p.2 z) (List.zip xs ys) zs
  | .bilinearQ8Blend => List.zipWith (fun p z => evalBilinearQ8BlendElem p.1 p.2 z) (List.zip xs ys) zs
  | .bilinearQ8Pack => List.zipWith (fun p z => evalBilinearQ8PackElem p.1 p.2 z) (List.zip xs ys) zs
  | .bilinearQ8Clamp10 => xs.map evalBilinearQ8Clamp10Elem
  | .av1CdefTap => List.zipWith (fun p z => evalAv1CdefTapElem p.1 p.2 z) (List.zip xs ys) zs
  | .down2x2FusedEq => List.zipWith (fun p z => evalDown2x2FusedEqElem p.1 p.2 z) (List.zip xs ys) zs
  | .down2x2FusedBrightness => List.zipWith evalDown2x2FusedBrightnessElem xs ys
  | .yuv420pStudioRange => List.zipWith evalYuv420pStudioRangeElem xs ys
  | .bt2020ToBt709Uv => List.zipWith evalBt2020ToBt709UvElem xs ys

/-- Pure Lean reference specification for `swscale_luma_gain_bias_simd`. -/
def leanSpecSwscaleGainBias (plane : List Int64) (gain bias : Int64) : List Int64 :=
  plane.map (fun px => px * gain + bias)

/-- Pure Lean reference specification for `flac_lpc_autocorr_dot_simd`. -/
def leanSpecFlacLpcAutocorrDot (samplesLag0 samplesLagK : List Int64) : List Int64 :=
  List.zipWith (fun x y => x * y) samplesLag0 samplesLagK

/-- Pure Lean reference specification for `opus_celt_pvq_mix_saxpy_gpu` (`alpha = 4`). -/
def leanSpecOpusCeltSaxpy (midBand sideBand : List Int64) : List Int64 :=
  List.zipWith (fun m s => (4 : Int64) * m + s) midBand sideBand

/-- Pure Lean reference specification for `av1_wiener_3tap_sym_gpu` (`3 * l[i] + 10 * c[i] + 3 * r[i]`). -/
def leanSpecAv1Wiener3TapSym (tapLeft tapCenter tapRight : List Int64) : List Int64 :=
  List.zipWith (fun s r => s + r * 3)
    (List.zipWith (fun l c => l * 3 + c * 10) tapLeft tapCenter)
    tapRight

/-- Pure Lean reference specification for `av1_cdef_fma_blend_gpu`. -/
def leanSpecAv1CdefFma (priTap dirWeight srcPixel : List Int64) : List Int64 :=
  List.zipWith (fun prod base => prod + base) (List.zipWith (fun p w => p * w) priTap dirWeight) srcPixel

/-- Pure Lean reference specification for `h264_idct_tuple_accum_sroa` (`seqFor` over `0..blocks`). -/
def leanSpecH264IdctTupleAccumSroa (blocks : Nat) (dcInit : UInt64) : UInt64 :=
  (List.range blocks).foldl (fun acc i =>
    let iv := i.toUInt64
    let f0 := acc + iv
    let f1 := iv * 2
    f0 + f1) dcInit

/-- Pure Lean reference specification for `bframe_bipred_blend_gpu` (`1 * refL0[i] + refL1[i]`). -/
def leanSpecBframeBiPredBlend (refL0 refL1 : List Int64) : List Int64 :=
  List.zipWith (fun l0 l1 => (1 : Int64) * l0 + l1) refL0 refL1

/-- Pure Lean reference specification for `hevc_sao_band_offset_add_gpu` (`reconSample[i] + bandOffset[i]`). -/
def leanSpecHevcSaoBandOffsetAdd (reconSample bandOffset : List Int64) : List Int64 :=
  List.zipWith (fun r o => r + o) reconSample bandOffset

/-- Pure Lean reference specification for `aac_imdct_window_mul_gpu` (`mdctSpec[i] * kbdWindow[i]`). -/
def leanSpecAacImdctWindowMul (mdctSpec kbdWindow : List Int64) : List Int64 :=
  List.zipWith (fun m w => m * w) mdctSpec kbdWindow

/-- Pure Lean reference specification for `prores_qscale_map_simd` (`dctCoeff[i] * 16 + 8`). -/
def leanSpecProresQscaleMap (dctCoeff : List Int64) : List Int64 :=
  dctCoeff.map (fun c => c * 16 + 8)

/-- Pure Lean reference specification for `boxblur_div9_recip_shift_simd`. -/
def leanSpecBoxBlurDiv9Recip (sum9Plane : List Int64) : List Int64 :=
  sum9Plane.map evalBoxBlurDiv9RecipElem

/-- Pure Lean reference specification for `pq10_studio_clamp_select_simd`. -/
def leanSpecPq10StudioClamp (luma10Plane : List Int64) : List Int64 :=
  luma10Plane.map evalPq10StudioClampElem

/-- Pure Lean reference specification for `swscale_down2x2_box_simd`. -/
def leanSpecSwscaleDown2x2Box (row0PairSum row1PairSum : List Int64) : List Int64 :=
  List.zipWith evalDown2x2BoxElem row0PairSum row1PairSum

/-- Pure Lean reference specification for `swscale_down3x3_box_simd`. -/
def leanSpecSwscaleDown3x3Box (row0TriSum row1TriSum row2TriSum : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalDown3x3BoxElem p.1 p.2 z) (List.zip row0TriSum row1TriSum) row2TriSum

/-- Pure Lean reference specification for `swscale_down3to2_bilinear_simd`. -/
def leanSpecSwscaleDown3to2Bilinear (rowAHoriz rowBHoriz : List Int64) : List Int64 :=
  List.zipWith evalDown3to2BilinearElem rowAHoriz rowBHoriz

/-- Pure Lean reference specification for `av1_cdef_dir_filter_simd`. -/
def leanSpecAv1CdefDirFilter (centerPx tapPosSum tapNegSum : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalAv1CdefDirFilterElem p.1 p.2 z) (List.zip centerPx tapPosSum) tapNegSum

/-- Universal Theorem (Kernel 1): `evalLnirKernel (.gainBias gain bias)` equals `leanSpecSwscaleGainBias`. -/
theorem evalLnir_swscale_gain_bias_equiv (plane : List Int64) (gain bias : Int64) :
    evalLnirKernel (.gainBias gain bias) plane [] [] = leanSpecSwscaleGainBias plane gain bias :=
  rfl

/-- Universal Theorem (Kernel 2): `evalLnirKernel .dotPairwise` equals `leanSpecFlacLpcAutocorrDot`. -/
theorem evalLnir_flac_lpc_dot_equiv (samplesLag0 samplesLagK : List Int64) :
    evalLnirKernel .dotPairwise samplesLag0 samplesLagK [] =
      leanSpecFlacLpcAutocorrDot samplesLag0 samplesLagK :=
  rfl

/-- Universal Theorem (Kernel 3): `evalLnirKernel (.saxpy 4)` equals `leanSpecOpusCeltSaxpy`. -/
theorem evalLnir_opus_celt_saxpy_equiv (midBand sideBand : List Int64) :
    evalLnirKernel (.saxpy 4) midBand sideBand [] = leanSpecOpusCeltSaxpy midBand sideBand :=
  rfl

/-- Universal Theorem (Kernel 4): `evalLnirKernel .wiener3TapSym` equals `leanSpecAv1Wiener3TapSym`. -/
theorem evalLnir_av1_wiener_3tap_sym_equiv (tapLeft tapCenter tapRight : List Int64) :
    evalLnirKernel .wiener3TapSym tapLeft tapCenter tapRight =
      leanSpecAv1Wiener3TapSym tapLeft tapCenter tapRight :=
  rfl

/-- Universal Theorem (Kernel 5): `evalLnirKernel .fmaBlend` equals `leanSpecAv1CdefFma`. -/
theorem evalLnir_av1_cdef_fma_equiv (priTap dirWeight srcPixel : List Int64) :
    evalLnirKernel .fmaBlend priTap dirWeight srcPixel =
      leanSpecAv1CdefFma priTap dirWeight srcPixel :=
  rfl

/-- Universal Theorem (Kernel 7): `evalLnirKernel (.saxpy 1)` equals `leanSpecBframeBiPredBlend`. -/
theorem evalLnir_bframe_bipred_blend_equiv (refL0 refL1 : List Int64) :
    evalLnirKernel (.saxpy 1) refL0 refL1 [] = leanSpecBframeBiPredBlend refL0 refL1 :=
  rfl

/-- Universal Theorem (Kernel 8): `evalLnirKernel .zipAdd` equals `leanSpecHevcSaoBandOffsetAdd`. -/
theorem evalLnir_hevc_sao_band_offset_add_equiv (reconSample bandOffset : List Int64) :
    evalLnirKernel .zipAdd reconSample bandOffset [] =
      leanSpecHevcSaoBandOffsetAdd reconSample bandOffset :=
  rfl

/-- Universal Theorem (Kernel 9): `evalLnirKernel .zipMul` equals `leanSpecAacImdctWindowMul`. -/
theorem evalLnir_aac_imdct_window_mul_equiv (mdctSpec kbdWindow : List Int64) :
    evalLnirKernel .zipMul mdctSpec kbdWindow [] =
      leanSpecAacImdctWindowMul mdctSpec kbdWindow :=
  rfl

/-- Universal Theorem (Kernel 10): `evalLnirKernel (.mapScaleAdd 16 8)` equals `leanSpecProresQscaleMap`. -/
theorem evalLnir_prores_qscale_map_equiv (dctCoeff : List Int64) :
    evalLnirKernel (.mapScaleAdd 16 8) dctCoeff [] [] =
      leanSpecProresQscaleMap dctCoeff :=
  rfl

/-- Universal Theorem (Kernel 11): `evalLnirKernel .boxBlurDiv9Recip` equals `leanSpecBoxBlurDiv9Recip`. -/
theorem evalLnir_boxblur_div9_recip_equiv (sum9Plane : List Int64) :
    evalLnirKernel .boxBlurDiv9Recip sum9Plane [] [] =
      leanSpecBoxBlurDiv9Recip sum9Plane :=
  rfl

/-- Universal Theorem (Kernel 12): `evalLnirKernel .pq10StudioClamp` equals `leanSpecPq10StudioClamp`. -/
theorem evalLnir_pq10_studio_clamp_equiv (luma10Plane : List Int64) :
    evalLnirKernel .pq10StudioClamp luma10Plane [] [] =
      leanSpecPq10StudioClamp luma10Plane :=
  rfl

/-- Universal Theorem (Kernel 13): `evalLnirKernel .down2x2Box` equals `leanSpecSwscaleDown2x2Box`. -/
theorem evalLnir_swscale_down2x2_box_equiv (row0PairSum row1PairSum : List Int64) :
    evalLnirKernel .down2x2Box row0PairSum row1PairSum [] =
      leanSpecSwscaleDown2x2Box row0PairSum row1PairSum :=
  rfl

/-- Universal Theorem (Kernel 14): `evalLnirKernel .down3x3Box` equals `leanSpecSwscaleDown3x3Box`. -/
theorem evalLnir_swscale_down3x3_box_equiv (row0TriSum row1TriSum row2TriSum : List Int64) :
    evalLnirKernel .down3x3Box row0TriSum row1TriSum row2TriSum =
      leanSpecSwscaleDown3x3Box row0TriSum row1TriSum row2TriSum :=
  rfl

/-- Universal Theorem (Kernel 15): `evalLnirKernel .down3to2Bilinear` equals `leanSpecSwscaleDown3to2Bilinear`. -/
theorem evalLnir_swscale_down3to2_bilinear_equiv (rowAHoriz rowBHoriz : List Int64) :
    evalLnirKernel .down3to2Bilinear rowAHoriz rowBHoriz [] =
      leanSpecSwscaleDown3to2Bilinear rowAHoriz rowBHoriz :=
  rfl

/-- Universal Theorem (Kernel 16): `evalLnirKernel .av1CdefDirFilter` equals `leanSpecAv1CdefDirFilter`. -/
theorem evalLnir_av1_cdef_dir_filter_equiv (centerPx tapPosSum tapNegSum : List Int64) :
    evalLnirKernel .av1CdefDirFilter centerPx tapPosSum tapNegSum =
      leanSpecAv1CdefDirFilter centerPx tapPosSum tapNegSum :=
  rfl

def leanSpecExtractU16LeMsb8 (samples : List Int64) : List Int64 :=
  samples.map evalExtractU16LeMsb8Elem

def leanSpecLumaStatsMoments (samples : List Int64) : List Int64 :=
  samples.map evalLumaStatsMomentsElem

def leanSpecLumaStatsPack (moments counts : List Int64) : List Int64 :=
  List.zipWith evalLumaStatsPackElem moments counts

def leanSpecLumaAcceptanceAccum (source reconstructed : List Int64) : List Int64 :=
  List.zipWith evalLumaAcceptanceAccumElem source reconstructed

def leanSpecLumaAcceptanceGate (sad blackSum refSum : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalLumaAcceptanceGateElem p.1 p.2 z) (List.zip sad blackSum) refSum

def leanSpecBilinearQ8Blend (p00 p01 fx : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalBilinearQ8BlendElem p.1 p.2 z) (List.zip p00 p01) fx

def leanSpecBilinearQ8Pack (top bottom fy : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalBilinearQ8PackElem p.1 p.2 z) (List.zip top bottom) fy

def leanSpecBilinearQ8Clamp10 (samples : List Int64) : List Int64 :=
  samples.map evalBilinearQ8Clamp10Elem

def leanSpecAv1CdefTap (neighbor center strength : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalAv1CdefTapElem p.1 p.2 z) (List.zip neighbor center) strength

def leanSpecDown2x2FusedEq (r0 r1 contrastQ8 : List Int64) : List Int64 :=
  List.zipWith (fun p z => evalDown2x2FusedEqElem p.1 p.2 z) (List.zip r0 r1) contrastQ8

def leanSpecDown2x2FusedBrightness (centered brightness : List Int64) : List Int64 :=
  List.zipWith evalDown2x2FusedBrightnessElem centered brightness

def leanSpecYuv420pStudioRange (samples isChroma : List Int64) : List Int64 :=
  List.zipWith evalYuv420pStudioRangeElem samples isChroma

def leanSpecBt2020ToBt709Uv (uPlane vPlane : List Int64) : List Int64 :=
  List.zipWith evalBt2020ToBt709UvElem uPlane vPlane

theorem evalLnir_extract_u16le_msb8_equiv (samples : List Int64) :
    evalLnirKernel .extractU16LeMsb8 samples [] [] = leanSpecExtractU16LeMsb8 samples := rfl

theorem evalLnir_luma_stats_moments_equiv (samples : List Int64) :
    evalLnirKernel .lumaStatsMoments samples [] [] = leanSpecLumaStatsMoments samples := rfl

theorem evalLnir_luma_stats_pack_equiv (moments counts : List Int64) :
    evalLnirKernel .lumaStatsPack moments counts [] = leanSpecLumaStatsPack moments counts := rfl

theorem evalLnir_luma_acceptance_accum_equiv (source reconstructed : List Int64) :
    evalLnirKernel .lumaAcceptanceAccum source reconstructed [] = leanSpecLumaAcceptanceAccum source reconstructed := rfl

theorem evalLnir_luma_acceptance_gate_equiv (sad blackSum refSum : List Int64) :
    evalLnirKernel .lumaAcceptanceGate sad blackSum refSum = leanSpecLumaAcceptanceGate sad blackSum refSum := rfl

theorem evalLnir_bilinear_q8_blend_equiv (p00 p01 fx : List Int64) :
    evalLnirKernel .bilinearQ8Blend p00 p01 fx = leanSpecBilinearQ8Blend p00 p01 fx := rfl

theorem evalLnir_bilinear_q8_pack_equiv (top bottom fy : List Int64) :
    evalLnirKernel .bilinearQ8Pack top bottom fy = leanSpecBilinearQ8Pack top bottom fy := rfl

theorem evalLnir_bilinear_q8_clamp10_equiv (samples : List Int64) :
    evalLnirKernel .bilinearQ8Clamp10 samples [] [] = leanSpecBilinearQ8Clamp10 samples := rfl

theorem evalLnir_av1_cdef_tap_equiv (neighbor center strength : List Int64) :
    evalLnirKernel .av1CdefTap neighbor center strength = leanSpecAv1CdefTap neighbor center strength := rfl

theorem evalLnir_down2x2_fused_eq_equiv (r0 r1 contrastQ8 : List Int64) :
    evalLnirKernel .down2x2FusedEq r0 r1 contrastQ8 = leanSpecDown2x2FusedEq r0 r1 contrastQ8 := rfl

theorem evalLnir_down2x2_fused_brightness_equiv (centered brightness : List Int64) :
    evalLnirKernel .down2x2FusedBrightness centered brightness [] = leanSpecDown2x2FusedBrightness centered brightness := rfl

theorem evalLnir_yuv420p_studio_range_equiv (samples isChroma : List Int64) :
    evalLnirKernel .yuv420pStudioRange samples isChroma [] = leanSpecYuv420pStudioRange samples isChroma := rfl

theorem evalLnir_bt2020_to_bt709_uv_equiv (uPlane vPlane : List Int64) :
    evalLnirKernel .bt2020ToBt709Uv uPlane vPlane [] = leanSpecBt2020ToBt709Uv uPlane vPlane := rfl

/-- Theorem: Typed `LnirKernelAst.toWireTokens` matches the exact wire tokens emitted in `emitLeanAvLnirWire`. -/
theorem lnirKernelAst_wire_tokens_match :
    (LnirKernelAst.saxpy 4).toWireTokens = ["K_saxpy", "4"] ∧
    LnirKernelAst.dotPairwise.toWireTokens = ["K_dot"] ∧
    LnirKernelAst.zipAdd.toWireTokens = ["K_za"] ∧
    LnirKernelAst.zipMul.toWireTokens = ["K_zm"] ∧
    (LnirKernelAst.mapScaleAdd 16 8).toWireTokens = ["K_msa", "16", "8"] := by
  decide

/-! ## Formal Scalar `lnir_px_*` Specifications & Tight Equivalence Theorems -/

/-- Formal evaluator for `@lnir_px_down2x2(sum4)`. -/
@[inline]
def specLnirPxDown2x2 (sum4 : UInt64) : UInt64 :=
  (sum4 + 2) >>> 2

/-- Formal evaluator for `@lnir_px_down2x2_fused_eq_u8(sum4, contrastQ8, brightness)`. -/
def specLnirPxDown2x2FusedEqU8 (sum4 contrastQ8 brightness : UInt64) : UInt64 :=
  let avg := (sum4 + 2) >>> 2
  let centered := avg - 128
  let prod32 := sext32U64 (centered * contrastQ8 + 128)
  let shifted := (prod32.toInt64 >>> 8).toUInt64
  let sum32 := sext32U64 (shifted + 128 + brightness)
  clampByteU64 sum32

/-- Formal evaluator for `@lnir_px_down3x3_u8(sum9)`. -/
@[inline]
def specLnirPxDown3x3U8 (sum9 : UInt64) : UInt64 :=
  ((sum9 + 4) * 7282) >>> 16

/-- Formal evaluator for `@lnir_px_down3x3_u16(sum9)`. -/
@[inline]
def specLnirPxDown3x3U16 (sum9 : UInt64) : UInt64 :=
  (sum9 + 4) / 9

/-- Formal evaluator for `@lnir_px_down3to2_u8(p00, p01, p10, p11, oddX, oddY)`. -/
def specLnirPxDown3to2U8 (p00 p01 p10 p11 oddX oddY : UInt64) : UInt64 :=
  let rowA := if (oddX &&& 1) != 0 then p00 + (p01 <<< 1) else (p00 <<< 1) + p01
  let rowB := if (oddX &&& 1) != 0 then p10 + (p11 <<< 1) else (p10 <<< 1) + p11
  let sum9 := if (oddY &&& 1) != 0 then rowA + (rowB <<< 1) else (rowA <<< 1) + rowB
  ((sum9 + 4) * 7282) >>> 16

/-- Formal evaluator for `@lnir_px_down3to2_u16_clamp10(colA, colB)`. -/
@[inline]
def specLnirPxDown3to2U16Clamp10 (colA colB : UInt64) : UInt64 :=
  let avg := (colA + colB + 2) >>> 2
  if 1023 < avg then 1023 else avg

/-- Formal evaluator for `@lnir_px_av1_cdef_tap(neighbor, center, priStr, damping)`. -/
def specLnirPxAv1CdefTap (neighbor center priStr damping : UInt64) : UInt64 :=
  let str := priStr &&& 2147483647
  let dmp := damping &&& 4294967295
  let shift := (if 0 < dmp then dmp else 1) &&& 31
  let ad := if center ≤ neighbor then neighbor - center else center - neighbor
  let shifted := ad >>> shift
  let mag :=
    if str ≤ shifted then 0
    else if ad ≤ str - shifted then ad
    else str - shifted
  if center ≤ neighbor then mag else 0 - mag

/-- Formal evaluator for `@lnir_px_av1_cdef_filter4_u8(px, c0, c1, c2, c3)`. -/
def specLnirPxAv1CdefFilter4U8 (px c0 c1 c2 c3 : UInt64) : UInt64 :=
  let sum := (c0 + c1) + (c2 + c3)
  let delta := ((sum + 2).toInt64 >>> 2).toUInt64
  clampByteU64 (px + delta)

/-- Formal evaluator for `@lnir_px_bilinear_q8(p00, p01, p10, p11, fx, fy)`. -/
def specLnirPxBilinearQ8 (p00 p01 p10 p11 fx fy : UInt64) : UInt64 :=
  let ifx := 256 - fx
  let ify := 256 - fy
  let top := p00 * ifx + p01 * fx
  let bot := p10 * ifx + p11 * fx
  (top * ify + bot * fy + 32768) >>> 16

/-- Formal evaluator for `@lnir_px_bilinear_q8_clamp10(p00, p01, p10, p11, fx, fy)`. -/
def specLnirPxBilinearQ8Clamp10 (p00 p01 p10 p11 fx fy : UInt64) : UInt64 :=
  let raw := specLnirPxBilinearQ8 p00 p01 p10 p11 fx fy
  if 1023 < raw then 1023 else raw

/-- Formal evaluator for `@lnir_px_extract_u16le_msb8(sample)`. -/
@[inline]
def specLnirPxExtractU16LeMsb8 (sample : UInt64) : UInt64 :=
  (sample >>> 2) &&& 255

/-- Formal evaluator for `@lnir_px_u16le_to_u10(sample)`. -/
@[inline]
def specLnirPxU16LeToU10 (sample : UInt64) : UInt64 :=
  sample >>> 2

/-- Formal evaluator for `@lnir_px_luma_stats_pack(sum, sumSq, count)` (zero-safe `B_div`). -/
def specLnirPxLumaStatsPack (sum sumSq count : UInt64) : UInt64 :=
  let mean := if count == 0 then 0 else sum / count
  let meanSq := if count == 0 then 0 else sumSq / count
  let sq := mean * mean
  let var := if sq < meanSq then meanSq - sq else 0
  (var <<< 32) ||| (mean &&& 4294967295)

/-- Formal evaluator for `@lnir_px_luma_acceptance_accum(refPx, dstPx)`. -/
def specLnirPxLumaAcceptanceAccum (refPx dstPx : UInt64) : UInt64 :=
  let ad := if dstPx ≤ refPx then refPx - dstPx else dstPx - refPx
  let black := if 16 ≤ refPx then refPx - 16 else 16 - refPx
  let sse := ad * ad
  ad ||| (black <<< 16) ||| (refPx <<< 32) ||| (sse <<< 48)

/-- Formal evaluator for `@lnir_px_luma_acceptance_gate(sad, blackSum, refSum, oldOk)`. -/
@[inline]
def specLnirPxLumaAcceptanceGate (sad blackSum refSum oldOk : UInt64) : UInt64 :=
  if 6144 ≤ refSum then
    if blackSum ≤ sad then 0 else oldOk
  else oldOk

/-- Formal evaluator for `@lnir_px_y_studio_clamp_u8(y)`. -/
@[inline]
def specLnirPxYStudioClampU8 (y : UInt64) : UInt64 :=
  if y < 16 then 16 else if 235 < y then 235 else y

/-- Formal evaluator for `@lnir_px_bt2020_to_bt709_uv_u8(uPx, vPx)`. -/
def specLnirPxBt2020ToBt709UvU8 (uPx vPx : UInt64) : UInt64 :=
  let u0 := uPx - 128
  let v0 := vPx - 128
  let neg74 : UInt64 := 0 - 74
  let neg42 : UInt64 := 0 - 42
  let uRaw := (((u0 * 1004 + v0 * neg74 + 512).toInt64 >>> 10).toUInt64) + 128
  let vRaw := (((u0 * neg42 + v0 * 986 + 512).toInt64 >>> 10).toUInt64) + 128
  let uOut := clampByteU64 uRaw
  let vOut := clampByteU64 vRaw
  (vOut <<< 8) ||| uOut

/-- Universal Theorem: Scalar `@lnir_px_down2x2` refines `(r0 + r1 + 2) >>> 2` (`evalDown2x2BoxElem`). -/
theorem specLnirPxDown2x2_eq_evalDown2x2Box (r0 r1 : Int64) :
    (specLnirPxDown2x2 (r0.toUInt64 + r1.toUInt64)).toInt64 = evalDown2x2BoxElem r0 r1 :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_down3x3_u8` refines `evalBoxBlurDiv9RecipElem`. -/
theorem specLnirPxDown3x3U8_eq_evalBoxBlurDiv9 (sum9 : Int64) :
    (specLnirPxDown3x3U8 sum9.toUInt64).toInt64 = evalBoxBlurDiv9RecipElem sum9 :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_down3x3_u16` matches exact `/ 9` rounding for all `sum9 ≤ 9 * 65535`. -/
theorem specLnirPxDown3x3U16_exact_div9 (sum9 : UInt64) (h : sum9 ≤ 589815) :
    (specLnirPxDown3x3U16 sum9).toNat = (sum9.toNat + 4) / 9 := by
  have hlt : sum9.toNat ≤ 589815 := h
  unfold specLnirPxDown3x3U16
  rw [UInt64.toNat_div, UInt64.toNat_add]
  change ((sum9.toNat + 4) % 18446744073709551616) / 9 = (sum9.toNat + 4) / 9
  omega

/-- Universal Theorem: `clampByteU64` always produces a value `≤ 255`. -/
theorem clampByteU64_le_255 (x : UInt64) : clampByteU64 x ≤ 255 := by
  unfold clampByteU64
  split
  · assumption
  · split
    · decide
    · decide

/-- Universal Theorem: Scalar `@lnir_px_down2x2_fused_eq_u8` composes `evalDown2x2FusedEqElem`
    with `evalDown2x2FusedBrightnessElem`, preserves `128`, and is `≤ 255`. -/
theorem specLnirPxDown2x2FusedEqU8_midpoint_and_bounded (r0 r1 contrastQ8 brightness : UInt64) :
    (specLnirPxDown2x2FusedEqU8 (r0 + r1) contrastQ8 brightness).toInt64 =
      evalDown2x2FusedBrightnessElem
        (evalDown2x2FusedEqElem r0.toInt64 r1.toInt64 contrastQ8.toInt64)
        brightness.toInt64 ∧
    specLnirPxDown2x2FusedEqU8 512 256 0 = 128 ∧
    specLnirPxDown2x2FusedEqU8 (r0 + r1) contrastQ8 brightness ≤ 255 := by
  refine ⟨rfl, by decide, ?_⟩
  unfold specLnirPxDown2x2FusedEqU8
  exact clampByteU64_le_255 _

private theorem uint64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

private theorem toInt64_toUInt64_id (x : UInt64) : x.toInt64.toUInt64 = x :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_down3to2_u8` refines `evalDown3to2BilinearElem` on even and odd X coordinates. -/
theorem specLnirPxDown3to2U8_even_eq_evalDown3to2 (p00 p01 p10 p11 : UInt64) :
    (specLnirPxDown3to2U8 p00 p01 p10 p11 0 0).toInt64 =
      evalDown3to2BilinearElem ((p00 <<< 1) + p01).toInt64 ((p10 <<< 1) + p11).toInt64 ∧
    (specLnirPxDown3to2U8 p00 p01 p10 p11 1 0).toInt64 =
      evalDown3to2BilinearElem (p00 + (p01 <<< 1)).toInt64 (p10 + (p11 <<< 1)).toInt64 := by
  have h2 (x : UInt64) : x <<< 1 = x * 2 := by
    apply uint64_eq_of_toNat
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
    change (x.toNat <<< 1) % 18446744073709551616 = (x.toNat * 2) % 18446744073709551616
    rw [Nat.shiftLeft_eq]
  have hc0 : ((0 : UInt64) &&& 1 != 0) = false := by decide
  have hc1 : ((1 : UInt64) &&& 1 != 0) = true := by decide
  unfold specLnirPxDown3to2U8 evalDown3to2BilinearElem
  simp only [hc0, hc1, Bool.false_eq_true, ↓reduceIte, toInt64_toUInt64_id, h2]
  exact ⟨trivial, trivial⟩

/-- Universal Theorem: Scalar `@lnir_px_down3to2_u16_clamp10` refines 2x2 shift-average with 10-bit clamping. -/
theorem specLnirPxDown3to2U16Clamp10_eq_clamp (colA colB : Int64) :
    (specLnirPxDown3to2U16Clamp10 colA.toUInt64 colB.toUInt64).toInt64 =
      evalBilinearQ8Clamp10Elem (evalDown2x2BoxElem colA colB) :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_bilinear_q8` composes `evalBilinearQ8BlendElem` and `evalBilinearQ8PackElem`. -/
theorem specLnirPxBilinearQ8_composes_blend_and_pack (p00 p01 p10 p11 fx fy : Int64) :
    (specLnirPxBilinearQ8 p00.toUInt64 p01.toUInt64 p10.toUInt64
      p11.toUInt64 fx.toUInt64 fy.toUInt64).toInt64 =
      evalBilinearQ8PackElem (evalBilinearQ8BlendElem p00 p01 fx)
        (evalBilinearQ8BlendElem p10 p11 fx) fy := by
  unfold specLnirPxBilinearQ8 evalBilinearQ8BlendElem evalBilinearQ8PackElem
  rfl

/-- Universal Theorem: Scalar `@lnir_px_bilinear_q8_clamp10` composes `specLnirPxBilinearQ8` with 10-bit clamping. -/
theorem specLnirPxBilinearQ8Clamp10_eq_clamp (p00 p01 p10 p11 fx fy : UInt64) :
    (specLnirPxBilinearQ8Clamp10 p00 p01 p10 p11 fx fy).toInt64 =
      evalBilinearQ8Clamp10Elem (specLnirPxBilinearQ8 p00 p01 p10 p11 fx fy).toInt64 := by
  unfold specLnirPxBilinearQ8Clamp10 evalBilinearQ8Clamp10Elem
  rfl

/-- Universal Theorem: Scalar `@lnir_px_extract_u16le_msb8` refines `evalExtractU16LeMsb8Elem`. -/
theorem specLnirPxExtractU16LeMsb8_eq_eval (sample : Int64) :
    (specLnirPxExtractU16LeMsb8 sample.toUInt64).toInt64 = evalExtractU16LeMsb8Elem sample :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_u16le_to_u10` preserves all 8 low bits matched by `specLnirPxExtractU16LeMsb8`. -/
theorem specLnirPxU16LeToU10_low8_eq_msb8 (sample : UInt64) :
    (specLnirPxU16LeToU10 sample) &&& 255 = specLnirPxExtractU16LeMsb8 sample :=
  rfl

/-- Universal Theorem: Scalar `@lnir_px_luma_stats_pack` returns `0` when `count = 0`
    and refines `evalLumaStatsPackElem` on 32-bit moments. -/
theorem specLnirPxLumaStatsPack_zero_and_moments (moments count : UInt64) (hPos : count ≠ 0) :
    specLnirPxLumaStatsPack moments moments 0 = 0 ∧
    (specLnirPxLumaStatsPack (moments &&& 0xFFFFFFFF) (moments >>> 32) count).toInt64 =
      evalLumaStatsPackElem moments.toInt64 count.toInt64 := by
  have hBeq : (count == 0) = false := beq_false_of_ne hPos
  constructor
  · simp [specLnirPxLumaStatsPack]
  · unfold specLnirPxLumaStatsPack evalLumaStatsPackElem
    simp [hBeq]

/-- Universal Theorem: Scalar `@lnir_px_luma_acceptance_accum` refines `evalLumaAcceptanceAccumElem`. -/
theorem specLnirPxLumaAcceptanceAccum_eq_eval (refPx dstPx : UInt64) :
    (specLnirPxLumaAcceptanceAccum refPx dstPx).toInt64 =
      evalLumaAcceptanceAccumElem refPx.toInt64 dstPx.toInt64 := by
  exact rfl

/-- Universal Theorem: Scalar `@lnir_px_luma_acceptance_gate` preserves `0` failure and matches block rejection when `oldOk = 1`. -/
theorem specLnirPxLumaAcceptanceGate_sound (sad blackSum refSum : UInt64) :
    specLnirPxLumaAcceptanceGate sad blackSum refSum 0 = 0 ∧
    (specLnirPxLumaAcceptanceGate sad blackSum refSum 1 = 0 ↔
      6144 ≤ refSum ∧ blackSum ≤ sad) := by
  unfold specLnirPxLumaAcceptanceGate
  constructor
  · split
    · split
      · rfl
      · rfl
    · rfl
  · by_cases h1 : 6144 ≤ refSum
    · by_cases h2 : blackSum ≤ sad
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]

/-- Universal Theorem: Scalar `@lnir_px_y_studio_clamp_u8` refines luma `evalYuv420pStudioRangeElem`. -/
theorem specLnirPxYStudioClampU8_eq_eval (y : Int64) :
    (specLnirPxYStudioClampU8 y.toUInt64).toInt64 = evalYuv420pStudioRangeElem y 0 := by
  unfold specLnirPxYStudioClampU8 evalYuv420pStudioRangeElem
  have h0 : ((0 : Int64).toUInt64 &&& 1 = 0) := by decide
  simp [h0]

private theorem nat_or_mul_pow2 {a b k : Nat} (ha : a < 2 ^ k) :
    (b * (2 ^ k) ||| a) = b * (2 ^ k) + a := by
  induction k generalizing a b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]
      omega
    have hmul : b * 2 ^ (k + 1) = (b * 2 ^ k) * 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    have hdiv : a / 2 < 2 ^ k := by
      rw [hpow] at ha
      omega
    have hBit : ((b * 2 ^ (k + 1) ||| a) % 2) = ((b * 2 ^ (k + 1) + a) % 2) := by
      have hev : (b * 2 ^ (k + 1)) % 2 = 0 := by
        rw [hmul]
        omega
      by_cases hodd : a % 2 = 1
      · have hsum : (b * 2 ^ (k + 1) + a) % 2 = 1 := by omega
        have hor : (b * 2 ^ (k + 1) ||| a) % 2 = 1 := by
          rw [Nat.or_mod_two_eq_one]
          exact Or.inr hodd
        omega
      · have ha0 : a % 2 = 0 := by omega
        have hsum : (b * 2 ^ (k + 1) + a) % 2 = 0 := by omega
        have hor : ¬((b * 2 ^ (k + 1) ||| a) % 2 = 1) := by
          rw [Nat.or_mod_two_eq_one]
          omega
        omega
    have hHalf : (b * 2 ^ (k + 1) ||| a) / 2 = (b * 2 ^ (k + 1) + a) / 2 := by
      change (b * 2 ^ (k + 1) ||| a) >>> 1 = _
      rw [Nat.shiftRight_or_distrib]
      simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      have hb2 : (b * 2 ^ (k + 1)) / 2 = b * 2 ^ k := by
        rw [hmul]
        omega
      rw [hb2, ih hdiv, hmul]
      omega
    omega

/-- Universal Theorem: Scalar `@lnir_px_av1_cdef_tap` refines `evalAv1CdefTapElem`
    across all parameterized `(damping <<< 32) | priStr` lanes. -/
theorem specLnirPxAv1CdefTap_eq_eval (neighbor center priStr damping : UInt64)
    (hStr : priStr < 2147483648) (hDamp : damping < 4294967296) :
    (specLnirPxAv1CdefTap neighbor center priStr damping).toInt64 =
      evalAv1CdefTapElem neighbor.toInt64 center.toInt64 (((damping <<< 32) ||| priStr).toInt64) := by
  have hdNat : damping.toNat < 4294967296 := hDamp
  have hsNat : priStr.toNat < 2147483648 := hStr
  have hMod : (damping.toNat <<< 32) % 18446744073709551616 = damping.toNat * 4294967296 := by
    rw [Nat.shiftLeft_eq]
    change (damping.toNat * 4294967296) % 18446744073709551616 = damping.toNat * 4294967296
    exact Nat.mod_eq_of_lt (by omega)
  have hOr : ((damping.toNat * 4294967296) ||| priStr.toNat) = damping.toNat * 4294967296 + priStr.toNat := by
    exact nat_or_mul_pow2 (k := 32) (by omega)
  have h1 : (((damping <<< 32) ||| priStr) &&& 2147483647) = (priStr &&& 2147483647) := by
    apply uint64_eq_of_toNat
    change (((damping.toNat <<< 32) % 18446744073709551616 ||| priStr.toNat) &&& (2 ^ 31 - 1)) =
      (priStr.toNat &&& (2 ^ 31 - 1))
    rw [hMod, hOr, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    change (damping.toNat * 4294967296 + priStr.toNat) % 2147483648 = priStr.toNat % 2147483648
    omega
  have h2 : (((damping <<< 32) ||| priStr) >>> 32) = (damping &&& 4294967295) := by
    apply uint64_eq_of_toNat
    change (((damping.toNat <<< 32) % 18446744073709551616 ||| priStr.toNat) >>> 32) =
      (damping.toNat &&& (2 ^ 32 - 1))
    rw [hMod, hOr, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    change (damping.toNat * 4294967296 + priStr.toNat) / 4294967296 = damping.toNat % 4294967296
    omega
  unfold specLnirPxAv1CdefTap evalAv1CdefTapElem
  dsimp only
  simp only [toInt64_toUInt64_id, h1, h2]
  rfl

/-- Universal Theorem: Scalar `@lnir_px_av1_cdef_filter4_u8` is bounded in `[0, 255]` and preserves `px ≤ 255` under zero taps. -/
theorem specLnirPxAv1CdefFilter4U8_zero_and_bounded (px c0 c1 c2 c3 : UInt64) (hPx : px ≤ 255) :
    specLnirPxAv1CdefFilter4U8 px 0 0 0 0 = px ∧
    specLnirPxAv1CdefFilter4U8 px c0 c1 c2 c3 ≤ 255 := by
  constructor
  · have hz : (((((0 : UInt64) + 0) + (0 + 0) + 2).toInt64 >>> 2).toUInt64) = 0 := by decide
    unfold specLnirPxAv1CdefFilter4U8
    dsimp only
    rw [hz, UInt64.add_zero]
    unfold clampByteU64
    simp [hPx]
  · unfold specLnirPxAv1CdefFilter4U8
    exact clampByteU64_le_255 _

/-- Universal Theorem: Scalar `@lnir_px_bt2020_to_bt709_uv_u8` refines `evalBt2020ToBt709UvElem`,
    maps `(128, 128)` to `0x8080`, and fits in 16 bits. -/
theorem specLnirPxBt2020ToBt709UvU8_neutral_and_bounded (uPx vPx : UInt64) :
    (specLnirPxBt2020ToBt709UvU8 uPx vPx).toInt64 =
      evalBt2020ToBt709UvElem uPx.toInt64 vPx.toInt64 ∧
    specLnirPxBt2020ToBt709UvU8 128 128 = 0x8080 ∧
    (specLnirPxBt2020ToBt709UvU8 uPx vPx >>> 16) = 0 := by
  refine ⟨rfl, by decide, ?_⟩
  have hPack (uOut vOut : UInt64) (hu : uOut ≤ 255) (hv : vOut ≤ 255) :
      (((vOut <<< 8) ||| uOut) >>> 16) = 0 := by
    have huN : uOut.toNat ≤ 255 := hu
    have hvN : vOut.toNat ≤ 255 := hv
    apply uint64_eq_of_toNat
    change (((vOut.toNat <<< 8) % 18446744073709551616 ||| uOut.toNat) >>> 16) = 0
    have hMod : (vOut.toNat <<< 8) % 18446744073709551616 = vOut.toNat * 256 := by
      rw [Nat.shiftLeft_eq]
      change (vOut.toNat * 256) % 18446744073709551616 = vOut.toNat * 256
      exact Nat.mod_eq_of_lt (by omega)
    have hOr : (vOut.toNat * 256 ||| uOut.toNat) = vOut.toNat * 256 + uOut.toNat := by
      exact nat_or_mul_pow2 (k := 8) (by omega)
    rw [hMod, hOr, Nat.shiftRight_eq_div_pow]
    change (vOut.toNat * 256 + uOut.toNat) / 65536 = 0
    omega
  unfold specLnirPxBt2020ToBt709UvU8
  dsimp only
  exact hPack _ _ (clampByteU64_le_255 _) (clampByteU64_le_255 _)


/-! ## Exact Pixel & Reciprocal Arithmetic Refinements (2x2 Box, 3x3 Box, 4-Tap Lanczos) -/

/-- Pure Lean 2x2 box-average pixel formula `((p00 + p01 + p10 + p11 + 2) / 4)` for 4K -> 1080p downscaling. -/
@[inline]
def specBox2x2DownscalePixel (p00 p01 p10 p11 : Nat) : Nat :=
  (p00 + p01 + p10 + p11 + 2) / 4

/-- Fast shift-based 2x2 box-average pixel formula `(p00 + p01 + p10 + p11 + 2) >>> 2`. -/
@[inline]
def fastBox2x2DownscalePixel (p00 p01 p10 p11 : Nat) : Nat :=
  (p00 + p01 + p10 + p11 + 2) >>> 2

/-- Universal Theorem: Fast bitwise shift `fastBox2x2DownscalePixel` is universally equal
    to `specBox2x2DownscalePixel` (`(a + b + c + d + 2) / 4`). -/
theorem fastBox2x2DownscalePixel_eq_spec :
    @specBox2x2DownscalePixel = @fastBox2x2DownscalePixel := by
  funext p00 p01 p10 p11
  unfold specBox2x2DownscalePixel fastBox2x2DownscalePixel
  rw [Nat.shiftRight_eq_div_pow]

/-- Universal Theorem: 2x2 box downscaling is idempotent on constant-luminance blocks. -/
theorem specBox2x2DownscalePixel_idempotent_const (v : Nat) :
    specBox2x2DownscalePixel v v v v = v := by
  unfold specBox2x2DownscalePixel
  omega

/-- Universal Theorem: For any 8-bit pixels `p00, p01, p10, p11 ≤ 255`,
    the 2x2 box downscaled pixel `specBox2x2DownscalePixel p00 p01 p10 p11 ≤ 255` never overflows `UInt8`. -/
theorem specBox2x2DownscalePixel_bounds_u8 (p00 p01 p10 p11 : Nat)
    (h00 : p00 ≤ 255) (h01 : p01 ≤ 255) (h10 : p10 ≤ 255) (h11 : p11 ≤ 255) :
    specBox2x2DownscalePixel p00 p01 p10 p11 ≤ 255 := by
  unfold specBox2x2DownscalePixel
  omega

/-- Universal Theorem: Replacing integer division `/ 9` with multiply-shift `((sum + 4) * 7282) >>> 16`
    is bit-exactly equal to `(sum + 4) / 9` for all 9-pixel 8-bit neighborhood sums `sum ≤ 9 * 255 = 2295`. -/
theorem fastBoxBlurDiv9_eq_spec (sum : Nat) (h : sum ≤ 2295) :
    ((sum + 4) * 7282) >>> 16 = (sum + 4) / 9 := by
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- Pure Lean normalized 4-tap symmetric filter formula `((9 * (p1 + p2) + 8 - (p0 + p3)) / 16)`
    (Catmull-Rom / 4-tap Lanczos integer approximation with weights `[-1, 9, 9, -1] / 16`). -/
@[inline]
def specLanczos4TapNormalizedPixel (p0 p1 p2 p3 : Nat) : Nat :=
  (9 * (p1 + p2) + 8 - (p0 + p3)) / 16

/-- Universal Theorem: The normalized 4-tap symmetric filter `[-1, 9, 9, -1] / 16`
    is idempotent on any uniform constant pixel `v : Nat`. -/
theorem specLanczos4TapNormalizedPixel_idempotent_const (v : Nat) :
    specLanczos4TapNormalizedPixel v v v v = v := by
  unfold specLanczos4TapNormalizedPixel
  omega

/-- Pure Lean 10-bit (`[0, 1023]`) 3x3 box-average pixel formula `(sum9 + 4) / 9` for 4K -> 720p HDR10 scaling. -/
@[inline]
def specBox3x3DownscaleU10Sum (sum9 : Nat) : Nat :=
  (sum9 + 4) / 9

/-- Fast reciprocal multiply-shift `((sum9 + 4) * 7282) >>> 16` for 10-bit 3x3 box-average (`sum9 ≤ 9 * 1023 = 9207`). -/
@[inline]
def fastBox3x3DownscaleU10Sum (sum9 : Nat) : Nat :=
  ((sum9 + 4) * 7282) >>> 16

/-- Universal Theorem: For all 9-pixel 10-bit neighborhood sums `sum9 ≤ 9 * 1023 = 9207`,
    the reciprocal multiply-shift `fastBox3x3DownscaleU10Sum sum9` is bit-exactly equal to `(sum9 + 4) / 9`
    and never exceeds 1023 (`≤ 1023`). -/
theorem fastBox3x3DownscaleU10Sum_eq_spec_and_bounded (sum9 : Nat) (h : sum9 ≤ 9207) :
    fastBox3x3DownscaleU10Sum sum9 = specBox3x3DownscaleU10Sum sum9 ∧
    specBox3x3DownscaleU10Sum sum9 ≤ 1023 := by
  unfold fastBox3x3DownscaleU10Sum specBox3x3DownscaleU10Sum
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-! ## Certified LNIR Kernel Descriptor Bounds & Aliasing Checker (`checkLnirKernel`, `checkLnirKernel_sound`) -/

/--
  Flat (non-dependent) LNIR 2D/SIMD Kernel Contract Descriptor (`LnirKernelDescriptor`):
  - Carries explicit numeric bounds (`width`, `height`, `bytesPerSample`, `srcStride`, `dstStride`,
    `srcCap`, `dstCap`, `simdVecBytes`, `srcBufId`, `dstBufId`, `inPlaceAllowed`, `dstExclusiveRc1`).
  - Validated by decidable checker `checkLnirKernel : LnirKernelDescriptor → Bool` before code emission,
    with `checkLnirKernel_sound` proving `checkLnirKernel k = true → LnirKernelMemSafe k`.
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
  4. Destination buffer has exclusive ownership (`dstExclusiveRc1 = true`) and never aliases `srcBufId`
     unless `inPlaceAllowed = true`.
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

/-- Decidable LNIR Translation Validation Checker (`checkLnirKernel`). -/
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

/-- Universal Theorem (`checkLnirKernel_sound`):
    If `checkLnirKernel k = true`, then `LnirKernelMemSafe k` holds universally (`∀ x < k.width, ∀ y < k.height`). -/
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

/-- Zero-copy `ByteArray` (`lean_sarray_object`) 64-bit lane alignment and exclusivity gate for `LeanNative` LLVM kernels. -/
def verifyLnirSArrayContract (byteSize minLanes : Nat) (isExclusive requireExclusive : Bool) : Bool :=
  decide (0 < byteSize ∧ byteSize % 8 = 0 ∧ minLanes * 8 ≤ byteSize ∧ (requireExclusive = true → isExclusive = true))

/-- Universal Theorem (`verifyLnirSArrayContract_sound`):
    If `verifyLnirSArrayContract` succeeds, the `ByteArray` has positive 8-byte-aligned capacity
    for `minLanes` 64-bit lanes and satisfies exclusivity. -/
theorem verifyLnirSArrayContract_sound (byteSize minLanes : Nat) (isExclusive requireExclusive : Bool)
    (h : verifyLnirSArrayContract byteSize minLanes isExclusive requireExclusive = true) :
    0 < byteSize ∧ byteSize % 8 = 0 ∧ minLanes * 8 ≤ byteSize ∧ (requireExclusive = true → isExclusive = true) := by
  unfold verifyLnirSArrayContract at h
  exact of_decide_eq_true h

/-- Pack a `List Int64` into an 8-byte-aligned little-endian `ByteArray` for zero-copy `LeanNative` SIMD execution. -/
def packInt64LanesLe (xs : List Int64) : ByteArray := Id.run do
  let mut ba := ByteArray.emptyWithCapacity (xs.length * 8)
  for x in xs do
    let u := x.toUInt64
    ba := ba.push (u &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 8) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 16) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 24) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 32) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 40) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 48) &&& 0xFF).toUInt8
    ba := ba.push ((u >>> 56) &&& 0xFF).toUInt8
  return ba

/-- Unpack an 8-byte-aligned little-endian `ByteArray` back into `List Int64` lanes. -/
def unpackInt64LanesLe (ba : ByteArray) : List Int64 := Id.run do
  let n := ba.size / 8
  let mut out : Array Int64 := Array.mkEmpty n
  for i in [:n] do
    let base := i * 8
    let u : UInt64 :=
      ba[base]!.toUInt64 |||
      (ba[base + 1]!.toUInt64 <<< 8) |||
      (ba[base + 2]!.toUInt64 <<< 16) |||
      (ba[base + 3]!.toUInt64 <<< 24) |||
      (ba[base + 4]!.toUInt64 <<< 32) |||
      (ba[base + 5]!.toUInt64 <<< 40) |||
      (ba[base + 6]!.toUInt64 <<< 48) |||
      (ba[base + 7]!.toUInt64 <<< 56)
    out := out.push (Int64.ofUInt64 u)
  return out.toList

/-- Pure Lean 10-bit PQ studio range (`[64, 940]`) clamp over `Nat`. -/
@[inline]
def specPq10StudioClampNat (u : Nat) : Nat :=
  if u < 64 then 64 else if 940 < u then 940 else u

/-- Universal Theorem (`specPq10StudioClampNat_bounds_and_idempotent`):
    For any `u : Nat`, `specPq10StudioClampNat u` lies within `[64, 940]` and is idempotent. -/
theorem specPq10StudioClampNat_bounds_and_idempotent (u : Nat) :
    64 ≤ specPq10StudioClampNat u ∧
    specPq10StudioClampNat u ≤ 940 ∧
    specPq10StudioClampNat (specPq10StudioClampNat u) = specPq10StudioClampNat u := by
  by_cases h1 : u < 64
  · simp [specPq10StudioClampNat, h1]
  · by_cases h2 : 940 < u <;> simp [specPq10StudioClampNat, h1, h2] <;> omega

/-! ## C-ABI Runtime Bridge to `lean-native-core`-Compiled Machine Code (`c/libleanav_lnir.o`) -/

/-- Invoke `lean-native-core`-compiled `@h264_idct_tuple_accum_sroa(blocks, dcInit)` directly over C-ABI. -/
@[extern "h264_idct_tuple_accum_sroa"]
opaque execLnirH264IdctTupleSroaC (blocks : UInt64) (dcInit : UInt64) : UInt64

@[extern "lnir_px_down2x2"]
opaque execLnirPxDown2x2C (sum4 : UInt64) : UInt64

@[extern "lnir_px_down2x2_fused_eq_u8"]
opaque execLnirPxDown2x2FusedEqU8C (sum4 contrastQ8 brightness : UInt64) : UInt64

@[extern "lnir_px_down3x3_u8"]
opaque execLnirPxDown3x3U8C (sum9 : UInt64) : UInt64

@[extern "lnir_px_down3x3_u16"]
opaque execLnirPxDown3x3U16C (sum9 : UInt64) : UInt64

@[extern "lnir_px_down3to2_u8"]
opaque execLnirPxDown3to2U8C (p00 p01 p10 p11 oddX oddY : UInt64) : UInt64

@[extern "lnir_px_down3to2_u16_clamp10"]
opaque execLnirPxDown3to2U16Clamp10C (colA colB : UInt64) : UInt64

@[extern "lnir_px_av1_cdef_tap"]
opaque execLnirPxAv1CdefTapC (neighbor center priStr damping : UInt64) : UInt64

@[extern "lnir_px_av1_cdef_filter4_u8"]
opaque execLnirPxAv1CdefFilter4U8C (px c0 c1 c2 c3 : UInt64) : UInt64

@[extern "lnir_px_bilinear_q8"]
opaque execLnirPxBilinearQ8C (p00 p01 p10 p11 fx fy : UInt64) : UInt64

@[extern "lnir_px_bilinear_q8_clamp10"]
opaque execLnirPxBilinearQ8Clamp10C (p00 p01 p10 p11 fx fy : UInt64) : UInt64

@[extern "lnir_px_extract_u16le_msb8"]
opaque execLnirPxExtractU16LeMsb8C (sample : UInt64) : UInt64

@[extern "lnir_px_u16le_to_u10"]
opaque execLnirPxU16LeToU10C (sample : UInt64) : UInt64

@[extern "lnir_px_luma_stats_pack"]
opaque execLnirPxLumaStatsPackC (sum sumSq count : UInt64) : UInt64

@[extern "lnir_px_luma_acceptance_accum"]
opaque execLnirPxLumaAcceptanceAccumC (refPx dstPx : UInt64) : UInt64

@[extern "lnir_px_luma_acceptance_gate"]
opaque execLnirPxLumaAcceptanceGateC (sad blackSum refSum oldOk : UInt64) : UInt64

@[extern "lnir_px_y_studio_clamp_u8"]
opaque execLnirPxYStudioClampU8C (y : UInt64) : UInt64

@[extern "lnir_px_bt2020_to_bt709_uv_u8"]
opaque execLnirPxBt2020ToBt709UvU8C (uPx vPx : UInt64) : UInt64

/-- Zero-copy `ByteArray` unary LNIR dispatcher
    (`0=swscale_gain_bias`, `1=prores_qscale`, `2=boxblur_div9_recip`, `3=pq10_studio_clamp`,
    `4=extract_u16le_msb8`, `5=luma_stats_moments`, `6=bilinear_q8_clamp10`). -/
@[extern "leanav_c_exec_lnir_unary_ba"]
opaque execLnirUnaryBaC (kernelId : UInt32) (ba0 : ByteArray) (arg0 : UInt64) (arg1 : UInt64) : ByteArray

/-- Zero-copy `ByteArray` binary LNIR dispatcher
    (`0=flac_lpc_dot`, `1=opus_celt_saxpy`, `2=bframe_bipred`, `3=hevc_sao_add`,
    `4=aac_imdct_mul`, `5=swscale_down2x2_box`, `6=swscale_down3to2_bilinear`,
    `7=luma_stats_pack`, `8=luma_acceptance_accum`, `9=down2x2_fused_brightness`, `10=yuv420p_studio_range`). -/
@[extern "leanav_c_exec_lnir_binary_ba"]
opaque execLnirBinaryBaC (kernelId : UInt32) (ba0 : ByteArray) (ba1 : @& ByteArray) : ByteArray

/-- Zero-copy `ByteArray` ternary LNIR dispatcher (`0=av1_wiener_3tap`, `1=av1_cdef_fma`, `2=swscale_down3x3_box`, `3=av1_cdef_dir_filter`,
    `4=luma_acceptance_gate`, `5=bilinear_q8_blend`, `6=bilinear_q8_pack`, `7=av1_cdef_tap`, `8=down2x2_fused_eq`). -/
@[extern "leanav_c_exec_lnir_ternary_ba"]
opaque execLnirTernaryBaC (kernelId : UInt32) (ba0 : ByteArray) (ba1 : @& ByteArray) (ba2 : @& ByteArray) : ByteArray

/-- Zero-copy `ByteArray` 2D strided plane LNIR dispatcher
    (`0=swscale_down2x2_u8`, `1=swscale_down2x2_fused_eq_u8`, `2=swscale_down3x3_u8`, `3=swscale_down3to2_u8`, `4=stencil2d_box3x3_u8`).
    `pAlpha` is a source byte offset, except for kernel 1 where it remains the Q8 gain. -/
@[extern "leanav_c_exec_lnir_scale2d_ba"]
opaque execLnirScale2dBaC (kernelId : UInt32) (src : @& ByteArray) (srcStride dstW dstH pAlpha arg1 : UInt64) : ByteArray

/-- Q8 bilinear scaling from a borrowed source slice with an explicit row stride.
    Invalid dimensions or source footprints return an empty array. -/
@[extern "leanav_c_exec_lnir_bilinear_q8_off_ba"]
opaque execLnirBilinearQ8OffBaC (src : @& ByteArray)
    (srcOff srcW srcH srcStride dstW dstH : UInt64) : ByteArray

-- Owned packed Y/U/V input; exclusive exact-size arrays are filtered in place.
-- Invalid lengths consume the input and return an empty array.
@[extern "leanav_c_exec_lnir_apply_filters_yuv420p_ba"]
opaque execLnirApplyFiltersYuv420pBaC (src : ByteArray) (yLen uvLen : UInt64)
    (flags : UInt32) : ByteArray

/-- Zero-copy fused 3-plane `YUV420P` `ByteArray` 2D LNIR dispatcher
    (`0=swscale_down2x2_u8`, `2=swscale_down3x3_u8`, `3=swscale_down3to2_u8`, `5=bilinear_q8_u8`). -/
@[extern "leanav_c_exec_lnir_scale2d_yuv420p_ba"]
opaque execLnirScale2dYuv420pBaC (kernelId : UInt32) (src : @& ByteArray) (srcW srcH dstW dstH : UInt64) : ByteArray

/-- Zero-copy `ByteArray` 2D AV1 CDEF directional deringing filter LNIR dispatcher (`@lean_native_av1_cdef_filter_u8`). -/
@[extern "leanav_c_exec_lnir_cdef_ba"]
opaque execLnirAv1CdefBaC (src : @& ByteArray) (w h priStr damping : UInt64) : ByteArray

/-- Single-allocation packed YUV420P10LE scaling through the U16LE runtime. -/
@[extern "leanav_c_exec_lnir_scale2d_yuv420p10le_ba"]
opaque execLnirScale2dYuv420p10LeBaC (src : @& ByteArray) (srcW srcH dstW dstH : UInt64) : ByteArray

@[extern "leanav_c_exec_lnir_luma_stats_u16le_ba"]
opaque execLnirLumaStatsU16LeBaC (src : @& ByteArray) (nPixels step : UInt64) : UInt64

@[extern "leanav_c_exec_lnir_extract_u16le_msb8_ba"]
opaque execLnirExtractU16LeMsb8BaC (src : @& ByteArray) (nPixels : UInt64) : ByteArray

/-- Zero-copy `ByteArray` strided luma mean & spatial variance LNIR dispatcher (`@lean_native_luma_stats_u8`). -/
@[extern "leanav_c_exec_lnir_luma_stats_ba"]
opaque execLnirLumaStatsBaC (src : @& ByteArray) (nPixels step : UInt64) : UInt64

/-- Zero-copy `ByteArray` 16x16 macroblock luma acceptance LNIR dispatcher (`@lean_native_luma_acceptance_16x16_u8`). -/
@[extern "leanav_c_exec_lnir_luma_acceptance_16x16_ba"]
opaque execLnirLumaAcceptance16x16BaC (src : @& ByteArray) (srcW srcH : UInt64) (dst : @& ByteArray) (dstW dstH : UInt64) : UInt64

/-- Zero-copy U16LE luma acceptance dispatcher. -/
@[extern "leanav_c_exec_lnir_luma_acceptance_16x16_u16le_ba"]
opaque execLnirLumaAcceptance16x16U16LeBaC (src : @& ByteArray) (srcW srcH : UInt64) (dst : @& ByteArray) (dstW dstH : UInt64) : UInt64

/-- Invoke `lean-native-core`-compiled `@lean_native_stencil2d_box3x3_u8` 2D 3x3 box-blur stencil
    on a contiguous `w x h` plane `ByteArray`. -/
@[inline]
def execLnirBoxBlur3x3BaC (src : @& ByteArray) (w h : UInt64) : ByteArray :=
  execLnirScale2dBaC 4 src w w h 0 0

/-- Invoke `lean-native-core`-compiled `swscale_luma_gain_bias_simd` in-place
    on an 8-byte-aligned `ByteArray` (`m_rc == 1` zero-copy fast path). -/
@[inline]
def execLnirSwscaleGainBiasBaC (ba : ByteArray) (gain : Int64) (bias : Int64) : ByteArray :=
  execLnirUnaryBaC 0 ba gain.toUInt64 bias.toUInt64

/-- Invoke `lean-native-core`-compiled `pq10_studio_clamp_select_simd` in-place
    on an 8-byte-aligned `ByteArray` (`m_rc == 1` zero-copy fast path). -/
@[inline]
def execLnirPq10StudioClampBaC (ba : ByteArray) : ByteArray :=
  execLnirUnaryBaC 3 ba 0 0

/-- Contract-guarded zero-copy `ByteArray` wrapper for `swscale_luma_gain_bias_simd`:
    enforces `verifyLnirSArrayContract` before calling the LLVM kernel. -/
def execLnirSwscaleGainBiasBaChecked (ba : ByteArray) (minLanes : Nat) (gain : Int64) (bias : Int64) : Option ByteArray :=
  if verifyLnirSArrayContract ba.size minLanes true true then
    some (execLnirSwscaleGainBiasBaC ba gain bias)
  else
    none

/-- Contract-guarded zero-copy `ByteArray` wrapper for `pq10_studio_clamp_select_simd`:
    enforces `verifyLnirSArrayContract` before calling the LLVM kernel. -/
def execLnirPq10StudioClampBaChecked (ba : ByteArray) (minLanes : Nat) : Option ByteArray :=
  if verifyLnirSArrayContract ba.size minLanes true true then
    some (execLnirPq10StudioClampBaC ba)
  else
    none

/-- Invoke `lean-native-core`-compiled `swscale_luma_gain_bias_simd` on an `Array Int64` buffer via zero-copy `ByteArray` packing. -/
def execLnirSwscaleGainBiasC (xs : Array Int64) (gain : Int64) (bias : Int64) : Array Int64 :=
  (unpackInt64LanesLe (execLnirUnaryBaC 0 (packInt64LanesLe xs.toList) gain.toUInt64 bias.toUInt64)).toArray

/-- Invoke `lean-native-core`-compiled `opus_celt_pvq_mix_saxpy_gpu` on two `Array Int64` buffers via zero-copy `ByteArray` packing. -/
def execLnirOpusCeltSaxpyC (xs : Array Int64) (ys : Array Int64) : Array Int64 :=
  (unpackInt64LanesLe (execLnirBinaryBaC 1 (packInt64LanesLe xs.toList) (packInt64LanesLe ys.toList))).toArray

/-- Invoke `lean-native-core`-compiled `av1_wiener_3tap_sym_gpu` on three `Array Int64` buffers via zero-copy `ByteArray` packing. -/
def execLnirAv1Wiener3TapC (xs : Array Int64) (ys : Array Int64) (zs : Array Int64) : Array Int64 :=
  (unpackInt64LanesLe (execLnirTernaryBaC 0 (packInt64LanesLe xs.toList) (packInt64LanesLe ys.toList) (packInt64LanesLe zs.toList))).toArray

/-- Invoke `lean-native-core`-compiled `av1_cdef_fma_blend_gpu` on three `Array Int64` buffers via zero-copy `ByteArray` packing. -/
def execLnirAv1CdefFmaC (xs : Array Int64) (ys : Array Int64) (zs : Array Int64) : Array Int64 :=
  (unpackInt64LanesLe (execLnirTernaryBaC 1 (packInt64LanesLe xs.toList) (packInt64LanesLe ys.toList) (packInt64LanesLe zs.toList))).toArray

/-- Invoke `lean-native-core`-compiled `pq10_studio_clamp_select_simd` on an `Array Int64` buffer via zero-copy `ByteArray` packing. -/
def execLnirPq10StudioClampC (xs : Array Int64) : Array Int64 :=
  (unpackInt64LanesLe (execLnirUnaryBaC 3 (packInt64LanesLe xs.toList) 0 0)).toArray

/-- Execute the 12 per-pixel arithmetic-core LNIR kernels (`extract_u16le_msb8_simd` through
    `yuv420p_studio_range_simd`) compiled into `libleanav_dsp.a` over adversarial 8-lane vectors
    (sign boundaries, zero divisors, clamp edges) and compare bit-for-bit with `evalLnirKernel`. -/
def verifyCompiledPixelCoreSuiteC (_ : Unit) : Bool :=
  let run1 (id : UInt32) (a : List Int64) := unpackInt64LanesLe (execLnirUnaryBaC id (packInt64LanesLe a) 0 0)
  let run2 (id : UInt32) (a b : List Int64) :=
    unpackInt64LanesLe (execLnirBinaryBaC id (packInt64LanesLe a) (packInt64LanesLe b))
  let run3 (id : UInt32) (a b c : List Int64) :=
    unpackInt64LanesLe (execLnirTernaryBaC id (packInt64LanesLe a) (packInt64LanesLe b) (packInt64LanesLe c))
  let s16 : List Int64 := [0, 3, 4, 1020, 1023, 4095, 65535, -1]
  let px : List Int64 := [0, 1, 15, 16, 128, 235, 240, 255]
  let px2 : List Int64 := [255, 0, 16, 15, 127, 236, 241, 1000]
  let moments : List Int64 := [
    0, ((20000 : Int64) <<< 32) ||| 100, ((72000 : Int64) <<< 32) ||| 240,
    65535, ((90000 : Int64) <<< 32) ||| 70000, 7, 0, 300
  ]
  let counts : List Int64 := [1, 1, 2, 0, 2, 7, 5, 1]
  let sad : List Int64 := [0, 10, 100, 5, 8000, 1, 500, 3]
  let black : List Int64 := [1, 10, 50, 6, 7000, 2, 400, 100]
  let refs : List Int64 := [0, 0, 0, 6143, 6144, 9000, 6143, 0]
  let fq8 : List Int64 := [0, 1, 128, 255, 256, 64, 200, 17]
  let pairSum : List Int64 := [0, 510, 255, 256, 128, 64, 1, 300]
  let contrast : List Int64 := [256, 512, 0, 128, 1024, -256, -371, 256]
  let centered : List Int64 := [-300, -129, -128, 0, 127, 128, 200, 601]
  let bright : List Int64 := [0, 0, 128, -1, 128, 127, 100, -61]
  let chroma : List Int64 := [0, 1, 0, 1, 2, 3, 0, 1]
  let strength : List Int64 := [
    0, 1, 2, ((3 : Int64) <<< 32) ||| 8, 8, ((2 : Int64) <<< 32) ||| 16, 63, 3
  ]
  run1 4 s16 == evalLnirKernel .extractU16LeMsb8 s16 [] [] &&
  run1 5 px == evalLnirKernel .lumaStatsMoments px [] [] &&
  run1 6 s16 == evalLnirKernel .bilinearQ8Clamp10 s16 [] [] &&
  run2 7 moments counts == evalLnirKernel .lumaStatsPack moments counts [] &&
  run2 8 px px2 == evalLnirKernel .lumaAcceptanceAccum px px2 [] &&
  run2 9 centered bright == evalLnirKernel .down2x2FusedBrightness centered bright [] &&
  run2 10 px2 chroma == evalLnirKernel .yuv420pStudioRange px2 chroma [] &&
  run2 11 px px2 == evalLnirKernel .bt2020ToBt709Uv px px2 [] &&
  run3 4 sad black refs == evalLnirKernel .lumaAcceptanceGate sad black refs &&
  run3 5 px px2 fq8 == evalLnirKernel .bilinearQ8Blend px px2 fq8 &&
  run3 6 px2 px fq8 == evalLnirKernel .bilinearQ8Pack px2 px fq8 &&
  run3 7 px2 px strength == evalLnirKernel .av1CdefTap px2 px strength &&
  run3 8 pairSum px2 contrast == evalLnirKernel .down2x2FusedEq pairSum px2 contrast

/-- Execute all 17 compiled scalar `@lnir_px_*` `LNIR_WIRE_V1` symbols directly over C-ABI
    on boundary, sign-extension, overflow, and zero-divisor inputs and compare against `specLnirPx*`. -/
def verifyCompiledScalarPixelCoresC (_ : Unit) : Bool :=
  let neg371 := ((-371 : Int64)).toUInt64
  let neg61 := ((-61 : Int64)).toUInt64
  let neg4 := ((-4 : Int64)).toUInt64
  let okA :=
    ([0, 3, 512, 1020, 262140] : List UInt64).all (fun s =>
      execLnirPxDown2x2C s == specLnirPxDown2x2 s) &&
    ([(512, 256, 0), (1020, neg371, neg61), (800, 0x7fffffff, 100), (0, 512, neg371)] :
        List (UInt64 × UInt64 × UInt64)).all (fun (s, c, b) =>
      execLnirPxDown2x2FusedEqU8C s c b == specLnirPxDown2x2FusedEqU8 s c b) &&
    ([0, 8, 900, 2295] : List UInt64).all (fun s =>
      execLnirPxDown3x3U8C s == specLnirPxDown3x3U8 s) &&
    ([0, 8, 9207, 589815] : List UInt64).all (fun s =>
      execLnirPxDown3x3U16C s == specLnirPxDown3x3U16 s)
  let okB :=
    ([(10, 20, 30, 40, 0, 0), (10, 20, 30, 40, 1, 0),
      (255, 0, 0, 255, 0, 1), (255, 255, 255, 255, 1, 1)] :
        List (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64)).all (fun (a, b, c, d, ox, oy) =>
      execLnirPxDown3to2U8C a b c d ox oy == specLnirPxDown3to2U8 a b c d ox oy) &&
    ([(0, 0), (2000, 2092), (65535, 65535)] : List (UInt64 × UInt64)).all (fun (a, b) =>
      execLnirPxDown3to2U16Clamp10C a b == specLnirPxDown3to2U16Clamp10 a b) &&
    ([(255, 0, 8, 0), (0, 255, 8, 3), (120, 128, 15, 33), (200, 100, 0, 2)] :
        List (UInt64 × UInt64 × UInt64 × UInt64)).all (fun (nb, px, st, dm) =>
      execLnirPxAv1CdefTapC nb px st dm == specLnirPxAv1CdefTap nb px st dm) &&
    ([(100, neg4, neg4, neg4, neg4), (2, neg4, neg4, neg4, neg4), (254, 8, 8, 8, 8)] :
        List (UInt64 × UInt64 × UInt64 × UInt64 × UInt64)).all (fun (px, c0, c1, c2, c3) =>
      execLnirPxAv1CdefFilter4U8C px c0 c1 c2 c3 == specLnirPxAv1CdefFilter4U8 px c0 c1 c2 c3)
  let okC :=
    ([(10, 20, 30, 40, 128, 128), (0, 255, 255, 0, 64, 192), (255, 255, 255, 255, 255, 255)] :
        List (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64)).all (fun (a, b, c, d, fx, fy) =>
      execLnirPxBilinearQ8C a b c d fx fy == specLnirPxBilinearQ8 a b c d fx fy) &&
    ([(100, 200, 300, 400, 128, 128), (65535, 65535, 65535, 65535, 128, 128)] :
        List (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64)).all (fun (a, b, c, d, fx, fy) =>
      execLnirPxBilinearQ8Clamp10C a b c d fx fy == specLnirPxBilinearQ8Clamp10 a b c d fx fy) &&
    ([0, 3, 4, 1023, 4095, 65535] : List UInt64).all (fun s =>
      execLnirPxExtractU16LeMsb8C s == specLnirPxExtractU16LeMsb8 s &&
      execLnirPxU16LeToU10C s == specLnirPxU16LeToU10 s)
  let okD :=
    ([(520, 70000, 4), (520, 70000, 0), (100, 2000, 10)] :
        List (UInt64 × UInt64 × UInt64)).all (fun (s, sq, n) =>
      execLnirPxLumaStatsPackC s sq n == specLnirPxLumaStatsPack s sq n) &&
    ([(200, 190), (0, 255), (16, 16)] : List (UInt64 × UInt64)).all (fun (r, d) =>
      execLnirPxLumaAcceptanceAccumC r d == specLnirPxLumaAcceptanceAccum r d) &&
    ([(500, 400, 7000, 1), (300, 400, 7000, 1), (500, 400, 6143, 1), (500, 400, 7000, 0)] :
        List (UInt64 × UInt64 × UInt64 × UInt64)).all (fun (s, bl, rf, ok) =>
      execLnirPxLumaAcceptanceGateC s bl rf ok == specLnirPxLumaAcceptanceGate s bl rf ok) &&
    ([0, 15, 16, 128, 235, 255] : List UInt64).all (fun y =>
      execLnirPxYStudioClampU8C y == specLnirPxYStudioClampU8 y) &&
    ([(128, 128), (0, 255), (255, 0), (16, 240)] : List (UInt64 × UInt64)).all (fun (u, v) =>
      execLnirPxBt2020ToBt709UvU8C u v == specLnirPxBt2020ToBt709UvU8 u v)
  okA && okB && okC && okD

/-- Execute all 12 `lean-native-core`-compiled LNIR DSP kernels linked in `libleanav_dsp.a`
    directly from Lean 4 over adversarial 8-lane vectors, returning `1` iff every compiled
    machine-code symbol matches the formal `evalLnirKernel` / `leanSpecH264IdctTupleAccumSroa` semantics bit-for-bit. -/
def verifyCompiledLnirSuiteC (_ : Unit) : UInt32 :=
  let vA : List Int64 := [0, 16, 63, 64, 128, 512, 940, 1023]
  let vB : List Int64 := [3, -5, 10, 20, -15, 7, 4, 2]
  let vC : List Int64 := [100, 200, 50, -30, 12, 0, 64, 999]
  let baA := packInt64LanesLe vA
  let baB := packInt64LanesLe vB
  let baC := packInt64LanesLe vC
  let ok1 := unpackInt64LanesLe (execLnirUnaryBaC 0 baA 5 ((-12 : Int64).toUInt64)) == evalLnirKernel (.gainBias 5 (-12)) vA [] []
  let ok2 := unpackInt64LanesLe (execLnirBinaryBaC 0 baA baB) == evalLnirKernel .dotPairwise vA vB []
  let ok3 := unpackInt64LanesLe (execLnirBinaryBaC 1 baA baB) == evalLnirKernel (.saxpy 4) vA vB []
  let ok4 := unpackInt64LanesLe (execLnirTernaryBaC 0 baA baB baC) == evalLnirKernel .wiener3TapSym vA vB vC
  let ok5 := unpackInt64LanesLe (execLnirTernaryBaC 1 baA baB baC) == evalLnirKernel .fmaBlend vA vB vC
  let ok6 := execLnirH264IdctTupleSroaC 16 7 == leanSpecH264IdctTupleAccumSroa 16 7
  let ok7 := unpackInt64LanesLe (execLnirBinaryBaC 2 baA baC) == evalLnirKernel (.saxpy 1) vA vC []
  let ok8 := unpackInt64LanesLe (execLnirBinaryBaC 3 baA baB) == evalLnirKernel .zipAdd vA vB []
  let ok9 := unpackInt64LanesLe (execLnirBinaryBaC 4 baA baB) == evalLnirKernel .zipMul vA vB []
  let ok10 := unpackInt64LanesLe (execLnirUnaryBaC 1 baA 0 0) == evalLnirKernel (.mapScaleAdd 16 8) vA [] []
  let ok11 := unpackInt64LanesLe (execLnirUnaryBaC 2 baA 0 0) == evalLnirKernel .boxBlurDiv9Recip vA [] []
  let ok12 := unpackInt64LanesLe (execLnirUnaryBaC 3 baA 0 0) == evalLnirKernel .pq10StudioClamp vA [] []
  let vP : List Int64 := [10, 20, 30, 40, 50, 60, 70, 80]
  let vQ : List Int64 := [14, 24, 34, 44, 54, 64, 74, 84]
  let vR : List Int64 := [18, 28, 38, 48, 58, 68, 78, 88]
  let baP := packInt64LanesLe vP
  let baQ := packInt64LanesLe vQ
  let baR := packInt64LanesLe vR
  let ok13 := unpackInt64LanesLe (execLnirBinaryBaC 5 baP baQ) == evalLnirKernel .down2x2Box vP vQ []
  let ok14 := unpackInt64LanesLe (execLnirTernaryBaC 2 baP baQ baR) == evalLnirKernel .down3x3Box vP vQ vR
  let ok15 := unpackInt64LanesLe (execLnirBinaryBaC 6 baP baQ) == evalLnirKernel .down3to2Bilinear vP vQ []
  let ok16 := unpackInt64LanesLe (execLnirTernaryBaC 3 baP baQ baR) == evalLnirKernel .av1CdefDirFilter vP vQ vR
  let box3x3In : ByteArray := { data := #[9, 9, 9, 9, 90, 9, 9, 9, 9] }
  let box3x3Out := execLnirBoxBlur3x3BaC box3x3In 3 3
  let ok17 := box3x3Out.size == 9 && box3x3Out.get! 4 == 18 && box3x3Out.get! 0 == 9
  let statsIn : ByteArray := { data := #[100, 120, 140, 160] }
  let statsOut := execLnirLumaStatsBaC statsIn 4 1
  let ok18 := (statsOut &&& 0xFFFFFFFF) == 130 && (statsOut >>> 32) == 500
  let shortOddOut := execLnirScale2dBaC 3 { data := #[90] } 1 1 1 0 0
  let ok19 := shortOddOut.size == 1 && shortOddOut.get! 0 == 0
  -- Unaligned offsets, vector-width rows and tails, all offset kernels, and bounds rejection.
  let offsetSrc : ByteArray := ⟨(Array.range 4096).map (fun i => (i * 37 + i / 11).toUInt8)⟩
  let ok20 := ([1, 7, 31] : List Nat).all fun off =>
    ([0, 2, 3, 4] : List UInt32).all fun k =>
      let dw : UInt64 := if k == 3 then 18 else 19
      let dh : UInt64 := if k == 3 then 4 else 3
      let st : UInt64 := if k == 4 then dw else 64
      let rows : Nat := if k == 0 then 6 else if k == 2 then 9 else if k == 3 then 6 else 3
      let slice := offsetSrc.extract off (off + st.toNat * rows)
      let actual := execLnirScale2dBaC k offsetSrc st dw dh off.toUInt64 0
      let expected := execLnirScale2dBaC k slice st dw dh 0 0
      let invalid := execLnirScale2dBaC k offsetSrc st dw dh 0xffffffffffffffff 0
      actual.data == expected.data && actual.size == (dw * dh).toNat &&
        invalid.size == actual.size && invalid.data.all (· == 0)
  let ok21 := ([0, 2, 3] : List UInt32).all fun k =>
    let sw : UInt64 := 24
    let sh : UInt64 := 12
    let dw : UInt64 := if k == 0 then 12 else if k == 2 then 8 else 16
    let dh : UInt64 := if k == 0 then 6 else if k == 2 then 4 else 8
    let scw : UInt64 := sw / 2
    let sch : UInt64 := sh / 2
    let dcw : UInt64 := dw / 2
    let dch : UInt64 := dh / 2
    let srcY : UInt64 := sw * sh
    let srcUv : UInt64 := scw * sch
    let srcTotal : Nat := (srcY + 2 * srcUv).toNat
    let fused := execLnirScale2dYuv420pBaC k offsetSrc sw sh dw dh
    let yExpected := execLnirScale2dBaC k offsetSrc sw dw dh 0 0
    let uExpected := execLnirScale2dBaC k offsetSrc scw dcw dch srcY 0
    let vExpected := execLnirScale2dBaC k offsetSrc scw dcw dch (srcY + srcUv) 0
    let expected := yExpected ++ uExpected ++ vExpected
    let shortIn := offsetSrc.extract 0 (srcTotal - 1)
    let invalidShort := execLnirScale2dYuv420pBaC k shortIn sw sh dw dh
    let invalidKernel := execLnirScale2dYuv420pBaC 99 offsetSrc sw sh dw dh
    let invalidBounds := execLnirScale2dYuv420pBaC k offsetSrc (dw - 2) sh dw dh
    fused.data == expected.data && fused.size == expected.size &&
      invalidShort.size == expected.size && invalidShort.data.all (· == 0) &&
      invalidKernel.size == expected.size && invalidKernel.data.all (· == 0) &&
      invalidBounds.size == expected.size && invalidBounds.data.all (· == 0)
  let accDst16 := offsetSrc.extract 7 (7 + 256)
  let acc1x1Id := execLnirLumaAcceptance16x16BaC offsetSrc 16 16 offsetSrc 16 16
  let acc1x1Diff := execLnirLumaAcceptance16x16BaC offsetSrc 16 16 accDst16 16 16
  let acc2x2Scaled := execLnirScale2dBaC 0 offsetSrc 32 16 16 0 0
  let acc2x2Exact := execLnirLumaAcceptance16x16BaC offsetSrc 32 32 acc2x2Scaled 16 16
  let accSmall := execLnirLumaAcceptance16x16BaC offsetSrc 8 8 offsetSrc 8 8
  let accInvalidShort := execLnirLumaAcceptance16x16BaC (offsetSrc.extract 0 100) 16 16 offsetSrc 16 16
  let ok22 :=
    (acc1x1Id &&& 0xFFFFFF) == 0 && ((acc1x1Id >>> 24) &&& 0xFFFF) == 480 && ((acc1x1Id >>> 40) &&& 1) == 1 &&
    (acc1x1Diff &&& 0xFFFFFF) > 0 &&
    (acc2x2Exact &&& 0xFFFFFF) == 0 && ((acc2x2Exact >>> 24) &&& 0xFFFF) == 480 && ((acc2x2Exact >>> 40) &&& 1) == 1 &&
    ((accSmall >>> 24) &&& 0xFFFF) == 450 &&
    accInvalidShort == 0
  let ok23 := verifyCompiledPixelCoreSuiteC ()
  let ok24 := verifyCompiledScalarPixelCoresC ()
  let allOk :=
    ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 &&
    ok9 && ok10 && ok11 && ok12 && ok13 && ok14 && ok15 && ok16 &&
    ok17 && ok18 && ok19 && ok20 && ok21 && ok22 && ok23 && ok24
  if allOk then 1 else 0

end LeanAV.NativeKernels
