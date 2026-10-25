/* Auto-generated C-ABI Header by lean-native compile-static-lib */
#ifndef LEAN_NATIVE_GENERATED_C_ABI_H
#define LEAN_NATIVE_GENERATED_C_ABI_H
#include <stdint.h>
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif

void* swscale_luma_gain_bias_simd(void* plane, uint64_t gainQ10, uint64_t biasQ10);
void* flac_lpc_autocorr_dot_simd(void* samplesLag0, void* samplesLagK);
void* opus_celt_pvq_mix_saxpy_gpu(void* midBand, void* sideBand);
void* av1_wiener_3tap_sym_gpu(void* tapLeft, void* tapCenter, void* tapRight);
void* av1_cdef_fma_blend_gpu(void* priTap, void* dirWeight, void* srcPixel);
uint64_t h264_idct_tuple_accum_sroa(uint64_t blocks, uint64_t dcInit);
void* bframe_bipred_blend_gpu(void* refL0, void* refL1);
void* hevc_sao_band_offset_add_gpu(void* reconSample, void* bandOffset);
void* aac_imdct_window_mul_gpu(void* mdctSpec, void* kbdWindow);
void* prores_qscale_map_simd(void* dctCoeff);
void* boxblur_div9_recip_shift_simd(void* sum9Plane);
void* pq10_studio_clamp_select_simd(void* luma10Plane);

#ifdef __cplusplus
}
#endif
#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */
