/* Auto-generated C99 Header by lean-native C-ABI Binding Generator */
#pragma once
#ifndef LEAN_NATIVE_GENERATED_C_ABI_H
#define LEAN_NATIVE_GENERATED_C_ABI_H
#include <stdint.h>
#include <stddef.h>
typedef struct { const void* data; size_t len; size_t stride_bytes; } lean_native_flat_slice_t;
typedef struct { void* data; size_t len; size_t cap; } lean_native_mut_slice_t;
/* Zero-Runtime SliceOut C-ABI Contract: packed u64 span (start:32 | len:24 | kind:8) */
typedef uint32_t (*lean_native_slice_out_scan_fn)(const uint8_t* ptr, size_t len, uint64_t* out_spans, size_t cap, uint64_t* state_io);
static inline uint64_t lean_native_pack_span(uint32_t start, uint32_t len, uint8_t kind) { return ((uint64_t)start << 32) | ((uint64_t)(len & 0xFFFFFFU) << 8) | (uint64_t)kind; }
static inline uint32_t lean_native_span_start(uint64_t span) { return (uint32_t)(span >> 32); }
static inline uint32_t lean_native_span_len(uint64_t span) { return (uint32_t)((span >> 8) & 0xFFFFFFU); }
static inline uint8_t lean_native_span_kind(uint64_t span) { return (uint8_t)(span & 0xFFU); }
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(lean_native_flat_slice_t) == 24, "lean_native_flat_slice_t size == 24");
_Static_assert(sizeof(lean_native_mut_slice_t) == 24, "lean_native_mut_slice_t size == 24");
#endif
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
void* swscale_down2x2_box_simd(void* row0PairSum, void* row1PairSum);
void* swscale_down3x3_box_simd(void* row0TriSum, void* row1TriSum, void* row2TriSum);
void* swscale_down3to2_bilinear_simd(void* rowAHoriz, void* rowBHoriz);
void* av1_cdef_dir_filter_simd(void* centerPx, void* tapPosSum, void* tapNegSum);
void lean_native_swscale_down2x2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH);
void lean_native_swscale_down2x2_fused_eq_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH, uint64_t contrastQ8, uint64_t brightness);
void lean_native_swscale_down3x3_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);
void lean_native_swscale_down3to2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);
void lean_native_av1_cdef_filter_u8(uint8_t* dst, const uint8_t* src, uint64_t w, uint64_t h, uint64_t priStr, uint64_t damping);
#ifdef __cplusplus
}
#endif
#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */
