/* Test-only interposition without ELF-specific linker --wrap support.
 * Compile the unchanged production bridge under private 10-bit LNIR wrapper
 * names, then expose the original symbols through atomic call counters.
 */
#define leanav_c_exec_lnir_scale2d_yuv420p10le_ba identity_test_real_scale
#define leanav_c_exec_lnir_luma_stats_u16le_ba identity_test_real_luma_stats
#define leanav_c_exec_lnir_extract_u16le_msb8_ba identity_test_real_extract_msb8
#include "../../c/leanav_simd_kernels.c"
#undef leanav_c_exec_lnir_scale2d_yuv420p10le_ba
#undef leanav_c_exec_lnir_luma_stats_u16le_ba
#undef leanav_c_exec_lnir_extract_u16le_msb8_ba
#include <lean/lean.h>
#include <stdatomic.h>

static _Atomic uint64_t scale_calls;
static _Atomic uint64_t stats_calls;
static _Atomic uint64_t extract_calls;

extern lean_obj_res identity_test_real_scale(
    b_lean_obj_arg, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t identity_test_real_luma_stats(
    b_lean_obj_arg, uint64_t, uint64_t);
extern lean_obj_res identity_test_real_extract_msb8(
    b_lean_obj_arg, uint64_t);

lean_obj_res leanav_c_exec_lnir_scale2d_yuv420p10le_ba(
    b_lean_obj_arg src, uint64_t sw, uint64_t sh, uint64_t dw, uint64_t dh) {
    atomic_fetch_add(&scale_calls, 1);
    return identity_test_real_scale(src, sw, sh, dw, dh);
}

uint64_t leanav_c_exec_lnir_luma_stats_u16le_ba(
    b_lean_obj_arg src, uint64_t n_pixels, uint64_t step) {
    atomic_fetch_add(&stats_calls, 1);
    return identity_test_real_luma_stats(src, n_pixels, step);
}

lean_obj_res leanav_c_exec_lnir_extract_u16le_msb8_ba(
    b_lean_obj_arg src, uint64_t n_pixels) {
    atomic_fetch_add(&extract_calls, 1);
    return identity_test_real_extract_msb8(src, n_pixels);
}

LEAN_EXPORT lean_obj_res identity_test_take_calls(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint64(atomic_exchange(&scale_calls, 0)));
}

LEAN_EXPORT lean_obj_res identity_test_take_luma_stats_calls(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint64(atomic_exchange(&stats_calls, 0)));
}

LEAN_EXPORT lean_obj_res identity_test_take_extract_msb8_calls(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint64(atomic_exchange(&extract_calls, 0)));
}
