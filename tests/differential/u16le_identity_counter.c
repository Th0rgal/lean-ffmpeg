/* Test-only interposition without ELF-specific linker --wrap support.
 * Compile the unchanged production bridge under a private scaler name, then
 * expose the original symbol through the counter. The archive still supplies
 * the production LLVM kernels; its duplicate bridge member is not extracted.
 */
#define leanav_c_exec_lnir_scale2d_yuv420p10le_ba identity_test_real_scale
#include "../../c/leanav_simd_kernels.c"
#undef leanav_c_exec_lnir_scale2d_yuv420p10le_ba
#include <lean/lean.h>
#include <stdatomic.h>
static _Atomic uint64_t calls;
extern lean_obj_res identity_test_real_scale(
    b_lean_obj_arg, uint64_t, uint64_t, uint64_t, uint64_t);
lean_obj_res leanav_c_exec_lnir_scale2d_yuv420p10le_ba(
    b_lean_obj_arg src, uint64_t sw, uint64_t sh, uint64_t dw, uint64_t dh) {
    atomic_fetch_add(&calls, 1);
    return identity_test_real_scale(src, sw, sh, dw, dh);
}
LEAN_EXPORT lean_obj_res identity_test_take_calls(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint64(atomic_exchange(&calls, 0)));
}
