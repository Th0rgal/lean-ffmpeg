/*
 * Irreducible C-ABI / POSIX / LLVM-LNIR Glue (`c/leanav_simd_kernels.c`)
 *
 * All media domain logic, codec/container parsing, ISO BMFF box patching,
 * pixel-domain scaling/tonemapping/CSC, and acceptance metrics live in pure
 * Lean 4 (`LeanAV/` modules). This file contains only the irreducible C glue:
 *   1. Phase 4/5 POSIX `fork` + `execvp` delegated execution shim (`leanav_c_exec_delegated_ffmpeg`).
 *   2. Phase 5 FFI ABI contract shims (`leanav_c_verify_plane_ffi_contract`,
 *      `leanav_c_ffi_abi_version`, `leanav_c_ffi_cancel_gate` with `__ATOMIC_SEQ_CST` fence,
 *      `leanav_c_ffi_probe_mp4_contract` with borrowed `lean_inc`).
 *   3. Zero-copy `lean_sarray_object` (`ByteArray`) pointer bridge to the 16
 *      `LNIR_WIRE_V1` kernels and 7 2D/reduction LLVM 18 routines (`leanav_c_exec_lnir_*_ba`).
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>
#if defined(__GLIBC__)
#include <malloc.h>
__attribute__((constructor))
static void leanav_init_glibc_malloc_arena(void) {
    mallopt(M_MMAP_THRESHOLD, 64 * 1024 * 1024);
    mallopt(M_TRIM_THRESHOLD, 128 * 1024 * 1024);
}
#endif

static const char *leanav_resolve_ffmpeg_exec_path(void) {
    const char *env_bin = getenv("LEANAV_FFMPEG_BIN");
    if (env_bin && env_bin[0] != '\0' && access(env_bin, X_OK) == 0) return env_bin;
    if (access("/tmp/opencode/ffmpeg-runtime-full/root/usr/bin/ffmpeg", X_OK) == 0) {
        return "/tmp/opencode/ffmpeg-runtime-full/root/usr/bin/ffmpeg";
    }
    if (access("/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg", X_OK) == 0) {
        return "/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg";
    }
    if (access("/tmp/opencode/ffmpeg_build/ffmpeg", X_OK) == 0) {
        return "/tmp/opencode/ffmpeg_build/ffmpeg";
    }
    if (access("/opt/homebrew/bin/ffmpeg", X_OK) == 0) {
        return "/opt/homebrew/bin/ffmpeg";
    }
    if (access("/usr/bin/ffmpeg", X_OK) == 0) {
        return "/usr/bin/ffmpeg";
    }
    if (access("/usr/local/bin/ffmpeg", X_OK) == 0) {
        return "/usr/local/bin/ffmpeg";
    }
    return "ffmpeg";
}

static pthread_once_t leanav_ld_env_once = PTHREAD_ONCE_INIT;

static void leanav_init_ld_env(void) {
    signal(SIGPIPE, SIG_IGN);
    if (access("/tmp/opencode/ffmpeg-runtime-full", R_OK) == 0) {
        const char *old_ld = getenv("LD_LIBRARY_PATH");
        char ld_buf[4096];
        const char *rt_ld = "/tmp/opencode/ffmpeg-runtime-full/root/usr/lib/x86_64-linux-gnu:/tmp/opencode/ffmpeg-runtime-full/root/usr/lib/x86_64-linux-gnu/blas:/tmp/opencode/ffmpeg-runtime-full/root/usr/lib/x86_64-linux-gnu/lapack:/tmp/opencode/ffmpeg-runtime-full/lib:/tmp/opencode/ffmpeg-runtime-full/lib/x86_64-linux-gnu";
        if (old_ld && old_ld[0] != '\0') {
            snprintf(ld_buf, sizeof(ld_buf), "%s:%s", rt_ld, old_ld);
        } else {
            snprintf(ld_buf, sizeof(ld_buf), "%s", rt_ld);
        }
        setenv("LD_LIBRARY_PATH", ld_buf, 1);
    }
}

static uint32_t leanav_exec_ffmpeg_argv(
    const char *const *c_argv,
    const char *out_path,
    uint32_t suppress_output
) {
    pthread_once(&leanav_ld_env_once, leanav_init_ld_env);
    const char *ffmpeg_bin = c_argv[0];
    int is_special_out = (!out_path || out_path[0] == '\0' ||
                          strcmp(out_path, "-") == 0 ||
                          strcmp(out_path, "/dev/null") == 0 ||
                          strncmp(out_path, "pipe:", 5) == 0 ||
                          strncmp(out_path, "md5:", 4) == 0);
    int existed_before = (!is_special_out && access(out_path, F_OK) == 0) ? 1 : 0;

    pid_t pid = fork();
    if (pid < 0) {
        return 1u;
    }
    if (pid == 0) {
        int devnull = open("/dev/null", O_RDWR);
        if (devnull >= 0) {
            dup2(devnull, STDIN_FILENO);
            if (suppress_output != 0u) {
                if (!out_path || (strcmp(out_path, "-") != 0 && strcmp(out_path, "md5:") != 0 && strncmp(out_path, "pipe:", 5) != 0)) {
                    dup2(devnull, STDOUT_FILENO);
                }
                dup2(devnull, STDERR_FILENO);
            }
            if (devnull > STDERR_FILENO) close(devnull);
        }
        execvp(ffmpeg_bin, (char *const *)c_argv);
        _exit(127);
    }
    int status = 0;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno == EINTR) continue;
        return 1u;
    }
    int ok = (WIFEXITED(status) && WEXITSTATUS(status) == 0) ? 1 : 0;
    if (!ok && !is_special_out && !existed_before && suppress_output != 0u) {
        unlink(out_path);
    }
    if (ok) return 0u;
    if (WIFEXITED(status) && WEXITSTATUS(status) != 0) return (uint32_t)WEXITSTATUS(status);
    if (WIFSIGNALED(status)) return (uint32_t)(128 + WTERMSIG(status));
    return 1u;
}

/*
 * Wave 51 (P4): Certified C-ABI / FFI Plane Contract Guard (`leanav_c_verify_plane_ffi_contract`):
 * Checks `lean_is_exclusive(ba)` (`m_rc == 1`) when `require_exclusive != 0` and delegates
 * geometry/alignment/tail-padding verification to `@[export leanav_lean_verify_plane_ffi_contract]`.
 */
extern uint32_t leanav_lean_verify_plane_ffi_contract(
    size_t actual_cap,
    size_t w,
    size_t h,
    size_t stride,
    size_t bytes_per_sample,
    size_t simd_vec_bytes
);

LEAN_EXPORT uint32_t leanav_c_verify_plane_ffi_contract(
    b_lean_obj_arg ba,
    size_t w,
    size_t h,
    size_t stride,
    size_t bytes_per_sample,
    size_t simd_vec_bytes,
    uint32_t require_exclusive
) {
    if (require_exclusive != 0u && !lean_is_exclusive((lean_object *)ba)) return 0u;
    return leanav_lean_verify_plane_ffi_contract(
        lean_sarray_size(ba), w, h, stride, bytes_per_sample, simd_vec_bytes
    );
}

/*
 * Phase 5 (Wave G): Borrowed-ABI C shims delegating to pure Lean 4 `@[export]` functions in `LeanAV/PlanIR.lean`.
 */
extern uint32_t leanav_lean_ffi_abi_version(lean_obj_arg unit);
extern uint32_t leanav_lean_ffi_cancel_gate(uint32_t cancel_flag, uint32_t frames_done, uint32_t max_frames);
extern uint64_t leanav_lean_ffi_probe_mp4_contract(lean_obj_arg ba, size_t max_read_bytes);

LEAN_EXPORT uint32_t leanav_c_ffi_abi_version(lean_obj_arg unit) {
    return leanav_lean_ffi_abi_version(unit);
}

LEAN_EXPORT uint32_t leanav_c_ffi_cancel_gate(
    uint32_t cancel_flag,
    uint32_t frames_done,
    uint32_t max_frames
) {
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
    return leanav_lean_ffi_cancel_gate(cancel_flag, frames_done, max_frames);
}

LEAN_EXPORT uint64_t leanav_c_ffi_probe_mp4_contract(
    b_lean_obj_arg ba,
    size_t max_read_bytes
) {
    lean_inc(ba);
    return leanav_lean_ffi_probe_mp4_contract(ba, max_read_bytes);
}

/*
 * Phase 4 (Waves E/F): Structured-Argv Delegated Execution (`leanav_c_exec_delegated_ffmpeg`).
 */
LEAN_EXPORT uint32_t leanav_c_exec_delegated_ffmpeg(
    b_lean_obj_arg argv_arr,
    b_lean_obj_arg out_path_str,
    uint32_t suppress_output
) {
    size_t n = lean_array_size(argv_arr);
    if (n == 0 || n > 2048) return 1u;
    const char *ffmpeg_bin = leanav_resolve_ffmpeg_exec_path();
    const char *out_path = lean_string_cstr(out_path_str);

    const char **c_argv = (const char **)calloc(n + 2, sizeof(char *));
    if (!c_argv) return 1u;
    c_argv[0] = ffmpeg_bin;
    for (size_t i = 0; i < n; i++) {
        lean_object *elem = lean_array_get_core(argv_arr, i);
        const char *tok = lean_string_cstr(elem);
        size_t str_sz = lean_string_size(elem);
        if (!tok || str_sz <= 1 || strlen(tok) + 1 != str_sz) {
            free(c_argv);
            return 1u;
        }
        c_argv[i + 1] = tok;
    }
    c_argv[n + 1] = NULL;
    uint32_t rc = leanav_exec_ffmpeg_argv(c_argv, out_path, suppress_output);
    free(c_argv);
    return rc;
}

/* ============================================================================
 * C-ABI Runtime Bridge to `lean-native-core`-Compiled LNIR Kernels (`c/leanav_lnir_kernels.h`)
 * ============================================================================
 */
#include "leanav_lnir_kernels.h"

static inline lean_obj_res leanav_clone_ba(lean_obj_arg ba) {
    size_t sz = lean_sarray_size(ba);
    lean_object *out = lean_alloc_sarray(1, sz, sz);
    if (sz > 0) {
        memcpy(lean_sarray_cptr(out), lean_sarray_cptr(ba), sz);
    }
    lean_dec(ba);
    return out;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_unary_ba(
    uint32_t kernel_id,
    lean_obj_arg ba0,
    uint64_t arg0,
    uint64_t arg1
) {
    size_t init_sz = lean_sarray_size(ba0);
    if (init_sz == 0 || (init_sz & 7u) != 0u) {
        return ba0;
    }
    if (!lean_is_exclusive(ba0)) {
        ba0 = leanav_clone_ba(ba0);
    }
    lean_sarray_object *s0 = lean_to_sarray(ba0);
    size_t byte_sz = s0->m_size;
    size_t n_lanes = byte_sz >> 3;
    s0->m_size = n_lanes;
    switch (kernel_id) {
        case 0u: (void)swscale_luma_gain_bias_simd(ba0, arg0, arg1); break;
        case 1u: (void)prores_qscale_map_simd(ba0); break;
        case 2u: (void)boxblur_div9_recip_shift_simd(ba0); break;
        case 3u: (void)pq10_studio_clamp_select_simd(ba0); break;
        default: break;
    }
    s0->m_size = byte_sz;
    return ba0;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_binary_ba(
    uint32_t kernel_id,
    lean_obj_arg ba0,
    b_lean_obj_arg ba1
) {
    size_t sz0 = lean_sarray_size(ba0);
    size_t sz1 = lean_sarray_size(ba1);
    size_t min_sz = (sz0 < sz1) ? sz0 : sz1;
    size_t n_lanes = min_sz >> 3;
    if (n_lanes == 0) {
        lean_dec(ba0);
        return lean_alloc_sarray(1, 0, 0);
    }
    if (!lean_is_exclusive(ba0) || (const void *)ba0 == (const void *)ba1) {
        ba0 = leanav_clone_ba(ba0);
    }
    lean_sarray_object *s0 = lean_to_sarray(ba0);
    s0->m_size = n_lanes;
    switch (kernel_id) {
        case 0u: (void)flac_lpc_autocorr_dot_simd(ba0, (void *)ba1); break;
        case 1u: (void)opus_celt_pvq_mix_saxpy_gpu(ba0, (void *)ba1); break;
        case 2u: (void)bframe_bipred_blend_gpu(ba0, (void *)ba1); break;
        case 3u: (void)hevc_sao_band_offset_add_gpu(ba0, (void *)ba1); break;
        case 4u: (void)aac_imdct_window_mul_gpu(ba0, (void *)ba1); break;
        case 5u: (void)swscale_down2x2_box_simd(ba0, (void *)ba1); break;
        case 6u: (void)swscale_down3to2_bilinear_simd(ba0, (void *)ba1); break;
        default: break;
    }
    s0->m_size = n_lanes << 3;
    return ba0;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_ternary_ba(
    uint32_t kernel_id,
    lean_obj_arg ba0,
    b_lean_obj_arg ba1,
    b_lean_obj_arg ba2
) {
    size_t sz0 = lean_sarray_size(ba0);
    size_t sz1 = lean_sarray_size(ba1);
    size_t sz2 = lean_sarray_size(ba2);
    size_t min_sz = sz0;
    if (sz1 < min_sz) min_sz = sz1;
    if (sz2 < min_sz) min_sz = sz2;
    size_t n_lanes = min_sz >> 3;
    if (n_lanes == 0) {
        lean_dec(ba0);
        return lean_alloc_sarray(1, 0, 0);
    }
    if (!lean_is_exclusive(ba0) || (const void *)ba0 == (const void *)ba1 || (const void *)ba0 == (const void *)ba2) {
        ba0 = leanav_clone_ba(ba0);
    }
    lean_object *ba2_eff = (lean_object *)ba2;
    int copied_ba2 = 0;
    if ((const void *)ba1 == (const void *)ba2) {
        lean_inc(ba2_eff);
        ba2_eff = leanav_clone_ba(ba2_eff);
        copied_ba2 = 1;
    }
    lean_sarray_object *s0 = lean_to_sarray(ba0);
    s0->m_size = n_lanes;
    switch (kernel_id) {
        case 0u: (void)av1_wiener_3tap_sym_gpu(ba0, (void *)ba1, (void *)ba2_eff); break;
        case 1u: (void)av1_cdef_fma_blend_gpu(ba0, (void *)ba1, (void *)ba2_eff); break;
        case 2u: (void)swscale_down3x3_box_simd(ba0, (void *)ba1, (void *)ba2_eff); break;
        case 3u: (void)av1_cdef_dir_filter_simd(ba0, (void *)ba1, (void *)ba2_eff); break;
        default: break;
    }
    s0->m_size = n_lanes << 3;
    if (copied_ba2) {
        lean_dec(ba2_eff);
    }
    return ba0;
}

static inline uint64_t leanav_scale2d_req_extent(uint32_t kernel_id, uint64_t d) {
    return (kernel_id <= 1u) ? (d * 2u)
         : (kernel_id == 2u) ? (d * 3u)
         : (kernel_id == 3u) ? ((d >> 1u) * 3u + ((d & 1u) ? 2u : 0u))
         : d;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_scale2d_ba(
    uint32_t kernel_id,
    b_lean_obj_arg src_ba,
    uint64_t src_stride,
    uint64_t dst_w,
    uint64_t dst_h,
    uint64_t p_alpha,
    uint64_t arg1
) {
    if (dst_w == 0 || dst_h == 0 || dst_w > 0x3FFFFFFFull || dst_h > 0x3FFFFFFFull) return lean_alloc_sarray(1, 0, 0);
    size_t total = (size_t)(dst_w * dst_h);
    lean_object *out = lean_alloc_sarray(1, total, total);
    uint8_t *dst_ptr = lean_sarray_cptr(out);
    uint64_t sh = leanav_scale2d_req_extent(kernel_id, dst_h);
    uint64_t mw = leanav_scale2d_req_extent(kernel_id, dst_w);
    uint64_t st = (kernel_id == 4u) ? dst_w : src_stride;
    uint64_t src_off = (kernel_id == 1u) ? 0u : p_alpha;
    uint64_t src_cap = (uint64_t)lean_sarray_size(src_ba);
    if (st < mw || st > 0x3FFFFFFFull) { memset(dst_ptr, 0, total); return out; }
    /* Dimension and stride caps above keep this footprint below UINT64_MAX. */
    uint64_t need = (sh - 1u) * st + mw;
    if (!(src_off <= src_cap && need <= src_cap - src_off)) { memset(dst_ptr, 0, total); return out; }
    const uint8_t *src_ptr = (const uint8_t *)lean_sarray_cptr(src_ba) + src_off;
    switch (kernel_id) {
        case 0u: lean_native_swscale_down2x2_u8(dst_ptr, src_ptr, src_stride, dst_w, dst_h); break;
        case 1u: lean_native_swscale_down2x2_fused_eq_u8(dst_ptr, src_ptr, src_stride, dst_w, dst_h, p_alpha, arg1); break;
        case 2u: lean_native_swscale_down3x3_u8(dst_ptr, src_ptr, src_stride, dst_w, dst_h); break;
        case 3u: lean_native_swscale_down3to2_u8(dst_ptr, src_ptr, src_stride, dst_w, dst_h); break;
        case 4u: lean_native_stencil2d_box3x3_u8(dst_ptr, src_ptr, dst_w, dst_h); break;
        default: memset(dst_ptr, 0, total); break;
    }
    return out;
}

/* Borrow the source slice; allocate only the destination. Invalid footprints
 * return an empty array. Bounds keep Q8 coordinate products within uint64_t. */
LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_bilinear_q8_off_ba(
    b_lean_obj_arg src_ba, uint64_t src_off, uint64_t src_w,
    uint64_t src_h, uint64_t src_stride, uint64_t dst_w, uint64_t dst_h
) {
    uint64_t cap = (uint64_t)lean_sarray_size(src_ba);
    if (!src_w || !src_h || src_w > 0xFFFFFFu || src_h > 0xFFFFFFu ||
        !dst_w || !dst_h || dst_w > 0xFFFFFFFFu || dst_h > 0xFFFFFFFFu ||
        src_stride < src_w || src_off > cap || src_w > cap - src_off ||
        src_h - 1u > (cap - src_off - src_w) / src_stride ||
        dst_w > (SIZE_MAX - sizeof(lean_sarray_object)) / dst_h)
        return lean_alloc_sarray(1, 0, 0);
    size_t total = (size_t)(dst_w * dst_h);
    lean_object *out = lean_alloc_sarray(1, total, total);
    lean_native_swscale_bilinear_q8_u8(lean_sarray_cptr(out),
        lean_sarray_cptr(src_ba) + src_off, src_w, src_h, src_stride, dst_w, dst_h);
    return out;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_scale2d_yuv420p_ba(
    uint32_t kernel_id,
    b_lean_obj_arg src_ba,
    uint64_t src_w,
    uint64_t src_h,
    uint64_t dst_w,
    uint64_t dst_h
) {
    if (dst_w < 2u || dst_h < 2u || (dst_w & 1u) != 0u || (dst_h & 1u) != 0u ||
        dst_w > 0x3FFFFFFFull || dst_h > 0x3FFFFFFFull) {
        return lean_alloc_sarray(1, 0, 0);
    }
    uint64_t dst_cw = dst_w >> 1u;
    uint64_t dst_ch = dst_h >> 1u;
    uint64_t dst_y = dst_w * dst_h;
    uint64_t dst_uv = dst_cw * dst_ch;
    uint64_t dst_total = dst_y + 2u * dst_uv;
    lean_obj_res out = lean_alloc_sarray(1, (size_t)dst_total, (size_t)dst_total);
    uint8_t *dst_ptr = lean_sarray_cptr(out);
    if ((kernel_id != 0u && kernel_id != 2u && kernel_id != 3u && kernel_id != 5u) ||
        src_w < 2u || src_h < 2u || (src_w & 1u) != 0u || (src_h & 1u) != 0u ||
        src_w > 0x3FFFFFFFull || src_h > 0x3FFFFFFFull ||
        (kernel_id == 5u && (src_w > 0xFFFFFFu || src_h > 0xFFFFFFu))) {
        memset(dst_ptr, 0, (size_t)dst_total);
        return out;
    }
    uint64_t src_cw = src_w >> 1u;
    uint64_t src_ch = src_h >> 1u;
    uint64_t src_y = src_w * src_h;
    uint64_t src_uv = src_cw * src_ch;
    uint64_t src_total = src_y + 2u * src_uv;
    uint64_t src_cap = (uint64_t)lean_sarray_size(src_ba);
    uint64_t y_mw = kernel_id == 5u ? src_w : leanav_scale2d_req_extent(kernel_id, dst_w);
    uint64_t y_sh = kernel_id == 5u ? src_h : leanav_scale2d_req_extent(kernel_id, dst_h);
    uint64_t c_mw = kernel_id == 5u ? src_cw : leanav_scale2d_req_extent(kernel_id, dst_cw);
    uint64_t c_sh = kernel_id == 5u ? src_ch : leanav_scale2d_req_extent(kernel_id, dst_ch);
    if (src_cap < src_total ||
        src_w < y_mw || src_h < y_sh || (y_sh - 1u) * src_w + y_mw > src_y ||
        src_cw < c_mw || src_ch < c_sh || (c_sh - 1u) * src_cw + c_mw > src_uv) {
        memset(dst_ptr, 0, (size_t)dst_total);
        return out;
    }
    const uint8_t *src_ptr = (const uint8_t *)lean_sarray_cptr(src_ba);
    const uint8_t *src_u = src_ptr + src_y;
    const uint8_t *src_v = src_u + src_uv;
    uint8_t *dst_u = dst_ptr + dst_y;
    uint8_t *dst_v = dst_u + dst_uv;
    switch (kernel_id) {
        case 5u:
            lean_native_swscale_bilinear_q8_u8(dst_ptr, src_ptr, src_w, src_h, src_w, dst_w, dst_h);
            lean_native_swscale_bilinear_q8_u8(dst_u, src_u, src_cw, src_ch, src_cw, dst_cw, dst_ch);
            lean_native_swscale_bilinear_q8_u8(dst_v, src_v, src_cw, src_ch, src_cw, dst_cw, dst_ch);
            break;
        case 0u:
            lean_native_swscale_down2x2_u8(dst_ptr, src_ptr, src_w, dst_w, dst_h);
            lean_native_swscale_down2x2_u8(dst_u, src_u, src_cw, dst_cw, dst_ch);
            lean_native_swscale_down2x2_u8(dst_v, src_v, src_cw, dst_cw, dst_ch);
            break;
        case 2u:
            lean_native_swscale_down3x3_u8(dst_ptr, src_ptr, src_w, dst_w, dst_h);
            lean_native_swscale_down3x3_u8(dst_u, src_u, src_cw, dst_cw, dst_ch);
            lean_native_swscale_down3x3_u8(dst_v, src_v, src_cw, dst_cw, dst_ch);
            break;
        case 3u:
            lean_native_swscale_down3to2_u8(dst_ptr, src_ptr, src_w, dst_w, dst_h);
            lean_native_swscale_down3to2_u8(dst_u, src_u, src_cw, dst_cw, dst_ch);
            lean_native_swscale_down3to2_u8(dst_v, src_v, src_cw, dst_cw, dst_ch);
            break;
        default:
            memset(dst_ptr, 0, (size_t)dst_total);
            break;
    }
    return out;
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_cdef_ba(
    b_lean_obj_arg src_ba,
    uint64_t w,
    uint64_t h,
    uint64_t pri_str,
    uint64_t damping
) {
    size_t total = (size_t)(w * h);
    lean_object *out = lean_alloc_sarray(1, total, total);
    if (total == 0) return out;
    if (lean_sarray_size(src_ba) < total) { memset(lean_sarray_cptr(out), 0, total); return out; }
    lean_native_av1_cdef_filter_u8(lean_sarray_cptr(out), lean_sarray_cptr(src_ba), w, h, pri_str, damping);
    return out;
}

LEAN_EXPORT uint64_t leanav_c_exec_lnir_luma_stats_ba(
    b_lean_obj_arg src_ba,
    uint64_t n_pixels,
    uint64_t step
) {
    size_t sz = lean_sarray_size(src_ba);
    uint64_t eff_n = (n_pixels < (uint64_t)sz) ? n_pixels : (uint64_t)sz;
    if (eff_n == 0 || step == 0) return 0ull;
    return lean_native_luma_stats_u8(lean_sarray_cptr(src_ba), eff_n, step);
}

extern uint64_t leanav_lean_classify_luma_psnr_x10_u64(uint64_t total_sq_err, uint64_t total_pix);
extern uint64_t leanav_lean_pack_acceptance_metrics_u64(uint64_t max_block_sad, uint64_t psnr_x10, uint32_t dist_lt_black);

static uint64_t leanav_luma_acceptance_16x16_ba(
    b_lean_obj_arg src_ba,
    uint64_t src_w,
    uint64_t src_h,
    b_lean_obj_arg dst_ba,
    uint64_t dst_w,
    uint64_t dst_h,
    uint64_t pixel_bytes,
    void (*kernel)(const uint8_t *, uint64_t, uint64_t, const uint8_t *, uint64_t, uint64_t, uint64_t *)
) {
    if (dst_w < 16u || dst_h < 16u || src_w < 2u || src_h < 2u ||
        src_w > 0x3FFFFFFFull || src_h > 0x3FFFFFFFull ||
        dst_w > 0x3FFFFFFFull || dst_h > 0x3FFFFFFFull) {
        return leanav_lean_pack_acceptance_metrics_u64(0ull, 450ull, 1u);
    }
    int is_1x1 = (src_w == dst_w && src_h == dst_h);
    int is_2x2 = (src_w == dst_w * 2u && src_h == dst_h * 2u);
    if (!is_1x1 && !is_2x2) return 0ull;
    /* Dimensions are bounded above by 2^30-1, so even two bytes/pixel fit UInt64. */
    uint64_t src_need = src_w * src_h * pixel_bytes;
    uint64_t dst_need = dst_w * dst_h * pixel_bytes;
    if ((uint64_t)lean_sarray_size(src_ba) < src_need ||
        (uint64_t)lean_sarray_size(dst_ba) < dst_need) {
        return 0ull;
    }
    uint64_t metrics[4] = {0ull, 0ull, 0ull, 1ull};
    kernel(
        lean_sarray_cptr(src_ba), src_w, src_h,
        lean_sarray_cptr(dst_ba), dst_w, dst_h,
        metrics
    );
    uint64_t psnr_x10 = leanav_lean_classify_luma_psnr_x10_u64(metrics[1], metrics[2]);
    return leanav_lean_pack_acceptance_metrics_u64(metrics[0], psnr_x10, (uint32_t)metrics[3]);
}

LEAN_EXPORT uint64_t leanav_c_exec_lnir_luma_acceptance_16x16_ba(
    b_lean_obj_arg src_ba, uint64_t src_w, uint64_t src_h,
    b_lean_obj_arg dst_ba, uint64_t dst_w, uint64_t dst_h
) {
    return leanav_luma_acceptance_16x16_ba(src_ba, src_w, src_h, dst_ba, dst_w, dst_h,
        1u, lean_native_luma_acceptance_16x16_u8);
}

LEAN_EXPORT uint64_t leanav_c_exec_lnir_luma_acceptance_16x16_u16le_ba(
    b_lean_obj_arg src_ba, uint64_t src_w, uint64_t src_h,
    b_lean_obj_arg dst_ba, uint64_t dst_w, uint64_t dst_h
) {
    return leanav_luma_acceptance_16x16_ba(src_ba, src_w, src_h, dst_ba, dst_w, dst_h,
        2u, lean_native_luma_acceptance_16x16_u16le);
}

/* Owned packed input; reuse only an exclusive, exact-size array. */
LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_apply_filters_yuv420p_ba(
    lean_obj_arg src_ba, uint64_t y_len, uint64_t uv_len, uint32_t flags
) {
    size_t cap = lean_sarray_size(src_ba);
    if (y_len > cap || uv_len > (cap - y_len) / 2u) {
        lean_dec_ref(src_ba);
        return lean_alloc_sarray(1, 0, 0);
    }
    size_t total = (size_t)(y_len + 2u * uv_len);
    if (cap == total && lean_is_exclusive(src_ba)) {
        lean_native_apply_filters_yuv420p_u8(
            lean_sarray_cptr(src_ba), lean_sarray_cptr(src_ba),
            (int64_t)y_len, (int64_t)uv_len, (int64_t)flags);
        return src_ba;
    }
    lean_obj_res out = lean_alloc_sarray(1, total, total);
    lean_native_apply_filters_yuv420p_u8(
        lean_sarray_cptr(src_ba), lean_sarray_cptr(out), y_len, uv_len, flags);
    lean_dec_ref(src_ba);
    return out;
}

/* Packed U16LE planes: validation and allocation only; DSP lives in LLVM. */
LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_scale2d_yuv420p10le_ba(
    b_lean_obj_arg src_ba, uint64_t sw, uint64_t sh, uint64_t dw, uint64_t dh) {
    if (sw < 2 || sh < 2 || dw < 2 || dh < 2 || ((sw | sh | dw | dh) & 1) ||
        sw > 0xFFFFFF || sh > 0xFFFFFF || dw > 0x3FFFFFFF || dh > 0x3FFFFFFF)
        return lean_alloc_sarray(1, 0, 0);
    uint64_t sy = sw * sh * 2, suv = (sw / 2) * (sh / 2) * 2;
    uint64_t dy = dw * dh * 2, duv = (dw / 2) * (dh / 2) * 2;
    uint64_t total = dy + 2 * duv;
    if (sy + 2 * suv > lean_sarray_size(src_ba) || total > SIZE_MAX - sizeof(lean_sarray_object))
        return lean_alloc_sarray(1, 0, 0);
    lean_object *out = lean_alloc_sarray(1, total, total);
    const uint8_t *src = lean_sarray_cptr(src_ba);
    uint8_t *dst = lean_sarray_cptr(out);
    lean_native_swscale_bilinear_q8_u16le(src, dst, sw, sh, dw, dh);
    lean_native_swscale_bilinear_q8_u16le(src + sy, dst + dy, sw / 2, sh / 2, dw / 2, dh / 2);
    lean_native_swscale_bilinear_q8_u16le(src + sy + suv, dst + dy + duv, sw / 2, sh / 2, dw / 2, dh / 2);
    return out;
}

LEAN_EXPORT uint64_t leanav_c_exec_lnir_luma_stats_u16le_ba(
    b_lean_obj_arg src_ba, uint64_t n_pixels, uint64_t step) {
    uint64_t cap = lean_sarray_size(src_ba) / 2;
    uint64_t n = n_pixels < cap ? n_pixels : cap;
    return lean_native_luma_stats_u16le(lean_sarray_cptr(src_ba), n, step);
}

LEAN_EXPORT lean_obj_res leanav_c_exec_lnir_extract_u16le_msb8_ba(
    b_lean_obj_arg src_ba, uint64_t n_pixels) {
    uint64_t cap = lean_sarray_size(src_ba) / 2;
    uint64_t n = n_pixels < cap ? n_pixels : cap;
    lean_object *out = lean_alloc_sarray(1, n, n);
    lean_native_extract_u16le_msb8(lean_sarray_cptr(src_ba), lean_sarray_cptr(out), n);
    return out;
}
