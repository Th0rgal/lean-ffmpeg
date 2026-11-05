#!/usr/bin/env python3
"""Deterministic LLVM 18 outer-shell generator and LNIR module splicer.

Replaces the 14 hand-written SIMD/scalar `@lean_native_*` built-in routines
emitted by `lean-native-core compile-llvm` with thin, target-independent
buffer-indexing outer shells that delegate every pixel/sample arithmetic step
to the 17 formally verified, TV-certified `@lnir_px_*` LNIR cores.
"""
import argparse
import re
import sys
from pathlib import Path

OUTER_PROTOS_C = [
    "void lean_native_swscale_down2x2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH);",
    "void lean_native_swscale_down2x2_fused_eq_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH, uint64_t contrastQ8, uint64_t brightness);",
    "void lean_native_swscale_down3x3_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);",
    "void lean_native_swscale_down3to2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);",
    "void lean_native_av1_cdef_filter_u8(uint8_t* dst, const uint8_t* src, uint64_t w, uint64_t h, uint64_t priStr, uint64_t damping);",
    "void lean_native_stencil2d_box3x3_u8(uint8_t* dst, const uint8_t* src, uint64_t w, uint64_t h);",
    "void lean_native_swscale_bilinear_q8_u16le(const uint8_t* src, uint8_t* dst, uint64_t src_w, uint64_t src_h, uint64_t dst_w, uint64_t dst_h);",
    "uint64_t lean_native_luma_stats_u16le(const uint8_t* src, uint64_t n_pixels, uint64_t step);",
    "void lean_native_extract_u16le_msb8(const uint8_t* src, uint8_t* dst, uint64_t n_pixels);",
    "uint64_t lean_native_luma_stats_u8(const uint8_t* src, uint64_t nPixels, uint64_t step);",
    "void lean_native_swscale_bilinear_q8_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t srcH, uint64_t srcStride, uint64_t dstW, uint64_t dstH);",
    "void lean_native_apply_filters_yuv420p_u8(const uint8_t* src, uint8_t* dst, uint64_t y_len, uint64_t uv_len, uint64_t flags);",
    "void lean_native_luma_acceptance_16x16_u8(const uint8_t* src, uint64_t srcW, uint64_t srcH, const uint8_t* dst, uint64_t dstW, uint64_t dstH, uint64_t* outMetrics4);",
    "void lean_native_luma_acceptance_16x16_u16le(const uint8_t* src, uint64_t srcW, uint64_t srcH, const uint8_t* dst, uint64_t dstW, uint64_t dstH, uint64_t* outMetrics4);",
]

EXPECTED_SHELL_CALLS = {
    "lean_native_swscale_down2x2_u8": ("lnir_px_down2x2",),
    "lean_native_swscale_down2x2_fused_eq_u8": ("lnir_px_down2x2_fused_eq_u8",),
    "lean_native_swscale_down3x3_u8": ("lnir_px_down3x3_u8",),
    "lean_native_swscale_down3to2_u8": ("lnir_px_down3to2_u8",),
    "lean_native_av1_cdef_filter_u8": ("lnir_px_av1_cdef_tap", "lnir_px_av1_cdef_filter4_u8"),
    "lean_native_stencil2d_box3x3_u8": ("lnir_px_down3x3_u8",),
    "lean_native_luma_stats_u8": ("lnir_px_luma_stats_pack",),
    "lean_native_luma_stats_u16le": ("lnir_px_u16le_to_u10", "lnir_px_luma_stats_pack"),
    "lean_native_swscale_bilinear_q8_u8": ("lnir_px_bilinear_q8",),
    "lean_native_swscale_bilinear_q8_u16le": (
        "lnir_px_down2x2",
        "lnir_px_down3x3_u16",
        "lnir_px_down3to2_u16_clamp10",
        "lnir_px_bilinear_q8_clamp10",
    ),
    "lean_native_extract_u16le_msb8": ("lnir_px_extract_u16le_msb8",),
    "lean_native_apply_filters_yuv420p_u8": (
        "lnir_px_y_studio_clamp_u8",
        "lnir_px_bt2020_to_bt709_uv_u8",
    ),
    "lean_native_luma_acceptance_16x16_u8": (
        "lnir_px_down2x2",
        "lnir_px_down3x3_u8",
        "lnir_px_bilinear_q8",
        "lnir_px_luma_acceptance_accum",
        "lnir_px_luma_acceptance_gate",
    ),
    "lean_native_luma_acceptance_16x16_u16le": (
        "lnir_px_extract_u16le_msb8",
        "lnir_px_down2x2",
        "lnir_px_down3x3_u8",
        "lnir_px_bilinear_q8",
        "lnir_px_luma_acceptance_accum",
        "lnir_px_luma_acceptance_gate",
    ),
}


def gen_shells_1_to_6() -> str:
    return """\
define weak_odr dso_local void @lean_native_swscale_down2x2_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %cw = icmp eq i64 %dstW, 0
  %ch = icmp eq i64 %dstH, 0
  %empty = or i1 %cw, %ch
  br i1 %empty, label %exit, label %row.body
row.body:
  %dy = phi i64 [ 0, %entry ], [ %dy.next, %row.latch ]
  %sy0 = shl i64 %dy, 1
  %sy1 = or i64 %sy0, 1
  %r0 = mul i64 %sy0, %srcStride
  %r1 = mul i64 %sy1, %srcStride
  %drow = mul i64 %dy, %dstW
  br label %col.body
col.body:
  %dx = phi i64 [ 0, %row.body ], [ %dx.next, %col.body ]
  %sx0 = shl i64 %dx, 1
  %sx1 = or i64 %sx0, 1
  %i00 = add i64 %r0, %sx0
  %i01 = add i64 %r0, %sx1
  %i10 = add i64 %r1, %sx0
  %i11 = add i64 %r1, %sx1
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %s0 = add i64 %v00, %v01
  %s1 = add i64 %v10, %v11
  %sum4 = add i64 %s0, %s1
  %avg64 = call i64 @lnir_px_down2x2(i64 %sum4)
  %out8 = trunc i64 %avg64 to i8
  %di = add i64 %drow, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %out8, ptr %dp, align 1
  %dx.next = add i64 %dx, 1
  %cdone = icmp eq i64 %dx.next, %dstW
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %dy.next = add i64 %dy, 1
  %rdone = icmp eq i64 %dy.next, %dstH
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down2x2_fused_eq_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH, i64 noundef %contrastQ8_64, i64 noundef %brightness64) #0 {
entry:
  %cw = icmp eq i64 %dstW, 0
  %ch = icmp eq i64 %dstH, 0
  %empty = or i1 %cw, %ch
  br i1 %empty, label %exit, label %check.ident
check.ident:
  %c32 = trunc i64 %contrastQ8_64 to i32
  %b32 = trunc i64 %brightness64 to i32
  %is256 = icmp eq i32 %c32, 256
  %is0 = icmp eq i32 %b32, 0
  %ident = and i1 %is256, %is0
  br i1 %ident, label %fast.ident, label %row.body
fast.ident:
  call void @lean_native_swscale_down2x2_u8(ptr %dst, ptr %src, i64 %srcStride, i64 %dstW, i64 %dstH)
  ret void
row.body:
  %dy = phi i64 [ 0, %check.ident ], [ %dy.next, %row.latch ]
  %sy0 = shl i64 %dy, 1
  %sy1 = or i64 %sy0, 1
  %r0 = mul i64 %sy0, %srcStride
  %r1 = mul i64 %sy1, %srcStride
  %drow = mul i64 %dy, %dstW
  br label %col.body
col.body:
  %dx = phi i64 [ 0, %row.body ], [ %dx.next, %col.body ]
  %sx0 = shl i64 %dx, 1
  %sx1 = or i64 %sx0, 1
  %i00 = add i64 %r0, %sx0
  %i01 = add i64 %r0, %sx1
  %i10 = add i64 %r1, %sx0
  %i11 = add i64 %r1, %sx1
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %s0 = add i64 %v00, %v01
  %s1 = add i64 %v10, %v11
  %sum4 = add i64 %s0, %s1
  %res64 = call i64 @lnir_px_down2x2_fused_eq_u8(i64 %sum4, i64 %contrastQ8_64, i64 %brightness64)
  %out8 = trunc i64 %res64 to i8
  %di = add i64 %drow, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %out8, ptr %dp, align 1
  %dx.next = add i64 %dx, 1
  %cdone = icmp eq i64 %dx.next, %dstW
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %dy.next = add i64 %dy, 1
  %rdone = icmp eq i64 %dy.next, %dstH
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %cw = icmp eq i64 %dstW, 0
  %ch = icmp eq i64 %dstH, 0
  %empty = or i1 %cw, %ch
  br i1 %empty, label %exit, label %row.body
row.body:
  %dy = phi i64 [ 0, %entry ], [ %dy.next, %row.latch ]
  %sy0 = mul i64 %dy, 3
  %sy1 = add i64 %sy0, 1
  %sy2 = add i64 %sy0, 2
  %r0 = mul i64 %sy0, %srcW
  %r1 = mul i64 %sy1, %srcW
  %r2 = mul i64 %sy2, %srcW
  %drow = mul i64 %dy, %dstW
  br label %col.body
col.body:
  %dx = phi i64 [ 0, %row.body ], [ %dx.next, %col.body ]
  %sx0 = mul i64 %dx, 3
  %sx1 = add i64 %sx0, 1
  %sx2 = add i64 %sx0, 2
  %i00 = add i64 %r0, %sx0
  %i01 = add i64 %r0, %sx1
  %i02 = add i64 %r0, %sx2
  %i10 = add i64 %r1, %sx0
  %i11 = add i64 %r1, %sx1
  %i12 = add i64 %r1, %sx2
  %i20 = add i64 %r2, %sx0
  %i21 = add i64 %r2, %sx1
  %i22 = add i64 %r2, %sx2
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p02 = getelementptr i8, ptr %src, i64 %i02
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %p12 = getelementptr i8, ptr %src, i64 %i12
  %p20 = getelementptr i8, ptr %src, i64 %i20
  %p21 = getelementptr i8, ptr %src, i64 %i21
  %p22 = getelementptr i8, ptr %src, i64 %i22
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b02 = load i8, ptr %p02, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %b12 = load i8, ptr %p12, align 1
  %b20 = load i8, ptr %p20, align 1
  %b21 = load i8, ptr %p21, align 1
  %b22 = load i8, ptr %p22, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v02 = zext i8 %b02 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %v12 = zext i8 %b12 to i64
  %v20 = zext i8 %b20 to i64
  %v21 = zext i8 %b21 to i64
  %v22 = zext i8 %b22 to i64
  %s0a = add i64 %v00, %v01
  %s0 = add i64 %s0a, %v02
  %s1a = add i64 %v10, %v11
  %s1 = add i64 %s1a, %v12
  %s2a = add i64 %v20, %v21
  %s2 = add i64 %s2a, %v22
  %s01 = add i64 %s0, %s1
  %sum9 = add i64 %s01, %s2
  %avg64 = call i64 @lnir_px_down3x3_u8(i64 %sum9)
  %out8 = trunc i64 %avg64 to i8
  %di = add i64 %drow, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %out8, ptr %dp, align 1
  %dx.next = add i64 %dx, 1
  %cdone = icmp eq i64 %dx.next, %dstW
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %dy.next = add i64 %dy, 1
  %rdone = icmp eq i64 %dy.next, %dstH
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down3to2_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %cw = icmp eq i64 %dstW, 0
  %ch = icmp eq i64 %dstH, 0
  %empty = or i1 %cw, %ch
  br i1 %empty, label %exit, label %row.body
row.body:
  %dy = phi i64 [ 0, %entry ], [ %dy.next, %row.latch ]
  %dyh = lshr i64 %dy, 1
  %syb = mul i64 %dyh, 3
  %oddY = and i64 %dy, 1
  %syA = add i64 %syb, %oddY
  %syB = add i64 %syA, 1
  %rA = mul i64 %syA, %srcW
  %rB = mul i64 %syB, %srcW
  %drow = mul i64 %dy, %dstW
  br label %col.body
col.body:
  %dx = phi i64 [ 0, %row.body ], [ %dx.next, %col.body ]
  %dxh = lshr i64 %dx, 1
  %sxb = mul i64 %dxh, 3
  %oddX = and i64 %dx, 1
  %sxA = add i64 %sxb, %oddX
  %sxB = add i64 %sxA, 1
  %i00 = add i64 %rA, %sxA
  %i01 = add i64 %rA, %sxB
  %i10 = add i64 %rB, %sxA
  %i11 = add i64 %rB, %sxB
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %avg64 = call i64 @lnir_px_down3to2_u8(i64 %v00, i64 %v01, i64 %v10, i64 %v11, i64 %oddX, i64 %oddY)
  %out8 = trunc i64 %avg64 to i8
  %di = add i64 %drow, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %out8, ptr %dp, align 1
  %dx.next = add i64 %dx, 1
  %cdone = icmp eq i64 %dx.next, %dstW
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %dy.next = add i64 %dy, 1
  %rdone = icmp eq i64 %dy.next, %dstH
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_av1_cdef_filter_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h, i64 noundef %priStr64, i64 noundef %damping64) #0 {
entry:
  %total = mul i64 %w, %h
  %has.bytes = icmp ugt i64 %total, 0
  br i1 %has.bytes, label %copy.init, label %exit
copy.init:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)
  %wlt = icmp ult i64 %w, 3
  %hlt = icmp ult i64 %h, 3
  %pri32 = trunc i64 %priStr64 to i32
  %ple0 = icmp sle i32 %pri32, 0
  %sk0 = or i1 %wlt, %hlt
  %skip = or i1 %sk0, %ple0
  br i1 %skip, label %exit, label %outer.ph
outer.ph:
  %hlim = sub i64 %h, 1
  %wlim = sub i64 %w, 1
  br label %row.body
row.body:
  %r = phi i64 [ 1, %outer.ph ], [ %r.next, %row.latch ]
  %rm1 = sub i64 %r, 1
  %rp1 = add i64 %r, 1
  %roff = mul i64 %r, %w
  %uoff = mul i64 %rm1, %w
  %doff = mul i64 %rp1, %w
  br label %col.body
col.body:
  %c = phi i64 [ 1, %row.body ], [ %c.next, %col.body ]
  %cm1 = sub i64 %c, 1
  %cp1 = add i64 %c, 1
  %ic = add i64 %roff, %c
  %in0 = add i64 %roff, %cm1
  %in1 = add i64 %roff, %cp1
  %in2 = add i64 %uoff, %c
  %in3 = add i64 %doff, %c
  %pc = getelementptr i8, ptr %src, i64 %ic
  %pn0 = getelementptr i8, ptr %src, i64 %in0
  %pn1 = getelementptr i8, ptr %src, i64 %in1
  %pn2 = getelementptr i8, ptr %src, i64 %in2
  %pn3 = getelementptr i8, ptr %src, i64 %in3
  %bc = load i8, ptr %pc, align 1
  %bn0 = load i8, ptr %pn0, align 1
  %bn1 = load i8, ptr %pn1, align 1
  %bn2 = load i8, ptr %pn2, align 1
  %bn3 = load i8, ptr %pn3, align 1
  %vc = zext i8 %bc to i64
  %vn0 = zext i8 %bn0 to i64
  %vn1 = zext i8 %bn1 to i64
  %vn2 = zext i8 %bn2 to i64
  %vn3 = zext i8 %bn3 to i64
  %t0 = call i64 @lnir_px_av1_cdef_tap(i64 %vn0, i64 %vc, i64 %priStr64, i64 %damping64)
  %t1 = call i64 @lnir_px_av1_cdef_tap(i64 %vn1, i64 %vc, i64 %priStr64, i64 %damping64)
  %t2 = call i64 @lnir_px_av1_cdef_tap(i64 %vn2, i64 %vc, i64 %priStr64, i64 %damping64)
  %t3 = call i64 @lnir_px_av1_cdef_tap(i64 %vn3, i64 %vc, i64 %priStr64, i64 %damping64)
  %out64 = call i64 @lnir_px_av1_cdef_filter4_u8(i64 %vc, i64 %t0, i64 %t1, i64 %t2, i64 %t3)
  %out8 = trunc i64 %out64 to i8
  %dp = getelementptr i8, ptr %dst, i64 %ic
  store i8 %out8, ptr %dp, align 1
  %c.next = add i64 %c, 1
  %cdone = icmp eq i64 %c.next, %wlim
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %r.next = add i64 %r, 1
  %rdone = icmp eq i64 %r.next, %hlim
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_stencil2d_box3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h) #0 {
entry:
  %total = mul i64 %w, %h
  %has.bytes = icmp ugt i64 %total, 0
  br i1 %has.bytes, label %copy.init, label %exit
copy.init:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)
  %wlt = icmp ult i64 %w, 3
  %hlt = icmp ult i64 %h, 3
  %skip = or i1 %wlt, %hlt
  br i1 %skip, label %exit, label %outer.ph
outer.ph:
  %hlim = sub i64 %h, 1
  %wlim = sub i64 %w, 1
  br label %row.body
row.body:
  %r = phi i64 [ 1, %outer.ph ], [ %r.next, %row.latch ]
  %rm1 = sub i64 %r, 1
  %rp1 = add i64 %r, 1
  %uoff = mul i64 %rm1, %w
  %roff = mul i64 %r, %w
  %doff = mul i64 %rp1, %w
  br label %col.body
col.body:
  %c = phi i64 [ 1, %row.body ], [ %c.next, %col.body ]
  %cm1 = sub i64 %c, 1
  %cp1 = add i64 %c, 1
  %i00 = add i64 %uoff, %cm1
  %i01 = add i64 %uoff, %c
  %i02 = add i64 %uoff, %cp1
  %i10 = add i64 %roff, %cm1
  %i11 = add i64 %roff, %c
  %i12 = add i64 %roff, %cp1
  %i20 = add i64 %doff, %cm1
  %i21 = add i64 %doff, %c
  %i22 = add i64 %doff, %cp1
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p02 = getelementptr i8, ptr %src, i64 %i02
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %p12 = getelementptr i8, ptr %src, i64 %i12
  %p20 = getelementptr i8, ptr %src, i64 %i20
  %p21 = getelementptr i8, ptr %src, i64 %i21
  %p22 = getelementptr i8, ptr %src, i64 %i22
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b02 = load i8, ptr %p02, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %b12 = load i8, ptr %p12, align 1
  %b20 = load i8, ptr %p20, align 1
  %b21 = load i8, ptr %p21, align 1
  %b22 = load i8, ptr %p22, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v02 = zext i8 %b02 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %v12 = zext i8 %b12 to i64
  %v20 = zext i8 %b20 to i64
  %v21 = zext i8 %b21 to i64
  %v22 = zext i8 %b22 to i64
  %s0a = add i64 %v00, %v01
  %s0 = add i64 %s0a, %v02
  %s1a = add i64 %v10, %v11
  %s1 = add i64 %s1a, %v12
  %s2a = add i64 %v20, %v21
  %s2 = add i64 %s2a, %v22
  %s01 = add i64 %s0, %s1
  %sum9 = add i64 %s01, %s2
  %avg64 = call i64 @lnir_px_down3x3_u8(i64 %sum9)
  %out8 = trunc i64 %avg64 to i8
  %dp = getelementptr i8, ptr %dst, i64 %i11
  store i8 %out8, ptr %dp, align 1
  %c.next = add i64 %c, 1
  %cdone = icmp eq i64 %c.next, %wlim
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %r.next = add i64 %r, 1
  %rdone = icmp eq i64 %r.next, %hlim
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}
"""


def gen_shells_7_to_12() -> str:
    return """\
define weak_odr dso_local i64 @lean_native_luma_stats_u8(ptr noalias noundef readonly %src, i64 noundef %nPixels, i64 noundef %step) #0 {
entry:
  %has.px = icmp ugt i64 %nPixels, 0
  %has.st = icmp ugt i64 %step, 0
  %ok = and i1 %has.px, %has.st
  br i1 %ok, label %loop.body, label %exit.zero
loop.body:
  %idx = phi i64 [ 0, %entry ], [ %idx.next, %loop.body ]
  %sum = phi i64 [ 0, %entry ], [ %sum.next, %loop.body ]
  %sumSq = phi i64 [ 0, %entry ], [ %sumSq.next, %loop.body ]
  %cnt = phi i64 [ 0, %entry ], [ %cnt.next, %loop.body ]
  %p = getelementptr i8, ptr %src, i64 %idx
  %b = load i8, ptr %p, align 1
  %v = zext i8 %b to i64
  %v2 = mul i64 %v, %v
  %sum.next = add i64 %sum, %v
  %sumSq.next = add i64 %sumSq, %v2
  %cnt.next = add i64 %cnt, 1
  %idx.next = add i64 %idx, %step
  %rem = sub i64 %nPixels, %idx
  %more = icmp ult i64 %step, %rem
  br i1 %more, label %loop.body, label %compute.out
compute.out:
  %packed = call i64 @lnir_px_luma_stats_pack(i64 %sum.next, i64 %sumSq.next, i64 %cnt.next)
  ret i64 %packed
exit.zero:
  ret i64 0
}

define weak_odr dso_local i64 @lean_native_luma_stats_u16le(ptr noalias noundef readonly %src, i64 noundef %nPixels, i64 noundef %step) #0 {
entry:
  %has.px = icmp ugt i64 %nPixels, 0
  %has.st = icmp ugt i64 %step, 0
  %ok = and i1 %has.px, %has.st
  br i1 %ok, label %loop.body, label %exit.zero
loop.body:
  %idx = phi i64 [ 0, %entry ], [ %idx.next, %loop.body ]
  %sum = phi i64 [ 0, %entry ], [ %sum.next, %loop.body ]
  %sumSq = phi i64 [ 0, %entry ], [ %sumSq.next, %loop.body ]
  %cnt = phi i64 [ 0, %entry ], [ %cnt.next, %loop.body ]
  %p = getelementptr i16, ptr %src, i64 %idx
  %b = load i16, ptr %p, align 1
  %raw = zext i16 %b to i64
  %v = call i64 @lnir_px_u16le_to_u10(i64 %raw)
  %v2 = mul i64 %v, %v
  %sum.next = add i64 %sum, %v
  %sumSq.next = add i64 %sumSq, %v2
  %cnt.next = add i64 %cnt, 1
  %idx.next = add i64 %idx, %step
  %rem = sub i64 %nPixels, %idx
  %more = icmp ult i64 %step, %rem
  br i1 %more, label %loop.body, label %compute.out
compute.out:
  %packed = call i64 @lnir_px_luma_stats_pack(i64 %sum.next, i64 %sumSq.next, i64 %cnt.next)
  ret i64 %packed
exit.zero:
  ret i64 0
}

define weak_odr dso_local void @lean_native_swscale_bilinear_q8_u8(ptr noalias noundef %dst, ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %sw0 = icmp eq i64 %srcW, 0
  %sh0 = icmp eq i64 %srcH, 0
  %dw0 = icmp eq i64 %dstW, 0
  %dh0 = icmp eq i64 %dstH, 0
  %s0 = or i1 %sw0, %sh0
  %d0 = or i1 %dw0, %dh0
  %empty = or i1 %s0, %d0
  br i1 %empty, label %exit, label %outer.ph
outer.ph:
  %lastX = sub i64 %srcW, 1
  %lastY = sub i64 %srcH, 1
  %sw128 = zext i64 %srcW to i128
  %sh128 = zext i64 %srcH to i128
  %dw128 = zext i64 %dstW to i128
  %dh128 = zext i64 %dstH to i128
  %scaleX = shl i128 %sw128, 8
  %scaleY = shl i128 %sh128, 8
  br label %row.body
row.body:
  %dy = phi i64 [ 0, %outer.ph ], [ %dy.next, %row.latch ]
  %dy128 = zext i64 %dy to i128
  %ny = mul i128 %dy128, %scaleY
  %qy128 = udiv i128 %ny, %dh128
  %qy = trunc i128 %qy128 to i64
  %rawY = lshr i64 %qy, 8
  %yin = icmp ult i64 %rawY, %srcH
  %sy0 = select i1 %yin, i64 %rawY, i64 %lastY
  %yp1 = add i64 %sy0, 1
  %ynin = icmp ult i64 %yp1, %srcH
  %sy1 = select i1 %ynin, i64 %yp1, i64 %lastY
  %fy = and i64 %qy, 255
  %r0 = mul i64 %sy0, %srcStride
  %r1 = mul i64 %sy1, %srcStride
  %drow = mul i64 %dy, %dstW
  br label %col.body
col.body:
  %dx = phi i64 [ 0, %row.body ], [ %dx.next, %col.body ]
  %dx128 = zext i64 %dx to i128
  %nx = mul i128 %dx128, %scaleX
  %qx128 = udiv i128 %nx, %dw128
  %qx = trunc i128 %qx128 to i64
  %rawX = lshr i64 %qx, 8
  %xin = icmp ult i64 %rawX, %srcW
  %sx0 = select i1 %xin, i64 %rawX, i64 %lastX
  %xp1 = add i64 %sx0, 1
  %xnin = icmp ult i64 %xp1, %srcW
  %sx1 = select i1 %xnin, i64 %xp1, i64 %lastX
  %fx = and i64 %qx, 255
  %i00 = add i64 %r0, %sx0
  %i01 = add i64 %r0, %sx1
  %i10 = add i64 %r1, %sx0
  %i11 = add i64 %r1, %sx1
  %p00 = getelementptr i8, ptr %src, i64 %i00
  %p01 = getelementptr i8, ptr %src, i64 %i01
  %p10 = getelementptr i8, ptr %src, i64 %i10
  %p11 = getelementptr i8, ptr %src, i64 %i11
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %v00 = zext i8 %b00 to i64
  %v01 = zext i8 %b01 to i64
  %v10 = zext i8 %b10 to i64
  %v11 = zext i8 %b11 to i64
  %out64 = call i64 @lnir_px_bilinear_q8(i64 %v00, i64 %v01, i64 %v10, i64 %v11, i64 %fx, i64 %fy)
  %out8 = trunc i64 %out64 to i8
  %di = add i64 %drow, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %out8, ptr %dp, align 1
  %dx.next = add i64 %dx, 1
  %cdone = icmp eq i64 %dx.next, %dstW
  br i1 %cdone, label %row.latch, label %col.body
row.latch:
  %dy.next = add i64 %dy, 1
  %rdone = icmp eq i64 %dy.next, %dstH
  br i1 %rdone, label %exit, label %row.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_bilinear_q8_u16le(ptr noalias noundef readonly %src, ptr noalias noundef %dst, i64 noundef %sw, i64 noundef %sh, i64 noundef %dw, i64 noundef %dh) #0 {
entry:
  %sw0 = icmp eq i64 %sw, 0
  %sh0 = icmp eq i64 %sh, 0
  %dw0 = icmp eq i64 %dw, 0
  %dh0 = icmp eq i64 %dh, 0
  %s0 = or i1 %sw0, %sh0
  %d0 = or i1 %dw0, %dh0
  %empty = or i1 %s0, %d0
  br i1 %empty, label %exit, label %check.same
check.same:
  %samew = icmp eq i64 %sw, %dw
  %sameh = icmp eq i64 %sh, %dh
  %same = and i1 %samew, %sameh
  br i1 %same, label %do.copy, label %dispatch
do.copy:
  %pixels = mul i64 %sw, %sh
  %bytes = shl i64 %pixels, 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %bytes, i1 false)
  ret void
dispatch:
  %sw128 = zext i64 %sw to i128
  %sh128 = zext i64 %sh to i128
  %dw128 = zext i64 %dw to i128
  %dh128 = zext i64 %dh to i128
  %w2 = mul i128 %dw128, 2
  %h2 = mul i128 %dh128, 2
  %eqw2 = icmp eq i128 %sw128, %w2
  %eqh2 = icmp eq i128 %sh128, %h2
  %is2 = and i1 %eqw2, %eqh2
  br i1 %is2, label %b2.row, label %check.3
check.3:
  %w3 = mul i128 %dw128, 3
  %h3 = mul i128 %dh128, 3
  %eqw3 = icmp eq i128 %sw128, %w3
  %eqh3 = icmp eq i128 %sh128, %h3
  %is3 = and i1 %eqw3, %eqh3
  br i1 %is3, label %b3.row, label %check.3to2
b2.row:
  %y2 = phi i64 [ 0, %dispatch ], [ %y2.next, %b2.latch ]
  %sy2_0 = shl i64 %y2, 1
  %sy2_1 = or i64 %sy2_0, 1
  %r2_0 = mul i64 %sy2_0, %sw
  %r2_1 = mul i64 %sy2_1, %sw
  %dr2 = mul i64 %y2, %dw
  br label %b2.col
b2.col:
  %x2 = phi i64 [ 0, %b2.row ], [ %x2.next, %b2.col ]
  %sx2_0 = shl i64 %x2, 1
  %sx2_1 = or i64 %sx2_0, 1
  %i2_00 = add i64 %r2_0, %sx2_0
  %i2_01 = add i64 %r2_0, %sx2_1
  %i2_10 = add i64 %r2_1, %sx2_0
  %i2_11 = add i64 %r2_1, %sx2_1
  %p2_00 = getelementptr i16, ptr %src, i64 %i2_00
  %p2_01 = getelementptr i16, ptr %src, i64 %i2_01
  %p2_10 = getelementptr i16, ptr %src, i64 %i2_10
  %p2_11 = getelementptr i16, ptr %src, i64 %i2_11
  %u2_00 = load i16, ptr %p2_00, align 1
  %u2_01 = load i16, ptr %p2_01, align 1
  %u2_10 = load i16, ptr %p2_10, align 1
  %u2_11 = load i16, ptr %p2_11, align 1
  %v2_00 = zext i16 %u2_00 to i64
  %v2_01 = zext i16 %u2_01 to i64
  %v2_10 = zext i16 %u2_10 to i64
  %v2_11 = zext i16 %u2_11 to i64
  %s2_0 = add i64 %v2_00, %v2_01
  %s2_1 = add i64 %v2_10, %v2_11
  %sum2_4 = add i64 %s2_0, %s2_1
  %avg2 = call i64 @lnir_px_down2x2(i64 %sum2_4)
  %out2 = trunc i64 %avg2 to i16
  %di2 = add i64 %dr2, %x2
  %dp2 = getelementptr i16, ptr %dst, i64 %di2
  store i16 %out2, ptr %dp2, align 1
  %x2.next = add i64 %x2, 1
  %c2done = icmp eq i64 %x2.next, %dw
  br i1 %c2done, label %b2.latch, label %b2.col
b2.latch:
  %y2.next = add i64 %y2, 1
  %r2done = icmp eq i64 %y2.next, %dh
  br i1 %r2done, label %exit, label %b2.row
b3.row:
  %y3 = phi i64 [ 0, %check.3 ], [ %y3.next, %b3.latch ]
  %sy3_0 = mul i64 %y3, 3
  %sy3_1 = add i64 %sy3_0, 1
  %sy3_2 = add i64 %sy3_0, 2
  %r3_0 = mul i64 %sy3_0, %sw
  %r3_1 = mul i64 %sy3_1, %sw
  %r3_2 = mul i64 %sy3_2, %sw
  %dr3 = mul i64 %y3, %dw
  br label %b3.col
b3.col:
  %x3 = phi i64 [ 0, %b3.row ], [ %x3.next, %b3.col ]
  %sx3_0 = mul i64 %x3, 3
  %sx3_1 = add i64 %sx3_0, 1
  %sx3_2 = add i64 %sx3_0, 2
  %i3_00 = add i64 %r3_0, %sx3_0
  %i3_01 = add i64 %r3_0, %sx3_1
  %i3_02 = add i64 %r3_0, %sx3_2
  %i3_10 = add i64 %r3_1, %sx3_0
  %i3_11 = add i64 %r3_1, %sx3_1
  %i3_12 = add i64 %r3_1, %sx3_2
  %i3_20 = add i64 %r3_2, %sx3_0
  %i3_21 = add i64 %r3_2, %sx3_1
  %i3_22 = add i64 %r3_2, %sx3_2
  %p3_00 = getelementptr i16, ptr %src, i64 %i3_00
  %p3_01 = getelementptr i16, ptr %src, i64 %i3_01
  %p3_02 = getelementptr i16, ptr %src, i64 %i3_02
  %p3_10 = getelementptr i16, ptr %src, i64 %i3_10
  %p3_11 = getelementptr i16, ptr %src, i64 %i3_11
  %p3_12 = getelementptr i16, ptr %src, i64 %i3_12
  %p3_20 = getelementptr i16, ptr %src, i64 %i3_20
  %p3_21 = getelementptr i16, ptr %src, i64 %i3_21
  %p3_22 = getelementptr i16, ptr %src, i64 %i3_22
  %u3_00 = load i16, ptr %p3_00, align 1
  %u3_01 = load i16, ptr %p3_01, align 1
  %u3_02 = load i16, ptr %p3_02, align 1
  %u3_10 = load i16, ptr %p3_10, align 1
  %u3_11 = load i16, ptr %p3_11, align 1
  %u3_12 = load i16, ptr %p3_12, align 1
  %u3_20 = load i16, ptr %p3_20, align 1
  %u3_21 = load i16, ptr %p3_21, align 1
  %u3_22 = load i16, ptr %p3_22, align 1
  %v3_00 = zext i16 %u3_00 to i64
  %v3_01 = zext i16 %u3_01 to i64
  %v3_02 = zext i16 %u3_02 to i64
  %v3_10 = zext i16 %u3_10 to i64
  %v3_11 = zext i16 %u3_11 to i64
  %v3_12 = zext i16 %u3_12 to i64
  %v3_20 = zext i16 %u3_20 to i64
  %v3_21 = zext i16 %u3_21 to i64
  %v3_22 = zext i16 %u3_22 to i64
  %s3_0a = add i64 %v3_00, %v3_01
  %s3_0 = add i64 %s3_0a, %v3_02
  %s3_1a = add i64 %v3_10, %v3_11
  %s3_1 = add i64 %s3_1a, %v3_12
  %s3_2a = add i64 %v3_20, %v3_21
  %s3_2 = add i64 %s3_2a, %v3_22
  %s3_01 = add i64 %s3_0, %s3_1
  %sum3_9 = add i64 %s3_01, %s3_2
  %avg3 = call i64 @lnir_px_down3x3_u16(i64 %sum3_9)
  %out3 = trunc i64 %avg3 to i16
  %di3 = add i64 %dr3, %x3
  %dp3 = getelementptr i16, ptr %dst, i64 %di3
  store i16 %out3, ptr %dp3, align 1
  %x3.next = add i64 %x3, 1
  %c3done = icmp eq i64 %x3.next, %dw
  br i1 %c3done, label %b3.latch, label %b3.col
b3.latch:
  %y3.next = add i64 %y3, 1
  %r3done = icmp eq i64 %y3.next, %dh
  br i1 %r3done, label %exit, label %b3.row
check.3to2:
  %sw2 = shl i128 %sw128, 1
  %sh2 = shl i128 %sh128, 1
  %rw = icmp eq i128 %sw2, %w3
  %rh = icmp eq i128 %sh2, %h3
  %mw = icmp uge i64 %sw, 3
  %mh = icmp uge i64 %sh, 3
  %r32 = and i1 %rw, %rh
  %m32 = and i1 %mw, %mh
  %is3to2 = and i1 %r32, %m32
  br i1 %is3to2, label %b32.row, label %q.setup
b32.row:
  %y32 = phi i64 [ 0, %check.3to2 ], [ %y32.next, %b32.latch ]
  %yh = lshr i64 %y32, 1
  %sy32_0 = add i64 %y32, %yh
  %yp = and i64 %y32, 1
  %sy32_1 = add i64 %sy32_0, %yp
  %r32_0 = mul i64 %sy32_0, %sw
  %r32_1 = mul i64 %sy32_1, %sw
  %dr32 = mul i64 %y32, %dw
  br label %b32.col
b32.col:
  %x32 = phi i64 [ 0, %b32.row ], [ %x32.next, %b32.col ]
  %xh = lshr i64 %x32, 1
  %sx32_0 = add i64 %x32, %xh
  %xp = and i64 %x32, 1
  %sx32_1 = add i64 %sx32_0, %xp
  %i32_00 = add i64 %r32_0, %sx32_0
  %i32_01 = add i64 %r32_0, %sx32_1
  %i32_10 = add i64 %r32_1, %sx32_0
  %i32_11 = add i64 %r32_1, %sx32_1
  %p32_00 = getelementptr i16, ptr %src, i64 %i32_00
  %p32_01 = getelementptr i16, ptr %src, i64 %i32_01
  %p32_10 = getelementptr i16, ptr %src, i64 %i32_10
  %p32_11 = getelementptr i16, ptr %src, i64 %i32_11
  %u32_00 = load i16, ptr %p32_00, align 1
  %u32_01 = load i16, ptr %p32_01, align 1
  %u32_10 = load i16, ptr %p32_10, align 1
  %u32_11 = load i16, ptr %p32_11, align 1
  %v32_00 = zext i16 %u32_00 to i64
  %v32_01 = zext i16 %u32_01 to i64
  %v32_10 = zext i16 %u32_10 to i64
  %v32_11 = zext i16 %u32_11 to i64
  %colA = add i64 %v32_00, %v32_10
  %colB = add i64 %v32_01, %v32_11
  %avg32 = call i64 @lnir_px_down3to2_u16_clamp10(i64 %colA, i64 %colB)
  %out32 = trunc i64 %avg32 to i16
  %di32 = add i64 %dr32, %x32
  %dp32 = getelementptr i16, ptr %dst, i64 %di32
  store i16 %out32, ptr %dp32, align 1
  %x32.next = add i64 %x32, 1
  %c32done = icmp eq i64 %x32.next, %dw
  br i1 %c32done, label %b32.latch, label %b32.col
b32.latch:
  %y32.next = add i64 %y32, 1
  %r32done = icmp eq i64 %y32.next, %dh
  br i1 %r32done, label %exit, label %b32.row
q.setup:
  %lastX = sub i64 %sw, 1
  %lastY = sub i64 %sh, 1
  %scaleX = shl i128 %sw128, 8
  %scaleY = shl i128 %sh128, 8
  br label %q.row
q.row:
  %qy_idx = phi i64 [ 0, %q.setup ], [ %qy.next, %q.latch ]
  %qy128_i = zext i64 %qy_idx to i128
  %qny = mul i128 %qy128_i, %scaleY
  %qqy128 = udiv i128 %qny, %dh128
  %qqy = trunc i128 %qqy128 to i64
  %qrawY = lshr i64 %qqy, 8
  %qyin = icmp ult i64 %qrawY, %sh
  %qsy0 = select i1 %qyin, i64 %qrawY, i64 %lastY
  %qyp1 = add i64 %qsy0, 1
  %qynin = icmp ult i64 %qyp1, %sh
  %qsy1 = select i1 %qynin, i64 %qyp1, i64 %lastY
  %qfy = and i64 %qqy, 255
  %qr0 = mul i64 %qsy0, %sw
  %qr1 = mul i64 %qsy1, %sw
  %qdr = mul i64 %qy_idx, %dw
  br label %q.col
q.col:
  %qx_idx = phi i64 [ 0, %q.row ], [ %qx.next, %q.col ]
  %qx128_i = zext i64 %qx_idx to i128
  %qnx = mul i128 %qx128_i, %scaleX
  %qqx128 = udiv i128 %qnx, %dw128
  %qqx = trunc i128 %qqx128 to i64
  %qrawX = lshr i64 %qqx, 8
  %qxin = icmp ult i64 %qrawX, %sw
  %qsx0 = select i1 %qxin, i64 %qrawX, i64 %lastX
  %qxp1 = add i64 %qsx0, 1
  %qxnin = icmp ult i64 %qxp1, %sw
  %qsx1 = select i1 %qxnin, i64 %qxp1, i64 %lastX
  %qfx = and i64 %qqx, 255
  %qi00 = add i64 %qr0, %qsx0
  %qi01 = add i64 %qr0, %qsx1
  %qi10 = add i64 %qr1, %qsx0
  %qi11 = add i64 %qr1, %qsx1
  %qp00 = getelementptr i16, ptr %src, i64 %qi00
  %qp01 = getelementptr i16, ptr %src, i64 %qi01
  %qp10 = getelementptr i16, ptr %src, i64 %qi10
  %qp11 = getelementptr i16, ptr %src, i64 %qi11
  %qu00 = load i16, ptr %qp00, align 1
  %qu01 = load i16, ptr %qp01, align 1
  %qu10 = load i16, ptr %qp10, align 1
  %qu11 = load i16, ptr %qp11, align 1
  %qv00 = zext i16 %qu00 to i64
  %qv01 = zext i16 %qu01 to i64
  %qv10 = zext i16 %qu10 to i64
  %qv11 = zext i16 %qu11 to i64
  %qres = call i64 @lnir_px_bilinear_q8_clamp10(i64 %qv00, i64 %qv01, i64 %qv10, i64 %qv11, i64 %qfx, i64 %qfy)
  %qout = trunc i64 %qres to i16
  %qdi = add i64 %qdr, %qx_idx
  %qdp = getelementptr i16, ptr %dst, i64 %qdi
  store i16 %qout, ptr %qdp, align 1
  %qx.next = add i64 %qx_idx, 1
  %qcdone = icmp eq i64 %qx.next, %dw
  br i1 %qcdone, label %q.latch, label %q.col
q.latch:
  %qy.next = add i64 %qy_idx, 1
  %qrdone = icmp eq i64 %qy.next, %dh
  br i1 %qrdone, label %exit, label %q.row
exit:
  ret void
}

define weak_odr dso_local void @lean_native_extract_u16le_msb8(ptr noalias noundef readonly %src, ptr noalias noundef %dst, i64 noundef %n) #0 {
entry:
  %has = icmp ugt i64 %n, 0
  br i1 %has, label %loop.body, label %exit
loop.body:
  %i = phi i64 [ 0, %entry ], [ %i.next, %loop.body ]
  %sp = getelementptr i16, ptr %src, i64 %i
  %raw16 = load i16, ptr %sp, align 1
  %raw64 = zext i16 %raw16 to i64
  %msb64 = call i64 @lnir_px_extract_u16le_msb8(i64 %raw64)
  %msb8 = trunc i64 %msb64 to i8
  %dp = getelementptr i8, ptr %dst, i64 %i
  store i8 %msb8, ptr %dp, align 1
  %i.next = add i64 %i, 1
  %done = icmp eq i64 %i.next, %n
  br i1 %done, label %exit, label %loop.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_apply_filters_yuv420p_u8(ptr noundef %src, ptr noundef %dst, i64 noundef %y_len, i64 noundef %uv_len, i64 noundef %flags) #0 {
entry:
  %yf = and i64 %flags, 2
  %cf = and i64 %flags, 1
  %tonemap = icmp ne i64 %yf, 0
  %csc = icmp ne i64 %cf, 0
  %same.ptr = icmp eq ptr %src, %dst
  %su = getelementptr i8, ptr %src, i64 %y_len
  %sv = getelementptr i8, ptr %su, i64 %uv_len
  %du = getelementptr i8, ptr %dst, i64 %y_len
  %dv = getelementptr i8, ptr %du, i64 %uv_len
  br i1 %tonemap, label %y.check, label %y.pass
y.pass:
  br i1 %same.ptr, label %c.dispatch, label %y.copycheck
y.copycheck:
  %y.pos = icmp ugt i64 %y_len, 0
  br i1 %y.pos, label %y.copy, label %c.dispatch
y.copy:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %y_len, i1 false)
  br label %c.dispatch
y.check:
  %yi = phi i64 [ 0, %entry ], [ %yi.next, %y.body ]
  %ymore = icmp ult i64 %yi, %y_len
  br i1 %ymore, label %y.body, label %c.dispatch
y.body:
  %ysp = getelementptr i8, ptr %src, i64 %yi
  %ydp = getelementptr i8, ptr %dst, i64 %yi
  %yb = load i8, ptr %ysp, align 1
  %y64 = zext i8 %yb to i64
  %ycl = call i64 @lnir_px_y_studio_clamp_u8(i64 %y64)
  %yout = trunc i64 %ycl to i8
  store i8 %yout, ptr %ydp, align 1
  %yi.next = add i64 %yi, 1
  br label %y.check
c.dispatch:
  br i1 %csc, label %c.check, label %c.pass
c.pass:
  br i1 %same.ptr, label %done, label %c.copycheck
c.copycheck:
  %uv2.len = shl i64 %uv_len, 1
  %uv.pos = icmp ugt i64 %uv2.len, 0
  br i1 %uv.pos, label %c.copy, label %done
c.copy:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %du, ptr align 1 %su, i64 %uv2.len, i1 false)
  br label %done
c.check:
  %ci = phi i64 [ 0, %c.dispatch ], [ %ci.next, %c.body ]
  %cmore = icmp ult i64 %ci, %uv_len
  br i1 %cmore, label %c.body, label %done
c.body:
  %usp = getelementptr i8, ptr %su, i64 %ci
  %vsp = getelementptr i8, ptr %sv, i64 %ci
  %udp = getelementptr i8, ptr %du, i64 %ci
  %vdp = getelementptr i8, ptr %dv, i64 %ci
  %ub = load i8, ptr %usp, align 1
  %vb = load i8, ptr %vsp, align 1
  %u64 = zext i8 %ub to i64
  %v64 = zext i8 %vb to i64
  %uvp = call i64 @lnir_px_bt2020_to_bt709_uv_u8(i64 %u64, i64 %v64)
  %uout = trunc i64 %uvp to i8
  %vhi = lshr i64 %uvp, 8
  %vout = trunc i64 %vhi to i8
  store i8 %uout, ptr %udp, align 1
  store i8 %vout, ptr %vdp, align 1
  %ci.next = add i64 %ci, 1
  br label %c.check
done:
  ret void
}
"""


def _gen_acceptance_load(ptr_reg: str, idx_reg: str, tag: str, is_u16: bool) -> tuple[str, str]:
    if not is_u16:
        lines = [
            f"  %p.{tag} = getelementptr i8, ptr {ptr_reg}, i64 {idx_reg}",
            f"  %b.{tag} = load i8, ptr %p.{tag}, align 1",
            f"  %v.{tag} = zext i8 %b.{tag} to i64",
        ]
        return "\n".join(lines), f"%v.{tag}"
    lines = [
        f"  %p.{tag} = getelementptr i16, ptr {ptr_reg}, i64 {idx_reg}",
        f"  %u.{tag} = load i16, ptr %p.{tag}, align 1",
        f"  %r.{tag} = zext i16 %u.{tag} to i64",
        f"  %v.{tag} = call i64 @lnir_px_extract_u16le_msb8(i64 %r.{tag})",
    ]
    return "\n".join(lines), f"%v.{tag}"


def gen_acceptance_shell(fn_name: str, is_u16: bool) -> str:
    ld_d, vd = _gen_acceptance_load("%dst", "%d.idx", "dst", is_u16)
    ld_1, v1 = _gen_acceptance_load("%src", "%s1.idx", "m1", is_u16)
    ld2_00, v2_00 = _gen_acceptance_load("%src", "%s2.00", "m2_00", is_u16)
    ld2_01, v2_01 = _gen_acceptance_load("%src", "%s2.01", "m2_01", is_u16)
    ld2_10, v2_10 = _gen_acceptance_load("%src", "%s2.10", "m2_10", is_u16)
    ld2_11, v2_11 = _gen_acceptance_load("%src", "%s2.11", "m2_11", is_u16)
    m3_lds = []
    m3_vs = []
    for rr in range(3):
        for cc in range(3):
            code, vr = _gen_acceptance_load("%src", f"%s3.{rr}{cc}", f"m3_{rr}{cc}", is_u16)
            m3_lds.append(code)
            m3_vs.append(vr)
    ldq_00, vq_00 = _gen_acceptance_load("%src", "%sq.00", "mq_00", is_u16)
    ldq_01, vq_01 = _gen_acceptance_load("%src", "%sq.01", "mq_01", is_u16)
    ldq_10, vq_10 = _gen_acceptance_load("%src", "%sq.10", "mq_10", is_u16)
    ldq_11, vq_11 = _gen_acceptance_load("%src", "%sq.11", "mq_11", is_u16)
    m3_block = "\n".join(m3_lds)
    return f"""\
define weak_odr dso_local void @{fn_name}(ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, ptr noalias noundef readonly %dst, i64 noundef %dstW, i64 noundef %dstH, ptr noalias noundef writeonly %outMetrics4) #0 {{
entry:
  store i64 0, ptr %outMetrics4, align 8
  %o1 = getelementptr i64, ptr %outMetrics4, i64 1
  %o2 = getelementptr i64, ptr %outMetrics4, i64 2
  %o3 = getelementptr i64, ptr %outMetrics4, i64 3
  store i64 0, ptr %o1, align 8
  store i64 0, ptr %o2, align 8
  store i64 1, ptr %o3, align 8
  %sw.ok = icmp ugt i64 %srcW, 0
  %sh.ok = icmp ugt i64 %srcH, 0
  %dw.ok = icmp uge i64 %dstW, 16
  %dh.ok = icmp uge i64 %dstH, 16
  %s.ok = and i1 %sw.ok, %sh.ok
  %d.ok = and i1 %dw.ok, %dh.ok
  %ok = and i1 %s.ok, %d.ok
  br i1 %ok, label %setup, label %exit
setup:
  %sw128 = zext i64 %srcW to i128
  %sh128 = zext i64 %srcH to i128
  %dw128 = zext i64 %dstW to i128
  %dh128 = zext i64 %dstH to i128
  %oneW = icmp eq i64 %srcW, %dstW
  %oneH = icmp eq i64 %srcH, %dstH
  %is1 = and i1 %oneW, %oneH
  %w2 = mul i128 %dw128, 2
  %h2 = mul i128 %dh128, 2
  %twoW = icmp eq i128 %sw128, %w2
  %twoH = icmp eq i128 %sh128, %h2
  %is2 = and i1 %twoW, %twoH
  %w3 = mul i128 %dw128, 3
  %h3 = mul i128 %dh128, 3
  %thrW = icmp eq i128 %sw128, %w3
  %thrH = icmp eq i128 %sh128, %h3
  %is3 = and i1 %thrW, %thrH
  %wide = icmp uge i64 %dstW, 256
  %tall = icmp uge i64 %dstH, 256
  %sx = select i1 %wide, i64 64, i64 16
  %sy = select i1 %tall, i64 64, i64 16
  %xlim = sub i64 %dstW, 16
  %ylim = sub i64 %dstH, 16
  %lastX = sub i64 %srcW, 1
  %lastY = sub i64 %srcH, 1
  %scaleX = shl i128 %sw128, 8
  %scaleY = shl i128 %sh128, 8
  br label %by.loop
by.loop:
  %byi = phi i64 [ 0, %setup ], [ %by.next, %by.latch ]
  %max.y = phi i64 [ 0, %setup ], [ %new.max, %by.latch ]
  %sse.y = phi i64 [ 0, %setup ], [ %new.sse, %by.latch ]
  %pix.y = phi i64 [ 0, %setup ], [ %new.pix, %by.latch ]
  %ok.y = phi i64 [ 1, %setup ], [ %new.ok, %by.latch ]
  br label %bx.loop
bx.loop:
  %bxi = phi i64 [ 0, %by.loop ], [ %bx.next, %block.end ]
  %old.max = phi i64 [ %max.y, %by.loop ], [ %new.max, %block.end ]
  %old.sse = phi i64 [ %sse.y, %by.loop ], [ %new.sse, %block.end ]
  %old.pix = phi i64 [ %pix.y, %by.loop ], [ %new.pix, %block.end ]
  %old.ok = phi i64 [ %ok.y, %by.loop ], [ %new.ok, %block.end ]
  br label %py.loop
py.loop:
  %yy = phi i64 [ 0, %bx.loop ], [ %yy.next, %py.latch ]
  %sad.r = phi i64 [ 0, %bx.loop ], [ %sad.next, %py.latch ]
  %blk.r = phi i64 [ 0, %bx.loop ], [ %blk.next, %py.latch ]
  %ref.r = phi i64 [ 0, %bx.loop ], [ %ref.next, %py.latch ]
  %sse.r = phi i64 [ 0, %bx.loop ], [ %sse.next, %py.latch ]
  %y = add i64 %byi, %yy
  %drow = mul i64 %y, %dstW
  br label %px.loop
px.loop:
  %xx = phi i64 [ 0, %py.loop ], [ %xx.next, %px.latch ]
  %sad = phi i64 [ %sad.r, %py.loop ], [ %sad.next, %px.latch ]
  %blk = phi i64 [ %blk.r, %py.loop ], [ %blk.next, %px.latch ]
  %ref = phi i64 [ %ref.r, %py.loop ], [ %ref.next, %px.latch ]
  %sse = phi i64 [ %sse.r, %py.loop ], [ %sse.next, %px.latch ]
  %x = add i64 %bxi, %xx
  %d.idx = add i64 %drow, %x
{ld_d}
  br i1 %is1, label %mode.1, label %check.2
check.2:
  br i1 %is2, label %mode.2, label %check.3
check.3:
  br i1 %is3, label %mode.3, label %mode.q8
mode.1:
  %s1.row = mul i64 %y, %srcW
  %s1.idx = add i64 %s1.row, %x
{ld_1}
  br label %px.latch
mode.2:
  %sy2.0 = shl i64 %y, 1
  %sy2.1 = or i64 %sy2.0, 1
  %sx2.0 = shl i64 %x, 1
  %sx2.1 = or i64 %sx2.0, 1
  %sr2.0 = mul i64 %sy2.0, %srcW
  %sr2.1 = mul i64 %sy2.1, %srcW
  %s2.00 = add i64 %sr2.0, %sx2.0
  %s2.01 = add i64 %sr2.0, %sx2.1
  %s2.10 = add i64 %sr2.1, %sx2.0
  %s2.11 = add i64 %sr2.1, %sx2.1
{ld2_00}
{ld2_01}
{ld2_10}
{ld2_11}
  %m2.s0 = add i64 {v2_00}, {v2_01}
  %m2.s1 = add i64 {v2_10}, {v2_11}
  %m2.sum = add i64 %m2.s0, %m2.s1
  %v.m2 = call i64 @lnir_px_down2x2(i64 %m2.sum)
  br label %px.latch
mode.3:
  %sy3.0 = mul i64 %y, 3
  %sy3.1 = add i64 %sy3.0, 1
  %sy3.2 = add i64 %sy3.0, 2
  %sx3.0 = mul i64 %x, 3
  %sx3.1 = add i64 %sx3.0, 1
  %sx3.2 = add i64 %sx3.0, 2
  %sr3.0 = mul i64 %sy3.0, %srcW
  %sr3.1 = mul i64 %sy3.1, %srcW
  %sr3.2 = mul i64 %sy3.2, %srcW
  %s3.00 = add i64 %sr3.0, %sx3.0
  %s3.01 = add i64 %sr3.0, %sx3.1
  %s3.02 = add i64 %sr3.0, %sx3.2
  %s3.10 = add i64 %sr3.1, %sx3.0
  %s3.11 = add i64 %sr3.1, %sx3.1
  %s3.12 = add i64 %sr3.1, %sx3.2
  %s3.20 = add i64 %sr3.2, %sx3.0
  %s3.21 = add i64 %sr3.2, %sx3.1
  %s3.22 = add i64 %sr3.2, %sx3.2
{m3_block}
  %m3.r0a = add i64 {m3_vs[0]}, {m3_vs[1]}
  %m3.r0 = add i64 %m3.r0a, {m3_vs[2]}
  %m3.r1a = add i64 {m3_vs[3]}, {m3_vs[4]}
  %m3.r1 = add i64 %m3.r1a, {m3_vs[5]}
  %m3.r2a = add i64 {m3_vs[6]}, {m3_vs[7]}
  %m3.r2 = add i64 %m3.r2a, {m3_vs[8]}
  %m3.r01 = add i64 %m3.r0, %m3.r1
  %m3.sum = add i64 %m3.r01, %m3.r2
  %v.m3 = call i64 @lnir_px_down3x3_u8(i64 %m3.sum)
  br label %px.latch
mode.q8:
  %y128 = zext i64 %y to i128
  %x128 = zext i64 %x to i128
  %ny = mul i128 %y128, %scaleY
  %nx = mul i128 %x128, %scaleX
  %qy128 = udiv i128 %ny, %dh128
  %qx128 = udiv i128 %nx, %dw128
  %qy = trunc i128 %qy128 to i64
  %qx = trunc i128 %qx128 to i64
  %rawY = lshr i64 %qy, 8
  %rawX = lshr i64 %qx, 8
  %yin = icmp ult i64 %rawY, %srcH
  %xin = icmp ult i64 %rawX, %srcW
  %qsy0 = select i1 %yin, i64 %rawY, i64 %lastY
  %qsx0 = select i1 %xin, i64 %rawX, i64 %lastX
  %qyp1 = add i64 %qsy0, 1
  %qxp1 = add i64 %qsx0, 1
  %qynin = icmp ult i64 %qyp1, %srcH
  %qxnin = icmp ult i64 %qxp1, %srcW
  %qsy1 = select i1 %qynin, i64 %qyp1, i64 %lastY
  %qsx1 = select i1 %qxnin, i64 %qxp1, i64 %lastX
  %fy = and i64 %qy, 255
  %fx = and i64 %qx, 255
  %qr0 = mul i64 %qsy0, %srcW
  %qr1 = mul i64 %qsy1, %srcW
  %sq.00 = add i64 %qr0, %qsx0
  %sq.01 = add i64 %qr0, %qsx1
  %sq.10 = add i64 %qr1, %qsx0
  %sq.11 = add i64 %qr1, %qsx1
{ldq_00}
{ldq_01}
{ldq_10}
{ldq_11}
  %v.mq = call i64 @lnir_px_bilinear_q8(i64 {vq_00}, i64 {vq_01}, i64 {vq_10}, i64 {vq_11}, i64 %fx, i64 %fy)
  br label %px.latch
px.latch:
  %ref.px = phi i64 [ {v1}, %mode.1 ], [ %v.m2, %mode.2 ], [ %v.m3, %mode.3 ], [ %v.mq, %mode.q8 ]
  %acc = call i64 @lnir_px_luma_acceptance_accum(i64 %ref.px, i64 {vd})
  %d.sad = and i64 %acc, 65535
  %s16 = lshr i64 %acc, 16
  %d.blk = and i64 %s16, 65535
  %s32 = lshr i64 %acc, 32
  %d.ref = and i64 %s32, 65535
  %d.sse = lshr i64 %acc, 48
  %sad.next = add i64 %sad, %d.sad
  %blk.next = add i64 %blk, %d.blk
  %ref.next = add i64 %ref, %d.ref
  %sse.next = add i64 %sse, %d.sse
  %xx.next = add i64 %xx, 1
  %xdone = icmp eq i64 %xx.next, 16
  br i1 %xdone, label %py.latch, label %px.loop
py.latch:
  %yy.next = add i64 %yy, 1
  %ydone = icmp eq i64 %yy.next, 16
  br i1 %ydone, label %block.end, label %py.loop
block.end:
  %gt = icmp ugt i64 %sad.next, %old.max
  %new.max = select i1 %gt, i64 %sad.next, i64 %old.max
  store i64 %new.max, ptr %outMetrics4, align 8
  %new.sse = add i64 %old.sse, %sse.next
  store i64 %new.sse, ptr %o1, align 8
  %new.pix = add i64 %old.pix, 256
  store i64 %new.pix, ptr %o2, align 8
  %new.ok = call i64 @lnir_px_luma_acceptance_gate(i64 %sad.next, i64 %blk.next, i64 %ref.next, i64 %old.ok)
  store i64 %new.ok, ptr %o3, align 8
  %bx.next = add i64 %bxi, %sx
  %more.x = icmp ule i64 %bx.next, %xlim
  br i1 %more.x, label %bx.loop, label %by.latch
by.latch:
  %by.next = add i64 %byi, %sy
  %more.y = icmp ule i64 %by.next, %ylim
  br i1 %more.y, label %by.loop, label %exit
exit:
  ret void
}}
"""


def gen_all_outer_shells() -> str:
    parts = [
        gen_shells_1_to_6().strip(),
        gen_shells_7_to_12().strip(),
        gen_acceptance_shell("lean_native_luma_acceptance_16x16_u8", False).strip(),
        gen_acceptance_shell("lean_native_luma_acceptance_16x16_u16le", True).strip(),
    ]
    return "\n\n".join(parts) + "\n"


def splice_llvm_module(raw_ir: str, arch: str) -> str:
    start_marker = "define weak_odr dso_local void @lean_native_swscale_down2x2_u8("
    if arch == "x86_64":
        end_marker = "; LNIRDecl: swscale_luma_gain_bias_simd"
    elif arch == "arm64":
        end_marker = "define weak_odr dso_local i8 @leansys_select_isa("
    else:
        raise ValueError(f"unsupported arch: {arch}")
    i0 = raw_ir.find(start_marker)
    i1 = raw_ir.find(end_marker)
    if i0 < 0 or i1 < 0 or i1 <= i0:
        raise RuntimeError(f"failed to locate splice markers in {arch} LLVM IR")
    prefix = raw_ir[:i0]
    suffix = raw_ir[i1:]
    if arch == "x86_64":
        suffix = suffix.replace(
            'attributes #0 = { nounwind uwtable "target-cpu"="x86-64-v2" }',
            "attributes #0 = { nounwind uwtable }",
        )
    spliced = prefix + gen_all_outer_shells() + "\n" + suffix
    verify_spliced_module(spliced, arch)
    return spliced


def verify_spliced_module(ir_text: str, arch: str) -> None:
    for shell_name, expected_callees in EXPECTED_SHELL_CALLS.items():
        m = re.findall(
            r"^define weak_odr dso_local [^\n]*@" + re.escape(shell_name) + r"\([^\n]*\n.*?^}",
            ir_text,
            re.M | re.S,
        )
        if len(m) != 1:
            raise AssertionError(f"{arch}: expected 1 definition of @{shell_name}, found {len(m)}")
        body = m[0]
        for callee in expected_callees:
            if f"@{callee}(" not in body:
                raise AssertionError(f"{arch}: @{shell_name} does not call @{callee}")


def patch_c_header(raw_header: str) -> str:
    needle = "#ifdef __cplusplus\n}\n#endif\n#endif"
    if needle not in raw_header:
        raise RuntimeError("unexpected C header footer from lean-native-core emit-c-header")
    extra = "\n".join(OUTER_PROTOS_C) + "\n"
    return raw_header.replace(needle, extra + needle, 1)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--splice-arch", choices=("x86_64", "arm64"))
    ap.add_argument("--in-ll", type=Path)
    ap.add_argument("--out-ll", type=Path)
    ap.add_argument("--patch-header", type=Path)
    ap.add_argument("--verify-checked-in", type=Path, help="repo root to verify")
    args = ap.parse_args()

    if args.splice_arch:
        if not args.in_ll or not args.out_ll:
            ap.error("--splice-arch requires --in-ll and --out-ll")
        out = splice_llvm_module(args.in_ll.read_text(), args.splice_arch)
        args.out_ll.write_text(out)
        return 0

    if args.patch_header:
        patched = patch_c_header(args.patch_header.read_text())
        args.patch_header.write_text(patched)
        return 0

    if args.verify_checked_in:
        root = args.verify_checked_in
        shells_by_arch = []
        px_by_arch = []
        for arch in ("x86_64", "arm64"):
            p = root / "c" / f"leanav_lnir_{arch}.ll"
            txt = p.read_text()
            verify_spliced_module(txt, arch)
            shells = [
                re.search(
                    r"^define weak_odr dso_local [^\n]*@" + re.escape(k) + r"\([^\n]*\n.*?^}",
                    txt,
                    re.M | re.S,
                ).group(0)
                for k in EXPECTED_SHELL_CALLS
            ]
            pxs = re.findall(r"^define dso_local i64 @lnir_px_[a-z0-9_]+\([^\n]*\n.*?^}", txt, re.M | re.S)
            if len(pxs) != 17:
                raise AssertionError(f"{arch}: expected 17 @lnir_px_* definitions, found {len(pxs)}")
            shells_by_arch.append("\n\n".join(shells))
            px_by_arch.append("\n\n".join(pxs))
        if shells_by_arch[0] != shells_by_arch[1]:
            raise AssertionError("x86_64 and arm64 outer shells differ")
        if px_by_arch[0] != px_by_arch[1]:
            raise AssertionError("x86_64 and arm64 @lnir_px_* definitions differ")
        print(f"[gen_lnir_outer_shells] OK: 14 outer shells wired to 17 @lnir_px_* cores (x86_64 == arm64)")
        return 0

    sys.stdout.write(gen_all_outer_shells())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())




