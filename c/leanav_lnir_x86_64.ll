; ModuleID = 'LeanAV.DSP.Kernels.optimized'
source_filename = "LeanAV.DSP.Kernels.lean"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; --- LeanNative Runtime Intrinsics & C ABI Entrypoints ---
declare i1 @llvm.expect.i1(i1, i1) #2
declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8 immarg) #2
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64) #2
declare { i64, i1 } @llvm.usub.with.overflow.i64(i64, i64) #2
declare { i256, i1 } @llvm.uadd.with.overflow.i256(i256, i256) #2
declare { i256, i1 } @llvm.usub.with.overflow.i256(i256, i256) #2
declare { i256, i1 } @llvm.umul.with.overflow.i256(i256, i256) #2
declare i256 @llvm.ctlz.i256(i256, i1 immarg) #2
declare void @llvm.trap()
declare void @lean_native_evm_sload(ptr, ptr, ptr)
declare void @lean_native_evm_sstore(ptr, ptr, ptr)
declare i64 @lean_native_trm_matryoshka_parity_u64(i64)
declare noalias ptr @malloc(i64 noundef)
declare void @free(ptr noundef)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg)

define weak_odr dso_local { i256, i1 } @lean_native_u256_uadd_limbs(i256 %a, i256 %b) #0 {
entry:
  %a0 = trunc i256 %a to i64
  %b0 = trunc i256 %b to i64
  %as1 = lshr i256 %a, 64
  %a1 = trunc i256 %as1 to i64
  %bs1 = lshr i256 %b, 64
  %b1 = trunc i256 %bs1 to i64
  %as2 = lshr i256 %a, 128
  %a2 = trunc i256 %as2 to i64
  %bs2 = lshr i256 %b, 128
  %b2 = trunc i256 %bs2 to i64
  %as3 = lshr i256 %a, 192
  %a3 = trunc i256 %as3 to i64
  %bs3 = lshr i256 %b, 192
  %b3 = trunc i256 %bs3 to i64
  %s0 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %a0, i64 %b0)
  %r0 = extractvalue { i64, i1 } %s0, 0
  %c0 = extractvalue { i64, i1 } %s0, 1
  %s1a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %a1, i64 %b1)
  %r1a = extractvalue { i64, i1 } %s1a, 0
  %c1a = extractvalue { i64, i1 } %s1a, 1
  %c0z = zext i1 %c0 to i64
  %s1b = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %r1a, i64 %c0z)
  %r1 = extractvalue { i64, i1 } %s1b, 0
  %c1b = extractvalue { i64, i1 } %s1b, 1
  %c1 = or i1 %c1a, %c1b
  %s2a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %a2, i64 %b2)
  %r2a = extractvalue { i64, i1 } %s2a, 0
  %c2a = extractvalue { i64, i1 } %s2a, 1
  %c1z = zext i1 %c1 to i64
  %s2b = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %r2a, i64 %c1z)
  %r2 = extractvalue { i64, i1 } %s2b, 0
  %c2b = extractvalue { i64, i1 } %s2b, 1
  %c2 = or i1 %c2a, %c2b
  %s3a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %a3, i64 %b3)
  %r3a = extractvalue { i64, i1 } %s3a, 0
  %c3a = extractvalue { i64, i1 } %s3a, 1
  %c2z = zext i1 %c2 to i64
  %s3b = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %r3a, i64 %c2z)
  %r3 = extractvalue { i64, i1 } %s3b, 0
  %c3b = extractvalue { i64, i1 } %s3b, 1
  %c3 = or i1 %c3a, %c3b
  %w0 = zext i64 %r0 to i256
  %w1 = zext i64 %r1 to i256
  %w1s = shl i256 %w1, 64
  %w2 = zext i64 %r2 to i256
  %w2s = shl i256 %w2, 128
  %w3 = zext i64 %r3 to i256
  %w3s = shl i256 %w3, 192
  %o01 = or i256 %w0, %w1s
  %o23 = or i256 %w2s, %w3s
  %res = or i256 %o01, %o23
  %p0 = insertvalue { i256, i1 } poison, i256 %res, 0
  %p1 = insertvalue { i256, i1 } %p0, i1 %c3, 1
  ret { i256, i1 } %p1
}

define weak_odr dso_local { i256, i1 } @lean_native_u256_usub_limbs(i256 %a, i256 %b) #0 {
entry:
  %a0 = trunc i256 %a to i64
  %b0 = trunc i256 %b to i64
  %as1 = lshr i256 %a, 64
  %a1 = trunc i256 %as1 to i64
  %bs1 = lshr i256 %b, 64
  %b1 = trunc i256 %bs1 to i64
  %as2 = lshr i256 %a, 128
  %a2 = trunc i256 %as2 to i64
  %bs2 = lshr i256 %b, 128
  %b2 = trunc i256 %bs2 to i64
  %as3 = lshr i256 %a, 192
  %a3 = trunc i256 %as3 to i64
  %bs3 = lshr i256 %b, 192
  %b3 = trunc i256 %bs3 to i64
  %s0 = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %a0, i64 %b0)
  %r0 = extractvalue { i64, i1 } %s0, 0
  %c0 = extractvalue { i64, i1 } %s0, 1
  %s1a = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %a1, i64 %b1)
  %r1a = extractvalue { i64, i1 } %s1a, 0
  %c1a = extractvalue { i64, i1 } %s1a, 1
  %c0z = zext i1 %c0 to i64
  %s1b = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %r1a, i64 %c0z)
  %r1 = extractvalue { i64, i1 } %s1b, 0
  %c1b = extractvalue { i64, i1 } %s1b, 1
  %c1 = or i1 %c1a, %c1b
  %s2a = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %a2, i64 %b2)
  %r2a = extractvalue { i64, i1 } %s2a, 0
  %c2a = extractvalue { i64, i1 } %s2a, 1
  %c1z = zext i1 %c1 to i64
  %s2b = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %r2a, i64 %c1z)
  %r2 = extractvalue { i64, i1 } %s2b, 0
  %c2b = extractvalue { i64, i1 } %s2b, 1
  %c2 = or i1 %c2a, %c2b
  %s3a = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %a3, i64 %b3)
  %r3a = extractvalue { i64, i1 } %s3a, 0
  %c3a = extractvalue { i64, i1 } %s3a, 1
  %c2z = zext i1 %c2 to i64
  %s3b = call { i64, i1 } @llvm.usub.with.overflow.i64(i64 %r3a, i64 %c2z)
  %r3 = extractvalue { i64, i1 } %s3b, 0
  %c3b = extractvalue { i64, i1 } %s3b, 1
  %c3 = or i1 %c3a, %c3b
  %w0 = zext i64 %r0 to i256
  %w1 = zext i64 %r1 to i256
  %w1s = shl i256 %w1, 64
  %w2 = zext i64 %r2 to i256
  %w2s = shl i256 %w2, 128
  %w3 = zext i64 %r3 to i256
  %w3s = shl i256 %w3, 192
  %o01 = or i256 %w0, %w1s
  %o23 = or i256 %w2s, %w3s
  %res = or i256 %o01, %o23
  %p0 = insertvalue { i256, i1 } poison, i256 %res, 0
  %p1 = insertvalue { i256, i1 } %p0, i1 %c3, 1
  ret { i256, i1 } %p1
}

define weak_odr dso_local void @lean_native_inc(ptr %obj, i64 %count) #0 {
entry:
  %is_null = icmp eq ptr %obj, null
  br i1 %is_null, label %done, label %check
check:
  %p_int = ptrtoint ptr %obj to i64
  %tag = and i64 %p_int, 1
  %is_scalar = icmp ne i64 %tag, 0
  br i1 %is_scalar, label %done, label %upd
upd:
  %rc = load i32, ptr %obj, align 4
  %is_pos = icmp sgt i32 %rc, 0
  br i1 %is_pos, label %do_inc, label %done
do_inc:
  %c32 = trunc i64 %count to i32
  %rc_prev = atomicrmw add ptr %obj, i32 %c32 monotonic, align 4
  br label %done
done:
  ret void
}

define weak_odr dso_local void @lean_native_dec(ptr %obj, i64 %count) #0 {
entry:
  %is_null = icmp eq ptr %obj, null
  br i1 %is_null, label %done, label %check
check:
  %p_int = ptrtoint ptr %obj to i64
  %tag = and i64 %p_int, 1
  %is_scalar = icmp ne i64 %tag, 0
  br i1 %is_scalar, label %done, label %upd
upd:
  %rc = load i32, ptr %obj, align 4
  %is_pos = icmp sgt i32 %rc, 0
  br i1 %is_pos, label %do_dec, label %done
do_dec:
  %c32 = trunc i64 %count to i32
  %rc_prev = atomicrmw sub ptr %obj, i32 %c32 acq_rel, align 4
  br label %done
done:
  ret void
}

define weak_odr dso_local ptr @lean_native_box_u64(i64 %val) #0 {
entry:
  %sh = shl i64 %val, 1
  %tagged = or i64 %sh, 1
  %p = inttoptr i64 %tagged to ptr
  ret ptr %p
}

define weak_odr dso_local i64 @lean_native_unbox_u64(ptr %boxed) #0 {
entry:
  %i = ptrtoint ptr %boxed to i64
  %v = lshr i64 %i, 1
  ret i64 %v
}

define weak_odr dso_local ptr @lean_native_ensure_exclusive(ptr %arr) #0 {
entry:
  %is_null = icmp eq ptr %arr, null
  br i1 %is_null, label %ret_same, label %chk_rc
chk_rc:
  %rc = load i32, ptr %arr, align 4
  %is_excl = icmp eq i32 %rc, 1
  %exp = call i1 @llvm.expect.i1(i1 %is_excl, i1 true)
  br i1 %exp, label %ret_same, label %clone
ret_same:
  ret ptr %arr
clone:
  %sz_ptr = getelementptr inbounds i64, ptr %arr, i64 1
  %sz = load i64, ptr %sz_ptr, align 8
  %bytes_data = shl i64 %sz, 3
  %total_bytes = add i64 %bytes_data, 24
  %new_arr = call noalias ptr @malloc(i64 %total_bytes)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %new_arr, ptr align 8 %arr, i64 %total_bytes, i1 false)
  store i32 1, ptr %new_arr, align 4
  %gt1 = icmp sgt i32 %rc, 1
  br i1 %gt1, label %dec_old, label %done_clone
dec_old:
  %rc_prev = atomicrmw sub ptr %arr, i32 1 acq_rel, align 4
  br label %done_clone
done_clone:
  ret ptr %new_arr
}

define weak_odr dso_local ptr @lean_native_ensure_exclusive_uninit(ptr %arr) #0 {
entry:
  %is_null = icmp eq ptr %arr, null
  br i1 %is_null, label %ret_same, label %chk_rc
chk_rc:
  %rc = load i32, ptr %arr, align 4
  %is_excl = icmp eq i32 %rc, 1
  %exp = call i1 @llvm.expect.i1(i1 %is_excl, i1 true)
  br i1 %exp, label %ret_same, label %clone
ret_same:
  ret ptr %arr
clone:
  %sz_ptr = getelementptr inbounds i64, ptr %arr, i64 1
  %sz = load i64, ptr %sz_ptr, align 8
  %bytes_data = shl i64 %sz, 3
  %total_bytes = add i64 %bytes_data, 24
  %new_arr = call noalias ptr @malloc(i64 %total_bytes)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %new_arr, ptr align 8 %arr, i64 24, i1 false)
  store i32 1, ptr %new_arr, align 4
  %gt1 = icmp sgt i32 %rc, 1
  br i1 %gt1, label %dec_old, label %done_clone
dec_old:
  %rc_prev = atomicrmw sub ptr %arr, i32 1 acq_rel, align 4
  br label %done_clone
done_clone:
  ret ptr %new_arr
}

define weak_odr dso_local void @lean_native_cpu_saxpy_u64(ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n) #0 {
entry:
  %cmp0 = icmp eq i64 %n, 0
  br i1 %cmp0, label %exit, label %loop
loop:
  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]
  %px = getelementptr inbounds i64, ptr %x, i64 %i
  %py = getelementptr inbounds i64, ptr %y, i64 %i
  %po = getelementptr inbounds i64, ptr %out, i64 %i
  %vx = load i64, ptr %px, align 8
  %vy = load i64, ptr %py, align 8
  %prod = mul i64 %vx, %alpha
  %res = add i64 %prod, %vy
  store i64 %res, ptr %po, align 8
  %i_next = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %i_next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0
exit:
  ret void
}

define weak_odr dso_local void @lean_native_cpu_map_scale_add_u64(ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n) #0 {
entry:
  %cmp0 = icmp eq i64 %n, 0
  br i1 %cmp0, label %exit, label %loop
loop:
  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]
  %pi = getelementptr inbounds i64, ptr %in0, i64 %i
  %po = getelementptr inbounds i64, ptr %out, i64 %i
  %vi = load i64, ptr %pi, align 8
  %prod = mul i64 %vi, %scale
  %res = add i64 %prod, %bias
  store i64 %res, ptr %po, align 8
  %i_next = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %i_next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0
exit:
  ret void
}

define weak_odr dso_local void @lean_native_cpu_zip_add_u64(ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n) #0 {
entry:
  %cmp0 = icmp eq i64 %n, 0
  br i1 %cmp0, label %exit, label %loop
loop:
  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]
  %p0 = getelementptr inbounds i64, ptr %in0, i64 %i
  %p1 = getelementptr inbounds i64, ptr %in1, i64 %i
  %po = getelementptr inbounds i64, ptr %out, i64 %i
  %v0 = load i64, ptr %p0, align 8
  %v1 = load i64, ptr %p1, align 8
  %res = add i64 %v0, %v1
  store i64 %res, ptr %po, align 8
  %i_next = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %i_next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0
exit:
  ret void
}

define weak_odr dso_local void @lean_native_cpu_xor_assign_u64(ptr noalias %dst, ptr noalias %src, i64 %n) #0 {
entry:
  %cmp0 = icmp eq i64 %n, 0
  br i1 %cmp0, label %exit, label %loop
loop:
  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]
  %pd = getelementptr inbounds i64, ptr %dst, i64 %i
  %ps = getelementptr inbounds i64, ptr %src, i64 %i
  %vd = load i64, ptr %pd, align 8
  %vs = load i64, ptr %ps, align 8
  %vx = xor i64 %vd, %vs
  store i64 %vx, ptr %pd, align 8
  %i_next = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %i_next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0
exit:
  ret void
}

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

define weak_odr dso_local void @lean_native_luma_acceptance_16x16_u8(ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, ptr noalias noundef readonly %dst, i64 noundef %dstW, i64 noundef %dstH, ptr noalias noundef writeonly %outMetrics4) #0 {
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
  %p.dst = getelementptr i8, ptr %dst, i64 %d.idx
  %b.dst = load i8, ptr %p.dst, align 1
  %v.dst = zext i8 %b.dst to i64
  br i1 %is1, label %mode.1, label %check.2
check.2:
  br i1 %is2, label %mode.2, label %check.3
check.3:
  br i1 %is3, label %mode.3, label %mode.q8
mode.1:
  %s1.row = mul i64 %y, %srcW
  %s1.idx = add i64 %s1.row, %x
  %p.m1 = getelementptr i8, ptr %src, i64 %s1.idx
  %b.m1 = load i8, ptr %p.m1, align 1
  %v.m1 = zext i8 %b.m1 to i64
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
  %p.m2_00 = getelementptr i8, ptr %src, i64 %s2.00
  %b.m2_00 = load i8, ptr %p.m2_00, align 1
  %v.m2_00 = zext i8 %b.m2_00 to i64
  %p.m2_01 = getelementptr i8, ptr %src, i64 %s2.01
  %b.m2_01 = load i8, ptr %p.m2_01, align 1
  %v.m2_01 = zext i8 %b.m2_01 to i64
  %p.m2_10 = getelementptr i8, ptr %src, i64 %s2.10
  %b.m2_10 = load i8, ptr %p.m2_10, align 1
  %v.m2_10 = zext i8 %b.m2_10 to i64
  %p.m2_11 = getelementptr i8, ptr %src, i64 %s2.11
  %b.m2_11 = load i8, ptr %p.m2_11, align 1
  %v.m2_11 = zext i8 %b.m2_11 to i64
  %m2.s0 = add i64 %v.m2_00, %v.m2_01
  %m2.s1 = add i64 %v.m2_10, %v.m2_11
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
  %p.m3_00 = getelementptr i8, ptr %src, i64 %s3.00
  %b.m3_00 = load i8, ptr %p.m3_00, align 1
  %v.m3_00 = zext i8 %b.m3_00 to i64
  %p.m3_01 = getelementptr i8, ptr %src, i64 %s3.01
  %b.m3_01 = load i8, ptr %p.m3_01, align 1
  %v.m3_01 = zext i8 %b.m3_01 to i64
  %p.m3_02 = getelementptr i8, ptr %src, i64 %s3.02
  %b.m3_02 = load i8, ptr %p.m3_02, align 1
  %v.m3_02 = zext i8 %b.m3_02 to i64
  %p.m3_10 = getelementptr i8, ptr %src, i64 %s3.10
  %b.m3_10 = load i8, ptr %p.m3_10, align 1
  %v.m3_10 = zext i8 %b.m3_10 to i64
  %p.m3_11 = getelementptr i8, ptr %src, i64 %s3.11
  %b.m3_11 = load i8, ptr %p.m3_11, align 1
  %v.m3_11 = zext i8 %b.m3_11 to i64
  %p.m3_12 = getelementptr i8, ptr %src, i64 %s3.12
  %b.m3_12 = load i8, ptr %p.m3_12, align 1
  %v.m3_12 = zext i8 %b.m3_12 to i64
  %p.m3_20 = getelementptr i8, ptr %src, i64 %s3.20
  %b.m3_20 = load i8, ptr %p.m3_20, align 1
  %v.m3_20 = zext i8 %b.m3_20 to i64
  %p.m3_21 = getelementptr i8, ptr %src, i64 %s3.21
  %b.m3_21 = load i8, ptr %p.m3_21, align 1
  %v.m3_21 = zext i8 %b.m3_21 to i64
  %p.m3_22 = getelementptr i8, ptr %src, i64 %s3.22
  %b.m3_22 = load i8, ptr %p.m3_22, align 1
  %v.m3_22 = zext i8 %b.m3_22 to i64
  %m3.r0a = add i64 %v.m3_00, %v.m3_01
  %m3.r0 = add i64 %m3.r0a, %v.m3_02
  %m3.r1a = add i64 %v.m3_10, %v.m3_11
  %m3.r1 = add i64 %m3.r1a, %v.m3_12
  %m3.r2a = add i64 %v.m3_20, %v.m3_21
  %m3.r2 = add i64 %m3.r2a, %v.m3_22
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
  %p.mq_00 = getelementptr i8, ptr %src, i64 %sq.00
  %b.mq_00 = load i8, ptr %p.mq_00, align 1
  %v.mq_00 = zext i8 %b.mq_00 to i64
  %p.mq_01 = getelementptr i8, ptr %src, i64 %sq.01
  %b.mq_01 = load i8, ptr %p.mq_01, align 1
  %v.mq_01 = zext i8 %b.mq_01 to i64
  %p.mq_10 = getelementptr i8, ptr %src, i64 %sq.10
  %b.mq_10 = load i8, ptr %p.mq_10, align 1
  %v.mq_10 = zext i8 %b.mq_10 to i64
  %p.mq_11 = getelementptr i8, ptr %src, i64 %sq.11
  %b.mq_11 = load i8, ptr %p.mq_11, align 1
  %v.mq_11 = zext i8 %b.mq_11 to i64
  %v.mq = call i64 @lnir_px_bilinear_q8(i64 %v.mq_00, i64 %v.mq_01, i64 %v.mq_10, i64 %v.mq_11, i64 %fx, i64 %fy)
  br label %px.latch
px.latch:
  %ref.px = phi i64 [ %v.m1, %mode.1 ], [ %v.m2, %mode.2 ], [ %v.m3, %mode.3 ], [ %v.mq, %mode.q8 ]
  %acc = call i64 @lnir_px_luma_acceptance_accum(i64 %ref.px, i64 %v.dst)
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
}

define weak_odr dso_local void @lean_native_luma_acceptance_16x16_u16le(ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, ptr noalias noundef readonly %dst, i64 noundef %dstW, i64 noundef %dstH, ptr noalias noundef writeonly %outMetrics4) #0 {
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
  %p.dst = getelementptr i16, ptr %dst, i64 %d.idx
  %u.dst = load i16, ptr %p.dst, align 1
  %r.dst = zext i16 %u.dst to i64
  %v.dst = call i64 @lnir_px_extract_u16le_msb8(i64 %r.dst)
  br i1 %is1, label %mode.1, label %check.2
check.2:
  br i1 %is2, label %mode.2, label %check.3
check.3:
  br i1 %is3, label %mode.3, label %mode.q8
mode.1:
  %s1.row = mul i64 %y, %srcW
  %s1.idx = add i64 %s1.row, %x
  %p.m1 = getelementptr i16, ptr %src, i64 %s1.idx
  %u.m1 = load i16, ptr %p.m1, align 1
  %r.m1 = zext i16 %u.m1 to i64
  %v.m1 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m1)
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
  %p.m2_00 = getelementptr i16, ptr %src, i64 %s2.00
  %u.m2_00 = load i16, ptr %p.m2_00, align 1
  %r.m2_00 = zext i16 %u.m2_00 to i64
  %v.m2_00 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m2_00)
  %p.m2_01 = getelementptr i16, ptr %src, i64 %s2.01
  %u.m2_01 = load i16, ptr %p.m2_01, align 1
  %r.m2_01 = zext i16 %u.m2_01 to i64
  %v.m2_01 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m2_01)
  %p.m2_10 = getelementptr i16, ptr %src, i64 %s2.10
  %u.m2_10 = load i16, ptr %p.m2_10, align 1
  %r.m2_10 = zext i16 %u.m2_10 to i64
  %v.m2_10 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m2_10)
  %p.m2_11 = getelementptr i16, ptr %src, i64 %s2.11
  %u.m2_11 = load i16, ptr %p.m2_11, align 1
  %r.m2_11 = zext i16 %u.m2_11 to i64
  %v.m2_11 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m2_11)
  %m2.s0 = add i64 %v.m2_00, %v.m2_01
  %m2.s1 = add i64 %v.m2_10, %v.m2_11
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
  %p.m3_00 = getelementptr i16, ptr %src, i64 %s3.00
  %u.m3_00 = load i16, ptr %p.m3_00, align 1
  %r.m3_00 = zext i16 %u.m3_00 to i64
  %v.m3_00 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_00)
  %p.m3_01 = getelementptr i16, ptr %src, i64 %s3.01
  %u.m3_01 = load i16, ptr %p.m3_01, align 1
  %r.m3_01 = zext i16 %u.m3_01 to i64
  %v.m3_01 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_01)
  %p.m3_02 = getelementptr i16, ptr %src, i64 %s3.02
  %u.m3_02 = load i16, ptr %p.m3_02, align 1
  %r.m3_02 = zext i16 %u.m3_02 to i64
  %v.m3_02 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_02)
  %p.m3_10 = getelementptr i16, ptr %src, i64 %s3.10
  %u.m3_10 = load i16, ptr %p.m3_10, align 1
  %r.m3_10 = zext i16 %u.m3_10 to i64
  %v.m3_10 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_10)
  %p.m3_11 = getelementptr i16, ptr %src, i64 %s3.11
  %u.m3_11 = load i16, ptr %p.m3_11, align 1
  %r.m3_11 = zext i16 %u.m3_11 to i64
  %v.m3_11 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_11)
  %p.m3_12 = getelementptr i16, ptr %src, i64 %s3.12
  %u.m3_12 = load i16, ptr %p.m3_12, align 1
  %r.m3_12 = zext i16 %u.m3_12 to i64
  %v.m3_12 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_12)
  %p.m3_20 = getelementptr i16, ptr %src, i64 %s3.20
  %u.m3_20 = load i16, ptr %p.m3_20, align 1
  %r.m3_20 = zext i16 %u.m3_20 to i64
  %v.m3_20 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_20)
  %p.m3_21 = getelementptr i16, ptr %src, i64 %s3.21
  %u.m3_21 = load i16, ptr %p.m3_21, align 1
  %r.m3_21 = zext i16 %u.m3_21 to i64
  %v.m3_21 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_21)
  %p.m3_22 = getelementptr i16, ptr %src, i64 %s3.22
  %u.m3_22 = load i16, ptr %p.m3_22, align 1
  %r.m3_22 = zext i16 %u.m3_22 to i64
  %v.m3_22 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.m3_22)
  %m3.r0a = add i64 %v.m3_00, %v.m3_01
  %m3.r0 = add i64 %m3.r0a, %v.m3_02
  %m3.r1a = add i64 %v.m3_10, %v.m3_11
  %m3.r1 = add i64 %m3.r1a, %v.m3_12
  %m3.r2a = add i64 %v.m3_20, %v.m3_21
  %m3.r2 = add i64 %m3.r2a, %v.m3_22
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
  %p.mq_00 = getelementptr i16, ptr %src, i64 %sq.00
  %u.mq_00 = load i16, ptr %p.mq_00, align 1
  %r.mq_00 = zext i16 %u.mq_00 to i64
  %v.mq_00 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.mq_00)
  %p.mq_01 = getelementptr i16, ptr %src, i64 %sq.01
  %u.mq_01 = load i16, ptr %p.mq_01, align 1
  %r.mq_01 = zext i16 %u.mq_01 to i64
  %v.mq_01 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.mq_01)
  %p.mq_10 = getelementptr i16, ptr %src, i64 %sq.10
  %u.mq_10 = load i16, ptr %p.mq_10, align 1
  %r.mq_10 = zext i16 %u.mq_10 to i64
  %v.mq_10 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.mq_10)
  %p.mq_11 = getelementptr i16, ptr %src, i64 %sq.11
  %u.mq_11 = load i16, ptr %p.mq_11, align 1
  %r.mq_11 = zext i16 %u.mq_11 to i64
  %v.mq_11 = call i64 @lnir_px_extract_u16le_msb8(i64 %r.mq_11)
  %v.mq = call i64 @lnir_px_bilinear_q8(i64 %v.mq_00, i64 %v.mq_01, i64 %v.mq_10, i64 %v.mq_11, i64 %fx, i64 %fy)
  br label %px.latch
px.latch:
  %ref.px = phi i64 [ %v.m1, %mode.1 ], [ %v.m2, %mode.2 ], [ %v.m3, %mode.3 ], [ %v.mq, %mode.q8 ]
  %acc = call i64 @lnir_px_luma_acceptance_accum(i64 %ref.px, i64 %v.dst)
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
}

; LNIRDecl: swscale_luma_gain_bias_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.singleThreaded, isaMask=1)
define dso_local ptr @swscale_luma_gain_bias_simd(ptr noalias noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v111 = alloca ptr, align 8
  store ptr null, ptr %slot_v111, align 8
  %slot_v112 = alloca ptr, align 8
  store ptr null, ptr %slot_v112, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca ptr, align 8
  store ptr null, ptr %slot_v6, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 0, ptr %slot_v3, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v4, align 8
  %ldp_3 = load ptr, ptr %slot_v0, align 8
  %cow_rc_4 = load i32, ptr %ldp_3, align 4
  %cow_excl_5 = icmp eq i32 %cow_rc_4, 1
  %cow_exp_6 = call i1 @llvm.expect.i1(i1 %cow_excl_5, i1 true)
  br i1 %cow_exp_6, label %cow_fast_7, label %cow_slow_8
cow_fast_7:
  store ptr %ldp_3, ptr %slot_v111, align 8
  br label %cow_merge_9
cow_slow_8:
  %cow_cloned_10 = call ptr @lean_native_ensure_exclusive(ptr %ldp_3)
  store ptr %cow_cloned_10, ptr %slot_v111, align 8
  br label %cow_merge_9
cow_merge_9:
  %ldp_11 = load ptr, ptr %slot_v111, align 8
  %data_ptr_12 = getelementptr inbounds i64, ptr %ldp_11, i64 3
  store ptr %data_ptr_12, ptr %slot_v112, align 8
  %ld_13 = load i64, ptr %slot_v3, align 8
  %ld_14 = load i64, ptr %slot_v4, align 8
  %ldp_15 = load ptr, ptr %slot_v111, align 8
  store ptr %ldp_15, ptr %slot_v6, align 8
  br label %loop_prehdr_16
loop_prehdr_16:
  br label %loop_hdr_17
loop_hdr_17:
  %loop_idx_21 = phi i64 [ %ld_13, %loop_prehdr_16 ], [ %loop_next_22, %loop_latch_19 ]
  store i64 %loop_idx_21, ptr %slot_v5, align 8
  %loop_cmp_23 = icmp ult i64 %loop_idx_21, %ld_14
  br i1 %loop_cmp_23, label %loop_body_18, label %loop_exit_20
loop_body_18:
  %ldp_24 = load ptr, ptr %slot_v112, align 8
  %ld_25 = load i64, ptr %slot_v5, align 8
  %rld_gep_26 = getelementptr inbounds i64, ptr %ldp_24, i64 %ld_25
  %rld_val_27 = load i64, ptr %rld_gep_26, align 8
  store i64 %rld_val_27, ptr %slot_v8, align 8
  %ld_28 = load i64, ptr %slot_v8, align 8
  %ld_29 = load i64, ptr %slot_v1, align 8
  %ld_30 = load i64, ptr %slot_v2, align 8
  %fma_mul_31 = mul i64 %ld_28, %ld_29
  %fma_add_32 = add i64 %fma_mul_31, %ld_30
  store i64 %fma_add_32, ptr %slot_v9, align 8
  %ldp_33 = load ptr, ptr %slot_v112, align 8
  %ld_34 = load i64, ptr %slot_v5, align 8
  %ld_35 = load i64, ptr %slot_v9, align 8
  %rst_gep_36 = getelementptr inbounds i64, ptr %ldp_33, i64 %ld_34
  store i64 %ld_35, ptr %rst_gep_36, align 8
  %ldp_37 = load ptr, ptr %slot_v6, align 8
  store ptr %ldp_37, ptr %slot_v6, align 8
  br label %loop_latch_19
loop_latch_19:
  %loop_next_22 = add nuw nsw i64 %loop_idx_21, 1
  br label %loop_hdr_17, !llvm.loop !0
loop_exit_20:
  %ldp_38 = load ptr, ptr %slot_v6, align 8
  ret ptr %ldp_38
}

; LNIRDecl: flac_lpc_autocorr_dot_simd (assurance=Tested, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @flac_lpc_autocorr_dot_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %p_in1_20 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_15
  %v_in1_21 = load i64, ptr %p_in1_20, align 8
  %zm_mul_22 = mul i64 %v_in0_19, %v_in1_21
  %p_out_23 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %zm_mul_22, ptr %p_out_23, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_24 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_24
}

; LNIRDecl: opus_celt_pvq_mix_saxpy_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @opus_celt_pvq_mix_saxpy_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %p_in1_20 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_15
  %v_in1_21 = load i64, ptr %p_in1_20, align 8
  %sax_mul_22 = mul i64 %v_in0_19, 4
  %sax_add_23 = add i64 %sax_mul_22, %v_in1_21
  %p_out_24 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sax_add_23, ptr %p_out_24, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_25 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_25
}

; LNIRDecl: av1_wiener_3tap_sym_gpu (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @av1_wiener_3tap_sym_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = mul i64 %cs_value_27, 10
  %fma_mul_33 = mul i64 %cs_value_23, 3
  %fma_add_34 = add i64 %fma_mul_33, %alu_32
  %fma_mul_35 = mul i64 %cs_value_31, 3
  %fma_add_36 = add i64 %fma_mul_35, %fma_add_34
  %p_out_37 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %fma_add_36, ptr %p_out_37, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_38 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_38
}

; LNIRDecl: av1_cdef_fma_blend_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @av1_cdef_fma_blend_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %fma_mul_32 = mul i64 %cs_value_23, %cs_value_27
  %fma_add_33 = add i64 %fma_mul_32, %cs_value_31
  %p_out_34 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %fma_add_33, ptr %p_out_34, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_35 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_35
}

; LNIRDecl: h264_idct_tuple_accum_sroa (assurance=TranslationValidated, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @h264_idct_tuple_accum_sroa(i64 noundef %arg_v0, i64 noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 0, ptr %slot_v2, align 8
  %ld_0 = load i64, ptr %slot_v2, align 8
  %ld_1 = load i64, ptr %slot_v0, align 8
  %ld_2 = load i64, ptr %slot_v1, align 8
  store i64 %ld_2, ptr %slot_v4, align 8
  br label %loop_prehdr_3
loop_prehdr_3:
  br label %loop_hdr_4
loop_hdr_4:
  %loop_idx_8 = phi i64 [ %ld_0, %loop_prehdr_3 ], [ %loop_next_9, %loop_latch_6 ]
  store i64 %loop_idx_8, ptr %slot_v3, align 8
  %loop_cmp_10 = icmp ult i64 %loop_idx_8, %ld_1
  br i1 %loop_cmp_10, label %loop_body_5, label %loop_exit_7
loop_body_5:
  %ld_11 = load i64, ptr %slot_v4, align 8
  %ld_12 = load i64, ptr %slot_v3, align 8
  %alu_13 = add i64 %ld_11, %ld_12
  store i64 %alu_13, ptr %slot_v5, align 8
  %ld_14 = load i64, ptr %slot_v3, align 8
  %alu_15 = shl i64 %ld_14, 1
  store i64 %alu_15, ptr %slot_v6, align 8
  %ld_16 = load i64, ptr %slot_v5, align 8
  store i64 %ld_16, ptr %slot_v8, align 8
  %ld_17 = load i64, ptr %slot_v6, align 8
  store i64 %ld_17, ptr %slot_v9, align 8
  %ld_18 = load i64, ptr %slot_v8, align 8
  %ld_19 = load i64, ptr %slot_v9, align 8
  %alu_20 = add i64 %ld_18, %ld_19
  store i64 %alu_20, ptr %slot_v10, align 8
  %ld_21 = load i64, ptr %slot_v10, align 8
  store i64 %ld_21, ptr %slot_v4, align 8
  br label %loop_latch_6
loop_latch_6:
  %loop_next_9 = add nuw nsw i64 %loop_idx_8, 1
  br label %loop_hdr_4, !llvm.loop !6
loop_exit_7:
  %ld_22 = load i64, ptr %slot_v4, align 8
  ret i64 %ld_22
}

; LNIRDecl: bframe_bipred_blend_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @bframe_bipred_blend_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %p_in1_20 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_15
  %v_in1_21 = load i64, ptr %p_in1_20, align 8
  %sax_mul_22 = mul i64 %v_in0_19, 1
  %sax_add_23 = add i64 %sax_mul_22, %v_in1_21
  %p_out_24 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sax_add_23, ptr %p_out_24, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_25 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_25
}

; LNIRDecl: hevc_sao_band_offset_add_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @hevc_sao_band_offset_add_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %p_in1_20 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_15
  %v_in1_21 = load i64, ptr %p_in1_20, align 8
  %za_add_22 = add i64 %v_in0_19, %v_in1_21
  %p_out_23 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %za_add_22, ptr %p_out_23, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_24 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_24
}

; LNIRDecl: aac_imdct_window_mul_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @aac_imdct_window_mul_gpu(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %p_in1_20 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_15
  %v_in1_21 = load i64, ptr %p_in1_20, align 8
  %zm_mul_22 = mul i64 %v_in0_19, %v_in1_21
  %p_out_23 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %zm_mul_22, ptr %p_out_23, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_24 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_24
}

; LNIRDecl: prores_qscale_map_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @prores_qscale_map_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %msa_mul_20 = mul i64 %v_in0_19, 16
  %msa_add_21 = add i64 %msa_mul_20, 8
  %p_out_22 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %msa_add_21, ptr %p_out_22, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_23 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_23
}

; LNIRDecl: boxblur_div9_recip_shift_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @boxblur_div9_recip_shift_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %alu_24 = add i64 %cs_value_23, 4
  %alu_25 = mul i64 %alu_24, 7282
  %alu_26 = lshr i64 %alu_25, 16
  %p_out_27 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_26, ptr %p_out_27, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_28
}

; LNIRDecl: pq10_studio_clamp_select_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @pq10_studio_clamp_select_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %cmp_lt_25 = icmp ult i64 %cs_value_23, 64
  %alu_24 = zext i1 %cmp_lt_25 to i64
  %cmp_lt_27 = icmp ult i64 940, %cs_value_23
  %alu_26 = zext i1 %cmp_lt_27 to i64
  %sel_cond_28 = icmp ne i64 %alu_26, 0
  %sel_29 = select i1 %sel_cond_28, i64 940, i64 %cs_value_23
  %sel_cond_30 = icmp ne i64 %alu_24, 0
  %sel_31 = select i1 %sel_cond_30, i64 64, i64 %sel_29
  %p_out_32 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_31, ptr %p_out_32, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_33 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_33
}

; LNIRDecl: swscale_down2x2_box_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @swscale_down2x2_box_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = add i64 %cs_value_23, %cs_value_27
  %alu_29 = add i64 %alu_28, 2
  %alu_30 = lshr i64 %alu_29, 2
  %p_out_31 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_30, ptr %p_out_31, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_32 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_32
}

; LNIRDecl: swscale_down3x3_box_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @swscale_down3x3_box_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = add i64 %cs_value_23, %cs_value_27
  %alu_33 = add i64 %alu_32, %cs_value_31
  %alu_34 = add i64 %alu_33, 4
  %alu_35 = mul i64 %alu_34, 7282
  %alu_36 = lshr i64 %alu_35, 16
  %p_out_37 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_36, ptr %p_out_37, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_38 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_38
}

; LNIRDecl: swscale_down3to2_bilinear_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @swscale_down3to2_bilinear_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = shl i64 %cs_value_23, 1
  %alu_29 = add i64 %alu_28, %cs_value_27
  %alu_30 = add i64 %alu_29, 4
  %alu_31 = mul i64 %alu_30, 7282
  %alu_32 = lshr i64 %alu_31, 16
  %p_out_33 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_32, ptr %p_out_33, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_34 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_34
}

; LNIRDecl: av1_cdef_dir_filter_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @av1_cdef_dir_filter_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = add i64 %cs_value_27, %cs_value_31
  %alu_33 = add i64 %alu_32, 2
  %alu_34 = lshr i64 %alu_33, 2
  %alu_35 = add i64 %cs_value_23, %alu_34
  %p_out_36 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_35, ptr %p_out_36, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_37 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_37
}

; LNIRDecl: extract_u16le_msb8_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @extract_u16le_msb8_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %alu_24 = lshr i64 %cs_value_23, 2
  %alu_25 = and i64 %alu_24, 255
  %p_out_26 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_25, ptr %p_out_26, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_27 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_27
}

; LNIRDecl: luma_stats_moments_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @luma_stats_moments_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %alu_24 = mul i64 %cs_value_23, %cs_value_23
  %alu_25 = shl i64 %alu_24, 32
  %alu_26 = and i64 %cs_value_23, 4294967295
  %alu_27 = or i64 %alu_25, %alu_26
  %p_out_28 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_27, ptr %p_out_28, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_29 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_29
}

; LNIRDecl: luma_stats_pack_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @luma_stats_pack_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = and i64 %cs_value_23, 4294967295
  %div_z_31 = icmp eq i64 %cs_value_27, 0
  %div_rhs_30 = select i1 %div_z_31, i64 1, i64 %cs_value_27
  %div_raw_32 = udiv i64 %alu_28, %div_rhs_30
  %alu_29 = select i1 %div_z_31, i64 0, i64 %div_raw_32
  %alu_33 = and i64 %cs_value_23, 4294967295
  %div_z_36 = icmp eq i64 %cs_value_27, 0
  %div_rhs_35 = select i1 %div_z_36, i64 1, i64 %cs_value_27
  %div_raw_37 = udiv i64 %alu_33, %div_rhs_35
  %alu_34 = select i1 %div_z_36, i64 0, i64 %div_raw_37
  %alu_38 = mul i64 %alu_29, %alu_34
  %alu_39 = lshr i64 %cs_value_23, 32
  %div_z_42 = icmp eq i64 %cs_value_27, 0
  %div_rhs_41 = select i1 %div_z_42, i64 1, i64 %cs_value_27
  %div_raw_43 = udiv i64 %alu_39, %div_rhs_41
  %alu_40 = select i1 %div_z_42, i64 0, i64 %div_raw_43
  %cmp_lt_45 = icmp ult i64 %alu_38, %alu_40
  %alu_44 = zext i1 %cmp_lt_45 to i64
  %alu_46 = lshr i64 %cs_value_23, 32
  %div_z_49 = icmp eq i64 %cs_value_27, 0
  %div_rhs_48 = select i1 %div_z_49, i64 1, i64 %cs_value_27
  %div_raw_50 = udiv i64 %alu_46, %div_rhs_48
  %alu_47 = select i1 %div_z_49, i64 0, i64 %div_raw_50
  %alu_51 = and i64 %cs_value_23, 4294967295
  %div_z_54 = icmp eq i64 %cs_value_27, 0
  %div_rhs_53 = select i1 %div_z_54, i64 1, i64 %cs_value_27
  %div_raw_55 = udiv i64 %alu_51, %div_rhs_53
  %alu_52 = select i1 %div_z_54, i64 0, i64 %div_raw_55
  %alu_56 = and i64 %cs_value_23, 4294967295
  %div_z_59 = icmp eq i64 %cs_value_27, 0
  %div_rhs_58 = select i1 %div_z_59, i64 1, i64 %cs_value_27
  %div_raw_60 = udiv i64 %alu_56, %div_rhs_58
  %alu_57 = select i1 %div_z_59, i64 0, i64 %div_raw_60
  %alu_61 = mul i64 %alu_52, %alu_57
  %alu_62 = sub i64 %alu_47, %alu_61
  %sel_cond_63 = icmp ne i64 %alu_44, 0
  %sel_64 = select i1 %sel_cond_63, i64 %alu_62, i64 0
  %alu_65 = shl i64 %sel_64, 32
  %alu_66 = and i64 %cs_value_23, 4294967295
  %div_z_69 = icmp eq i64 %cs_value_27, 0
  %div_rhs_68 = select i1 %div_z_69, i64 1, i64 %cs_value_27
  %div_raw_70 = udiv i64 %alu_66, %div_rhs_68
  %alu_67 = select i1 %div_z_69, i64 0, i64 %div_raw_70
  %alu_71 = and i64 %alu_67, 4294967295
  %alu_72 = or i64 %alu_65, %alu_71
  %p_out_73 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_72, ptr %p_out_73, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_74 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_74
}

; LNIRDecl: luma_acceptance_accum_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @luma_acceptance_accum_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %cmp_le_29 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_28 = zext i1 %cmp_le_29 to i64
  %alu_30 = sub i64 %cs_value_23, %cs_value_27
  %alu_31 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_32 = icmp ne i64 %alu_28, 0
  %sel_33 = select i1 %sel_cond_32, i64 %alu_30, i64 %alu_31
  %cmp_le_35 = icmp ule i64 16, %cs_value_23
  %alu_34 = zext i1 %cmp_le_35 to i64
  %alu_36 = sub i64 %cs_value_23, 16
  %alu_37 = sub i64 16, %cs_value_23
  %sel_cond_38 = icmp ne i64 %alu_34, 0
  %sel_39 = select i1 %sel_cond_38, i64 %alu_36, i64 %alu_37
  %alu_40 = shl i64 %sel_39, 16
  %alu_41 = or i64 %sel_33, %alu_40
  %alu_42 = shl i64 %cs_value_23, 32
  %alu_43 = or i64 %alu_41, %alu_42
  %cmp_le_45 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_44 = zext i1 %cmp_le_45 to i64
  %alu_46 = sub i64 %cs_value_23, %cs_value_27
  %alu_47 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_48 = icmp ne i64 %alu_44, 0
  %sel_49 = select i1 %sel_cond_48, i64 %alu_46, i64 %alu_47
  %cmp_le_51 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_50 = zext i1 %cmp_le_51 to i64
  %alu_52 = sub i64 %cs_value_23, %cs_value_27
  %alu_53 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_54 = icmp ne i64 %alu_50, 0
  %sel_55 = select i1 %sel_cond_54, i64 %alu_52, i64 %alu_53
  %alu_56 = mul i64 %sel_49, %sel_55
  %alu_57 = shl i64 %alu_56, 48
  %alu_58 = or i64 %alu_43, %alu_57
  %p_out_59 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_58, ptr %p_out_59, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_60 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_60
}

; LNIRDecl: luma_acceptance_gate_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @luma_acceptance_gate_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %cmp_le_33 = icmp ule i64 6144, %cs_value_31
  %alu_32 = zext i1 %cmp_le_33 to i64
  %cmp_le_35 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_34 = zext i1 %cmp_le_35 to i64
  %sel_cond_36 = icmp ne i64 %alu_34, 0
  %sel_37 = select i1 %sel_cond_36, i64 0, i64 1
  %sel_cond_38 = icmp ne i64 %alu_32, 0
  %sel_39 = select i1 %sel_cond_38, i64 %sel_37, i64 1
  %p_out_40 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_39, ptr %p_out_40, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_41 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_41
}

; LNIRDecl: bilinear_q8_blend_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @bilinear_q8_blend_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = sub i64 256, %cs_value_31
  %alu_33 = mul i64 %cs_value_27, %cs_value_31
  %fma_mul_34 = mul i64 %cs_value_23, %alu_32
  %fma_add_35 = add i64 %fma_mul_34, %alu_33
  %p_out_36 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %fma_add_35, ptr %p_out_36, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_37 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_37
}

; LNIRDecl: bilinear_q8_pack_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @bilinear_q8_pack_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = sub i64 256, %cs_value_31
  %alu_33 = mul i64 %cs_value_27, %cs_value_31
  %fma_mul_34 = mul i64 %cs_value_23, %alu_32
  %fma_add_35 = add i64 %fma_mul_34, %alu_33
  %alu_36 = add i64 %fma_add_35, 32768
  %alu_37 = lshr i64 %alu_36, 16
  %p_out_38 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_37, ptr %p_out_38, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_39 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_39
}

; LNIRDecl: bilinear_q8_clamp10_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @bilinear_q8_clamp10_simd(ptr noalias noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v0, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %cmp_lt_25 = icmp ult i64 1023, %cs_value_23
  %alu_24 = zext i1 %cmp_lt_25 to i64
  %sel_cond_26 = icmp ne i64 %alu_24, 0
  %sel_27 = select i1 %sel_cond_26, i64 1023, i64 %cs_value_23
  %p_out_28 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_27, ptr %p_out_28, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_29 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_29
}

; LNIRDecl: av1_cdef_tap_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @av1_cdef_tap_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %cmp_le_33 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_32 = zext i1 %cmp_le_33 to i64
  %alu_34 = and i64 %cs_value_31, 2147483647
  %cmp_le_36 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_35 = zext i1 %cmp_le_36 to i64
  %alu_37 = sub i64 %cs_value_23, %cs_value_27
  %alu_38 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_39 = icmp ne i64 %alu_35, 0
  %sel_40 = select i1 %sel_cond_39, i64 %alu_37, i64 %alu_38
  %alu_41 = lshr i64 %cs_value_31, 32
  %cmp_lt_43 = icmp ult i64 0, %alu_41
  %alu_42 = zext i1 %cmp_lt_43 to i64
  %alu_44 = lshr i64 %cs_value_31, 32
  %sel_cond_45 = icmp ne i64 %alu_42, 0
  %sel_46 = select i1 %sel_cond_45, i64 %alu_44, i64 1
  %alu_47 = and i64 %sel_46, 31
  %sh_amt_49 = and i64 %alu_47, 63
  %alu_48 = lshr i64 %sel_40, %sh_amt_49
  %cmp_le_51 = icmp ule i64 %alu_34, %alu_48
  %alu_50 = zext i1 %cmp_le_51 to i64
  %cmp_le_53 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_52 = zext i1 %cmp_le_53 to i64
  %alu_54 = sub i64 %cs_value_23, %cs_value_27
  %alu_55 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_56 = icmp ne i64 %alu_52, 0
  %sel_57 = select i1 %sel_cond_56, i64 %alu_54, i64 %alu_55
  %alu_58 = and i64 %cs_value_31, 2147483647
  %cmp_le_60 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_59 = zext i1 %cmp_le_60 to i64
  %alu_61 = sub i64 %cs_value_23, %cs_value_27
  %alu_62 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_63 = icmp ne i64 %alu_59, 0
  %sel_64 = select i1 %sel_cond_63, i64 %alu_61, i64 %alu_62
  %alu_65 = lshr i64 %cs_value_31, 32
  %cmp_lt_67 = icmp ult i64 0, %alu_65
  %alu_66 = zext i1 %cmp_lt_67 to i64
  %alu_68 = lshr i64 %cs_value_31, 32
  %sel_cond_69 = icmp ne i64 %alu_66, 0
  %sel_70 = select i1 %sel_cond_69, i64 %alu_68, i64 1
  %alu_71 = and i64 %sel_70, 31
  %sh_amt_73 = and i64 %alu_71, 63
  %alu_72 = lshr i64 %sel_64, %sh_amt_73
  %alu_74 = sub i64 %alu_58, %alu_72
  %cmp_le_76 = icmp ule i64 %sel_57, %alu_74
  %alu_75 = zext i1 %cmp_le_76 to i64
  %cmp_le_78 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_77 = zext i1 %cmp_le_78 to i64
  %alu_79 = sub i64 %cs_value_23, %cs_value_27
  %alu_80 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_81 = icmp ne i64 %alu_77, 0
  %sel_82 = select i1 %sel_cond_81, i64 %alu_79, i64 %alu_80
  %alu_83 = and i64 %cs_value_31, 2147483647
  %cmp_le_85 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_84 = zext i1 %cmp_le_85 to i64
  %alu_86 = sub i64 %cs_value_23, %cs_value_27
  %alu_87 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_88 = icmp ne i64 %alu_84, 0
  %sel_89 = select i1 %sel_cond_88, i64 %alu_86, i64 %alu_87
  %alu_90 = lshr i64 %cs_value_31, 32
  %cmp_lt_92 = icmp ult i64 0, %alu_90
  %alu_91 = zext i1 %cmp_lt_92 to i64
  %alu_93 = lshr i64 %cs_value_31, 32
  %sel_cond_94 = icmp ne i64 %alu_91, 0
  %sel_95 = select i1 %sel_cond_94, i64 %alu_93, i64 1
  %alu_96 = and i64 %sel_95, 31
  %sh_amt_98 = and i64 %alu_96, 63
  %alu_97 = lshr i64 %sel_89, %sh_amt_98
  %alu_99 = sub i64 %alu_83, %alu_97
  %sel_cond_100 = icmp ne i64 %alu_75, 0
  %sel_101 = select i1 %sel_cond_100, i64 %sel_82, i64 %alu_99
  %sel_cond_102 = icmp ne i64 %alu_50, 0
  %sel_103 = select i1 %sel_cond_102, i64 0, i64 %sel_101
  %alu_104 = and i64 %cs_value_31, 2147483647
  %cmp_le_106 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_105 = zext i1 %cmp_le_106 to i64
  %alu_107 = sub i64 %cs_value_23, %cs_value_27
  %alu_108 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_109 = icmp ne i64 %alu_105, 0
  %sel_110 = select i1 %sel_cond_109, i64 %alu_107, i64 %alu_108
  %alu_111 = lshr i64 %cs_value_31, 32
  %cmp_lt_113 = icmp ult i64 0, %alu_111
  %alu_112 = zext i1 %cmp_lt_113 to i64
  %alu_114 = lshr i64 %cs_value_31, 32
  %sel_cond_115 = icmp ne i64 %alu_112, 0
  %sel_116 = select i1 %sel_cond_115, i64 %alu_114, i64 1
  %alu_117 = and i64 %sel_116, 31
  %sh_amt_119 = and i64 %alu_117, 63
  %alu_118 = lshr i64 %sel_110, %sh_amt_119
  %cmp_le_121 = icmp ule i64 %alu_104, %alu_118
  %alu_120 = zext i1 %cmp_le_121 to i64
  %cmp_le_123 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_122 = zext i1 %cmp_le_123 to i64
  %alu_124 = sub i64 %cs_value_23, %cs_value_27
  %alu_125 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_126 = icmp ne i64 %alu_122, 0
  %sel_127 = select i1 %sel_cond_126, i64 %alu_124, i64 %alu_125
  %alu_128 = and i64 %cs_value_31, 2147483647
  %cmp_le_130 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_129 = zext i1 %cmp_le_130 to i64
  %alu_131 = sub i64 %cs_value_23, %cs_value_27
  %alu_132 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_133 = icmp ne i64 %alu_129, 0
  %sel_134 = select i1 %sel_cond_133, i64 %alu_131, i64 %alu_132
  %alu_135 = lshr i64 %cs_value_31, 32
  %cmp_lt_137 = icmp ult i64 0, %alu_135
  %alu_136 = zext i1 %cmp_lt_137 to i64
  %alu_138 = lshr i64 %cs_value_31, 32
  %sel_cond_139 = icmp ne i64 %alu_136, 0
  %sel_140 = select i1 %sel_cond_139, i64 %alu_138, i64 1
  %alu_141 = and i64 %sel_140, 31
  %sh_amt_143 = and i64 %alu_141, 63
  %alu_142 = lshr i64 %sel_134, %sh_amt_143
  %alu_144 = sub i64 %alu_128, %alu_142
  %cmp_le_146 = icmp ule i64 %sel_127, %alu_144
  %alu_145 = zext i1 %cmp_le_146 to i64
  %cmp_le_148 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_147 = zext i1 %cmp_le_148 to i64
  %alu_149 = sub i64 %cs_value_23, %cs_value_27
  %alu_150 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_151 = icmp ne i64 %alu_147, 0
  %sel_152 = select i1 %sel_cond_151, i64 %alu_149, i64 %alu_150
  %alu_153 = and i64 %cs_value_31, 2147483647
  %cmp_le_155 = icmp ule i64 %cs_value_27, %cs_value_23
  %alu_154 = zext i1 %cmp_le_155 to i64
  %alu_156 = sub i64 %cs_value_23, %cs_value_27
  %alu_157 = sub i64 %cs_value_27, %cs_value_23
  %sel_cond_158 = icmp ne i64 %alu_154, 0
  %sel_159 = select i1 %sel_cond_158, i64 %alu_156, i64 %alu_157
  %alu_160 = lshr i64 %cs_value_31, 32
  %cmp_lt_162 = icmp ult i64 0, %alu_160
  %alu_161 = zext i1 %cmp_lt_162 to i64
  %alu_163 = lshr i64 %cs_value_31, 32
  %sel_cond_164 = icmp ne i64 %alu_161, 0
  %sel_165 = select i1 %sel_cond_164, i64 %alu_163, i64 1
  %alu_166 = and i64 %sel_165, 31
  %sh_amt_168 = and i64 %alu_166, 63
  %alu_167 = lshr i64 %sel_159, %sh_amt_168
  %alu_169 = sub i64 %alu_153, %alu_167
  %sel_cond_170 = icmp ne i64 %alu_145, 0
  %sel_171 = select i1 %sel_cond_170, i64 %sel_152, i64 %alu_169
  %sel_cond_172 = icmp ne i64 %alu_120, 0
  %sel_173 = select i1 %sel_cond_172, i64 0, i64 %sel_171
  %alu_174 = sub i64 0, %sel_173
  %sel_cond_175 = icmp ne i64 %alu_32, 0
  %sel_176 = select i1 %sel_cond_175, i64 %sel_103, i64 %alu_174
  %p_out_177 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_176, ptr %p_out_177, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_178 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_178
}

; LNIRDecl: down2x2_fused_eq_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @down2x2_fused_eq_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1, ptr noalias noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca ptr, align 8
  store ptr null, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca ptr, align 8
  store ptr null, ptr %slot_v4, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  store ptr %arg_v2, ptr %slot_v2, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %ldp_28 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_29 = getelementptr inbounds i64, ptr %ldp_28, i64 3
  %cs_at_30 = getelementptr inbounds i64, ptr %cs_ptr_29, i64 %par_iv_15
  %cs_value_31 = load i64, ptr %cs_at_30, align 8
  %alu_32 = add i64 %cs_value_23, %cs_value_27
  %alu_33 = add i64 %alu_32, 2
  %alu_34 = lshr i64 %alu_33, 2
  %alu_35 = sub i64 %alu_34, 128
  %fma_mul_36 = mul i64 %alu_35, %cs_value_31
  %fma_add_37 = add i64 %fma_mul_36, 128
  %alu_38 = shl i64 %fma_add_37, 32
  %alu_39 = ashr i64 %alu_38, 32
  %alu_40 = ashr i64 %alu_39, 8
  %alu_41 = add i64 %alu_40, 128
  %p_out_42 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_41, ptr %p_out_42, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_43 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_43
}

; LNIRDecl: down2x2_fused_brightness_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @down2x2_fused_brightness_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = add i64 %cs_value_23, %cs_value_27
  %alu_29 = shl i64 %alu_28, 32
  %alu_30 = ashr i64 %alu_29, 32
  %cmp_le_32 = icmp ule i64 %alu_30, 255
  %alu_31 = zext i1 %cmp_le_32 to i64
  %alu_33 = add i64 %cs_value_23, %cs_value_27
  %alu_34 = shl i64 %alu_33, 32
  %alu_35 = ashr i64 %alu_34, 32
  %alu_36 = add i64 %cs_value_23, %cs_value_27
  %alu_37 = shl i64 %alu_36, 32
  %alu_38 = ashr i64 %alu_37, 32
  %alu_39 = lshr i64 %alu_38, 63
  %sel_cond_40 = icmp ne i64 %alu_39, 0
  %sel_41 = select i1 %sel_cond_40, i64 0, i64 255
  %sel_cond_42 = icmp ne i64 %alu_31, 0
  %sel_43 = select i1 %sel_cond_42, i64 %alu_35, i64 %sel_41
  %p_out_44 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_43, ptr %p_out_44, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_45 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_45
}

; LNIRDecl: yuv420p_studio_range_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @yuv420p_studio_range_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = and i64 %cs_value_27, 1
  %cmp_lt_30 = icmp ult i64 %cs_value_23, 16
  %alu_29 = zext i1 %cmp_lt_30 to i64
  %cmp_lt_32 = icmp ult i64 240, %cs_value_23
  %alu_31 = zext i1 %cmp_lt_32 to i64
  %sel_cond_33 = icmp ne i64 %alu_31, 0
  %sel_34 = select i1 %sel_cond_33, i64 240, i64 %cs_value_23
  %sel_cond_35 = icmp ne i64 %alu_29, 0
  %sel_36 = select i1 %sel_cond_35, i64 16, i64 %sel_34
  %cmp_lt_38 = icmp ult i64 %cs_value_23, 16
  %alu_37 = zext i1 %cmp_lt_38 to i64
  %cmp_lt_40 = icmp ult i64 235, %cs_value_23
  %alu_39 = zext i1 %cmp_lt_40 to i64
  %sel_cond_41 = icmp ne i64 %alu_39, 0
  %sel_42 = select i1 %sel_cond_41, i64 235, i64 %cs_value_23
  %sel_cond_43 = icmp ne i64 %alu_37, 0
  %sel_44 = select i1 %sel_cond_43, i64 16, i64 %sel_42
  %sel_cond_45 = icmp ne i64 %alu_28, 0
  %sel_46 = select i1 %sel_cond_45, i64 %sel_36, i64 %sel_44
  %p_out_47 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %sel_46, ptr %p_out_47, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_48 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_48
}

; LNIRDecl: bt2020_to_bt709_uv_simd (assurance=TranslationValidated, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
define dso_local ptr @bt2020_to_bt709_uv_simd(ptr noalias noundef %arg_v0, ptr noalias noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca ptr, align 8
  store ptr null, ptr %slot_v0, align 8
  %slot_v1 = alloca ptr, align 8
  store ptr null, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca ptr, align 8
  store ptr null, ptr %slot_v3, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store ptr %arg_v0, ptr %slot_v0, align 8
  store ptr %arg_v1, ptr %slot_v1, align 8
  %ldp_0 = load ptr, ptr %slot_v0, align 8
  %sz_ptr_1 = getelementptr inbounds i64, ptr %ldp_0, i64 1
  %sz_val_2 = load i64, ptr %sz_ptr_1, align 8
  store i64 %sz_val_2, ptr %slot_v2, align 8
  %ld_3 = load i64, ptr %slot_v2, align 8
  %ldp_4 = load ptr, ptr %slot_v0, align 8
  %ldp_5 = load ptr, ptr %slot_v1, align 8
  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition
  %par_out_6 = call ptr @lean_native_ensure_exclusive_uninit(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  br label %par_prehdr_10
par_prehdr_10:
  br label %par_cond_11
par_cond_11:
  %par_iv_15 = phi i64 [ 0, %par_prehdr_10 ], [ %par_iv_next_16, %par_latch_13 ]
  %par_cmp_17 = icmp ult i64 %par_iv_15, %ld_3
  br i1 %par_cmp_17, label %par_body_12, label %par_exit_14
par_body_12:
  %p_in0_18 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_15
  %v_in0_19 = load i64, ptr %p_in0_18, align 8
  %ldp_20 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_21 = getelementptr inbounds i64, ptr %ldp_20, i64 3
  %cs_at_22 = getelementptr inbounds i64, ptr %cs_ptr_21, i64 %par_iv_15
  %cs_value_23 = load i64, ptr %cs_at_22, align 8
  %ldp_24 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_25 = getelementptr inbounds i64, ptr %ldp_24, i64 3
  %cs_at_26 = getelementptr inbounds i64, ptr %cs_ptr_25, i64 %par_iv_15
  %cs_value_27 = load i64, ptr %cs_at_26, align 8
  %alu_28 = sub i64 %cs_value_23, 128
  %alu_29 = sub i64 %cs_value_27, 128
  %alu_30 = mul i64 %alu_29, 986
  %fma_mul_31 = mul i64 %alu_28, 18446744073709551574
  %fma_add_32 = add i64 %fma_mul_31, %alu_30
  %alu_33 = add i64 %fma_add_32, 512
  %alu_34 = ashr i64 %alu_33, 10
  %alu_35 = add i64 %alu_34, 128
  %cmp_le_37 = icmp ule i64 %alu_35, 255
  %alu_36 = zext i1 %cmp_le_37 to i64
  %alu_38 = sub i64 %cs_value_23, 128
  %alu_39 = sub i64 %cs_value_27, 128
  %alu_40 = mul i64 %alu_39, 986
  %fma_mul_41 = mul i64 %alu_38, 18446744073709551574
  %fma_add_42 = add i64 %fma_mul_41, %alu_40
  %alu_43 = add i64 %fma_add_42, 512
  %alu_44 = ashr i64 %alu_43, 10
  %alu_45 = add i64 %alu_44, 128
  %alu_46 = sub i64 %cs_value_23, 128
  %alu_47 = sub i64 %cs_value_27, 128
  %alu_48 = mul i64 %alu_47, 986
  %fma_mul_49 = mul i64 %alu_46, 18446744073709551574
  %fma_add_50 = add i64 %fma_mul_49, %alu_48
  %alu_51 = add i64 %fma_add_50, 512
  %alu_52 = ashr i64 %alu_51, 10
  %alu_53 = add i64 %alu_52, 128
  %alu_54 = lshr i64 %alu_53, 63
  %sel_cond_55 = icmp ne i64 %alu_54, 0
  %sel_56 = select i1 %sel_cond_55, i64 0, i64 255
  %sel_cond_57 = icmp ne i64 %alu_36, 0
  %sel_58 = select i1 %sel_cond_57, i64 %alu_45, i64 %sel_56
  %alu_59 = shl i64 %sel_58, 8
  %alu_60 = sub i64 %cs_value_23, 128
  %alu_61 = sub i64 %cs_value_27, 128
  %alu_62 = mul i64 %alu_61, 18446744073709551542
  %fma_mul_63 = mul i64 %alu_60, 1004
  %fma_add_64 = add i64 %fma_mul_63, %alu_62
  %alu_65 = add i64 %fma_add_64, 512
  %alu_66 = ashr i64 %alu_65, 10
  %alu_67 = add i64 %alu_66, 128
  %cmp_le_69 = icmp ule i64 %alu_67, 255
  %alu_68 = zext i1 %cmp_le_69 to i64
  %alu_70 = sub i64 %cs_value_23, 128
  %alu_71 = sub i64 %cs_value_27, 128
  %alu_72 = mul i64 %alu_71, 18446744073709551542
  %fma_mul_73 = mul i64 %alu_70, 1004
  %fma_add_74 = add i64 %fma_mul_73, %alu_72
  %alu_75 = add i64 %fma_add_74, 512
  %alu_76 = ashr i64 %alu_75, 10
  %alu_77 = add i64 %alu_76, 128
  %alu_78 = sub i64 %cs_value_23, 128
  %alu_79 = sub i64 %cs_value_27, 128
  %alu_80 = mul i64 %alu_79, 18446744073709551542
  %fma_mul_81 = mul i64 %alu_78, 1004
  %fma_add_82 = add i64 %fma_mul_81, %alu_80
  %alu_83 = add i64 %fma_add_82, 512
  %alu_84 = ashr i64 %alu_83, 10
  %alu_85 = add i64 %alu_84, 128
  %alu_86 = lshr i64 %alu_85, 63
  %sel_cond_87 = icmp ne i64 %alu_86, 0
  %sel_88 = select i1 %sel_cond_87, i64 0, i64 255
  %sel_cond_89 = icmp ne i64 %alu_68, 0
  %sel_90 = select i1 %sel_cond_89, i64 %alu_77, i64 %sel_88
  %alu_91 = or i64 %alu_59, %sel_90
  %p_out_92 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_15
  store i64 %alu_91, ptr %p_out_92, align 8
  br label %par_latch_13
par_latch_13:
  %par_iv_next_16 = add nuw nsw i64 %par_iv_15, 1
  br label %par_cond_11, !llvm.loop !0
par_exit_14:
  %ldp_93 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_93
}

; LNIRDecl: lnir_px_down2x2 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down2x2(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = add i64 %ld_0, 2
  %alu_2 = lshr i64 %alu_1, 2
  store i64 %alu_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_3
}

; LNIRDecl: lnir_px_down2x2_fused_eq_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down2x2_fused_eq_u8(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = add i64 %ld_0, 2
  %alu_2 = lshr i64 %alu_1, 2
  store i64 %alu_2, ptr %slot_v3, align 8
  %ld_3 = load i64, ptr %slot_v3, align 8
  %alu_4 = sub i64 %ld_3, 128
  store i64 %alu_4, ptr %slot_v4, align 8
  %ld_5 = load i64, ptr %slot_v4, align 8
  %ld_6 = load i64, ptr %slot_v1, align 8
  %alu_7 = mul i64 %ld_5, %ld_6
  %alu_8 = add i64 %alu_7, 128
  %alu_9 = shl i64 %alu_8, 32
  %alu_10 = ashr i64 %alu_9, 32
  store i64 %alu_10, ptr %slot_v5, align 8
  %ld_11 = load i64, ptr %slot_v5, align 8
  %alu_12 = ashr i64 %ld_11, 8
  store i64 %alu_12, ptr %slot_v6, align 8
  %ld_13 = load i64, ptr %slot_v6, align 8
  %alu_14 = add i64 %ld_13, 128
  %ld_15 = load i64, ptr %slot_v2, align 8
  %alu_16 = add i64 %alu_14, %ld_15
  %alu_17 = shl i64 %alu_16, 32
  %alu_18 = ashr i64 %alu_17, 32
  store i64 %alu_18, ptr %slot_v7, align 8
  %ld_19 = load i64, ptr %slot_v7, align 8
  %cmp_le_21 = icmp ule i64 %ld_19, 255
  %alu_20 = zext i1 %cmp_le_21 to i64
  %ld_22 = load i64, ptr %slot_v7, align 8
  %ld_23 = load i64, ptr %slot_v7, align 8
  %alu_24 = lshr i64 %ld_23, 63
  %sel_cond_25 = icmp ne i64 %alu_24, 0
  %sel_26 = select i1 %sel_cond_25, i64 0, i64 255
  %sel_cond_27 = icmp ne i64 %alu_20, 0
  %sel_28 = select i1 %sel_cond_27, i64 %ld_22, i64 %sel_26
  store i64 %sel_28, ptr %slot_v8, align 8
  %ld_29 = load i64, ptr %slot_v8, align 8
  ret i64 %ld_29
}

; LNIRDecl: lnir_px_down3x3_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down3x3_u8(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = add i64 %ld_0, 4
  %alu_2 = mul i64 %alu_1, 7282
  %alu_3 = lshr i64 %alu_2, 16
  store i64 %alu_3, ptr %slot_v1, align 8
  %ld_4 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_4
}

; LNIRDecl: lnir_px_down3x3_u16 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down3x3_u16(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = add i64 %ld_0, 4
  %alu_2 = udiv i64 %alu_1, 9
  store i64 %alu_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_3
}

; LNIRDecl: lnir_px_down3to2_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down3to2_u8(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3, i64 noundef %arg_v4, i64 noundef %arg_v5) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  store i64 %arg_v4, ptr %slot_v4, align 8
  store i64 %arg_v5, ptr %slot_v5, align 8
  %ld_0 = load i64, ptr %slot_v4, align 8
  %alu_1 = and i64 %ld_0, 1
  %ld_2 = load i64, ptr %slot_v0, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  %alu_4 = shl i64 %ld_3, 1
  %alu_5 = add i64 %ld_2, %alu_4
  %ld_6 = load i64, ptr %slot_v0, align 8
  %alu_7 = shl i64 %ld_6, 1
  %ld_8 = load i64, ptr %slot_v1, align 8
  %alu_9 = add i64 %alu_7, %ld_8
  %sel_cond_10 = icmp ne i64 %alu_1, 0
  %sel_11 = select i1 %sel_cond_10, i64 %alu_5, i64 %alu_9
  store i64 %sel_11, ptr %slot_v6, align 8
  %ld_12 = load i64, ptr %slot_v4, align 8
  %alu_13 = and i64 %ld_12, 1
  %ld_14 = load i64, ptr %slot_v2, align 8
  %ld_15 = load i64, ptr %slot_v3, align 8
  %alu_16 = shl i64 %ld_15, 1
  %alu_17 = add i64 %ld_14, %alu_16
  %ld_18 = load i64, ptr %slot_v2, align 8
  %alu_19 = shl i64 %ld_18, 1
  %ld_20 = load i64, ptr %slot_v3, align 8
  %alu_21 = add i64 %alu_19, %ld_20
  %sel_cond_22 = icmp ne i64 %alu_13, 0
  %sel_23 = select i1 %sel_cond_22, i64 %alu_17, i64 %alu_21
  store i64 %sel_23, ptr %slot_v7, align 8
  %ld_24 = load i64, ptr %slot_v5, align 8
  %alu_25 = and i64 %ld_24, 1
  %ld_26 = load i64, ptr %slot_v6, align 8
  %ld_27 = load i64, ptr %slot_v7, align 8
  %alu_28 = shl i64 %ld_27, 1
  %alu_29 = add i64 %ld_26, %alu_28
  %ld_30 = load i64, ptr %slot_v6, align 8
  %alu_31 = shl i64 %ld_30, 1
  %ld_32 = load i64, ptr %slot_v7, align 8
  %alu_33 = add i64 %alu_31, %ld_32
  %sel_cond_34 = icmp ne i64 %alu_25, 0
  %sel_35 = select i1 %sel_cond_34, i64 %alu_29, i64 %alu_33
  store i64 %sel_35, ptr %slot_v8, align 8
  %ld_36 = load i64, ptr %slot_v8, align 8
  %alu_37 = add i64 %ld_36, 4
  %alu_38 = mul i64 %alu_37, 7282
  %alu_39 = lshr i64 %alu_38, 16
  store i64 %alu_39, ptr %slot_v9, align 8
  %ld_40 = load i64, ptr %slot_v9, align 8
  ret i64 %ld_40
}

; LNIRDecl: lnir_px_down3to2_u16_clamp10 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_down3to2_u16_clamp10(i64 noundef %arg_v0, i64 noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %ld_1 = load i64, ptr %slot_v1, align 8
  %alu_2 = add i64 %ld_0, %ld_1
  %alu_3 = add i64 %alu_2, 2
  %alu_4 = lshr i64 %alu_3, 2
  store i64 %alu_4, ptr %slot_v2, align 8
  %ld_5 = load i64, ptr %slot_v2, align 8
  %cmp_lt_7 = icmp ult i64 1023, %ld_5
  %alu_6 = zext i1 %cmp_lt_7 to i64
  %ld_8 = load i64, ptr %slot_v2, align 8
  %sel_cond_9 = icmp ne i64 %alu_6, 0
  %sel_10 = select i1 %sel_cond_9, i64 1023, i64 %ld_8
  store i64 %sel_10, ptr %slot_v3, align 8
  %ld_11 = load i64, ptr %slot_v3, align 8
  ret i64 %ld_11
}

; LNIRDecl: lnir_px_av1_cdef_tap (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_av1_cdef_tap(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  %ld_0 = load i64, ptr %slot_v2, align 8
  %alu_1 = and i64 %ld_0, 2147483647
  store i64 %alu_1, ptr %slot_v4, align 8
  %ld_2 = load i64, ptr %slot_v3, align 8
  %alu_3 = and i64 %ld_2, 4294967295
  store i64 %alu_3, ptr %slot_v5, align 8
  %ld_4 = load i64, ptr %slot_v5, align 8
  %cmp_lt_6 = icmp ult i64 0, %ld_4
  %alu_5 = zext i1 %cmp_lt_6 to i64
  %ld_7 = load i64, ptr %slot_v5, align 8
  %sel_cond_8 = icmp ne i64 %alu_5, 0
  %sel_9 = select i1 %sel_cond_8, i64 %ld_7, i64 1
  %alu_10 = and i64 %sel_9, 31
  store i64 %alu_10, ptr %slot_v6, align 8
  %ld_11 = load i64, ptr %slot_v1, align 8
  %ld_12 = load i64, ptr %slot_v0, align 8
  %cmp_le_14 = icmp ule i64 %ld_11, %ld_12
  %alu_13 = zext i1 %cmp_le_14 to i64
  %ld_15 = load i64, ptr %slot_v0, align 8
  %ld_16 = load i64, ptr %slot_v1, align 8
  %alu_17 = sub i64 %ld_15, %ld_16
  %ld_18 = load i64, ptr %slot_v1, align 8
  %ld_19 = load i64, ptr %slot_v0, align 8
  %alu_20 = sub i64 %ld_18, %ld_19
  %sel_cond_21 = icmp ne i64 %alu_13, 0
  %sel_22 = select i1 %sel_cond_21, i64 %alu_17, i64 %alu_20
  store i64 %sel_22, ptr %slot_v7, align 8
  %ld_23 = load i64, ptr %slot_v7, align 8
  %ld_24 = load i64, ptr %slot_v6, align 8
  %sh_amt_26 = and i64 %ld_24, 63
  %alu_25 = lshr i64 %ld_23, %sh_amt_26
  store i64 %alu_25, ptr %slot_v8, align 8
  %ld_27 = load i64, ptr %slot_v4, align 8
  %ld_28 = load i64, ptr %slot_v8, align 8
  %cmp_le_30 = icmp ule i64 %ld_27, %ld_28
  %alu_29 = zext i1 %cmp_le_30 to i64
  %ld_31 = load i64, ptr %slot_v7, align 8
  %ld_32 = load i64, ptr %slot_v4, align 8
  %ld_33 = load i64, ptr %slot_v8, align 8
  %alu_34 = sub i64 %ld_32, %ld_33
  %cmp_le_36 = icmp ule i64 %ld_31, %alu_34
  %alu_35 = zext i1 %cmp_le_36 to i64
  %ld_37 = load i64, ptr %slot_v7, align 8
  %ld_38 = load i64, ptr %slot_v4, align 8
  %ld_39 = load i64, ptr %slot_v8, align 8
  %alu_40 = sub i64 %ld_38, %ld_39
  %sel_cond_41 = icmp ne i64 %alu_35, 0
  %sel_42 = select i1 %sel_cond_41, i64 %ld_37, i64 %alu_40
  %sel_cond_43 = icmp ne i64 %alu_29, 0
  %sel_44 = select i1 %sel_cond_43, i64 0, i64 %sel_42
  store i64 %sel_44, ptr %slot_v9, align 8
  %ld_45 = load i64, ptr %slot_v1, align 8
  %ld_46 = load i64, ptr %slot_v0, align 8
  %cmp_le_48 = icmp ule i64 %ld_45, %ld_46
  %alu_47 = zext i1 %cmp_le_48 to i64
  %ld_49 = load i64, ptr %slot_v9, align 8
  %ld_50 = load i64, ptr %slot_v9, align 8
  %alu_51 = sub i64 0, %ld_50
  %sel_cond_52 = icmp ne i64 %alu_47, 0
  %sel_53 = select i1 %sel_cond_52, i64 %ld_49, i64 %alu_51
  store i64 %sel_53, ptr %slot_v10, align 8
  %ld_54 = load i64, ptr %slot_v10, align 8
  ret i64 %ld_54
}

; LNIRDecl: lnir_px_av1_cdef_filter4_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_av1_cdef_filter4_u8(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3, i64 noundef %arg_v4) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  store i64 %arg_v4, ptr %slot_v4, align 8
  %ld_0 = load i64, ptr %slot_v1, align 8
  %ld_1 = load i64, ptr %slot_v2, align 8
  %alu_2 = add i64 %ld_0, %ld_1
  %ld_3 = load i64, ptr %slot_v3, align 8
  %ld_4 = load i64, ptr %slot_v4, align 8
  %alu_5 = add i64 %ld_3, %ld_4
  %alu_6 = add i64 %alu_2, %alu_5
  store i64 %alu_6, ptr %slot_v5, align 8
  %ld_7 = load i64, ptr %slot_v5, align 8
  %alu_8 = add i64 %ld_7, 2
  %alu_9 = ashr i64 %alu_8, 2
  store i64 %alu_9, ptr %slot_v6, align 8
  %ld_10 = load i64, ptr %slot_v0, align 8
  %ld_11 = load i64, ptr %slot_v6, align 8
  %alu_12 = add i64 %ld_10, %ld_11
  store i64 %alu_12, ptr %slot_v7, align 8
  %ld_13 = load i64, ptr %slot_v7, align 8
  %cmp_le_15 = icmp ule i64 %ld_13, 255
  %alu_14 = zext i1 %cmp_le_15 to i64
  %ld_16 = load i64, ptr %slot_v7, align 8
  %ld_17 = load i64, ptr %slot_v7, align 8
  %alu_18 = lshr i64 %ld_17, 63
  %sel_cond_19 = icmp ne i64 %alu_18, 0
  %sel_20 = select i1 %sel_cond_19, i64 0, i64 255
  %sel_cond_21 = icmp ne i64 %alu_14, 0
  %sel_22 = select i1 %sel_cond_21, i64 %ld_16, i64 %sel_20
  store i64 %sel_22, ptr %slot_v8, align 8
  %ld_23 = load i64, ptr %slot_v8, align 8
  ret i64 %ld_23
}

; LNIRDecl: lnir_px_bilinear_q8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_bilinear_q8(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3, i64 noundef %arg_v4, i64 noundef %arg_v5) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  store i64 %arg_v4, ptr %slot_v4, align 8
  store i64 %arg_v5, ptr %slot_v5, align 8
  %ld_0 = load i64, ptr %slot_v4, align 8
  %alu_1 = sub i64 256, %ld_0
  store i64 %alu_1, ptr %slot_v6, align 8
  %ld_2 = load i64, ptr %slot_v5, align 8
  %alu_3 = sub i64 256, %ld_2
  store i64 %alu_3, ptr %slot_v7, align 8
  %ld_4 = load i64, ptr %slot_v0, align 8
  %ld_5 = load i64, ptr %slot_v6, align 8
  %alu_6 = mul i64 %ld_4, %ld_5
  %ld_7 = load i64, ptr %slot_v1, align 8
  %ld_8 = load i64, ptr %slot_v4, align 8
  %alu_9 = mul i64 %ld_7, %ld_8
  %alu_10 = add i64 %alu_6, %alu_9
  store i64 %alu_10, ptr %slot_v8, align 8
  %ld_11 = load i64, ptr %slot_v2, align 8
  %ld_12 = load i64, ptr %slot_v6, align 8
  %alu_13 = mul i64 %ld_11, %ld_12
  %ld_14 = load i64, ptr %slot_v3, align 8
  %ld_15 = load i64, ptr %slot_v4, align 8
  %alu_16 = mul i64 %ld_14, %ld_15
  %alu_17 = add i64 %alu_13, %alu_16
  store i64 %alu_17, ptr %slot_v9, align 8
  %ld_18 = load i64, ptr %slot_v8, align 8
  %ld_19 = load i64, ptr %slot_v7, align 8
  %alu_20 = mul i64 %ld_18, %ld_19
  %ld_21 = load i64, ptr %slot_v9, align 8
  %ld_22 = load i64, ptr %slot_v5, align 8
  %alu_23 = mul i64 %ld_21, %ld_22
  %alu_24 = add i64 %alu_20, %alu_23
  %alu_25 = add i64 %alu_24, 32768
  %alu_26 = lshr i64 %alu_25, 16
  store i64 %alu_26, ptr %slot_v10, align 8
  %ld_27 = load i64, ptr %slot_v10, align 8
  ret i64 %ld_27
}

; LNIRDecl: lnir_px_bilinear_q8_clamp10 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_bilinear_q8_clamp10(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3, i64 noundef %arg_v4, i64 noundef %arg_v5) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  %slot_v9 = alloca i64, align 8
  store i64 0, ptr %slot_v9, align 8
  %slot_v10 = alloca i64, align 8
  store i64 0, ptr %slot_v10, align 8
  %slot_v11 = alloca i64, align 8
  store i64 0, ptr %slot_v11, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  store i64 %arg_v4, ptr %slot_v4, align 8
  store i64 %arg_v5, ptr %slot_v5, align 8
  %ld_0 = load i64, ptr %slot_v4, align 8
  %alu_1 = sub i64 256, %ld_0
  store i64 %alu_1, ptr %slot_v6, align 8
  %ld_2 = load i64, ptr %slot_v5, align 8
  %alu_3 = sub i64 256, %ld_2
  store i64 %alu_3, ptr %slot_v7, align 8
  %ld_4 = load i64, ptr %slot_v0, align 8
  %ld_5 = load i64, ptr %slot_v6, align 8
  %alu_6 = mul i64 %ld_4, %ld_5
  %ld_7 = load i64, ptr %slot_v1, align 8
  %ld_8 = load i64, ptr %slot_v4, align 8
  %alu_9 = mul i64 %ld_7, %ld_8
  %alu_10 = add i64 %alu_6, %alu_9
  store i64 %alu_10, ptr %slot_v8, align 8
  %ld_11 = load i64, ptr %slot_v2, align 8
  %ld_12 = load i64, ptr %slot_v6, align 8
  %alu_13 = mul i64 %ld_11, %ld_12
  %ld_14 = load i64, ptr %slot_v3, align 8
  %ld_15 = load i64, ptr %slot_v4, align 8
  %alu_16 = mul i64 %ld_14, %ld_15
  %alu_17 = add i64 %alu_13, %alu_16
  store i64 %alu_17, ptr %slot_v9, align 8
  %ld_18 = load i64, ptr %slot_v8, align 8
  %ld_19 = load i64, ptr %slot_v7, align 8
  %alu_20 = mul i64 %ld_18, %ld_19
  %ld_21 = load i64, ptr %slot_v9, align 8
  %ld_22 = load i64, ptr %slot_v5, align 8
  %alu_23 = mul i64 %ld_21, %ld_22
  %alu_24 = add i64 %alu_20, %alu_23
  %alu_25 = add i64 %alu_24, 32768
  %alu_26 = lshr i64 %alu_25, 16
  store i64 %alu_26, ptr %slot_v10, align 8
  %ld_27 = load i64, ptr %slot_v10, align 8
  %cmp_lt_29 = icmp ult i64 1023, %ld_27
  %alu_28 = zext i1 %cmp_lt_29 to i64
  %ld_30 = load i64, ptr %slot_v10, align 8
  %sel_cond_31 = icmp ne i64 %alu_28, 0
  %sel_32 = select i1 %sel_cond_31, i64 1023, i64 %ld_30
  store i64 %sel_32, ptr %slot_v11, align 8
  %ld_33 = load i64, ptr %slot_v11, align 8
  ret i64 %ld_33
}

; LNIRDecl: lnir_px_extract_u16le_msb8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_extract_u16le_msb8(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = lshr i64 %ld_0, 2
  %alu_2 = and i64 %alu_1, 255
  store i64 %alu_2, ptr %slot_v1, align 8
  %ld_3 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_3
}

; LNIRDecl: lnir_px_u16le_to_u10 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_u16le_to_u10(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = lshr i64 %ld_0, 2
  store i64 %alu_1, ptr %slot_v1, align 8
  %ld_2 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_2
}

; LNIRDecl: lnir_px_luma_stats_pack (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_luma_stats_pack(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %ld_1 = load i64, ptr %slot_v2, align 8
  %div_z_4 = icmp eq i64 %ld_1, 0
  %div_rhs_3 = select i1 %div_z_4, i64 1, i64 %ld_1
  %div_raw_5 = udiv i64 %ld_0, %div_rhs_3
  %alu_2 = select i1 %div_z_4, i64 0, i64 %div_raw_5
  store i64 %alu_2, ptr %slot_v3, align 8
  %ld_6 = load i64, ptr %slot_v1, align 8
  %ld_7 = load i64, ptr %slot_v2, align 8
  %div_z_10 = icmp eq i64 %ld_7, 0
  %div_rhs_9 = select i1 %div_z_10, i64 1, i64 %ld_7
  %div_raw_11 = udiv i64 %ld_6, %div_rhs_9
  %alu_8 = select i1 %div_z_10, i64 0, i64 %div_raw_11
  store i64 %alu_8, ptr %slot_v4, align 8
  %ld_12 = load i64, ptr %slot_v3, align 8
  %ld_13 = load i64, ptr %slot_v3, align 8
  %alu_14 = mul i64 %ld_12, %ld_13
  store i64 %alu_14, ptr %slot_v5, align 8
  %ld_15 = load i64, ptr %slot_v5, align 8
  %ld_16 = load i64, ptr %slot_v4, align 8
  %cmp_lt_18 = icmp ult i64 %ld_15, %ld_16
  %alu_17 = zext i1 %cmp_lt_18 to i64
  %ld_19 = load i64, ptr %slot_v4, align 8
  %ld_20 = load i64, ptr %slot_v5, align 8
  %alu_21 = sub i64 %ld_19, %ld_20
  %sel_cond_22 = icmp ne i64 %alu_17, 0
  %sel_23 = select i1 %sel_cond_22, i64 %alu_21, i64 0
  store i64 %sel_23, ptr %slot_v6, align 8
  %ld_24 = load i64, ptr %slot_v6, align 8
  %alu_25 = shl i64 %ld_24, 32
  %ld_26 = load i64, ptr %slot_v3, align 8
  %alu_27 = and i64 %ld_26, 4294967295
  %alu_28 = or i64 %alu_25, %alu_27
  store i64 %alu_28, ptr %slot_v7, align 8
  %ld_29 = load i64, ptr %slot_v7, align 8
  ret i64 %ld_29
}

; LNIRDecl: lnir_px_luma_acceptance_accum (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_luma_acceptance_accum(i64 noundef %arg_v0, i64 noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  %ld_0 = load i64, ptr %slot_v1, align 8
  %ld_1 = load i64, ptr %slot_v0, align 8
  %cmp_le_3 = icmp ule i64 %ld_0, %ld_1
  %alu_2 = zext i1 %cmp_le_3 to i64
  %ld_4 = load i64, ptr %slot_v0, align 8
  %ld_5 = load i64, ptr %slot_v1, align 8
  %alu_6 = sub i64 %ld_4, %ld_5
  %ld_7 = load i64, ptr %slot_v1, align 8
  %ld_8 = load i64, ptr %slot_v0, align 8
  %alu_9 = sub i64 %ld_7, %ld_8
  %sel_cond_10 = icmp ne i64 %alu_2, 0
  %sel_11 = select i1 %sel_cond_10, i64 %alu_6, i64 %alu_9
  store i64 %sel_11, ptr %slot_v2, align 8
  %ld_12 = load i64, ptr %slot_v0, align 8
  %cmp_le_14 = icmp ule i64 16, %ld_12
  %alu_13 = zext i1 %cmp_le_14 to i64
  %ld_15 = load i64, ptr %slot_v0, align 8
  %alu_16 = sub i64 %ld_15, 16
  %ld_17 = load i64, ptr %slot_v0, align 8
  %alu_18 = sub i64 16, %ld_17
  %sel_cond_19 = icmp ne i64 %alu_13, 0
  %sel_20 = select i1 %sel_cond_19, i64 %alu_16, i64 %alu_18
  store i64 %sel_20, ptr %slot_v3, align 8
  %ld_21 = load i64, ptr %slot_v2, align 8
  %ld_22 = load i64, ptr %slot_v2, align 8
  %alu_23 = mul i64 %ld_21, %ld_22
  store i64 %alu_23, ptr %slot_v4, align 8
  %ld_24 = load i64, ptr %slot_v2, align 8
  %ld_25 = load i64, ptr %slot_v3, align 8
  %alu_26 = shl i64 %ld_25, 16
  %alu_27 = or i64 %ld_24, %alu_26
  %ld_28 = load i64, ptr %slot_v0, align 8
  %alu_29 = shl i64 %ld_28, 32
  %alu_30 = or i64 %alu_27, %alu_29
  %ld_31 = load i64, ptr %slot_v4, align 8
  %alu_32 = shl i64 %ld_31, 48
  %alu_33 = or i64 %alu_30, %alu_32
  store i64 %alu_33, ptr %slot_v5, align 8
  %ld_34 = load i64, ptr %slot_v5, align 8
  ret i64 %ld_34
}

; LNIRDecl: lnir_px_luma_acceptance_gate (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_luma_acceptance_gate(i64 noundef %arg_v0, i64 noundef %arg_v1, i64 noundef %arg_v2, i64 noundef %arg_v3) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  store i64 %arg_v2, ptr %slot_v2, align 8
  store i64 %arg_v3, ptr %slot_v3, align 8
  %ld_0 = load i64, ptr %slot_v2, align 8
  %cmp_le_2 = icmp ule i64 6144, %ld_0
  %alu_1 = zext i1 %cmp_le_2 to i64
  %ld_3 = load i64, ptr %slot_v1, align 8
  %ld_4 = load i64, ptr %slot_v0, align 8
  %cmp_le_6 = icmp ule i64 %ld_3, %ld_4
  %alu_5 = zext i1 %cmp_le_6 to i64
  %ld_7 = load i64, ptr %slot_v3, align 8
  %sel_cond_8 = icmp ne i64 %alu_5, 0
  %sel_9 = select i1 %sel_cond_8, i64 0, i64 %ld_7
  %ld_10 = load i64, ptr %slot_v3, align 8
  %sel_cond_11 = icmp ne i64 %alu_1, 0
  %sel_12 = select i1 %sel_cond_11, i64 %sel_9, i64 %ld_10
  store i64 %sel_12, ptr %slot_v4, align 8
  %ld_13 = load i64, ptr %slot_v4, align 8
  ret i64 %ld_13
}

; LNIRDecl: lnir_px_y_studio_clamp_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_y_studio_clamp_u8(i64 noundef %arg_v0) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %cmp_lt_2 = icmp ult i64 %ld_0, 16
  %alu_1 = zext i1 %cmp_lt_2 to i64
  %ld_3 = load i64, ptr %slot_v0, align 8
  %cmp_lt_5 = icmp ult i64 235, %ld_3
  %alu_4 = zext i1 %cmp_lt_5 to i64
  %ld_6 = load i64, ptr %slot_v0, align 8
  %sel_cond_7 = icmp ne i64 %alu_4, 0
  %sel_8 = select i1 %sel_cond_7, i64 235, i64 %ld_6
  %sel_cond_9 = icmp ne i64 %alu_1, 0
  %sel_10 = select i1 %sel_cond_9, i64 16, i64 %sel_8
  store i64 %sel_10, ptr %slot_v1, align 8
  %ld_11 = load i64, ptr %slot_v1, align 8
  ret i64 %ld_11
}

; LNIRDecl: lnir_px_bt2020_to_bt709_uv_u8 (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
define dso_local i64 @lnir_px_bt2020_to_bt709_uv_u8(i64 noundef %arg_v0, i64 noundef %arg_v1) #0 {
entry:
  %slot_v0 = alloca i64, align 8
  store i64 0, ptr %slot_v0, align 8
  %slot_v1 = alloca i64, align 8
  store i64 0, ptr %slot_v1, align 8
  %slot_v2 = alloca i64, align 8
  store i64 0, ptr %slot_v2, align 8
  %slot_v3 = alloca i64, align 8
  store i64 0, ptr %slot_v3, align 8
  %slot_v4 = alloca i64, align 8
  store i64 0, ptr %slot_v4, align 8
  %slot_v5 = alloca i64, align 8
  store i64 0, ptr %slot_v5, align 8
  %slot_v6 = alloca i64, align 8
  store i64 0, ptr %slot_v6, align 8
  %slot_v7 = alloca i64, align 8
  store i64 0, ptr %slot_v7, align 8
  %slot_v8 = alloca i64, align 8
  store i64 0, ptr %slot_v8, align 8
  store i64 %arg_v0, ptr %slot_v0, align 8
  store i64 %arg_v1, ptr %slot_v1, align 8
  %ld_0 = load i64, ptr %slot_v0, align 8
  %alu_1 = sub i64 %ld_0, 128
  store i64 %alu_1, ptr %slot_v2, align 8
  %ld_2 = load i64, ptr %slot_v1, align 8
  %alu_3 = sub i64 %ld_2, 128
  store i64 %alu_3, ptr %slot_v3, align 8
  %ld_4 = load i64, ptr %slot_v2, align 8
  %alu_5 = mul i64 %ld_4, 1004
  %ld_6 = load i64, ptr %slot_v3, align 8
  %alu_7 = mul i64 %ld_6, 18446744073709551542
  %alu_8 = add i64 %alu_5, %alu_7
  %alu_9 = add i64 %alu_8, 512
  %alu_10 = ashr i64 %alu_9, 10
  %alu_11 = add i64 %alu_10, 128
  store i64 %alu_11, ptr %slot_v4, align 8
  %ld_12 = load i64, ptr %slot_v2, align 8
  %alu_13 = mul i64 %ld_12, 18446744073709551574
  %ld_14 = load i64, ptr %slot_v3, align 8
  %alu_15 = mul i64 %ld_14, 986
  %alu_16 = add i64 %alu_13, %alu_15
  %alu_17 = add i64 %alu_16, 512
  %alu_18 = ashr i64 %alu_17, 10
  %alu_19 = add i64 %alu_18, 128
  store i64 %alu_19, ptr %slot_v5, align 8
  %ld_20 = load i64, ptr %slot_v4, align 8
  %cmp_le_22 = icmp ule i64 %ld_20, 255
  %alu_21 = zext i1 %cmp_le_22 to i64
  %ld_23 = load i64, ptr %slot_v4, align 8
  %ld_24 = load i64, ptr %slot_v4, align 8
  %alu_25 = lshr i64 %ld_24, 63
  %sel_cond_26 = icmp ne i64 %alu_25, 0
  %sel_27 = select i1 %sel_cond_26, i64 0, i64 255
  %sel_cond_28 = icmp ne i64 %alu_21, 0
  %sel_29 = select i1 %sel_cond_28, i64 %ld_23, i64 %sel_27
  store i64 %sel_29, ptr %slot_v6, align 8
  %ld_30 = load i64, ptr %slot_v5, align 8
  %cmp_le_32 = icmp ule i64 %ld_30, 255
  %alu_31 = zext i1 %cmp_le_32 to i64
  %ld_33 = load i64, ptr %slot_v5, align 8
  %ld_34 = load i64, ptr %slot_v5, align 8
  %alu_35 = lshr i64 %ld_34, 63
  %sel_cond_36 = icmp ne i64 %alu_35, 0
  %sel_37 = select i1 %sel_cond_36, i64 0, i64 255
  %sel_cond_38 = icmp ne i64 %alu_31, 0
  %sel_39 = select i1 %sel_cond_38, i64 %ld_33, i64 %sel_37
  store i64 %sel_39, ptr %slot_v7, align 8
  %ld_40 = load i64, ptr %slot_v7, align 8
  %alu_41 = shl i64 %ld_40, 8
  %ld_42 = load i64, ptr %slot_v6, align 8
  %alu_43 = or i64 %alu_41, %ld_42
  store i64 %alu_43, ptr %slot_v8, align 8
  %ld_44 = load i64, ptr %slot_v8, align 8
  ret i64 %ld_44
}

; Lean 4 C-ABI Wrapper Thunk for swscale_luma_gain_bias_simd
define dso_local ptr @lean_native_abi_swscale_luma_gain_bias_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %ret = call ptr @swscale_luma_gain_bias_simd(ptr %abi_arg0, i64 %unboxed_1, i64 %unboxed_2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for flac_lpc_autocorr_dot_simd
define dso_local ptr @lean_native_abi_flac_lpc_autocorr_dot_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @flac_lpc_autocorr_dot_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for opus_celt_pvq_mix_saxpy_gpu
define dso_local ptr @lean_native_abi_opus_celt_pvq_mix_saxpy_gpu(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @opus_celt_pvq_mix_saxpy_gpu(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for av1_wiener_3tap_sym_gpu
define dso_local ptr @lean_native_abi_av1_wiener_3tap_sym_gpu(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @av1_wiener_3tap_sym_gpu(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for av1_cdef_fma_blend_gpu
define dso_local ptr @lean_native_abi_av1_cdef_fma_blend_gpu(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @av1_cdef_fma_blend_gpu(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for h264_idct_tuple_accum_sroa
define dso_local ptr @lean_native_abi_h264_idct_tuple_accum_sroa(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %ret64 = call i64 @h264_idct_tuple_accum_sroa(i64 %unboxed_0, i64 %unboxed_1)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for bframe_bipred_blend_gpu
define dso_local ptr @lean_native_abi_bframe_bipred_blend_gpu(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @bframe_bipred_blend_gpu(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for hevc_sao_band_offset_add_gpu
define dso_local ptr @lean_native_abi_hevc_sao_band_offset_add_gpu(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @hevc_sao_band_offset_add_gpu(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for aac_imdct_window_mul_gpu
define dso_local ptr @lean_native_abi_aac_imdct_window_mul_gpu(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @aac_imdct_window_mul_gpu(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for prores_qscale_map_simd
define dso_local ptr @lean_native_abi_prores_qscale_map_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @prores_qscale_map_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for boxblur_div9_recip_shift_simd
define dso_local ptr @lean_native_abi_boxblur_div9_recip_shift_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @boxblur_div9_recip_shift_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for pq10_studio_clamp_select_simd
define dso_local ptr @lean_native_abi_pq10_studio_clamp_select_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @pq10_studio_clamp_select_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for swscale_down2x2_box_simd
define dso_local ptr @lean_native_abi_swscale_down2x2_box_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @swscale_down2x2_box_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for swscale_down3x3_box_simd
define dso_local ptr @lean_native_abi_swscale_down3x3_box_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @swscale_down3x3_box_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for swscale_down3to2_bilinear_simd
define dso_local ptr @lean_native_abi_swscale_down3to2_bilinear_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @swscale_down3to2_bilinear_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for av1_cdef_dir_filter_simd
define dso_local ptr @lean_native_abi_av1_cdef_dir_filter_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @av1_cdef_dir_filter_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for extract_u16le_msb8_simd
define dso_local ptr @lean_native_abi_extract_u16le_msb8_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @extract_u16le_msb8_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for luma_stats_moments_simd
define dso_local ptr @lean_native_abi_luma_stats_moments_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @luma_stats_moments_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for luma_stats_pack_simd
define dso_local ptr @lean_native_abi_luma_stats_pack_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @luma_stats_pack_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for luma_acceptance_accum_simd
define dso_local ptr @lean_native_abi_luma_acceptance_accum_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @luma_acceptance_accum_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for luma_acceptance_gate_simd
define dso_local ptr @lean_native_abi_luma_acceptance_gate_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @luma_acceptance_gate_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for bilinear_q8_blend_simd
define dso_local ptr @lean_native_abi_bilinear_q8_blend_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @bilinear_q8_blend_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for bilinear_q8_pack_simd
define dso_local ptr @lean_native_abi_bilinear_q8_pack_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @bilinear_q8_pack_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for bilinear_q8_clamp10_simd
define dso_local ptr @lean_native_abi_bilinear_q8_clamp10_simd(ptr %abi_arg0) #0 {
entry:
  %ret = call ptr @bilinear_q8_clamp10_simd(ptr %abi_arg0)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for av1_cdef_tap_simd
define dso_local ptr @lean_native_abi_av1_cdef_tap_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @av1_cdef_tap_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for down2x2_fused_eq_simd
define dso_local ptr @lean_native_abi_down2x2_fused_eq_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %ret = call ptr @down2x2_fused_eq_simd(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for down2x2_fused_brightness_simd
define dso_local ptr @lean_native_abi_down2x2_fused_brightness_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @down2x2_fused_brightness_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for yuv420p_studio_range_simd
define dso_local ptr @lean_native_abi_yuv420p_studio_range_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @yuv420p_studio_range_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for bt2020_to_bt709_uv_simd
define dso_local ptr @lean_native_abi_bt2020_to_bt709_uv_simd(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %ret = call ptr @bt2020_to_bt709_uv_simd(ptr %abi_arg0, ptr %abi_arg1)
  ret ptr %ret
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down2x2
define dso_local ptr @lean_native_abi_lnir_px_down2x2(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_down2x2(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down2x2_fused_eq_u8
define dso_local ptr @lean_native_abi_lnir_px_down2x2_fused_eq_u8(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %ret64 = call i64 @lnir_px_down2x2_fused_eq_u8(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down3x3_u8
define dso_local ptr @lean_native_abi_lnir_px_down3x3_u8(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_down3x3_u8(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down3x3_u16
define dso_local ptr @lean_native_abi_lnir_px_down3x3_u16(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_down3x3_u16(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down3to2_u8
define dso_local ptr @lean_native_abi_lnir_px_down3to2_u8(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3, ptr %abi_arg4, ptr %abi_arg5) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %raw_4 = ptrtoint ptr %abi_arg4 to i64
  %unboxed_4 = lshr i64 %raw_4, 1
  %raw_5 = ptrtoint ptr %abi_arg5 to i64
  %unboxed_5 = lshr i64 %raw_5, 1
  %ret64 = call i64 @lnir_px_down3to2_u8(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3, i64 %unboxed_4, i64 %unboxed_5)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_down3to2_u16_clamp10
define dso_local ptr @lean_native_abi_lnir_px_down3to2_u16_clamp10(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %ret64 = call i64 @lnir_px_down3to2_u16_clamp10(i64 %unboxed_0, i64 %unboxed_1)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_av1_cdef_tap
define dso_local ptr @lean_native_abi_lnir_px_av1_cdef_tap(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %ret64 = call i64 @lnir_px_av1_cdef_tap(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_av1_cdef_filter4_u8
define dso_local ptr @lean_native_abi_lnir_px_av1_cdef_filter4_u8(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3, ptr %abi_arg4) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %raw_4 = ptrtoint ptr %abi_arg4 to i64
  %unboxed_4 = lshr i64 %raw_4, 1
  %ret64 = call i64 @lnir_px_av1_cdef_filter4_u8(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3, i64 %unboxed_4)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_bilinear_q8
define dso_local ptr @lean_native_abi_lnir_px_bilinear_q8(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3, ptr %abi_arg4, ptr %abi_arg5) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %raw_4 = ptrtoint ptr %abi_arg4 to i64
  %unboxed_4 = lshr i64 %raw_4, 1
  %raw_5 = ptrtoint ptr %abi_arg5 to i64
  %unboxed_5 = lshr i64 %raw_5, 1
  %ret64 = call i64 @lnir_px_bilinear_q8(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3, i64 %unboxed_4, i64 %unboxed_5)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_bilinear_q8_clamp10
define dso_local ptr @lean_native_abi_lnir_px_bilinear_q8_clamp10(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3, ptr %abi_arg4, ptr %abi_arg5) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %raw_4 = ptrtoint ptr %abi_arg4 to i64
  %unboxed_4 = lshr i64 %raw_4, 1
  %raw_5 = ptrtoint ptr %abi_arg5 to i64
  %unboxed_5 = lshr i64 %raw_5, 1
  %ret64 = call i64 @lnir_px_bilinear_q8_clamp10(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3, i64 %unboxed_4, i64 %unboxed_5)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_extract_u16le_msb8
define dso_local ptr @lean_native_abi_lnir_px_extract_u16le_msb8(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_extract_u16le_msb8(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_u16le_to_u10
define dso_local ptr @lean_native_abi_lnir_px_u16le_to_u10(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_u16le_to_u10(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_luma_stats_pack
define dso_local ptr @lean_native_abi_lnir_px_luma_stats_pack(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %ret64 = call i64 @lnir_px_luma_stats_pack(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_luma_acceptance_accum
define dso_local ptr @lean_native_abi_lnir_px_luma_acceptance_accum(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %ret64 = call i64 @lnir_px_luma_acceptance_accum(i64 %unboxed_0, i64 %unboxed_1)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_luma_acceptance_gate
define dso_local ptr @lean_native_abi_lnir_px_luma_acceptance_gate(ptr %abi_arg0, ptr %abi_arg1, ptr %abi_arg2, ptr %abi_arg3) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %raw_2 = ptrtoint ptr %abi_arg2 to i64
  %unboxed_2 = lshr i64 %raw_2, 1
  %raw_3 = ptrtoint ptr %abi_arg3 to i64
  %unboxed_3 = lshr i64 %raw_3, 1
  %ret64 = call i64 @lnir_px_luma_acceptance_gate(i64 %unboxed_0, i64 %unboxed_1, i64 %unboxed_2, i64 %unboxed_3)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_y_studio_clamp_u8
define dso_local ptr @lean_native_abi_lnir_px_y_studio_clamp_u8(ptr %abi_arg0) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %ret64 = call i64 @lnir_px_y_studio_clamp_u8(i64 %unboxed_0)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

; Lean 4 C-ABI Wrapper Thunk for lnir_px_bt2020_to_bt709_uv_u8
define dso_local ptr @lean_native_abi_lnir_px_bt2020_to_bt709_uv_u8(ptr %abi_arg0, ptr %abi_arg1) #0 {
entry:
  %raw_0 = ptrtoint ptr %abi_arg0 to i64
  %unboxed_0 = lshr i64 %raw_0, 1
  %raw_1 = ptrtoint ptr %abi_arg1 to i64
  %unboxed_1 = lshr i64 %raw_1, 1
  %ret64 = call i64 @lnir_px_bt2020_to_bt709_uv_u8(i64 %unboxed_0, i64 %unboxed_1)
  %shl = shl i64 %ret64, 1
  %tagged = or i64 %shl, 1
  %boxptr = inttoptr i64 %tagged to ptr
  ret ptr %boxptr
}

attributes #0 = { nounwind uwtable }
attributes #1 = { noinline nounwind optnone uwtable }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(none) }

!llvm.ident = !{!4}
!0 = distinct !{!0, !1, !7, !8}
!1 = !{!"llvm.loop.vectorize.enable", i1 true}
!2 = !{!"llvm.loop.unroll.count", i32 4}
!3 = distinct !{!3, !5}
!4 = !{!"lean-native LLVM 18 verified backend"}
!5 = !{!"llvm.loop.vectorize.enable", i1 false}
!6 = distinct !{!6, !2}
!7 = !{!"llvm.loop.interleave.count", i32 4}
!8 = !{!"llvm.loop.vectorize.width", i32 4}
