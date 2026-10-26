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
  %cmp_h = icmp eq i64 %dstH, 0
  %cmp_w = icmp eq i64 %dstW, 0
  %empty = or i1 %cmp_h, %cmp_w
  br i1 %empty, label %exit, label %outer.ph
outer.ph:
  %vec_end = and i64 %dstW, -16
  %has_vec = icmp uge i64 %dstW, 16
  br label %outer.body
outer.body:
  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]
  %sy0 = shl nuw i64 %dy, 1
  %sy1 = or i64 %sy0, 1
  %r0_off = mul nuw i64 %sy0, %srcStride
  %r1_off = mul nuw i64 %sy1, %srcStride
  %dst_off = mul nuw i64 %dy, %dstW
  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off
  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off
  br i1 %has_vec, label %vec.body, label %scalar.check
vec.body:
  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]
  %vsx0 = shl nuw i64 %vdx, 1
  %vsx1 = add nuw i64 %vsx0, 16
  %vp00 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx0
  %vp01 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx1
  %vp10 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx0
  %vp11 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx1
  %vr0_lo = load <16 x i8>, ptr %vp00, align 1
  %vr0_hi = load <16 x i8>, ptr %vp01, align 1
  %vr1_lo = load <16 x i8>, ptr %vp10, align 1
  %vr1_hi = load <16 x i8>, ptr %vp11, align 1
  %r0_even = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %r0_odd  = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %r1_even = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %r1_odd  = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %z00 = zext <16 x i8> %r0_even to <16 x i16>
  %z01 = zext <16 x i8> %r0_odd to <16 x i16>
  %z10 = zext <16 x i8> %r1_even to <16 x i16>
  %z11 = zext <16 x i8> %r1_odd to <16 x i16>
  %vs0 = add nuw nsw <16 x i16> %z00, %z01
  %vs1 = add nuw nsw <16 x i16> %z10, %z11
  %vsum = add nuw nsw <16 x i16> %vs0, %vs1
  %vrnd = add nuw nsw <16 x i16> %vsum, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>
  %vavg = lshr <16 x i16> %vrnd, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>
  %vout = trunc <16 x i16> %vavg to <16 x i8>
  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx
  store <16 x i8> %vout, ptr %vdst_p, align 1
  %vdx_next = add nuw i64 %vdx, 16
  %vdone = icmp eq i64 %vdx_next, %vec_end
  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6
scalar.check:
  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]
  %has_rem = icmp ult i64 %dx_start, %dstW
  br i1 %has_rem, label %inner.body, label %outer.latch
inner.body:
  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]
  %sx0 = shl nuw i64 %dx, 1
  %sx1 = or i64 %sx0, 1
  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0
  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1
  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0
  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1
  %b00 = load i8, ptr %p00_ptr, align 1
  %b01 = load i8, ptr %p01_ptr, align 1
  %b10 = load i8, ptr %p10_ptr, align 1
  %b11 = load i8, ptr %p11_ptr, align 1
  %u00 = zext i8 %b00 to i32
  %u01 = zext i8 %b01 to i32
  %u10 = zext i8 %b10 to i32
  %u11 = zext i8 %b11 to i32
  %s0 = add nuw nsw i32 %u00, %u01
  %s1 = add nuw nsw i32 %u10, %u11
  %sum = add nuw nsw i32 %s0, %s1
  %rnd = add nuw nsw i32 %sum, 2
  %avg = lshr i32 %rnd, 2
  %out_b = trunc i32 %avg to i8
  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx
  store i8 %out_b, ptr %dst_ptr, align 1
  %dx_next = add nuw i64 %dx, 1
  %done_x = icmp eq i64 %dx_next, %dstW
  br i1 %done_x, label %outer.latch, label %inner.body
outer.latch:
  %dy_next = add nuw i64 %dy, 1
  %done_y = icmp eq i64 %dy_next, %dstH
  br i1 %done_y, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down2x2_fused_eq_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH, i64 noundef %contrastQ8_64, i64 noundef %brightness64) #0 {
entry:
  %is_id_c = icmp eq i64 %contrastQ8_64, 256
  %is_id_b = icmp eq i64 %brightness64, 0
  %is_id = and i1 %is_id_c, %is_id_b
  br i1 %is_id, label %fast_id, label %chk_empty
fast_id:
  call void @lean_native_swscale_down2x2_u8(ptr %dst, ptr %src, i64 %srcStride, i64 %dstW, i64 %dstH)
  ret void
chk_empty:
  %cmp_h = icmp eq i64 %dstH, 0
  %cmp_w = icmp eq i64 %dstW, 0
  %empty = or i1 %cmp_h, %cmp_w
  br i1 %empty, label %exit, label %outer.ph
outer.ph:
  %cQ8 = trunc i64 %contrastQ8_64 to i32
  %brt = trunc i64 %brightness64 to i32
  br label %outer.body
outer.body:
  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]
  %sy0 = shl nuw i64 %dy, 1
  %sy1 = or i64 %sy0, 1
  %r0_off = mul nuw i64 %sy0, %srcStride
  %r1_off = mul nuw i64 %sy1, %srcStride
  %dst_off = mul nuw i64 %dy, %dstW
  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off
  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off
  br label %inner.body
inner.body:
  %dx = phi i64 [ 0, %outer.body ], [ %dx_next, %inner.body ]
  %sx0 = shl nuw i64 %dx, 1
  %sx1 = or i64 %sx0, 1
  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0
  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1
  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0
  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1
  %b00 = load i8, ptr %p00_ptr, align 1
  %b01 = load i8, ptr %p01_ptr, align 1
  %b10 = load i8, ptr %p10_ptr, align 1
  %b11 = load i8, ptr %p11_ptr, align 1
  %u00 = zext i8 %b00 to i32
  %u01 = zext i8 %b01 to i32
  %u10 = zext i8 %b10 to i32
  %u11 = zext i8 %b11 to i32
  %s0 = add nuw nsw i32 %u00, %u01
  %s1 = add nuw nsw i32 %u10, %u11
  %sum = add nuw nsw i32 %s0, %s1
  %rnd = add nuw nsw i32 %sum, 2
  %avg = lshr i32 %rnd, 2
  %cnt = sub nsw i32 %avg, 128
  %mulc = mul nsw i32 %cnt, %cQ8
  %rndc = add nsw i32 %mulc, 128
  %shrc = ashr i32 %rndc, 8
  %add128 = add nsw i32 %shrc, 128
  %scaled = add nsw i32 %add128, %brt
  %lt0 = icmp slt i32 %scaled, 0
  %gt255 = icmp sgt i32 %scaled, 255
  %cl0 = select i1 %lt0, i32 0, i32 %scaled
  %cl = select i1 %gt255, i32 255, i32 %cl0
  %out_b = trunc i32 %cl to i8
  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx
  store i8 %out_b, ptr %dst_ptr, align 1
  %dx_next = add nuw i64 %dx, 1
  %done_x = icmp eq i64 %dx_next, %dstW
  br i1 %done_x, label %outer.latch, label %inner.body, !llvm.loop !0
outer.latch:
  %dy_next = add nuw i64 %dy, 1
  %done_y = icmp eq i64 %dy_next, %dstH
  br i1 %done_y, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %cmp_h = icmp eq i64 %dstH, 0
  %cmp_w = icmp eq i64 %dstW, 0
  %empty = or i1 %cmp_h, %cmp_w
  br i1 %empty, label %exit, label %outer.ph
outer.ph:
  %vec_end = and i64 %dstW, -8
  %has_vec = icmp uge i64 %dstW, 8
  br label %outer.body
outer.body:
  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]
  %sy0 = mul nuw i64 %dy, 3
  %sy1 = add nuw i64 %sy0, 1
  %sy2 = add nuw i64 %sy0, 2
  %r0_off = mul nuw i64 %sy0, %srcW
  %r1_off = mul nuw i64 %sy1, %srcW
  %r2_off = mul nuw i64 %sy2, %srcW
  %dst_off = mul nuw i64 %dy, %dstW
  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off
  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off
  %r2_ptr = getelementptr inbounds i8, ptr %src, i64 %r2_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off
  br i1 %has_vec, label %vec.body, label %scalar.check
vec.body:
  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]
  %vsx0 = mul nuw i64 %vdx, 3
  %vsx1 = add nuw i64 %vsx0, 16
  %vp00 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx0
  %vp01 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx1
  %vp10 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx0
  %vp11 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx1
  %vp20 = getelementptr inbounds i8, ptr %r2_ptr, i64 %vsx0
  %vp21 = getelementptr inbounds i8, ptr %r2_ptr, i64 %vsx1
  %vr0_lo = load <16 x i8>, ptr %vp00, align 1
  %vr0_hi8 = load <8 x i8>, ptr %vp01, align 1
  %vr0_hi = shufflevector <8 x i8> %vr0_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>
  %vr1_lo = load <16 x i8>, ptr %vp10, align 1
  %vr1_hi8 = load <8 x i8>, ptr %vp11, align 1
  %vr1_hi = shufflevector <8 x i8> %vr1_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>
  %vr2_lo = load <16 x i8>, ptr %vp20, align 1
  %vr2_hi8 = load <8 x i8>, ptr %vp21, align 1
  %vr2_hi = shufflevector <8 x i8> %vr2_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>
  %r0_c0 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>
  %r0_c1 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>
  %r0_c2 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>
  %r1_c0 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>
  %r1_c1 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>
  %r1_c2 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>
  %r2_c0 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>
  %r2_c1 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>
  %r2_c2 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>
  %z00 = zext <8 x i8> %r0_c0 to <8 x i16>
  %z01 = zext <8 x i8> %r0_c1 to <8 x i16>
  %z02 = zext <8 x i8> %r0_c2 to <8 x i16>
  %z10 = zext <8 x i8> %r1_c0 to <8 x i16>
  %z11 = zext <8 x i8> %r1_c1 to <8 x i16>
  %z12 = zext <8 x i8> %r1_c2 to <8 x i16>
  %z20 = zext <8 x i8> %r2_c0 to <8 x i16>
  %z21 = zext <8 x i8> %r2_c1 to <8 x i16>
  %z22 = zext <8 x i8> %r2_c2 to <8 x i16>
  %s0a = add nuw nsw <8 x i16> %z00, %z01
  %s0 = add nuw nsw <8 x i16> %s0a, %z02
  %s1a = add nuw nsw <8 x i16> %z10, %z11
  %s1 = add nuw nsw <8 x i16> %s1a, %z12
  %s2a = add nuw nsw <8 x i16> %z20, %z21
  %s2 = add nuw nsw <8 x i16> %s2a, %z22
  %s01 = add nuw nsw <8 x i16> %s0, %s1
  %sum9 = add nuw nsw <8 x i16> %s01, %s2
  %sum32 = zext <8 x i16> %sum9 to <8 x i32>
  %rnd = add nuw nsw <8 x i32> %sum32, <i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4>
  %prod = mul nuw nsw <8 x i32> %rnd, <i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282>
  %avg = lshr <8 x i32> %prod, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>
  %vout = trunc <8 x i32> %avg to <8 x i8>
  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx
  store <8 x i8> %vout, ptr %vdst_p, align 1
  %vdx_next = add nuw i64 %vdx, 8
  %vdone = icmp eq i64 %vdx_next, %vec_end
  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6
scalar.check:
  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]
  %has_rem = icmp ult i64 %dx_start, %dstW
  br i1 %has_rem, label %inner.body, label %outer.latch
inner.body:
  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]
  %sx0 = mul nuw i64 %dx, 3
  %sx1 = add nuw i64 %sx0, 1
  %sx2 = add nuw i64 %sx0, 2
  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0
  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1
  %p02_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx2
  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0
  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1
  %p12_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx2
  %p20_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx0
  %p21_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx1
  %p22_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx2
  %b00 = load i8, ptr %p00_ptr, align 1
  %b01 = load i8, ptr %p01_ptr, align 1
  %b02 = load i8, ptr %p02_ptr, align 1
  %b10 = load i8, ptr %p10_ptr, align 1
  %b11 = load i8, ptr %p11_ptr, align 1
  %b12 = load i8, ptr %p12_ptr, align 1
  %b20 = load i8, ptr %p20_ptr, align 1
  %b21 = load i8, ptr %p21_ptr, align 1
  %b22 = load i8, ptr %p22_ptr, align 1
  %u00 = zext i8 %b00 to i32
  %u01 = zext i8 %b01 to i32
  %u02 = zext i8 %b02 to i32
  %u10 = zext i8 %b10 to i32
  %u11 = zext i8 %b11 to i32
  %u12 = zext i8 %b12 to i32
  %u20 = zext i8 %b20 to i32
  %u21 = zext i8 %b21 to i32
  %u22 = zext i8 %b22 to i32
  %sr0a = add nuw nsw i32 %u00, %u01
  %sr0 = add nuw nsw i32 %sr0a, %u02
  %sr1a = add nuw nsw i32 %u10, %u11
  %sr1 = add nuw nsw i32 %sr1a, %u12
  %sr2a = add nuw nsw i32 %u20, %u21
  %sr2 = add nuw nsw i32 %sr2a, %u22
  %sr01 = add nuw nsw i32 %sr0, %sr1
  %ssum9 = add nuw nsw i32 %sr01, %sr2
  %srnd = add nuw nsw i32 %ssum9, 4
  %sprod = mul nuw nsw i32 %srnd, 7282
  %savg = lshr i32 %sprod, 16
  %out_b = trunc i32 %savg to i8
  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx
  store i8 %out_b, ptr %dst_ptr, align 1
  %dx_next = add nuw i64 %dx, 1
  %done_x = icmp eq i64 %dx_next, %dstW
  br i1 %done_x, label %outer.latch, label %inner.body
outer.latch:
  %dy_next = add nuw i64 %dy, 1
  %done_y = icmp eq i64 %dy_next, %dstH
  br i1 %done_y, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_swscale_down3to2_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %cmp_h = icmp eq i64 %dstH, 0
  %cmp_w = icmp eq i64 %dstW, 0
  %empty = or i1 %cmp_h, %cmp_w
  br i1 %empty, label %exit, label %outer.ph
outer.ph:
  %vec_end = and i64 %dstW, -16
  %has_vec = icmp uge i64 %dstW, 16
  br label %outer.body
outer.body:
  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]
  %dy_half = lshr i64 %dy, 1
  %sy_base = mul nuw i64 %dy_half, 3
  %dy_odd = and i64 %dy, 1
  %is_odd_y = icmp ne i64 %dy_odd, 0
  %syA = add nuw i64 %sy_base, %dy_odd
  %syB = add nuw i64 %syA, 1
  %rA_off = mul nuw i64 %syA, %srcW
  %rB_off = mul nuw i64 %syB, %srcW
  %dst_off = mul nuw i64 %dy, %dstW
  %rA_ptr = getelementptr inbounds i8, ptr %src, i64 %rA_off
  %rB_ptr = getelementptr inbounds i8, ptr %src, i64 %rB_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off
  %vwA = select i1 %is_odd_y, <16 x i16> <i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1>, <16 x i16> <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>
  %vwB = select i1 %is_odd_y, <16 x i16> <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>, <16 x i16> <i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1>
  br i1 %has_vec, label %vec.body, label %scalar.check
vec.body:
  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]
  %vdx_half = lshr i64 %vdx, 1
  %vsx0 = mul nuw i64 %vdx_half, 3
  %vsx1 = add nuw i64 %vsx0, 16
  %vpA0 = getelementptr inbounds i8, ptr %rA_ptr, i64 %vsx0
  %vpA1 = getelementptr inbounds i8, ptr %rA_ptr, i64 %vsx1
  %vpB0 = getelementptr inbounds i8, ptr %rB_ptr, i64 %vsx0
  %vpB1 = getelementptr inbounds i8, ptr %rB_ptr, i64 %vsx1
  %vrA_lo = load <16 x i8>, ptr %vpA0, align 1
  %vrA_hi8 = load <8 x i8>, ptr %vpA1, align 1
  %vrA_hi = shufflevector <8 x i8> %vrA_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>
  %vrB_lo = load <16 x i8>, ptr %vpB0, align 1
  %vrB_hi8 = load <8 x i8>, ptr %vpB1, align 1
  %vrB_hi = shufflevector <8 x i8> %vrB_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>
  %rA_c0 = shufflevector <16 x i8> %vrA_lo, <16 x i8> %vrA_hi, <16 x i32> <i32 0, i32 1, i32 3, i32 4, i32 6, i32 7, i32 9, i32 10, i32 12, i32 13, i32 15, i32 16, i32 18, i32 19, i32 21, i32 22>
  %rA_c1 = shufflevector <16 x i8> %vrA_lo, <16 x i8> %vrA_hi, <16 x i32> <i32 1, i32 2, i32 4, i32 5, i32 7, i32 8, i32 10, i32 11, i32 13, i32 14, i32 16, i32 17, i32 19, i32 20, i32 22, i32 23>
  %rB_c0 = shufflevector <16 x i8> %vrB_lo, <16 x i8> %vrB_hi, <16 x i32> <i32 0, i32 1, i32 3, i32 4, i32 6, i32 7, i32 9, i32 10, i32 12, i32 13, i32 15, i32 16, i32 18, i32 19, i32 21, i32 22>
  %rB_c1 = shufflevector <16 x i8> %vrB_lo, <16 x i8> %vrB_hi, <16 x i32> <i32 1, i32 2, i32 4, i32 5, i32 7, i32 8, i32 10, i32 11, i32 13, i32 14, i32 16, i32 17, i32 19, i32 20, i32 22, i32 23>
  %zA0 = zext <16 x i8> %rA_c0 to <16 x i16>
  %zA1 = zext <16 x i8> %rA_c1 to <16 x i16>
  %zB0 = zext <16 x i8> %rB_c0 to <16 x i16>
  %zB1 = zext <16 x i8> %rB_c1 to <16 x i16>
  %mA0 = mul nuw nsw <16 x i16> %zA0, <i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1>
  %mA1 = mul nuw nsw <16 x i16> %zA1, <i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2>
  %rowA_h = add nuw nsw <16 x i16> %mA0, %mA1
  %mB0 = mul nuw nsw <16 x i16> %zB0, <i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1>
  %mB1 = mul nuw nsw <16 x i16> %zB1, <i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2>
  %rowB_h = add nuw nsw <16 x i16> %mB0, %mB1
  %wrowA = mul nuw nsw <16 x i16> %rowA_h, %vwA
  %wrowB = mul nuw nsw <16 x i16> %rowB_h, %vwB
  %sum9 = add nuw nsw <16 x i16> %wrowA, %wrowB
  %sum32 = zext <16 x i16> %sum9 to <16 x i32>
  %rnd = add nuw nsw <16 x i32> %sum32, <i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4>
  %prod = mul nuw nsw <16 x i32> %rnd, <i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282>
  %avg = lshr <16 x i32> %prod, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>
  %vout = trunc <16 x i32> %avg to <16 x i8>
  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx
  store <16 x i8> %vout, ptr %vdst_p, align 1
  %vdx_next = add nuw i64 %vdx, 16
  %vdone = icmp eq i64 %vdx_next, %vec_end
  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6
scalar.check:
  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]
  %has_rem = icmp ult i64 %dx_start, %dstW
  br i1 %has_rem, label %inner.body, label %outer.latch
inner.body:
  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]
  %dx_half = lshr i64 %dx, 1
  %sx_base = mul nuw i64 %dx_half, 3
  %dx_odd = and i64 %dx, 1
  %is_odd_x = icmp ne i64 %dx_odd, 0
  %sxA = add nuw i64 %sx_base, %dx_odd
  %sxB = add nuw i64 %sxA, 1
  %p00_ptr = getelementptr inbounds i8, ptr %rA_ptr, i64 %sxA
  %p01_ptr = getelementptr inbounds i8, ptr %rA_ptr, i64 %sxB
  %p10_ptr = getelementptr inbounds i8, ptr %rB_ptr, i64 %sxA
  %p11_ptr = getelementptr inbounds i8, ptr %rB_ptr, i64 %sxB
  %b00 = load i8, ptr %p00_ptr, align 1
  %b01 = load i8, ptr %p01_ptr, align 1
  %b10 = load i8, ptr %p10_ptr, align 1
  %b11 = load i8, ptr %p11_ptr, align 1
  %u00 = zext i8 %b00 to i32
  %u01 = zext i8 %b01 to i32
  %u10 = zext i8 %b10 to i32
  %u11 = zext i8 %b11 to i32
  %u00_2 = shl nuw nsw i32 %u00, 1
  %u01_2 = shl nuw nsw i32 %u01, 1
  %u10_2 = shl nuw nsw i32 %u10, 1
  %u11_2 = shl nuw nsw i32 %u11, 1
  %rA_even = add nuw nsw i32 %u00_2, %u01
  %rA_odd  = add nuw nsw i32 %u00, %u01_2
  %rB_even = add nuw nsw i32 %u10_2, %u11
  %rB_odd  = add nuw nsw i32 %u10, %u11_2
  %rowA_h_s = select i1 %is_odd_x, i32 %rA_odd, i32 %rA_even
  %rowB_h_s = select i1 %is_odd_x, i32 %rB_odd, i32 %rB_even
  %rowA_h_2 = shl nuw nsw i32 %rowA_h_s, 1
  %rowB_h_2 = shl nuw nsw i32 %rowB_h_s, 1
  %s_even_y = add nuw nsw i32 %rowA_h_2, %rowB_h_s
  %s_odd_y  = add nuw nsw i32 %rowA_h_s, %rowB_h_2
  %ssum9 = select i1 %is_odd_y, i32 %s_odd_y, i32 %s_even_y
  %srnd = add nuw nsw i32 %ssum9, 4
  %sprod = mul nuw nsw i32 %srnd, 7282
  %savg = lshr i32 %sprod, 16
  %out_b = trunc i32 %savg to i8
  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx
  store i8 %out_b, ptr %dst_ptr, align 1
  %dx_next = add nuw i64 %dx, 1
  %done_x = icmp eq i64 %dx_next, %dstW
  br i1 %done_x, label %outer.latch, label %inner.body
outer.latch:
  %dy_next = add nuw i64 %dy, 1
  %done_y = icmp eq i64 %dy_next, %dstH
  br i1 %done_y, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_av1_cdef_filter_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h, i64 noundef %priStr64, i64 noundef %damping64) #0 {
entry:
  %total = mul nuw i64 %w, %h
  %has_bytes = icmp ugt i64 %total, 0
  br i1 %has_bytes, label %copy.init, label %exit
copy.init:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)
  %w_lt3 = icmp ult i64 %w, 3
  %h_lt3 = icmp ult i64 %h, 3
  %pri32 = trunc i64 %priStr64 to i32
  %pri_le0 = icmp sle i32 %pri32, 0
  %skip0 = or i1 %w_lt3, %h_lt3
  %skip = or i1 %skip0, %pri_le0
  br i1 %skip, label %exit, label %outer.ph
outer.ph:
  %h_limit = sub nuw i64 %h, 1
  %w_limit = sub nuw i64 %w, 1
  %dmp32 = trunc i64 %damping64 to i32
  %dmp_pos = icmp ugt i32 %dmp32, 0
  %shift = select i1 %dmp_pos, i32 %dmp32, i32 1
  br label %outer.body
outer.body:
  %r = phi i64 [ 1, %outer.ph ], [ %r_next, %outer.latch ]
  %r_prev = sub nuw i64 %r, 1
  %r_next_row = add nuw i64 %r, 1
  %row_off = mul nuw i64 %r, %w
  %up_off  = mul nuw i64 %r_prev, %w
  %dn_off  = mul nuw i64 %r_next_row, %w
  %row_ptr = getelementptr inbounds i8, ptr %src, i64 %row_off
  %up_ptr  = getelementptr inbounds i8, ptr %src, i64 %up_off
  %dn_ptr  = getelementptr inbounds i8, ptr %src, i64 %dn_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %row_off
  br label %inner.body
inner.body:
  %c = phi i64 [ 1, %outer.body ], [ %c_next, %inner.body ]
  %c_prev = sub nuw i64 %c, 1
  %c_plus = add nuw i64 %c, 1
  %p_px = getelementptr inbounds i8, ptr %row_ptr, i64 %c
  %p_n0 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev
  %p_n1 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus
  %p_n2 = getelementptr inbounds i8, ptr %up_ptr, i64 %c
  %p_n3 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c
  %b_px = load i8, ptr %p_px, align 1
  %b_n0 = load i8, ptr %p_n0, align 1
  %b_n1 = load i8, ptr %p_n1, align 1
  %b_n2 = load i8, ptr %p_n2, align 1
  %b_n3 = load i8, ptr %p_n3, align 1
  %px = zext i8 %b_px to i32
  %n0 = zext i8 %b_n0 to i32
  %n1 = zext i8 %b_n1 to i32
  %n2 = zext i8 %b_n2 to i32
  %n3 = zext i8 %b_n3 to i32
  %d0 = sub nsw i32 %n0, %px
  %neg0 = icmp slt i32 %d0, 0
  %nd0 = sub nsw i32 0, %d0
  %ad0 = select i1 %neg0, i32 %nd0, i32 %d0
  %sh0 = ashr i32 %ad0, %shift
  %tm0 = sub nsw i32 %pri32, %sh0
  %t0_lt0 = icmp slt i32 %tm0, 0
  %ad0_lt = icmp slt i32 %ad0, %tm0
  %min0 = select i1 %ad0_lt, i32 %ad0, i32 %tm0
  %mag0 = select i1 %t0_lt0, i32 0, i32 %min0
  %nmag0 = sub nsw i32 0, %mag0
  %c0 = select i1 %neg0, i32 %nmag0, i32 %mag0
  %d1 = sub nsw i32 %n1, %px
  %neg1 = icmp slt i32 %d1, 0
  %nd1 = sub nsw i32 0, %d1
  %ad1 = select i1 %neg1, i32 %nd1, i32 %d1
  %sh1 = ashr i32 %ad1, %shift
  %tm1 = sub nsw i32 %pri32, %sh1
  %t1_lt0 = icmp slt i32 %tm1, 0
  %ad1_lt = icmp slt i32 %ad1, %tm1
  %min1 = select i1 %ad1_lt, i32 %ad1, i32 %tm1
  %mag1 = select i1 %t1_lt0, i32 0, i32 %min1
  %nmag1 = sub nsw i32 0, %mag1
  %c1 = select i1 %neg1, i32 %nmag1, i32 %mag1
  %d2 = sub nsw i32 %n2, %px
  %neg2 = icmp slt i32 %d2, 0
  %nd2 = sub nsw i32 0, %d2
  %ad2 = select i1 %neg2, i32 %nd2, i32 %d2
  %sh2 = ashr i32 %ad2, %shift
  %tm2 = sub nsw i32 %pri32, %sh2
  %t2_lt0 = icmp slt i32 %tm2, 0
  %ad2_lt = icmp slt i32 %ad2, %tm2
  %min2 = select i1 %ad2_lt, i32 %ad2, i32 %tm2
  %mag2 = select i1 %t2_lt0, i32 0, i32 %min2
  %nmag2 = sub nsw i32 0, %mag2
  %c2 = select i1 %neg2, i32 %nmag2, i32 %mag2
  %d3 = sub nsw i32 %n3, %px
  %neg3 = icmp slt i32 %d3, 0
  %nd3 = sub nsw i32 0, %d3
  %ad3 = select i1 %neg3, i32 %nd3, i32 %d3
  %sh3 = ashr i32 %ad3, %shift
  %tm3 = sub nsw i32 %pri32, %sh3
  %t3_lt0 = icmp slt i32 %tm3, 0
  %ad3_lt = icmp slt i32 %ad3, %tm3
  %min3 = select i1 %ad3_lt, i32 %ad3, i32 %tm3
  %mag3 = select i1 %t3_lt0, i32 0, i32 %min3
  %nmag3 = sub nsw i32 0, %mag3
  %c3 = select i1 %neg3, i32 %nmag3, i32 %mag3
  %s01 = add nsw i32 %c0, %c1
  %s23 = add nsw i32 %c2, %c3
  %sum = add nsw i32 %s01, %s23
  %srnd = add nsw i32 %sum, 2
  %sdiv = ashr i32 %srnd, 2
  %out_raw = add nsw i32 %px, %sdiv
  %lt0 = icmp slt i32 %out_raw, 0
  %gt255 = icmp sgt i32 %out_raw, 255
  %cl0 = select i1 %lt0, i32 0, i32 %out_raw
  %cl = select i1 %gt255, i32 255, i32 %cl0
  %out_b = trunc i32 %cl to i8
  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %c
  store i8 %out_b, ptr %dst_p, align 1
  %c_next = add nuw nsw i64 %c, 1
  %done_c = icmp eq i64 %c_next, %w_limit
  br i1 %done_c, label %outer.latch, label %inner.body, !llvm.loop !0
outer.latch:
  %r_next = add nuw nsw i64 %r, 1
  %done_r = icmp eq i64 %r_next, %h_limit
  br i1 %done_r, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local void @lean_native_stencil2d_box3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h) #0 {
entry:
  %total = mul nuw i64 %w, %h
  %has_bytes = icmp ugt i64 %total, 0
  br i1 %has_bytes, label %copy.init, label %exit
copy.init:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)
  %w_lt3 = icmp ult i64 %w, 3
  %h_lt3 = icmp ult i64 %h, 3
  %skip = or i1 %w_lt3, %h_lt3
  br i1 %skip, label %exit, label %outer.ph
outer.ph:
  %h_limit = sub nuw i64 %h, 1
  %w_limit = sub nuw i64 %w, 1
  br label %outer.body
outer.body:
  %r = phi i64 [ 1, %outer.ph ], [ %r_next, %outer.latch ]
  %r_prev = sub nuw i64 %r, 1
  %r_next_row = add nuw i64 %r, 1
  %up_off  = mul nuw i64 %r_prev, %w
  %row_off = mul nuw i64 %r, %w
  %dn_off  = mul nuw i64 %r_next_row, %w
  %up_ptr  = getelementptr inbounds i8, ptr %src, i64 %up_off
  %row_ptr = getelementptr inbounds i8, ptr %src, i64 %row_off
  %dn_ptr  = getelementptr inbounds i8, ptr %src, i64 %dn_off
  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %row_off
  br label %inner.body
inner.body:
  %c = phi i64 [ 1, %outer.body ], [ %c_next, %inner.body ]
  %c_prev = sub nuw i64 %c, 1
  %c_plus = add nuw i64 %c, 1
  %p00 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_prev
  %p01 = getelementptr inbounds i8, ptr %up_ptr, i64 %c
  %p02 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_plus
  %p10 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev
  %p11 = getelementptr inbounds i8, ptr %row_ptr, i64 %c
  %p12 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus
  %p20 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c_prev
  %p21 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c
  %p22 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c_plus
  %b00 = load i8, ptr %p00, align 1
  %b01 = load i8, ptr %p01, align 1
  %b02 = load i8, ptr %p02, align 1
  %b10 = load i8, ptr %p10, align 1
  %b11 = load i8, ptr %p11, align 1
  %b12 = load i8, ptr %p12, align 1
  %b20 = load i8, ptr %p20, align 1
  %b21 = load i8, ptr %p21, align 1
  %b22 = load i8, ptr %p22, align 1
  %u00 = zext i8 %b00 to i32
  %u01 = zext i8 %b01 to i32
  %u02 = zext i8 %b02 to i32
  %u10 = zext i8 %b10 to i32
  %u11 = zext i8 %b11 to i32
  %u12 = zext i8 %b12 to i32
  %u20 = zext i8 %b20 to i32
  %u21 = zext i8 %b21 to i32
  %u22 = zext i8 %b22 to i32
  %s0 = add nuw nsw i32 %u00, %u01
  %s1 = add nuw nsw i32 %s0, %u02
  %s2 = add nuw nsw i32 %s1, %u10
  %s3 = add nuw nsw i32 %s2, %u11
  %s4 = add nuw nsw i32 %s3, %u12
  %s5 = add nuw nsw i32 %s4, %u20
  %s6 = add nuw nsw i32 %s5, %u21
  %sum9 = add nuw nsw i32 %s6, %u22
  %rnd = add nuw nsw i32 %sum9, 4
  %prod = mul nuw nsw i32 %rnd, 7282
  %avg = lshr i32 %prod, 16
  %out_b = trunc i32 %avg to i8
  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %c
  store i8 %out_b, ptr %dst_p, align 1
  %c_next = add nuw nsw i64 %c, 1
  %done_c = icmp eq i64 %c_next, %w_limit
  br i1 %done_c, label %outer.latch, label %inner.body, !llvm.loop !0
outer.latch:
  %r_next = add nuw nsw i64 %r, 1
  %done_r = icmp eq i64 %r_next, %h_limit
  br i1 %done_r, label %exit, label %outer.body
exit:
  ret void
}

define weak_odr dso_local i64 @lean_native_luma_stats_u8(ptr noalias noundef readonly %src, i64 noundef %nPixels, i64 noundef %step) #0 {
entry:
  %has_px = icmp ugt i64 %nPixels, 0
  %step_pos = icmp ugt i64 %step, 0
  %ok = and i1 %has_px, %step_pos
  br i1 %ok, label %loop.body, label %exit.zero
loop.body:
  %idx = phi i64 [ 0, %entry ], [ %idx_next, %loop.body ]
  %sum = phi i64 [ 0, %entry ], [ %sum_next, %loop.body ]
  %sumSq = phi i64 [ 0, %entry ], [ %sumSq_next, %loop.body ]
  %cnt = phi i64 [ 0, %entry ], [ %cnt_next, %loop.body ]
  %p = getelementptr inbounds i8, ptr %src, i64 %idx
  %b = load i8, ptr %p, align 1
  %v = zext i8 %b to i64
  %v2 = mul nuw i64 %v, %v
  %sum_next = add nuw i64 %sum, %v
  %sumSq_next = add nuw i64 %sumSq, %v2
  %cnt_next = add nuw i64 %cnt, 1
  %idx_next = add nuw i64 %idx, %step
  %more = icmp ult i64 %idx_next, %nPixels
  br i1 %more, label %loop.body, label %compute.out, !llvm.loop !0
compute.out:
  %mean = udiv i64 %sum_next, %cnt_next
  %meanSq = udiv i64 %sumSq_next, %cnt_next
  %sq = mul nuw i64 %mean, %mean
  %gt = icmp ugt i64 %meanSq, %sq
  %diff = sub nuw i64 %meanSq, %sq
  %var = select i1 %gt, i64 %diff, i64 0
  %var_hi = shl i64 %var, 32
  %mean_lo = and i64 %mean, 4294967295
  %packed = or i64 %var_hi, %mean_lo
  ret i64 %packed
exit.zero:
  ret i64 0
}

define weak_odr dso_local void @lean_native_swscale_bilinear_q8_u8(ptr noalias noundef %dst, ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH) #0 {
entry:
  %sx0_tab = alloca [4096 x i64], align 16
  %sx1_tab = alloca [4096 x i64], align 16
  %fx_tab = alloca [4096 x i32], align 16
  %sw0 = icmp eq i64 %srcW, 0
  %sh0 = icmp eq i64 %srcH, 0
  %dw0 = icmp eq i64 %dstW, 0
  %dh0 = icmp eq i64 %dstH, 0
  %s0 = or i1 %sw0, %sh0
  %d0 = or i1 %dw0, %dh0
  %empty = or i1 %s0, %d0
  %lastX = sub i64 %srcW, 1
  %lastY = sub i64 %srcH, 1
  %scaleX = shl i64 %srcW, 8
  %scaleY = shl i64 %srcH, 8
  %use_tab = icmp ule i64 %dstW, 4096
  br i1 %empty, label %exit, label %check.tab
check.tab:
  br i1 %use_tab, label %init.xtab, label %row
init.xtab:
  %tx = phi i64 [ 0, %check.tab ], [ %tx_next, %init.xtab ]
  %tnx = mul i64 %tx, %scaleX
  %tqx = udiv i64 %tnx, %dstW
  %trawX = lshr i64 %tqx, 8
  %txIn = icmp ult i64 %trawX, %srcW
  %tsx0 = select i1 %txIn, i64 %trawX, i64 %lastX
  %txPlus = add i64 %tsx0, 1
  %txNextIn = icmp ult i64 %txPlus, %srcW
  %tsx1 = select i1 %txNextIn, i64 %txPlus, i64 %tsx0
  %tfx64 = and i64 %tqx, 255
  %tfx = trunc i64 %tfx64 to i32
  %tsx0p = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %tx
  store i64 %tsx0, ptr %tsx0p, align 8
  %tsx1p = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %tx
  store i64 %tsx1, ptr %tsx1p, align 8
  %tfxp = getelementptr inbounds [4096 x i32], ptr %fx_tab, i64 0, i64 %tx
  store i32 %tfx, ptr %tfxp, align 4
  %tx_next = add nuw i64 %tx, 1
  %tdone = icmp eq i64 %tx_next, %dstW
  br i1 %tdone, label %row, label %init.xtab
row:
  %dy = phi i64 [ 0, %check.tab ], [ 0, %init.xtab ], [ %nextY, %rowEnd ]
  %ny = mul i64 %dy, %scaleY
  %qy = udiv i64 %ny, %dstH
  %rawY = lshr i64 %qy, 8
  %yIn = icmp ult i64 %rawY, %srcH
  %sy0 = select i1 %yIn, i64 %rawY, i64 %lastY
  %yPlus = add i64 %sy0, 1
  %yNextIn = icmp ult i64 %yPlus, %srcH
  %sy1 = select i1 %yNextIn, i64 %yPlus, i64 %sy0
  %fy64 = and i64 %qy, 255
  %fy = trunc i64 %fy64 to i32
  %ify = sub i32 256, %fy
  %r0 = mul i64 %sy0, %srcStride
  %r1 = mul i64 %sy1, %srcStride
  %dr = mul i64 %dy, %dstW
  %fy_seed = insertelement <4 x i32> poison, i32 %fy, i64 0
  %fy4 = shufflevector <4 x i32> %fy_seed, <4 x i32> poison, <4 x i32> zeroinitializer
  %ify_seed = insertelement <4 x i32> poison, i32 %ify, i64 0
  %ify4 = shufflevector <4 x i32> %ify_seed, <4 x i32> poison, <4 x i32> zeroinitializer
  br i1 %use_tab, label %vec.check, label %col
vec.check:
  %dx4 = phi i64 [ 0, %row ], [ %next4, %vec.body ]
  %next4 = add nuw i64 %dx4, 4
  %fits4 = icmp ule i64 %next4, %dstW
  br i1 %fits4, label %vec.body, label %tail.check
vec.body:
  %fxp4 = getelementptr inbounds [4096 x i32], ptr %fx_tab, i64 0, i64 %dx4
  %fx4 = load <4 x i32>, ptr %fxp4, align 16
  %ifx4 = sub <4 x i32> <i32 256, i32 256, i32 256, i32 256>, %fx4
  %vx0 = add i64 %dx4, 0
  %vsx0p0 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx0
  %vsx0_0 = load i64, ptr %vsx0p0, align 8
  %vsx1p0 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx0
  %vsx1_0 = load i64, ptr %vsx1p0, align 8
  %vi00_0 = add i64 %r0, %vsx0_0
  %va00_0 = getelementptr i8, ptr %src, i64 %vi00_0
  %vb00_0 = load i8, ptr %va00_0, align 1
  %vp00_0 = zext i8 %vb00_0 to i32
  %v00_0 = insertelement <4 x i32> poison, i32 %vp00_0, i64 0
  %vi01_0 = add i64 %r0, %vsx1_0
  %va01_0 = getelementptr i8, ptr %src, i64 %vi01_0
  %vb01_0 = load i8, ptr %va01_0, align 1
  %vp01_0 = zext i8 %vb01_0 to i32
  %v01_0 = insertelement <4 x i32> poison, i32 %vp01_0, i64 0
  %vi10_0 = add i64 %r1, %vsx0_0
  %va10_0 = getelementptr i8, ptr %src, i64 %vi10_0
  %vb10_0 = load i8, ptr %va10_0, align 1
  %vp10_0 = zext i8 %vb10_0 to i32
  %v10_0 = insertelement <4 x i32> poison, i32 %vp10_0, i64 0
  %vi11_0 = add i64 %r1, %vsx1_0
  %va11_0 = getelementptr i8, ptr %src, i64 %vi11_0
  %vb11_0 = load i8, ptr %va11_0, align 1
  %vp11_0 = zext i8 %vb11_0 to i32
  %v11_0 = insertelement <4 x i32> poison, i32 %vp11_0, i64 0
  %vx1 = add i64 %dx4, 1
  %vsx0p1 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx1
  %vsx0_1 = load i64, ptr %vsx0p1, align 8
  %vsx1p1 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx1
  %vsx1_1 = load i64, ptr %vsx1p1, align 8
  %vi00_1 = add i64 %r0, %vsx0_1
  %va00_1 = getelementptr i8, ptr %src, i64 %vi00_1
  %vb00_1 = load i8, ptr %va00_1, align 1
  %vp00_1 = zext i8 %vb00_1 to i32
  %v00_1 = insertelement <4 x i32> %v00_0, i32 %vp00_1, i64 1
  %vi01_1 = add i64 %r0, %vsx1_1
  %va01_1 = getelementptr i8, ptr %src, i64 %vi01_1
  %vb01_1 = load i8, ptr %va01_1, align 1
  %vp01_1 = zext i8 %vb01_1 to i32
  %v01_1 = insertelement <4 x i32> %v01_0, i32 %vp01_1, i64 1
  %vi10_1 = add i64 %r1, %vsx0_1
  %va10_1 = getelementptr i8, ptr %src, i64 %vi10_1
  %vb10_1 = load i8, ptr %va10_1, align 1
  %vp10_1 = zext i8 %vb10_1 to i32
  %v10_1 = insertelement <4 x i32> %v10_0, i32 %vp10_1, i64 1
  %vi11_1 = add i64 %r1, %vsx1_1
  %va11_1 = getelementptr i8, ptr %src, i64 %vi11_1
  %vb11_1 = load i8, ptr %va11_1, align 1
  %vp11_1 = zext i8 %vb11_1 to i32
  %v11_1 = insertelement <4 x i32> %v11_0, i32 %vp11_1, i64 1
  %vx2 = add i64 %dx4, 2
  %vsx0p2 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx2
  %vsx0_2 = load i64, ptr %vsx0p2, align 8
  %vsx1p2 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx2
  %vsx1_2 = load i64, ptr %vsx1p2, align 8
  %vi00_2 = add i64 %r0, %vsx0_2
  %va00_2 = getelementptr i8, ptr %src, i64 %vi00_2
  %vb00_2 = load i8, ptr %va00_2, align 1
  %vp00_2 = zext i8 %vb00_2 to i32
  %v00_2 = insertelement <4 x i32> %v00_1, i32 %vp00_2, i64 2
  %vi01_2 = add i64 %r0, %vsx1_2
  %va01_2 = getelementptr i8, ptr %src, i64 %vi01_2
  %vb01_2 = load i8, ptr %va01_2, align 1
  %vp01_2 = zext i8 %vb01_2 to i32
  %v01_2 = insertelement <4 x i32> %v01_1, i32 %vp01_2, i64 2
  %vi10_2 = add i64 %r1, %vsx0_2
  %va10_2 = getelementptr i8, ptr %src, i64 %vi10_2
  %vb10_2 = load i8, ptr %va10_2, align 1
  %vp10_2 = zext i8 %vb10_2 to i32
  %v10_2 = insertelement <4 x i32> %v10_1, i32 %vp10_2, i64 2
  %vi11_2 = add i64 %r1, %vsx1_2
  %va11_2 = getelementptr i8, ptr %src, i64 %vi11_2
  %vb11_2 = load i8, ptr %va11_2, align 1
  %vp11_2 = zext i8 %vb11_2 to i32
  %v11_2 = insertelement <4 x i32> %v11_1, i32 %vp11_2, i64 2
  %vx3 = add i64 %dx4, 3
  %vsx0p3 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx3
  %vsx0_3 = load i64, ptr %vsx0p3, align 8
  %vsx1p3 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx3
  %vsx1_3 = load i64, ptr %vsx1p3, align 8
  %vi00_3 = add i64 %r0, %vsx0_3
  %va00_3 = getelementptr i8, ptr %src, i64 %vi00_3
  %vb00_3 = load i8, ptr %va00_3, align 1
  %vp00_3 = zext i8 %vb00_3 to i32
  %v00_3 = insertelement <4 x i32> %v00_2, i32 %vp00_3, i64 3
  %vi01_3 = add i64 %r0, %vsx1_3
  %va01_3 = getelementptr i8, ptr %src, i64 %vi01_3
  %vb01_3 = load i8, ptr %va01_3, align 1
  %vp01_3 = zext i8 %vb01_3 to i32
  %v01_3 = insertelement <4 x i32> %v01_2, i32 %vp01_3, i64 3
  %vi10_3 = add i64 %r1, %vsx0_3
  %va10_3 = getelementptr i8, ptr %src, i64 %vi10_3
  %vb10_3 = load i8, ptr %va10_3, align 1
  %vp10_3 = zext i8 %vb10_3 to i32
  %v10_3 = insertelement <4 x i32> %v10_2, i32 %vp10_3, i64 3
  %vi11_3 = add i64 %r1, %vsx1_3
  %va11_3 = getelementptr i8, ptr %src, i64 %vi11_3
  %vb11_3 = load i8, ptr %va11_3, align 1
  %vp11_3 = zext i8 %vb11_3 to i32
  %v11_3 = insertelement <4 x i32> %v11_2, i32 %vp11_3, i64 3
  %w004 = mul <4 x i32> %ifx4, %v00_3
  %w014 = mul <4 x i32> %fx4, %v01_3
  %w104 = mul <4 x i32> %ifx4, %v10_3
  %w114 = mul <4 x i32> %fx4, %v11_3
  %top4 = add <4 x i32> %w004, %w014
  %bot4 = add <4 x i32> %w104, %w114
  %wt4 = mul <4 x i32> %ify4, %top4
  %wb4 = mul <4 x i32> %fy4, %bot4
  %sum4 = add <4 x i32> %wt4, %wb4
  %rounded4 = add <4 x i32> %sum4, <i32 32768, i32 32768, i32 32768, i32 32768>
  %res4 = lshr <4 x i32> %rounded4, <i32 16, i32 16, i32 16, i32 16>
  %bytes4 = trunc <4 x i32> %res4 to <4 x i8>
  %di4 = add i64 %dr, %dx4
  %dp4 = getelementptr i8, ptr %dst, i64 %di4
  store <4 x i8> %bytes4, ptr %dp4, align 1
  br label %vec.check
tail.check:
  %has_tail = icmp ult i64 %dx4, %dstW
  br i1 %has_tail, label %col, label %rowEnd
col:
  %dx = phi i64 [ 0, %row ], [ %dx4, %tail.check ], [ %nextX, %col.compute ]
  br i1 %use_tab, label %col.from_tab, label %col.from_div
col.from_tab:
  %sx0p = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %dx
  %sx0_t = load i64, ptr %sx0p, align 8
  %sx1p = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %dx
  %sx1_t = load i64, ptr %sx1p, align 8
  %fxp = getelementptr inbounds [4096 x i32], ptr %fx_tab, i64 0, i64 %dx
  %fx_t = load i32, ptr %fxp, align 4
  br label %col.compute
col.from_div:
  %nx = mul i64 %dx, %scaleX
  %qx_d = udiv i64 %nx, %dstW
  %drawX = lshr i64 %qx_d, 8
  %dxIn = icmp ult i64 %drawX, %srcW
  %dsx0 = select i1 %dxIn, i64 %drawX, i64 %lastX
  %dxPlus = add i64 %dsx0, 1
  %dxNextIn = icmp ult i64 %dxPlus, %srcW
  %dsx1 = select i1 %dxNextIn, i64 %dxPlus, i64 %dsx0
  %dfx64 = and i64 %qx_d, 255
  %dfx = trunc i64 %dfx64 to i32
  br label %col.compute
col.compute:
  %sx0 = phi i64 [ %sx0_t, %col.from_tab ], [ %dsx0, %col.from_div ]
  %sx1 = phi i64 [ %sx1_t, %col.from_tab ], [ %dsx1, %col.from_div ]
  %fx = phi i32 [ %fx_t, %col.from_tab ], [ %dfx, %col.from_div ]
  %ifx = sub i32 256, %fx
  %i00 = add i64 %r0, %sx0
  %a00 = getelementptr i8, ptr %src, i64 %i00
  %b00 = load i8, ptr %a00, align 1
  %p00 = zext i8 %b00 to i32
  %w00 = mul i32 %p00, %ifx
  %i01 = add i64 %r0, %sx1
  %a01 = getelementptr i8, ptr %src, i64 %i01
  %b01 = load i8, ptr %a01, align 1
  %p01 = zext i8 %b01 to i32
  %w01 = mul i32 %p01, %fx
  %i10 = add i64 %r1, %sx0
  %a10 = getelementptr i8, ptr %src, i64 %i10
  %b10 = load i8, ptr %a10, align 1
  %p10 = zext i8 %b10 to i32
  %w10 = mul i32 %p10, %ifx
  %i11 = add i64 %r1, %sx1
  %a11 = getelementptr i8, ptr %src, i64 %i11
  %b11 = load i8, ptr %a11, align 1
  %p11 = zext i8 %b11 to i32
  %w11 = mul i32 %p11, %fx
  %top = add i32 %w00, %w01
  %bot = add i32 %w10, %w11
  %wt = mul i32 %top, %ify
  %wb = mul i32 %bot, %fy
  %sum = add i32 %wt, %wb
  %rounded = add i32 %sum, 32768
  %value = lshr i32 %rounded, 16
  %byte = trunc i32 %value to i8
  %di = add i64 %dr, %dx
  %dp = getelementptr i8, ptr %dst, i64 %di
  store i8 %byte, ptr %dp, align 1
  %nextX = add i64 %dx, 1
  %moreX = icmp ult i64 %nextX, %dstW
  br i1 %moreX, label %col, label %rowEnd, !llvm.loop !0
rowEnd:
  %nextY = add i64 %dy, 1
  %moreY = icmp ult i64 %nextY, %dstH
  br i1 %moreY, label %row, label %exit
exit:
  ret void
}

declare i32 @llvm.vector.reduce.add.v16i32(<16 x i32>)
define weak_odr dso_local void @lean_native_luma_acceptance_16x16_u8(ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, ptr noalias noundef readonly %dst, i64 noundef %dstW, i64 noundef %dstH, ptr noalias noundef writeonly %outMetrics4) #0 {
entry:
  store i64 0, ptr %outMetrics4, align 8
  %o1 = getelementptr i64, ptr %outMetrics4, i64 1
  %o2 = getelementptr i64, ptr %outMetrics4, i64 2
  %o3 = getelementptr i64, ptr %outMetrics4, i64 3
  store i64 0, ptr %o1, align 8
  store i64 0, ptr %o2, align 8
  store i64 1, ptr %o3, align 8
  %wok = icmp uge i64 %dstW, 16
  %hok = icmp uge i64 %dstH, 16
  %ok = and i1 %wok, %hok
  %one = icmp eq i64 %srcW, %dstW
  %wide = icmp uge i64 %dstW, 256
  %tall = icmp uge i64 %dstH, 256
  %sx = select i1 %wide, i64 64, i64 16
  %sy = select i1 %tall, i64 64, i64 16
  %xlim = sub i64 %dstW, 16
  %ylim = sub i64 %dstH, 16
  br i1 %ok, label %by, label %exit
by:
  %byi = phi i64 [ 0, %entry ], [ %byn, %nexty ]
  %oldmaxy = phi i64 [ 0, %entry ], [ %newmax, %nexty ]
  %oldsqy = phi i64 [ 0, %entry ], [ %newsq, %nexty ]
  %oldpixy = phi i64 [ 0, %entry ], [ %newpix, %nexty ]
  %oldoky = phi i64 [ 1, %entry ], [ %newok, %nexty ]
  br label %bx
bx:
  %bxi = phi i64 [ 0, %by ], [ %bxn, %blockend ]
  %oldmax = phi i64 [ %oldmaxy, %by ], [ %newmax, %blockend ]
  %oldsq = phi i64 [ %oldsqy, %by ], [ %newsq, %blockend ]
  %oldpix = phi i64 [ %oldpixy, %by ], [ %newpix, %blockend ]
  %oldok = phi i64 [ %oldoky, %by ], [ %newok, %blockend ]
  br label %row
row:
  %y = phi i64 [ 0, %bx ], [ %yn, %reduce ]
  %sad = phi i32 [ 0, %bx ], [ %sadn, %reduce ]
  %black = phi i32 [ 0, %bx ], [ %blackn, %reduce ]
  %refsum = phi i32 [ 0, %bx ], [ %refn, %reduce ]
  %sse = phi i32 [ 0, %bx ], [ %ssen, %reduce ]
  %dy = add i64 %byi, %y
  %dr = mul i64 %dy, %dstW
  %di = add i64 %dr, %bxi
  %dp = getelementptr i8, ptr %dst, i64 %di
  %db = load <16 x i8>, ptr %dp, align 1
  %d = zext <16 x i8> %db to <16 x i32>
  br i1 %one, label %same, label %half
same:
  %sp = getelementptr i8, ptr %src, i64 %di
  %sb = load <16 x i8>, ptr %sp, align 1
  %r1 = zext <16 x i8> %sb to <16 x i32>
  br label %reduce
half:
  %sr = mul i64 %dy, %srcW
  %si0 = add i64 %sr, %bxi
  %si = shl i64 %si0, 1
  %si1 = add i64 %si, %srcW
  %p0 = getelementptr i8, ptr %src, i64 %si
  %p1 = getelementptr i8, ptr %src, i64 %si1
  %a = load <32 x i8>, ptr %p0, align 1
  %b = load <32 x i8>, ptr %p1, align 1
  %ae8 = shufflevector <32 x i8> %a, <32 x i8> poison, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %ae = zext <16 x i8> %ae8 to <16 x i32>
  %ao8 = shufflevector <32 x i8> %a, <32 x i8> poison, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %ao = zext <16 x i8> %ao8 to <16 x i32>
  %be8 = shufflevector <32 x i8> %b, <32 x i8> poison, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %be = zext <16 x i8> %be8 to <16 x i32>
  %bo8 = shufflevector <32 x i8> %b, <32 x i8> poison, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %bo = zext <16 x i8> %bo8 to <16 x i32>
  %ab = add <16 x i32> %ae, %ao
  %bb = add <16 x i32> %be, %bo
  %sum = add <16 x i32> %ab, %bb
  %rounded = add <16 x i32> %sum, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %r2 = lshr <16 x i32> %rounded, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  br label %reduce
reduce:
  %r = phi <16 x i32> [ %r1, %same ], [ %r2, %half ]
  %dge = icmp uge <16 x i32> %d, %r
  %drd = sub <16 x i32> %d, %r
  %rdd = sub <16 x i32> %r, %d
  %ad = select <16 x i1> %dge, <16 x i32> %drd, <16 x i32> %rdd
  %rge = icmp uge <16 x i32> %r, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>
  %r16 = sub <16 x i32> %r, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>
  %b16 = sub <16 x i32> <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>, %r
  %bd = select <16 x i1> %rge, <16 x i32> %r16, <16 x i32> %b16
  %sq = mul <16 x i32> %ad, %ad
  %rsad = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %ad)
  %rblack = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %bd)
  %rref = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %r)
  %rsse = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %sq)
  %sadn = add i32 %sad, %rsad
  %blackn = add i32 %black, %rblack
  %refn = add i32 %refsum, %rref
  %ssen = add i32 %sse, %rsse
  %yn = add i64 %y, 1
  %rowdone = icmp eq i64 %yn, 16
  br i1 %rowdone, label %blockend, label %row
blockend:
  %sad64 = zext i32 %sadn to i64
  %sq64 = zext i32 %ssen to i64
  %larger = icmp ugt i64 %sad64, %oldmax
  %newmax = select i1 %larger, i64 %sad64, i64 %oldmax
  store i64 %newmax, ptr %outMetrics4, align 8
  %newsq = add i64 %oldsq, %sq64
  store i64 %newsq, ptr %o1, align 8
  %newpix = add i64 %oldpix, 256
  store i64 %newpix, ptr %o2, align 8
  %bright = icmp uge i32 %refn, 6144
  %worse = icmp uge i32 %sadn, %blackn
  %bad = and i1 %bright, %worse
  %newok = select i1 %bad, i64 0, i64 %oldok
  store i64 %newok, ptr %o3, align 8
  %bxn = add i64 %bxi, %sx
  %morex = icmp ule i64 %bxn, %xlim
  br i1 %morex, label %bx, label %nexty
nexty:
  %byn = add i64 %byi, %sy
  %morey = icmp ule i64 %byn, %ylim
  br i1 %morey, label %by, label %exit
exit:
  ret void
}

; LNIRDecl: swscale_luma_gain_bias_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.singleThreaded, isaMask=1)
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

; LNIRDecl: flac_lpc_autocorr_dot_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
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

; LNIRDecl: av1_wiener_3tap_sym_gpu (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
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

; LNIRDecl: h264_idct_tuple_accum_sroa (assurance=VerifiedKernelProof, isGpuCand=false, rcMode=LeanNative.IR.RcMode.freestanding, isaMask=1)
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

; LNIRDecl: swscale_down3to2_bilinear_simd (assurance=VerifiedKernelProof, isGpuCand=true, rcMode=LeanNative.IR.RcMode.atomic, isaMask=257)
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

attributes #0 = { nounwind uwtable "target-cpu"="x86-64-v2" }
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

; Packed Y/U/V filter: source and destination may alias exactly.
declare <16 x i8> @llvm.umax.v16i8(<16 x i8>, <16 x i8>)
declare <16 x i8> @llvm.umin.v16i8(<16 x i8>, <16 x i8>)
define weak_odr dso_local void @lean_native_apply_filters_yuv420p_u8(ptr %src, ptr %dst, i64 %y_len, i64 %uv_len, i64 %flags) #0 {
entry:
  %yf = and i64 %flags, 2
  %cf = and i64 %flags, 1
  %tonemap = icmp ne i64 %yf, 0
  %csc = icmp ne i64 %cf, 0
  %yvlen = and i64 %y_len, -16
  %cvlen = and i64 %uv_len, -16
  %su = getelementptr i8, ptr %src, i64 %y_len
  %sv = getelementptr i8, ptr %su, i64 %uv_len
  %du = getelementptr i8, ptr %dst, i64 %y_len
  %dv = getelementptr i8, ptr %du, i64 %uv_len
  br label %yvcheck
yvcheck:
  %yi = phi i64 [ 0, %entry ], [ %yn, %yvbody ]
  %yvmore = icmp ult i64 %yi, %yvlen
  br i1 %yvmore, label %yvbody, label %yscheck
yvbody:
  %ysp = getelementptr i8, ptr %src, i64 %yi
  %ydp = getelementptr i8, ptr %dst, i64 %yi
  %yb = load <16 x i8>, ptr %ysp, align 1
  %ylo = call <16 x i8> @llvm.umax.v16i8(<16 x i8> %yb, <16 x i8> <i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16, i8 16>)
  %yhi = call <16 x i8> @llvm.umin.v16i8(<16 x i8> %ylo, <16 x i8> <i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235, i8 235>)
  %yo = select i1 %tonemap, <16 x i8> %yhi, <16 x i8> %yb
  store <16 x i8> %yo, ptr %ydp, align 1
  %yn = add i64 %yi, 16
  br label %yvcheck
yscheck:
  %ysi = phi i64 [ %yi, %yvcheck ], [ %ysn, %ysbody ]
  %ysmore = icmp ult i64 %ysi, %y_len
  br i1 %ysmore, label %ysbody, label %cvcheck
ysbody:
  %yssp = getelementptr i8, ptr %src, i64 %ysi
  %ysdp = getelementptr i8, ptr %dst, i64 %ysi
  %ysb = load i8, ptr %yssp, align 1
  %yslow = icmp ult i8 %ysb, 16
  %yslo = select i1 %yslow, i8 16, i8 %ysb
  %yshigh = icmp ugt i8 %yslo, 235
  %yshi = select i1 %yshigh, i8 235, i8 %yslo
  %yso = select i1 %tonemap, i8 %yshi, i8 %ysb
  store i8 %yso, ptr %ysdp, align 1
  %ysn = add i64 %ysi, 1
  br label %yscheck
cvcheck:
  %cvi = phi i64 [ 0, %yscheck ], [ %cvn, %cvbody ]
  %cvmore = icmp ult i64 %cvi, %cvlen
  br i1 %cvmore, label %cvbody, label %cscheck
cvbody:
  %cvusp = getelementptr i8, ptr %su, i64 %cvi
  %cvudp = getelementptr i8, ptr %du, i64 %cvi
  %cvub = load <16 x i8>, ptr %cvusp, align 1
  %cvuz = zext <16 x i8> %cvub to <16 x i32>
  %cvu0 = sub <16 x i32> %cvuz, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %cvvsp = getelementptr i8, ptr %sv, i64 %cvi
  %cvvdp = getelementptr i8, ptr %dv, i64 %cvi
  %cvvb = load <16 x i8>, ptr %cvvsp, align 1
  %cvvz = zext <16 x i8> %cvvb to <16 x i32>
  %cvv0 = sub <16 x i32> %cvvz, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %cvua = mul <16 x i32> %cvu0, <i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004, i32 1004>
  %cvubprod = mul <16 x i32> %cvv0, <i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74, i32 -74>
  %cvusum = add <16 x i32> %cvua, %cvubprod
  %cvuround = add <16 x i32> %cvusum, <i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512>
  %cvushift = ashr <16 x i32> %cvuround, <i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10>
  %cvuoff = add <16 x i32> %cvushift, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %cvulow = icmp slt <16 x i32> %cvuoff, <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %cvulo = select <16 x i1> %cvulow, <16 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>, <16 x i32> %cvuoff
  %cvuhigh = icmp sgt <16 x i32> %cvulo, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %cvuhi = select <16 x i1> %cvuhigh, <16 x i32> <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>, <16 x i32> %cvulo
  %cvubyte = trunc <16 x i32> %cvuhi to <16 x i8>
  %cvuout = select i1 %csc, <16 x i8> %cvubyte, <16 x i8> %cvub
  store <16 x i8> %cvuout, ptr %cvudp, align 1
  %cvva = mul <16 x i32> %cvu0, <i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42, i32 -42>
  %cvvbprod = mul <16 x i32> %cvv0, <i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986, i32 986>
  %cvvsum = add <16 x i32> %cvva, %cvvbprod
  %cvvround = add <16 x i32> %cvvsum, <i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512, i32 512>
  %cvvshift = ashr <16 x i32> %cvvround, <i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10, i32 10>
  %cvvoff = add <16 x i32> %cvvshift, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %cvvlow = icmp slt <16 x i32> %cvvoff, <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %cvvlo = select <16 x i1> %cvvlow, <16 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>, <16 x i32> %cvvoff
  %cvvhigh = icmp sgt <16 x i32> %cvvlo, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %cvvhi = select <16 x i1> %cvvhigh, <16 x i32> <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>, <16 x i32> %cvvlo
  %cvvbyte = trunc <16 x i32> %cvvhi to <16 x i8>
  %cvvout = select i1 %csc, <16 x i8> %cvvbyte, <16 x i8> %cvvb
  store <16 x i8> %cvvout, ptr %cvvdp, align 1
  %cvn = add i64 %cvi, 16
  br label %cvcheck
cscheck:
  %csi = phi i64 [ %cvi, %cvcheck ], [ %csn, %csbody ]
  %csmore = icmp ult i64 %csi, %uv_len
  br i1 %csmore, label %csbody, label %done
csbody:
  %csusp = getelementptr i8, ptr %su, i64 %csi
  %csudp = getelementptr i8, ptr %du, i64 %csi
  %csub = load i8, ptr %csusp, align 1
  %csuz = zext i8 %csub to i32
  %csu0 = sub i32 %csuz, 128
  %csvsp = getelementptr i8, ptr %sv, i64 %csi
  %csvdp = getelementptr i8, ptr %dv, i64 %csi
  %csvb = load i8, ptr %csvsp, align 1
  %csvz = zext i8 %csvb to i32
  %csv0 = sub i32 %csvz, 128
  %csua = mul i32 %csu0, 1004
  %csubprod = mul i32 %csv0, -74
  %csusum = add i32 %csua, %csubprod
  %csuround = add i32 %csusum, 512
  %csushift = ashr i32 %csuround, 10
  %csuoff = add i32 %csushift, 128
  %csulow = icmp slt i32 %csuoff, 0
  %csulo = select i1 %csulow, i32 0, i32 %csuoff
  %csuhigh = icmp sgt i32 %csulo, 255
  %csuhi = select i1 %csuhigh, i32 255, i32 %csulo
  %csubyte = trunc i32 %csuhi to i8
  %csuout = select i1 %csc, i8 %csubyte, i8 %csub
  store i8 %csuout, ptr %csudp, align 1
  %csva = mul i32 %csu0, -42
  %csvbprod = mul i32 %csv0, 986
  %csvsum = add i32 %csva, %csvbprod
  %csvround = add i32 %csvsum, 512
  %csvshift = ashr i32 %csvround, 10
  %csvoff = add i32 %csvshift, 128
  %csvlow = icmp slt i32 %csvoff, 0
  %csvlo = select i1 %csvlow, i32 0, i32 %csvoff
  %csvhigh = icmp sgt i32 %csvlo, 255
  %csvhi = select i1 %csvhigh, i32 255, i32 %csvlo
  %csvbyte = trunc i32 %csvhi to i8
  %csvout = select i1 %csc, i8 %csvbyte, i8 %csvb
  store i8 %csvout, ptr %csvdp, align 1
  %csn = add i64 %csi, 1
  br label %cscheck
done:
  ret void
}
