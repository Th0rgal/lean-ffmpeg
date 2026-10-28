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
  %vec_end = and i64 %dstW, -16
  %has_vec = icmp uge i64 %dstW, 16
  %vcQ8_seed = insertelement <16 x i32> poison, i32 %cQ8, i64 0
  %vcQ8 = shufflevector <16 x i32> %vcQ8_seed, <16 x i32> poison, <16 x i32> zeroinitializer
  %vbrt_seed = insertelement <16 x i32> poison, i32 %brt, i64 0
  %vbrt = shufflevector <16 x i32> %vbrt_seed, <16 x i32> poison, <16 x i32> zeroinitializer
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
  %vavg16 = lshr <16 x i16> %vrnd, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>
  %vavg32 = zext <16 x i16> %vavg16 to <16 x i32>
  %vcnt = sub <16 x i32> %vavg32, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %vmulc = mul <16 x i32> %vcnt, %vcQ8
  %vrndc = add <16 x i32> %vmulc, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %vshrc = ashr <16 x i32> %vrndc, <i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8, i32 8>
  %vadd128 = add <16 x i32> %vshrc, <i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128, i32 128>
  %vscaled = add <16 x i32> %vadd128, %vbrt
  %vlt0 = icmp slt <16 x i32> %vscaled, zeroinitializer
  %vgt255 = icmp sgt <16 x i32> %vscaled, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %vcl0 = select <16 x i1> %vlt0, <16 x i32> zeroinitializer, <16 x i32> %vscaled
  %vcl = select <16 x i1> %vgt255, <16 x i32> <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>, <16 x i32> %vcl0
  %vout = trunc <16 x i32> %vcl to <16 x i8>
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
  %cnt = sub nsw i32 %avg, 128
  %mulc = mul i32 %cnt, %cQ8
  %rndc = add i32 %mulc, 128
  %shrc = ashr i32 %rndc, 8
  %add128 = add i32 %shrc, 128
  %scaled = add i32 %add128, %brt
  %lt0 = icmp slt i32 %scaled, 0
  %gt255 = icmp sgt i32 %scaled, 255
  %cl0 = select i1 %lt0, i32 0, i32 %scaled
  %cl = select i1 %gt255, i32 255, i32 %cl0
  %out_b = trunc i32 %cl to i8
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
  %shift_raw = select i1 %dmp_pos, i32 %dmp32, i32 1
  %shift = and i32 %shift_raw, 31
  %interior_w = sub nuw i64 %w, 2
  %vec_count = and i64 %interior_w, -8
  %vec_end = add nuw i64 1, %vec_count
  %has_vec = icmp uge i64 %w, 10
  %vpri_seed = insertelement <8 x i32> poison, i32 %pri32, i64 0
  %vpri = shufflevector <8 x i32> %vpri_seed, <8 x i32> poison, <8 x i32> zeroinitializer
  %vshift_seed = insertelement <8 x i32> poison, i32 %shift, i64 0
  %vshift = shufflevector <8 x i32> %vshift_seed, <8 x i32> poison, <8 x i32> zeroinitializer
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
  br i1 %has_vec, label %vec.body, label %scalar.check
vec.body:
  %c = phi i64 [ 1, %outer.body ], [ %c_next, %vec.body ]
  %vc_prev = sub nuw i64 %c, 1
  %vc_plus = add nuw i64 %c, 1
  %vp_px = getelementptr inbounds i8, ptr %row_ptr, i64 %c
  %vp_n0 = getelementptr inbounds i8, ptr %row_ptr, i64 %vc_prev
  %vp_n1 = getelementptr inbounds i8, ptr %row_ptr, i64 %vc_plus
  %vp_n2 = getelementptr inbounds i8, ptr %up_ptr, i64 %c
  %vp_n3 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c
  %vb_px = load <8 x i8>, ptr %vp_px, align 1
  %vb_n0 = load <8 x i8>, ptr %vp_n0, align 1
  %vb_n1 = load <8 x i8>, ptr %vp_n1, align 1
  %vb_n2 = load <8 x i8>, ptr %vp_n2, align 1
  %vb_n3 = load <8 x i8>, ptr %vp_n3, align 1
  %vpx = zext <8 x i8> %vb_px to <8 x i32>
  %vn_0 = zext <8 x i8> %vb_n0 to <8 x i32>
  %vn_1 = zext <8 x i8> %vb_n1 to <8 x i32>
  %vn_2 = zext <8 x i8> %vb_n2 to <8 x i32>
  %vn_3 = zext <8 x i8> %vb_n3 to <8 x i32>
  %vd_0 = sub nsw <8 x i32> %vn_0, %vpx
  %vneg_0 = icmp slt <8 x i32> %vd_0, zeroinitializer
  %vnd_0 = sub nsw <8 x i32> zeroinitializer, %vd_0
  %vad_0 = select <8 x i1> %vneg_0, <8 x i32> %vnd_0, <8 x i32> %vd_0
  %vsh_0 = ashr <8 x i32> %vad_0, %vshift
  %vtm_0 = sub nsw <8 x i32> %vpri, %vsh_0
  %vt_lt0_0 = icmp slt <8 x i32> %vtm_0, zeroinitializer
  %vad_lt_0 = icmp slt <8 x i32> %vad_0, %vtm_0
  %vmin_0 = select <8 x i1> %vad_lt_0, <8 x i32> %vad_0, <8 x i32> %vtm_0
  %vmag_0 = select <8 x i1> %vt_lt0_0, <8 x i32> zeroinitializer, <8 x i32> %vmin_0
  %vnmag_0 = sub nsw <8 x i32> zeroinitializer, %vmag_0
  %vc_0 = select <8 x i1> %vneg_0, <8 x i32> %vnmag_0, <8 x i32> %vmag_0
  %vd_1 = sub nsw <8 x i32> %vn_1, %vpx
  %vneg_1 = icmp slt <8 x i32> %vd_1, zeroinitializer
  %vnd_1 = sub nsw <8 x i32> zeroinitializer, %vd_1
  %vad_1 = select <8 x i1> %vneg_1, <8 x i32> %vnd_1, <8 x i32> %vd_1
  %vsh_1 = ashr <8 x i32> %vad_1, %vshift
  %vtm_1 = sub nsw <8 x i32> %vpri, %vsh_1
  %vt_lt0_1 = icmp slt <8 x i32> %vtm_1, zeroinitializer
  %vad_lt_1 = icmp slt <8 x i32> %vad_1, %vtm_1
  %vmin_1 = select <8 x i1> %vad_lt_1, <8 x i32> %vad_1, <8 x i32> %vtm_1
  %vmag_1 = select <8 x i1> %vt_lt0_1, <8 x i32> zeroinitializer, <8 x i32> %vmin_1
  %vnmag_1 = sub nsw <8 x i32> zeroinitializer, %vmag_1
  %vc_1 = select <8 x i1> %vneg_1, <8 x i32> %vnmag_1, <8 x i32> %vmag_1
  %vd_2 = sub nsw <8 x i32> %vn_2, %vpx
  %vneg_2 = icmp slt <8 x i32> %vd_2, zeroinitializer
  %vnd_2 = sub nsw <8 x i32> zeroinitializer, %vd_2
  %vad_2 = select <8 x i1> %vneg_2, <8 x i32> %vnd_2, <8 x i32> %vd_2
  %vsh_2 = ashr <8 x i32> %vad_2, %vshift
  %vtm_2 = sub nsw <8 x i32> %vpri, %vsh_2
  %vt_lt0_2 = icmp slt <8 x i32> %vtm_2, zeroinitializer
  %vad_lt_2 = icmp slt <8 x i32> %vad_2, %vtm_2
  %vmin_2 = select <8 x i1> %vad_lt_2, <8 x i32> %vad_2, <8 x i32> %vtm_2
  %vmag_2 = select <8 x i1> %vt_lt0_2, <8 x i32> zeroinitializer, <8 x i32> %vmin_2
  %vnmag_2 = sub nsw <8 x i32> zeroinitializer, %vmag_2
  %vc_2 = select <8 x i1> %vneg_2, <8 x i32> %vnmag_2, <8 x i32> %vmag_2
  %vd_3 = sub nsw <8 x i32> %vn_3, %vpx
  %vneg_3 = icmp slt <8 x i32> %vd_3, zeroinitializer
  %vnd_3 = sub nsw <8 x i32> zeroinitializer, %vd_3
  %vad_3 = select <8 x i1> %vneg_3, <8 x i32> %vnd_3, <8 x i32> %vd_3
  %vsh_3 = ashr <8 x i32> %vad_3, %vshift
  %vtm_3 = sub nsw <8 x i32> %vpri, %vsh_3
  %vt_lt0_3 = icmp slt <8 x i32> %vtm_3, zeroinitializer
  %vad_lt_3 = icmp slt <8 x i32> %vad_3, %vtm_3
  %vmin_3 = select <8 x i1> %vad_lt_3, <8 x i32> %vad_3, <8 x i32> %vtm_3
  %vmag_3 = select <8 x i1> %vt_lt0_3, <8 x i32> zeroinitializer, <8 x i32> %vmin_3
  %vnmag_3 = sub nsw <8 x i32> zeroinitializer, %vmag_3
  %vc_3 = select <8 x i1> %vneg_3, <8 x i32> %vnmag_3, <8 x i32> %vmag_3
  %vs01 = add nsw <8 x i32> %vc_0, %vc_1
  %vs23 = add nsw <8 x i32> %vc_2, %vc_3
  %vsum = add nsw <8 x i32> %vs01, %vs23
  %vsrnd = add nsw <8 x i32> %vsum, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %vsdiv = ashr <8 x i32> %vsrnd, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %vout_raw = add nsw <8 x i32> %vpx, %vsdiv
  %vlt0 = icmp slt <8 x i32> %vout_raw, zeroinitializer
  %vgt255 = icmp sgt <8 x i32> %vout_raw, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %vcl0 = select <8 x i1> %vlt0, <8 x i32> zeroinitializer, <8 x i32> %vout_raw
  %vcl = select <8 x i1> %vgt255, <8 x i32> <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>, <8 x i32> %vcl0
  %vout_b = trunc <8 x i32> %vcl to <8 x i8>
  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %c
  store <8 x i8> %vout_b, ptr %vdst_p, align 1
  %c_next = add nuw i64 %c, 8
  %vec_done = icmp eq i64 %c_next, %vec_end
  br i1 %vec_done, label %scalar.check, label %vec.body
scalar.check:
  %dx_start = phi i64 [ 1, %outer.body ], [ %vec_end, %vec.body ]
  %has_rem = icmp ult i64 %dx_start, %w_limit
  br i1 %has_rem, label %inner.body, label %outer.latch
inner.body:
  %sc = phi i64 [ %dx_start, %scalar.check ], [ %sc_next, %inner.body ]
  %c_prev = sub nuw i64 %sc, 1
  %c_plus = add nuw i64 %sc, 1
  %p_px = getelementptr inbounds i8, ptr %row_ptr, i64 %sc
  %p_n0 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev
  %p_n1 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus
  %p_n2 = getelementptr inbounds i8, ptr %up_ptr, i64 %sc
  %p_n3 = getelementptr inbounds i8, ptr %dn_ptr, i64 %sc
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
  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %sc
  store i8 %out_b, ptr %dst_p, align 1
  %sc_next = add nuw nsw i64 %sc, 1
  %done_c = icmp eq i64 %sc_next, %w_limit
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
  %interior_w = sub nuw i64 %w, 2
  %vec_count = and i64 %interior_w, -8
  %vec_end = add nuw i64 1, %vec_count
  %has_vec = icmp uge i64 %w, 10
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
  br i1 %has_vec, label %vec.body, label %scalar.check
vec.body:
  %c = phi i64 [ 1, %outer.body ], [ %c_next, %vec.body ]
  %vc_prev = sub nuw i64 %c, 1
  %vc_plus = add nuw i64 %c, 1
  %vp00 = getelementptr inbounds i8, ptr %up_ptr, i64 %vc_prev
  %vb00 = load <8 x i8>, ptr %vp00, align 1
  %vu00 = zext <8 x i8> %vb00 to <8 x i16>
  %vp01 = getelementptr inbounds i8, ptr %up_ptr, i64 %c
  %vb01 = load <8 x i8>, ptr %vp01, align 1
  %vu01 = zext <8 x i8> %vb01 to <8 x i16>
  %vp02 = getelementptr inbounds i8, ptr %up_ptr, i64 %vc_plus
  %vb02 = load <8 x i8>, ptr %vp02, align 1
  %vu02 = zext <8 x i8> %vb02 to <8 x i16>
  %vp10 = getelementptr inbounds i8, ptr %row_ptr, i64 %vc_prev
  %vb10 = load <8 x i8>, ptr %vp10, align 1
  %vu10 = zext <8 x i8> %vb10 to <8 x i16>
  %vp11 = getelementptr inbounds i8, ptr %row_ptr, i64 %c
  %vb11 = load <8 x i8>, ptr %vp11, align 1
  %vu11 = zext <8 x i8> %vb11 to <8 x i16>
  %vp12 = getelementptr inbounds i8, ptr %row_ptr, i64 %vc_plus
  %vb12 = load <8 x i8>, ptr %vp12, align 1
  %vu12 = zext <8 x i8> %vb12 to <8 x i16>
  %vp20 = getelementptr inbounds i8, ptr %dn_ptr, i64 %vc_prev
  %vb20 = load <8 x i8>, ptr %vp20, align 1
  %vu20 = zext <8 x i8> %vb20 to <8 x i16>
  %vp21 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c
  %vb21 = load <8 x i8>, ptr %vp21, align 1
  %vu21 = zext <8 x i8> %vb21 to <8 x i16>
  %vp22 = getelementptr inbounds i8, ptr %dn_ptr, i64 %vc_plus
  %vb22 = load <8 x i8>, ptr %vp22, align 1
  %vu22 = zext <8 x i8> %vb22 to <8 x i16>
  %vsum2 = add nuw nsw <8 x i16> %vu00, %vu01
  %vsum3 = add nuw nsw <8 x i16> %vsum2, %vu02
  %vsum4 = add nuw nsw <8 x i16> %vsum3, %vu10
  %vsum5 = add nuw nsw <8 x i16> %vsum4, %vu11
  %vsum6 = add nuw nsw <8 x i16> %vsum5, %vu12
  %vsum7 = add nuw nsw <8 x i16> %vsum6, %vu20
  %vsum8 = add nuw nsw <8 x i16> %vsum7, %vu21
  %vsum9 = add nuw nsw <8 x i16> %vsum8, %vu22
  %vsum32 = zext <8 x i16> %vsum9 to <8 x i32>
  %vrnd = add nuw nsw <8 x i32> %vsum32, <i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4>
  %vprod = mul nuw nsw <8 x i32> %vrnd, <i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282>
  %vavg = lshr <8 x i32> %vprod, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>
  %vout = trunc <8 x i32> %vavg to <8 x i8>
  %vdst = getelementptr inbounds i8, ptr %dst_row, i64 %c
  store <8 x i8> %vout, ptr %vdst, align 1
  %c_next = add nuw i64 %c, 8
  %vec_done = icmp eq i64 %c_next, %vec_end
  br i1 %vec_done, label %scalar.check, label %vec.body
scalar.check:
  %dx_start = phi i64 [ 1, %outer.body ], [ %vec_end, %vec.body ]
  %has_rem = icmp ult i64 %dx_start, %w_limit
  br i1 %has_rem, label %inner.body, label %outer.latch
inner.body:
  %sc = phi i64 [ %dx_start, %scalar.check ], [ %sc_next, %inner.body ]
  %c_prev = sub nuw i64 %sc, 1
  %c_plus = add nuw i64 %sc, 1
  %p00 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_prev
  %p01 = getelementptr inbounds i8, ptr %up_ptr, i64 %sc
  %p02 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_plus
  %p10 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev
  %p11 = getelementptr inbounds i8, ptr %row_ptr, i64 %sc
  %p12 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus
  %p20 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c_prev
  %p21 = getelementptr inbounds i8, ptr %dn_ptr, i64 %sc
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
  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %sc
  store i8 %out_b, ptr %dst_p, align 1
  %sc_next = add nuw nsw i64 %sc, 1
  %done_c = icmp eq i64 %sc_next, %w_limit
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
  br i1 %ok, label %dispatch, label %exit.zero
dispatch:
  %contiguous = icmp eq i64 %step, 1
  br i1 %contiguous, label %vec16.check, label %stride.check
stride.check:
  %strided = icmp eq i64 %step, 16
  br i1 %strided, label %vec4.check, label %scalar.check
vec16.check:
  %vec16.idx = phi i64 [ 0, %dispatch ], [ %vec16.idx.next, %vec16.body ]
  %vec16.sum = phi i64 [ 0, %dispatch ], [ %vec16.sum.next, %vec16.body ]
  %vec16.sumSq = phi i64 [ 0, %dispatch ], [ %vec16.sumSq.next, %vec16.body ]
  %vec16.cnt = phi i64 [ 0, %dispatch ], [ %vec16.cnt.next, %vec16.body ]
  %vec16.remaining = sub i64 %nPixels, %vec16.idx
  %vec16.enough = icmp uge i64 %vec16.remaining, 16
  br i1 %vec16.enough, label %vec16.body, label %scalar.check
vec16.body:
  %vp = getelementptr i8, ptr %src, i64 %vec16.idx
  %vb = load <16 x i8>, ptr %vp, align 1
  %vraw = zext <16 x i8> %vb to <16 x i32>
  %v16 = add <16 x i32> %vraw, zeroinitializer
  %vec16.sq = mul nuw <16 x i32> %v16, %v16
  %vec16.sum.r = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %v16)
  %vec16.sum.wide = zext i32 %vec16.sum.r to i64
  %vec16.sum.next = add i64 %vec16.sum, %vec16.sum.wide
  %vec16.sumSq.r = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %vec16.sq)
  %vec16.sumSq.wide = zext i32 %vec16.sumSq.r to i64
  %vec16.sumSq.next = add i64 %vec16.sumSq, %vec16.sumSq.wide
  %vec16.cnt.next = add nuw i64 %vec16.cnt, 16
  %vec16.idx.next = add nuw i64 %vec16.idx, 16
  br label %vec16.check
vec4.check:
  %vec4.idx = phi i64 [ 0, %stride.check ], [ %vec4.idx.next, %vec4.body ]
  %vec4.sum = phi i64 [ 0, %stride.check ], [ %vec4.sum.next, %vec4.body ]
  %vec4.sumSq = phi i64 [ 0, %stride.check ], [ %vec4.sumSq.next, %vec4.body ]
  %vec4.cnt = phi i64 [ 0, %stride.check ], [ %vec4.cnt.next, %vec4.body ]
  %vec4.remaining = sub i64 %nPixels, %vec4.idx
  %vec4.enough = icmp uge i64 %vec4.remaining, 49
  br i1 %vec4.enough, label %vec4.body, label %scalar.check
vec4.body:
  %si0 = add i64 %vec4.idx, 0
  %sp0 = getelementptr i8, ptr %src, i64 %si0
  %sb0 = load i8, ptr %sp0, align 1
  %sr0 = zext i8 %sb0 to i32
  %sv0 = add i32 %sr0, 0
  %pack0 = insertelement <4 x i32> poison, i32 %sv0, i32 0
  %si1 = add i64 %vec4.idx, 16
  %sp1 = getelementptr i8, ptr %src, i64 %si1
  %sb1 = load i8, ptr %sp1, align 1
  %sr1 = zext i8 %sb1 to i32
  %sv1 = add i32 %sr1, 0
  %pack1 = insertelement <4 x i32> %pack0, i32 %sv1, i32 1
  %si2 = add i64 %vec4.idx, 32
  %sp2 = getelementptr i8, ptr %src, i64 %si2
  %sb2 = load i8, ptr %sp2, align 1
  %sr2 = zext i8 %sb2 to i32
  %sv2 = add i32 %sr2, 0
  %pack2 = insertelement <4 x i32> %pack1, i32 %sv2, i32 2
  %si3 = add i64 %vec4.idx, 48
  %sp3 = getelementptr i8, ptr %src, i64 %si3
  %sb3 = load i8, ptr %sp3, align 1
  %sr3 = zext i8 %sb3 to i32
  %sv3 = add i32 %sr3, 0
  %pack3 = insertelement <4 x i32> %pack2, i32 %sv3, i32 3
  %vec4.sq = mul nuw <4 x i32> %pack3, %pack3
  %vec4.sum.r = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %pack3)
  %vec4.sum.wide = zext i32 %vec4.sum.r to i64
  %vec4.sum.next = add i64 %vec4.sum, %vec4.sum.wide
  %vec4.sumSq.r = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %vec4.sq)
  %vec4.sumSq.wide = zext i32 %vec4.sumSq.r to i64
  %vec4.sumSq.next = add i64 %vec4.sumSq, %vec4.sumSq.wide
  %vec4.cnt.next = add nuw i64 %vec4.cnt, 4
  %vec4.advance = add i64 %vec4.idx, 64
  %vec4.more = icmp ugt i64 %vec4.remaining, 64
  %vec4.idx.next = select i1 %vec4.more, i64 %vec4.advance, i64 %nPixels
  br label %vec4.check
scalar.check:
  %initial.idx = phi i64 [ 0, %stride.check ], [ %vec16.idx, %vec16.check ], [ %vec4.idx, %vec4.check ]
  %initial.sum = phi i64 [ 0, %stride.check ], [ %vec16.sum, %vec16.check ], [ %vec4.sum, %vec4.check ]
  %initial.sumSq = phi i64 [ 0, %stride.check ], [ %vec16.sumSq, %vec16.check ], [ %vec4.sumSq, %vec4.check ]
  %initial.cnt = phi i64 [ 0, %stride.check ], [ %vec16.cnt, %vec16.check ], [ %vec4.cnt, %vec4.check ]
  %tail = icmp ult i64 %initial.idx, %nPixels
  br i1 %tail, label %loop.body, label %compute.out
loop.body:
  %idx = phi i64 [ %initial.idx, %scalar.check ], [ %idx_next, %loop.body ]
  %sum = phi i64 [ %initial.sum, %scalar.check ], [ %sum_next, %loop.body ]
  %sumSq = phi i64 [ %initial.sumSq, %scalar.check ], [ %sumSq_next, %loop.body ]
  %cnt = phi i64 [ %initial.cnt, %scalar.check ], [ %cnt_next, %loop.body ]
  %p = getelementptr i8, ptr %src, i64 %idx
  %b = load i8, ptr %p, align 1
  %v = zext i8 %b to i64
  %v2 = mul nuw i64 %v, %v
  %sum_next = add i64 %sum, %v
  %sumSq_next = add i64 %sumSq, %v2
  %cnt_next = add nuw i64 %cnt, 1
  %idx_next = add i64 %idx, %step
  %remaining = sub i64 %nPixels, %idx
  %more = icmp ult i64 %step, %remaining
  br i1 %more, label %loop.body, label %compute.out
compute.out:
  %final.sum = phi i64 [ %initial.sum, %scalar.check ], [ %sum_next, %loop.body ]
  %final.sumSq = phi i64 [ %initial.sumSq, %scalar.check ], [ %sumSq_next, %loop.body ]
  %final.cnt = phi i64 [ %initial.cnt, %scalar.check ], [ %cnt_next, %loop.body ]
  %mean = udiv i64 %final.sum, %final.cnt
  %meanSq = udiv i64 %final.sumSq, %final.cnt
  %sq = mul nuw i64 %mean, %mean
  %gt = icmp ugt i64 %meanSq, %sq
  %diff = sub i64 %meanSq, %sq
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
  br i1 %moreX, label %col, label %rowEnd
rowEnd:
  %nextY = add i64 %dy, 1
  %moreY = icmp ult i64 %nextY, %dstH
  br i1 %moreY, label %row, label %exit
exit:
  ret void
}

declare i32 @llvm.vector.reduce.add.v16i32(<16 x i32>)

declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>)

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
  %oneW = icmp eq i64 %srcW, %dstW
  %oneH = icmp eq i64 %srcH, %dstH
  %one = and i1 %oneW, %oneH
  %twoWsize = mul i64 %dstW, 2
  %twoW = icmp eq i64 %srcW, %twoWsize
  %twoHsize = mul i64 %dstH, 2
  %twoH = icmp eq i64 %srcH, %twoHsize
  %two = and i1 %twoW, %twoH
  %threeWsize = mul i64 %dstW, 3
  %threeW = icmp eq i64 %srcW, %threeWsize
  %threeHsize = mul i64 %dstH, 3
  %threeH = icmp eq i64 %srcH, %threeHsize
  %three = and i1 %threeW, %threeH
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
  br i1 %one, label %same, label %choose2
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
choose2:
  br i1 %two, label %half, label %choose3
choose3:
  br i1 %three, label %third, label %q8
third:
  %ty = mul i64 %dy, 3
  %tr = mul i64 %ty, %srcW
  %tx0 = add i64 %bxi, 0
  %txs0 = mul i64 %tx0, 3
  %tb0 = add i64 %tr, %txs0
  %t0_0row = mul i64 %srcW, 0
  %t0_0off = add i64 %t0_0row, 0
  %t0_0idx = add i64 %tb0, %t0_0off
  %t0_0ptr = getelementptr i8, ptr %src, i64 %t0_0idx
  %t0_0raw = load i8, ptr %t0_0ptr, align 1
  %t0_0 = zext i8 %t0_0raw to i32
  %t0_1row = mul i64 %srcW, 0
  %t0_1off = add i64 %t0_1row, 1
  %t0_1idx = add i64 %tb0, %t0_1off
  %t0_1ptr = getelementptr i8, ptr %src, i64 %t0_1idx
  %t0_1raw = load i8, ptr %t0_1ptr, align 1
  %t0_1 = zext i8 %t0_1raw to i32
  %t0_2row = mul i64 %srcW, 0
  %t0_2off = add i64 %t0_2row, 2
  %t0_2idx = add i64 %tb0, %t0_2off
  %t0_2ptr = getelementptr i8, ptr %src, i64 %t0_2idx
  %t0_2raw = load i8, ptr %t0_2ptr, align 1
  %t0_2 = zext i8 %t0_2raw to i32
  %t0_3row = mul i64 %srcW, 1
  %t0_3off = add i64 %t0_3row, 0
  %t0_3idx = add i64 %tb0, %t0_3off
  %t0_3ptr = getelementptr i8, ptr %src, i64 %t0_3idx
  %t0_3raw = load i8, ptr %t0_3ptr, align 1
  %t0_3 = zext i8 %t0_3raw to i32
  %t0_4row = mul i64 %srcW, 1
  %t0_4off = add i64 %t0_4row, 1
  %t0_4idx = add i64 %tb0, %t0_4off
  %t0_4ptr = getelementptr i8, ptr %src, i64 %t0_4idx
  %t0_4raw = load i8, ptr %t0_4ptr, align 1
  %t0_4 = zext i8 %t0_4raw to i32
  %t0_5row = mul i64 %srcW, 1
  %t0_5off = add i64 %t0_5row, 2
  %t0_5idx = add i64 %tb0, %t0_5off
  %t0_5ptr = getelementptr i8, ptr %src, i64 %t0_5idx
  %t0_5raw = load i8, ptr %t0_5ptr, align 1
  %t0_5 = zext i8 %t0_5raw to i32
  %t0_6row = mul i64 %srcW, 2
  %t0_6off = add i64 %t0_6row, 0
  %t0_6idx = add i64 %tb0, %t0_6off
  %t0_6ptr = getelementptr i8, ptr %src, i64 %t0_6idx
  %t0_6raw = load i8, ptr %t0_6ptr, align 1
  %t0_6 = zext i8 %t0_6raw to i32
  %t0_7row = mul i64 %srcW, 2
  %t0_7off = add i64 %t0_7row, 1
  %t0_7idx = add i64 %tb0, %t0_7off
  %t0_7ptr = getelementptr i8, ptr %src, i64 %t0_7idx
  %t0_7raw = load i8, ptr %t0_7ptr, align 1
  %t0_7 = zext i8 %t0_7raw to i32
  %t0_8row = mul i64 %srcW, 2
  %t0_8off = add i64 %t0_8row, 2
  %t0_8idx = add i64 %tb0, %t0_8off
  %t0_8ptr = getelementptr i8, ptr %src, i64 %t0_8idx
  %t0_8raw = load i8, ptr %t0_8ptr, align 1
  %t0_8 = zext i8 %t0_8raw to i32
  %ts0_1 = add i32 %t0_0, %t0_1
  %ts0_2 = add i32 %ts0_1, %t0_2
  %ts0_3 = add i32 %ts0_2, %t0_3
  %ts0_4 = add i32 %ts0_3, %t0_4
  %ts0_5 = add i32 %ts0_4, %t0_5
  %ts0_6 = add i32 %ts0_5, %t0_6
  %ts0_7 = add i32 %ts0_6, %t0_7
  %ts0_8 = add i32 %ts0_7, %t0_8
  %ta0 = add i32 %ts0_8, 4
  %tm0 = mul i32 %ta0, 7282
  %tv0 = lshr i32 %tm0, 16
  %third0 = insertelement <16 x i32> poison, i32 %tv0, i64 0
  %tx1 = add i64 %bxi, 1
  %txs1 = mul i64 %tx1, 3
  %tb1 = add i64 %tr, %txs1
  %t1_0row = mul i64 %srcW, 0
  %t1_0off = add i64 %t1_0row, 0
  %t1_0idx = add i64 %tb1, %t1_0off
  %t1_0ptr = getelementptr i8, ptr %src, i64 %t1_0idx
  %t1_0raw = load i8, ptr %t1_0ptr, align 1
  %t1_0 = zext i8 %t1_0raw to i32
  %t1_1row = mul i64 %srcW, 0
  %t1_1off = add i64 %t1_1row, 1
  %t1_1idx = add i64 %tb1, %t1_1off
  %t1_1ptr = getelementptr i8, ptr %src, i64 %t1_1idx
  %t1_1raw = load i8, ptr %t1_1ptr, align 1
  %t1_1 = zext i8 %t1_1raw to i32
  %t1_2row = mul i64 %srcW, 0
  %t1_2off = add i64 %t1_2row, 2
  %t1_2idx = add i64 %tb1, %t1_2off
  %t1_2ptr = getelementptr i8, ptr %src, i64 %t1_2idx
  %t1_2raw = load i8, ptr %t1_2ptr, align 1
  %t1_2 = zext i8 %t1_2raw to i32
  %t1_3row = mul i64 %srcW, 1
  %t1_3off = add i64 %t1_3row, 0
  %t1_3idx = add i64 %tb1, %t1_3off
  %t1_3ptr = getelementptr i8, ptr %src, i64 %t1_3idx
  %t1_3raw = load i8, ptr %t1_3ptr, align 1
  %t1_3 = zext i8 %t1_3raw to i32
  %t1_4row = mul i64 %srcW, 1
  %t1_4off = add i64 %t1_4row, 1
  %t1_4idx = add i64 %tb1, %t1_4off
  %t1_4ptr = getelementptr i8, ptr %src, i64 %t1_4idx
  %t1_4raw = load i8, ptr %t1_4ptr, align 1
  %t1_4 = zext i8 %t1_4raw to i32
  %t1_5row = mul i64 %srcW, 1
  %t1_5off = add i64 %t1_5row, 2
  %t1_5idx = add i64 %tb1, %t1_5off
  %t1_5ptr = getelementptr i8, ptr %src, i64 %t1_5idx
  %t1_5raw = load i8, ptr %t1_5ptr, align 1
  %t1_5 = zext i8 %t1_5raw to i32
  %t1_6row = mul i64 %srcW, 2
  %t1_6off = add i64 %t1_6row, 0
  %t1_6idx = add i64 %tb1, %t1_6off
  %t1_6ptr = getelementptr i8, ptr %src, i64 %t1_6idx
  %t1_6raw = load i8, ptr %t1_6ptr, align 1
  %t1_6 = zext i8 %t1_6raw to i32
  %t1_7row = mul i64 %srcW, 2
  %t1_7off = add i64 %t1_7row, 1
  %t1_7idx = add i64 %tb1, %t1_7off
  %t1_7ptr = getelementptr i8, ptr %src, i64 %t1_7idx
  %t1_7raw = load i8, ptr %t1_7ptr, align 1
  %t1_7 = zext i8 %t1_7raw to i32
  %t1_8row = mul i64 %srcW, 2
  %t1_8off = add i64 %t1_8row, 2
  %t1_8idx = add i64 %tb1, %t1_8off
  %t1_8ptr = getelementptr i8, ptr %src, i64 %t1_8idx
  %t1_8raw = load i8, ptr %t1_8ptr, align 1
  %t1_8 = zext i8 %t1_8raw to i32
  %ts1_1 = add i32 %t1_0, %t1_1
  %ts1_2 = add i32 %ts1_1, %t1_2
  %ts1_3 = add i32 %ts1_2, %t1_3
  %ts1_4 = add i32 %ts1_3, %t1_4
  %ts1_5 = add i32 %ts1_4, %t1_5
  %ts1_6 = add i32 %ts1_5, %t1_6
  %ts1_7 = add i32 %ts1_6, %t1_7
  %ts1_8 = add i32 %ts1_7, %t1_8
  %ta1 = add i32 %ts1_8, 4
  %tm1 = mul i32 %ta1, 7282
  %tv1 = lshr i32 %tm1, 16
  %third1 = insertelement <16 x i32> %third0, i32 %tv1, i64 1
  %tx2 = add i64 %bxi, 2
  %txs2 = mul i64 %tx2, 3
  %tb2 = add i64 %tr, %txs2
  %t2_0row = mul i64 %srcW, 0
  %t2_0off = add i64 %t2_0row, 0
  %t2_0idx = add i64 %tb2, %t2_0off
  %t2_0ptr = getelementptr i8, ptr %src, i64 %t2_0idx
  %t2_0raw = load i8, ptr %t2_0ptr, align 1
  %t2_0 = zext i8 %t2_0raw to i32
  %t2_1row = mul i64 %srcW, 0
  %t2_1off = add i64 %t2_1row, 1
  %t2_1idx = add i64 %tb2, %t2_1off
  %t2_1ptr = getelementptr i8, ptr %src, i64 %t2_1idx
  %t2_1raw = load i8, ptr %t2_1ptr, align 1
  %t2_1 = zext i8 %t2_1raw to i32
  %t2_2row = mul i64 %srcW, 0
  %t2_2off = add i64 %t2_2row, 2
  %t2_2idx = add i64 %tb2, %t2_2off
  %t2_2ptr = getelementptr i8, ptr %src, i64 %t2_2idx
  %t2_2raw = load i8, ptr %t2_2ptr, align 1
  %t2_2 = zext i8 %t2_2raw to i32
  %t2_3row = mul i64 %srcW, 1
  %t2_3off = add i64 %t2_3row, 0
  %t2_3idx = add i64 %tb2, %t2_3off
  %t2_3ptr = getelementptr i8, ptr %src, i64 %t2_3idx
  %t2_3raw = load i8, ptr %t2_3ptr, align 1
  %t2_3 = zext i8 %t2_3raw to i32
  %t2_4row = mul i64 %srcW, 1
  %t2_4off = add i64 %t2_4row, 1
  %t2_4idx = add i64 %tb2, %t2_4off
  %t2_4ptr = getelementptr i8, ptr %src, i64 %t2_4idx
  %t2_4raw = load i8, ptr %t2_4ptr, align 1
  %t2_4 = zext i8 %t2_4raw to i32
  %t2_5row = mul i64 %srcW, 1
  %t2_5off = add i64 %t2_5row, 2
  %t2_5idx = add i64 %tb2, %t2_5off
  %t2_5ptr = getelementptr i8, ptr %src, i64 %t2_5idx
  %t2_5raw = load i8, ptr %t2_5ptr, align 1
  %t2_5 = zext i8 %t2_5raw to i32
  %t2_6row = mul i64 %srcW, 2
  %t2_6off = add i64 %t2_6row, 0
  %t2_6idx = add i64 %tb2, %t2_6off
  %t2_6ptr = getelementptr i8, ptr %src, i64 %t2_6idx
  %t2_6raw = load i8, ptr %t2_6ptr, align 1
  %t2_6 = zext i8 %t2_6raw to i32
  %t2_7row = mul i64 %srcW, 2
  %t2_7off = add i64 %t2_7row, 1
  %t2_7idx = add i64 %tb2, %t2_7off
  %t2_7ptr = getelementptr i8, ptr %src, i64 %t2_7idx
  %t2_7raw = load i8, ptr %t2_7ptr, align 1
  %t2_7 = zext i8 %t2_7raw to i32
  %t2_8row = mul i64 %srcW, 2
  %t2_8off = add i64 %t2_8row, 2
  %t2_8idx = add i64 %tb2, %t2_8off
  %t2_8ptr = getelementptr i8, ptr %src, i64 %t2_8idx
  %t2_8raw = load i8, ptr %t2_8ptr, align 1
  %t2_8 = zext i8 %t2_8raw to i32
  %ts2_1 = add i32 %t2_0, %t2_1
  %ts2_2 = add i32 %ts2_1, %t2_2
  %ts2_3 = add i32 %ts2_2, %t2_3
  %ts2_4 = add i32 %ts2_3, %t2_4
  %ts2_5 = add i32 %ts2_4, %t2_5
  %ts2_6 = add i32 %ts2_5, %t2_6
  %ts2_7 = add i32 %ts2_6, %t2_7
  %ts2_8 = add i32 %ts2_7, %t2_8
  %ta2 = add i32 %ts2_8, 4
  %tm2 = mul i32 %ta2, 7282
  %tv2 = lshr i32 %tm2, 16
  %third2 = insertelement <16 x i32> %third1, i32 %tv2, i64 2
  %tx3 = add i64 %bxi, 3
  %txs3 = mul i64 %tx3, 3
  %tb3 = add i64 %tr, %txs3
  %t3_0row = mul i64 %srcW, 0
  %t3_0off = add i64 %t3_0row, 0
  %t3_0idx = add i64 %tb3, %t3_0off
  %t3_0ptr = getelementptr i8, ptr %src, i64 %t3_0idx
  %t3_0raw = load i8, ptr %t3_0ptr, align 1
  %t3_0 = zext i8 %t3_0raw to i32
  %t3_1row = mul i64 %srcW, 0
  %t3_1off = add i64 %t3_1row, 1
  %t3_1idx = add i64 %tb3, %t3_1off
  %t3_1ptr = getelementptr i8, ptr %src, i64 %t3_1idx
  %t3_1raw = load i8, ptr %t3_1ptr, align 1
  %t3_1 = zext i8 %t3_1raw to i32
  %t3_2row = mul i64 %srcW, 0
  %t3_2off = add i64 %t3_2row, 2
  %t3_2idx = add i64 %tb3, %t3_2off
  %t3_2ptr = getelementptr i8, ptr %src, i64 %t3_2idx
  %t3_2raw = load i8, ptr %t3_2ptr, align 1
  %t3_2 = zext i8 %t3_2raw to i32
  %t3_3row = mul i64 %srcW, 1
  %t3_3off = add i64 %t3_3row, 0
  %t3_3idx = add i64 %tb3, %t3_3off
  %t3_3ptr = getelementptr i8, ptr %src, i64 %t3_3idx
  %t3_3raw = load i8, ptr %t3_3ptr, align 1
  %t3_3 = zext i8 %t3_3raw to i32
  %t3_4row = mul i64 %srcW, 1
  %t3_4off = add i64 %t3_4row, 1
  %t3_4idx = add i64 %tb3, %t3_4off
  %t3_4ptr = getelementptr i8, ptr %src, i64 %t3_4idx
  %t3_4raw = load i8, ptr %t3_4ptr, align 1
  %t3_4 = zext i8 %t3_4raw to i32
  %t3_5row = mul i64 %srcW, 1
  %t3_5off = add i64 %t3_5row, 2
  %t3_5idx = add i64 %tb3, %t3_5off
  %t3_5ptr = getelementptr i8, ptr %src, i64 %t3_5idx
  %t3_5raw = load i8, ptr %t3_5ptr, align 1
  %t3_5 = zext i8 %t3_5raw to i32
  %t3_6row = mul i64 %srcW, 2
  %t3_6off = add i64 %t3_6row, 0
  %t3_6idx = add i64 %tb3, %t3_6off
  %t3_6ptr = getelementptr i8, ptr %src, i64 %t3_6idx
  %t3_6raw = load i8, ptr %t3_6ptr, align 1
  %t3_6 = zext i8 %t3_6raw to i32
  %t3_7row = mul i64 %srcW, 2
  %t3_7off = add i64 %t3_7row, 1
  %t3_7idx = add i64 %tb3, %t3_7off
  %t3_7ptr = getelementptr i8, ptr %src, i64 %t3_7idx
  %t3_7raw = load i8, ptr %t3_7ptr, align 1
  %t3_7 = zext i8 %t3_7raw to i32
  %t3_8row = mul i64 %srcW, 2
  %t3_8off = add i64 %t3_8row, 2
  %t3_8idx = add i64 %tb3, %t3_8off
  %t3_8ptr = getelementptr i8, ptr %src, i64 %t3_8idx
  %t3_8raw = load i8, ptr %t3_8ptr, align 1
  %t3_8 = zext i8 %t3_8raw to i32
  %ts3_1 = add i32 %t3_0, %t3_1
  %ts3_2 = add i32 %ts3_1, %t3_2
  %ts3_3 = add i32 %ts3_2, %t3_3
  %ts3_4 = add i32 %ts3_3, %t3_4
  %ts3_5 = add i32 %ts3_4, %t3_5
  %ts3_6 = add i32 %ts3_5, %t3_6
  %ts3_7 = add i32 %ts3_6, %t3_7
  %ts3_8 = add i32 %ts3_7, %t3_8
  %ta3 = add i32 %ts3_8, 4
  %tm3 = mul i32 %ta3, 7282
  %tv3 = lshr i32 %tm3, 16
  %third3 = insertelement <16 x i32> %third2, i32 %tv3, i64 3
  %tx4 = add i64 %bxi, 4
  %txs4 = mul i64 %tx4, 3
  %tb4 = add i64 %tr, %txs4
  %t4_0row = mul i64 %srcW, 0
  %t4_0off = add i64 %t4_0row, 0
  %t4_0idx = add i64 %tb4, %t4_0off
  %t4_0ptr = getelementptr i8, ptr %src, i64 %t4_0idx
  %t4_0raw = load i8, ptr %t4_0ptr, align 1
  %t4_0 = zext i8 %t4_0raw to i32
  %t4_1row = mul i64 %srcW, 0
  %t4_1off = add i64 %t4_1row, 1
  %t4_1idx = add i64 %tb4, %t4_1off
  %t4_1ptr = getelementptr i8, ptr %src, i64 %t4_1idx
  %t4_1raw = load i8, ptr %t4_1ptr, align 1
  %t4_1 = zext i8 %t4_1raw to i32
  %t4_2row = mul i64 %srcW, 0
  %t4_2off = add i64 %t4_2row, 2
  %t4_2idx = add i64 %tb4, %t4_2off
  %t4_2ptr = getelementptr i8, ptr %src, i64 %t4_2idx
  %t4_2raw = load i8, ptr %t4_2ptr, align 1
  %t4_2 = zext i8 %t4_2raw to i32
  %t4_3row = mul i64 %srcW, 1
  %t4_3off = add i64 %t4_3row, 0
  %t4_3idx = add i64 %tb4, %t4_3off
  %t4_3ptr = getelementptr i8, ptr %src, i64 %t4_3idx
  %t4_3raw = load i8, ptr %t4_3ptr, align 1
  %t4_3 = zext i8 %t4_3raw to i32
  %t4_4row = mul i64 %srcW, 1
  %t4_4off = add i64 %t4_4row, 1
  %t4_4idx = add i64 %tb4, %t4_4off
  %t4_4ptr = getelementptr i8, ptr %src, i64 %t4_4idx
  %t4_4raw = load i8, ptr %t4_4ptr, align 1
  %t4_4 = zext i8 %t4_4raw to i32
  %t4_5row = mul i64 %srcW, 1
  %t4_5off = add i64 %t4_5row, 2
  %t4_5idx = add i64 %tb4, %t4_5off
  %t4_5ptr = getelementptr i8, ptr %src, i64 %t4_5idx
  %t4_5raw = load i8, ptr %t4_5ptr, align 1
  %t4_5 = zext i8 %t4_5raw to i32
  %t4_6row = mul i64 %srcW, 2
  %t4_6off = add i64 %t4_6row, 0
  %t4_6idx = add i64 %tb4, %t4_6off
  %t4_6ptr = getelementptr i8, ptr %src, i64 %t4_6idx
  %t4_6raw = load i8, ptr %t4_6ptr, align 1
  %t4_6 = zext i8 %t4_6raw to i32
  %t4_7row = mul i64 %srcW, 2
  %t4_7off = add i64 %t4_7row, 1
  %t4_7idx = add i64 %tb4, %t4_7off
  %t4_7ptr = getelementptr i8, ptr %src, i64 %t4_7idx
  %t4_7raw = load i8, ptr %t4_7ptr, align 1
  %t4_7 = zext i8 %t4_7raw to i32
  %t4_8row = mul i64 %srcW, 2
  %t4_8off = add i64 %t4_8row, 2
  %t4_8idx = add i64 %tb4, %t4_8off
  %t4_8ptr = getelementptr i8, ptr %src, i64 %t4_8idx
  %t4_8raw = load i8, ptr %t4_8ptr, align 1
  %t4_8 = zext i8 %t4_8raw to i32
  %ts4_1 = add i32 %t4_0, %t4_1
  %ts4_2 = add i32 %ts4_1, %t4_2
  %ts4_3 = add i32 %ts4_2, %t4_3
  %ts4_4 = add i32 %ts4_3, %t4_4
  %ts4_5 = add i32 %ts4_4, %t4_5
  %ts4_6 = add i32 %ts4_5, %t4_6
  %ts4_7 = add i32 %ts4_6, %t4_7
  %ts4_8 = add i32 %ts4_7, %t4_8
  %ta4 = add i32 %ts4_8, 4
  %tm4 = mul i32 %ta4, 7282
  %tv4 = lshr i32 %tm4, 16
  %third4 = insertelement <16 x i32> %third3, i32 %tv4, i64 4
  %tx5 = add i64 %bxi, 5
  %txs5 = mul i64 %tx5, 3
  %tb5 = add i64 %tr, %txs5
  %t5_0row = mul i64 %srcW, 0
  %t5_0off = add i64 %t5_0row, 0
  %t5_0idx = add i64 %tb5, %t5_0off
  %t5_0ptr = getelementptr i8, ptr %src, i64 %t5_0idx
  %t5_0raw = load i8, ptr %t5_0ptr, align 1
  %t5_0 = zext i8 %t5_0raw to i32
  %t5_1row = mul i64 %srcW, 0
  %t5_1off = add i64 %t5_1row, 1
  %t5_1idx = add i64 %tb5, %t5_1off
  %t5_1ptr = getelementptr i8, ptr %src, i64 %t5_1idx
  %t5_1raw = load i8, ptr %t5_1ptr, align 1
  %t5_1 = zext i8 %t5_1raw to i32
  %t5_2row = mul i64 %srcW, 0
  %t5_2off = add i64 %t5_2row, 2
  %t5_2idx = add i64 %tb5, %t5_2off
  %t5_2ptr = getelementptr i8, ptr %src, i64 %t5_2idx
  %t5_2raw = load i8, ptr %t5_2ptr, align 1
  %t5_2 = zext i8 %t5_2raw to i32
  %t5_3row = mul i64 %srcW, 1
  %t5_3off = add i64 %t5_3row, 0
  %t5_3idx = add i64 %tb5, %t5_3off
  %t5_3ptr = getelementptr i8, ptr %src, i64 %t5_3idx
  %t5_3raw = load i8, ptr %t5_3ptr, align 1
  %t5_3 = zext i8 %t5_3raw to i32
  %t5_4row = mul i64 %srcW, 1
  %t5_4off = add i64 %t5_4row, 1
  %t5_4idx = add i64 %tb5, %t5_4off
  %t5_4ptr = getelementptr i8, ptr %src, i64 %t5_4idx
  %t5_4raw = load i8, ptr %t5_4ptr, align 1
  %t5_4 = zext i8 %t5_4raw to i32
  %t5_5row = mul i64 %srcW, 1
  %t5_5off = add i64 %t5_5row, 2
  %t5_5idx = add i64 %tb5, %t5_5off
  %t5_5ptr = getelementptr i8, ptr %src, i64 %t5_5idx
  %t5_5raw = load i8, ptr %t5_5ptr, align 1
  %t5_5 = zext i8 %t5_5raw to i32
  %t5_6row = mul i64 %srcW, 2
  %t5_6off = add i64 %t5_6row, 0
  %t5_6idx = add i64 %tb5, %t5_6off
  %t5_6ptr = getelementptr i8, ptr %src, i64 %t5_6idx
  %t5_6raw = load i8, ptr %t5_6ptr, align 1
  %t5_6 = zext i8 %t5_6raw to i32
  %t5_7row = mul i64 %srcW, 2
  %t5_7off = add i64 %t5_7row, 1
  %t5_7idx = add i64 %tb5, %t5_7off
  %t5_7ptr = getelementptr i8, ptr %src, i64 %t5_7idx
  %t5_7raw = load i8, ptr %t5_7ptr, align 1
  %t5_7 = zext i8 %t5_7raw to i32
  %t5_8row = mul i64 %srcW, 2
  %t5_8off = add i64 %t5_8row, 2
  %t5_8idx = add i64 %tb5, %t5_8off
  %t5_8ptr = getelementptr i8, ptr %src, i64 %t5_8idx
  %t5_8raw = load i8, ptr %t5_8ptr, align 1
  %t5_8 = zext i8 %t5_8raw to i32
  %ts5_1 = add i32 %t5_0, %t5_1
  %ts5_2 = add i32 %ts5_1, %t5_2
  %ts5_3 = add i32 %ts5_2, %t5_3
  %ts5_4 = add i32 %ts5_3, %t5_4
  %ts5_5 = add i32 %ts5_4, %t5_5
  %ts5_6 = add i32 %ts5_5, %t5_6
  %ts5_7 = add i32 %ts5_6, %t5_7
  %ts5_8 = add i32 %ts5_7, %t5_8
  %ta5 = add i32 %ts5_8, 4
  %tm5 = mul i32 %ta5, 7282
  %tv5 = lshr i32 %tm5, 16
  %third5 = insertelement <16 x i32> %third4, i32 %tv5, i64 5
  %tx6 = add i64 %bxi, 6
  %txs6 = mul i64 %tx6, 3
  %tb6 = add i64 %tr, %txs6
  %t6_0row = mul i64 %srcW, 0
  %t6_0off = add i64 %t6_0row, 0
  %t6_0idx = add i64 %tb6, %t6_0off
  %t6_0ptr = getelementptr i8, ptr %src, i64 %t6_0idx
  %t6_0raw = load i8, ptr %t6_0ptr, align 1
  %t6_0 = zext i8 %t6_0raw to i32
  %t6_1row = mul i64 %srcW, 0
  %t6_1off = add i64 %t6_1row, 1
  %t6_1idx = add i64 %tb6, %t6_1off
  %t6_1ptr = getelementptr i8, ptr %src, i64 %t6_1idx
  %t6_1raw = load i8, ptr %t6_1ptr, align 1
  %t6_1 = zext i8 %t6_1raw to i32
  %t6_2row = mul i64 %srcW, 0
  %t6_2off = add i64 %t6_2row, 2
  %t6_2idx = add i64 %tb6, %t6_2off
  %t6_2ptr = getelementptr i8, ptr %src, i64 %t6_2idx
  %t6_2raw = load i8, ptr %t6_2ptr, align 1
  %t6_2 = zext i8 %t6_2raw to i32
  %t6_3row = mul i64 %srcW, 1
  %t6_3off = add i64 %t6_3row, 0
  %t6_3idx = add i64 %tb6, %t6_3off
  %t6_3ptr = getelementptr i8, ptr %src, i64 %t6_3idx
  %t6_3raw = load i8, ptr %t6_3ptr, align 1
  %t6_3 = zext i8 %t6_3raw to i32
  %t6_4row = mul i64 %srcW, 1
  %t6_4off = add i64 %t6_4row, 1
  %t6_4idx = add i64 %tb6, %t6_4off
  %t6_4ptr = getelementptr i8, ptr %src, i64 %t6_4idx
  %t6_4raw = load i8, ptr %t6_4ptr, align 1
  %t6_4 = zext i8 %t6_4raw to i32
  %t6_5row = mul i64 %srcW, 1
  %t6_5off = add i64 %t6_5row, 2
  %t6_5idx = add i64 %tb6, %t6_5off
  %t6_5ptr = getelementptr i8, ptr %src, i64 %t6_5idx
  %t6_5raw = load i8, ptr %t6_5ptr, align 1
  %t6_5 = zext i8 %t6_5raw to i32
  %t6_6row = mul i64 %srcW, 2
  %t6_6off = add i64 %t6_6row, 0
  %t6_6idx = add i64 %tb6, %t6_6off
  %t6_6ptr = getelementptr i8, ptr %src, i64 %t6_6idx
  %t6_6raw = load i8, ptr %t6_6ptr, align 1
  %t6_6 = zext i8 %t6_6raw to i32
  %t6_7row = mul i64 %srcW, 2
  %t6_7off = add i64 %t6_7row, 1
  %t6_7idx = add i64 %tb6, %t6_7off
  %t6_7ptr = getelementptr i8, ptr %src, i64 %t6_7idx
  %t6_7raw = load i8, ptr %t6_7ptr, align 1
  %t6_7 = zext i8 %t6_7raw to i32
  %t6_8row = mul i64 %srcW, 2
  %t6_8off = add i64 %t6_8row, 2
  %t6_8idx = add i64 %tb6, %t6_8off
  %t6_8ptr = getelementptr i8, ptr %src, i64 %t6_8idx
  %t6_8raw = load i8, ptr %t6_8ptr, align 1
  %t6_8 = zext i8 %t6_8raw to i32
  %ts6_1 = add i32 %t6_0, %t6_1
  %ts6_2 = add i32 %ts6_1, %t6_2
  %ts6_3 = add i32 %ts6_2, %t6_3
  %ts6_4 = add i32 %ts6_3, %t6_4
  %ts6_5 = add i32 %ts6_4, %t6_5
  %ts6_6 = add i32 %ts6_5, %t6_6
  %ts6_7 = add i32 %ts6_6, %t6_7
  %ts6_8 = add i32 %ts6_7, %t6_8
  %ta6 = add i32 %ts6_8, 4
  %tm6 = mul i32 %ta6, 7282
  %tv6 = lshr i32 %tm6, 16
  %third6 = insertelement <16 x i32> %third5, i32 %tv6, i64 6
  %tx7 = add i64 %bxi, 7
  %txs7 = mul i64 %tx7, 3
  %tb7 = add i64 %tr, %txs7
  %t7_0row = mul i64 %srcW, 0
  %t7_0off = add i64 %t7_0row, 0
  %t7_0idx = add i64 %tb7, %t7_0off
  %t7_0ptr = getelementptr i8, ptr %src, i64 %t7_0idx
  %t7_0raw = load i8, ptr %t7_0ptr, align 1
  %t7_0 = zext i8 %t7_0raw to i32
  %t7_1row = mul i64 %srcW, 0
  %t7_1off = add i64 %t7_1row, 1
  %t7_1idx = add i64 %tb7, %t7_1off
  %t7_1ptr = getelementptr i8, ptr %src, i64 %t7_1idx
  %t7_1raw = load i8, ptr %t7_1ptr, align 1
  %t7_1 = zext i8 %t7_1raw to i32
  %t7_2row = mul i64 %srcW, 0
  %t7_2off = add i64 %t7_2row, 2
  %t7_2idx = add i64 %tb7, %t7_2off
  %t7_2ptr = getelementptr i8, ptr %src, i64 %t7_2idx
  %t7_2raw = load i8, ptr %t7_2ptr, align 1
  %t7_2 = zext i8 %t7_2raw to i32
  %t7_3row = mul i64 %srcW, 1
  %t7_3off = add i64 %t7_3row, 0
  %t7_3idx = add i64 %tb7, %t7_3off
  %t7_3ptr = getelementptr i8, ptr %src, i64 %t7_3idx
  %t7_3raw = load i8, ptr %t7_3ptr, align 1
  %t7_3 = zext i8 %t7_3raw to i32
  %t7_4row = mul i64 %srcW, 1
  %t7_4off = add i64 %t7_4row, 1
  %t7_4idx = add i64 %tb7, %t7_4off
  %t7_4ptr = getelementptr i8, ptr %src, i64 %t7_4idx
  %t7_4raw = load i8, ptr %t7_4ptr, align 1
  %t7_4 = zext i8 %t7_4raw to i32
  %t7_5row = mul i64 %srcW, 1
  %t7_5off = add i64 %t7_5row, 2
  %t7_5idx = add i64 %tb7, %t7_5off
  %t7_5ptr = getelementptr i8, ptr %src, i64 %t7_5idx
  %t7_5raw = load i8, ptr %t7_5ptr, align 1
  %t7_5 = zext i8 %t7_5raw to i32
  %t7_6row = mul i64 %srcW, 2
  %t7_6off = add i64 %t7_6row, 0
  %t7_6idx = add i64 %tb7, %t7_6off
  %t7_6ptr = getelementptr i8, ptr %src, i64 %t7_6idx
  %t7_6raw = load i8, ptr %t7_6ptr, align 1
  %t7_6 = zext i8 %t7_6raw to i32
  %t7_7row = mul i64 %srcW, 2
  %t7_7off = add i64 %t7_7row, 1
  %t7_7idx = add i64 %tb7, %t7_7off
  %t7_7ptr = getelementptr i8, ptr %src, i64 %t7_7idx
  %t7_7raw = load i8, ptr %t7_7ptr, align 1
  %t7_7 = zext i8 %t7_7raw to i32
  %t7_8row = mul i64 %srcW, 2
  %t7_8off = add i64 %t7_8row, 2
  %t7_8idx = add i64 %tb7, %t7_8off
  %t7_8ptr = getelementptr i8, ptr %src, i64 %t7_8idx
  %t7_8raw = load i8, ptr %t7_8ptr, align 1
  %t7_8 = zext i8 %t7_8raw to i32
  %ts7_1 = add i32 %t7_0, %t7_1
  %ts7_2 = add i32 %ts7_1, %t7_2
  %ts7_3 = add i32 %ts7_2, %t7_3
  %ts7_4 = add i32 %ts7_3, %t7_4
  %ts7_5 = add i32 %ts7_4, %t7_5
  %ts7_6 = add i32 %ts7_5, %t7_6
  %ts7_7 = add i32 %ts7_6, %t7_7
  %ts7_8 = add i32 %ts7_7, %t7_8
  %ta7 = add i32 %ts7_8, 4
  %tm7 = mul i32 %ta7, 7282
  %tv7 = lshr i32 %tm7, 16
  %third7 = insertelement <16 x i32> %third6, i32 %tv7, i64 7
  %tx8 = add i64 %bxi, 8
  %txs8 = mul i64 %tx8, 3
  %tb8 = add i64 %tr, %txs8
  %t8_0row = mul i64 %srcW, 0
  %t8_0off = add i64 %t8_0row, 0
  %t8_0idx = add i64 %tb8, %t8_0off
  %t8_0ptr = getelementptr i8, ptr %src, i64 %t8_0idx
  %t8_0raw = load i8, ptr %t8_0ptr, align 1
  %t8_0 = zext i8 %t8_0raw to i32
  %t8_1row = mul i64 %srcW, 0
  %t8_1off = add i64 %t8_1row, 1
  %t8_1idx = add i64 %tb8, %t8_1off
  %t8_1ptr = getelementptr i8, ptr %src, i64 %t8_1idx
  %t8_1raw = load i8, ptr %t8_1ptr, align 1
  %t8_1 = zext i8 %t8_1raw to i32
  %t8_2row = mul i64 %srcW, 0
  %t8_2off = add i64 %t8_2row, 2
  %t8_2idx = add i64 %tb8, %t8_2off
  %t8_2ptr = getelementptr i8, ptr %src, i64 %t8_2idx
  %t8_2raw = load i8, ptr %t8_2ptr, align 1
  %t8_2 = zext i8 %t8_2raw to i32
  %t8_3row = mul i64 %srcW, 1
  %t8_3off = add i64 %t8_3row, 0
  %t8_3idx = add i64 %tb8, %t8_3off
  %t8_3ptr = getelementptr i8, ptr %src, i64 %t8_3idx
  %t8_3raw = load i8, ptr %t8_3ptr, align 1
  %t8_3 = zext i8 %t8_3raw to i32
  %t8_4row = mul i64 %srcW, 1
  %t8_4off = add i64 %t8_4row, 1
  %t8_4idx = add i64 %tb8, %t8_4off
  %t8_4ptr = getelementptr i8, ptr %src, i64 %t8_4idx
  %t8_4raw = load i8, ptr %t8_4ptr, align 1
  %t8_4 = zext i8 %t8_4raw to i32
  %t8_5row = mul i64 %srcW, 1
  %t8_5off = add i64 %t8_5row, 2
  %t8_5idx = add i64 %tb8, %t8_5off
  %t8_5ptr = getelementptr i8, ptr %src, i64 %t8_5idx
  %t8_5raw = load i8, ptr %t8_5ptr, align 1
  %t8_5 = zext i8 %t8_5raw to i32
  %t8_6row = mul i64 %srcW, 2
  %t8_6off = add i64 %t8_6row, 0
  %t8_6idx = add i64 %tb8, %t8_6off
  %t8_6ptr = getelementptr i8, ptr %src, i64 %t8_6idx
  %t8_6raw = load i8, ptr %t8_6ptr, align 1
  %t8_6 = zext i8 %t8_6raw to i32
  %t8_7row = mul i64 %srcW, 2
  %t8_7off = add i64 %t8_7row, 1
  %t8_7idx = add i64 %tb8, %t8_7off
  %t8_7ptr = getelementptr i8, ptr %src, i64 %t8_7idx
  %t8_7raw = load i8, ptr %t8_7ptr, align 1
  %t8_7 = zext i8 %t8_7raw to i32
  %t8_8row = mul i64 %srcW, 2
  %t8_8off = add i64 %t8_8row, 2
  %t8_8idx = add i64 %tb8, %t8_8off
  %t8_8ptr = getelementptr i8, ptr %src, i64 %t8_8idx
  %t8_8raw = load i8, ptr %t8_8ptr, align 1
  %t8_8 = zext i8 %t8_8raw to i32
  %ts8_1 = add i32 %t8_0, %t8_1
  %ts8_2 = add i32 %ts8_1, %t8_2
  %ts8_3 = add i32 %ts8_2, %t8_3
  %ts8_4 = add i32 %ts8_3, %t8_4
  %ts8_5 = add i32 %ts8_4, %t8_5
  %ts8_6 = add i32 %ts8_5, %t8_6
  %ts8_7 = add i32 %ts8_6, %t8_7
  %ts8_8 = add i32 %ts8_7, %t8_8
  %ta8 = add i32 %ts8_8, 4
  %tm8 = mul i32 %ta8, 7282
  %tv8 = lshr i32 %tm8, 16
  %third8 = insertelement <16 x i32> %third7, i32 %tv8, i64 8
  %tx9 = add i64 %bxi, 9
  %txs9 = mul i64 %tx9, 3
  %tb9 = add i64 %tr, %txs9
  %t9_0row = mul i64 %srcW, 0
  %t9_0off = add i64 %t9_0row, 0
  %t9_0idx = add i64 %tb9, %t9_0off
  %t9_0ptr = getelementptr i8, ptr %src, i64 %t9_0idx
  %t9_0raw = load i8, ptr %t9_0ptr, align 1
  %t9_0 = zext i8 %t9_0raw to i32
  %t9_1row = mul i64 %srcW, 0
  %t9_1off = add i64 %t9_1row, 1
  %t9_1idx = add i64 %tb9, %t9_1off
  %t9_1ptr = getelementptr i8, ptr %src, i64 %t9_1idx
  %t9_1raw = load i8, ptr %t9_1ptr, align 1
  %t9_1 = zext i8 %t9_1raw to i32
  %t9_2row = mul i64 %srcW, 0
  %t9_2off = add i64 %t9_2row, 2
  %t9_2idx = add i64 %tb9, %t9_2off
  %t9_2ptr = getelementptr i8, ptr %src, i64 %t9_2idx
  %t9_2raw = load i8, ptr %t9_2ptr, align 1
  %t9_2 = zext i8 %t9_2raw to i32
  %t9_3row = mul i64 %srcW, 1
  %t9_3off = add i64 %t9_3row, 0
  %t9_3idx = add i64 %tb9, %t9_3off
  %t9_3ptr = getelementptr i8, ptr %src, i64 %t9_3idx
  %t9_3raw = load i8, ptr %t9_3ptr, align 1
  %t9_3 = zext i8 %t9_3raw to i32
  %t9_4row = mul i64 %srcW, 1
  %t9_4off = add i64 %t9_4row, 1
  %t9_4idx = add i64 %tb9, %t9_4off
  %t9_4ptr = getelementptr i8, ptr %src, i64 %t9_4idx
  %t9_4raw = load i8, ptr %t9_4ptr, align 1
  %t9_4 = zext i8 %t9_4raw to i32
  %t9_5row = mul i64 %srcW, 1
  %t9_5off = add i64 %t9_5row, 2
  %t9_5idx = add i64 %tb9, %t9_5off
  %t9_5ptr = getelementptr i8, ptr %src, i64 %t9_5idx
  %t9_5raw = load i8, ptr %t9_5ptr, align 1
  %t9_5 = zext i8 %t9_5raw to i32
  %t9_6row = mul i64 %srcW, 2
  %t9_6off = add i64 %t9_6row, 0
  %t9_6idx = add i64 %tb9, %t9_6off
  %t9_6ptr = getelementptr i8, ptr %src, i64 %t9_6idx
  %t9_6raw = load i8, ptr %t9_6ptr, align 1
  %t9_6 = zext i8 %t9_6raw to i32
  %t9_7row = mul i64 %srcW, 2
  %t9_7off = add i64 %t9_7row, 1
  %t9_7idx = add i64 %tb9, %t9_7off
  %t9_7ptr = getelementptr i8, ptr %src, i64 %t9_7idx
  %t9_7raw = load i8, ptr %t9_7ptr, align 1
  %t9_7 = zext i8 %t9_7raw to i32
  %t9_8row = mul i64 %srcW, 2
  %t9_8off = add i64 %t9_8row, 2
  %t9_8idx = add i64 %tb9, %t9_8off
  %t9_8ptr = getelementptr i8, ptr %src, i64 %t9_8idx
  %t9_8raw = load i8, ptr %t9_8ptr, align 1
  %t9_8 = zext i8 %t9_8raw to i32
  %ts9_1 = add i32 %t9_0, %t9_1
  %ts9_2 = add i32 %ts9_1, %t9_2
  %ts9_3 = add i32 %ts9_2, %t9_3
  %ts9_4 = add i32 %ts9_3, %t9_4
  %ts9_5 = add i32 %ts9_4, %t9_5
  %ts9_6 = add i32 %ts9_5, %t9_6
  %ts9_7 = add i32 %ts9_6, %t9_7
  %ts9_8 = add i32 %ts9_7, %t9_8
  %ta9 = add i32 %ts9_8, 4
  %tm9 = mul i32 %ta9, 7282
  %tv9 = lshr i32 %tm9, 16
  %third9 = insertelement <16 x i32> %third8, i32 %tv9, i64 9
  %tx10 = add i64 %bxi, 10
  %txs10 = mul i64 %tx10, 3
  %tb10 = add i64 %tr, %txs10
  %t10_0row = mul i64 %srcW, 0
  %t10_0off = add i64 %t10_0row, 0
  %t10_0idx = add i64 %tb10, %t10_0off
  %t10_0ptr = getelementptr i8, ptr %src, i64 %t10_0idx
  %t10_0raw = load i8, ptr %t10_0ptr, align 1
  %t10_0 = zext i8 %t10_0raw to i32
  %t10_1row = mul i64 %srcW, 0
  %t10_1off = add i64 %t10_1row, 1
  %t10_1idx = add i64 %tb10, %t10_1off
  %t10_1ptr = getelementptr i8, ptr %src, i64 %t10_1idx
  %t10_1raw = load i8, ptr %t10_1ptr, align 1
  %t10_1 = zext i8 %t10_1raw to i32
  %t10_2row = mul i64 %srcW, 0
  %t10_2off = add i64 %t10_2row, 2
  %t10_2idx = add i64 %tb10, %t10_2off
  %t10_2ptr = getelementptr i8, ptr %src, i64 %t10_2idx
  %t10_2raw = load i8, ptr %t10_2ptr, align 1
  %t10_2 = zext i8 %t10_2raw to i32
  %t10_3row = mul i64 %srcW, 1
  %t10_3off = add i64 %t10_3row, 0
  %t10_3idx = add i64 %tb10, %t10_3off
  %t10_3ptr = getelementptr i8, ptr %src, i64 %t10_3idx
  %t10_3raw = load i8, ptr %t10_3ptr, align 1
  %t10_3 = zext i8 %t10_3raw to i32
  %t10_4row = mul i64 %srcW, 1
  %t10_4off = add i64 %t10_4row, 1
  %t10_4idx = add i64 %tb10, %t10_4off
  %t10_4ptr = getelementptr i8, ptr %src, i64 %t10_4idx
  %t10_4raw = load i8, ptr %t10_4ptr, align 1
  %t10_4 = zext i8 %t10_4raw to i32
  %t10_5row = mul i64 %srcW, 1
  %t10_5off = add i64 %t10_5row, 2
  %t10_5idx = add i64 %tb10, %t10_5off
  %t10_5ptr = getelementptr i8, ptr %src, i64 %t10_5idx
  %t10_5raw = load i8, ptr %t10_5ptr, align 1
  %t10_5 = zext i8 %t10_5raw to i32
  %t10_6row = mul i64 %srcW, 2
  %t10_6off = add i64 %t10_6row, 0
  %t10_6idx = add i64 %tb10, %t10_6off
  %t10_6ptr = getelementptr i8, ptr %src, i64 %t10_6idx
  %t10_6raw = load i8, ptr %t10_6ptr, align 1
  %t10_6 = zext i8 %t10_6raw to i32
  %t10_7row = mul i64 %srcW, 2
  %t10_7off = add i64 %t10_7row, 1
  %t10_7idx = add i64 %tb10, %t10_7off
  %t10_7ptr = getelementptr i8, ptr %src, i64 %t10_7idx
  %t10_7raw = load i8, ptr %t10_7ptr, align 1
  %t10_7 = zext i8 %t10_7raw to i32
  %t10_8row = mul i64 %srcW, 2
  %t10_8off = add i64 %t10_8row, 2
  %t10_8idx = add i64 %tb10, %t10_8off
  %t10_8ptr = getelementptr i8, ptr %src, i64 %t10_8idx
  %t10_8raw = load i8, ptr %t10_8ptr, align 1
  %t10_8 = zext i8 %t10_8raw to i32
  %ts10_1 = add i32 %t10_0, %t10_1
  %ts10_2 = add i32 %ts10_1, %t10_2
  %ts10_3 = add i32 %ts10_2, %t10_3
  %ts10_4 = add i32 %ts10_3, %t10_4
  %ts10_5 = add i32 %ts10_4, %t10_5
  %ts10_6 = add i32 %ts10_5, %t10_6
  %ts10_7 = add i32 %ts10_6, %t10_7
  %ts10_8 = add i32 %ts10_7, %t10_8
  %ta10 = add i32 %ts10_8, 4
  %tm10 = mul i32 %ta10, 7282
  %tv10 = lshr i32 %tm10, 16
  %third10 = insertelement <16 x i32> %third9, i32 %tv10, i64 10
  %tx11 = add i64 %bxi, 11
  %txs11 = mul i64 %tx11, 3
  %tb11 = add i64 %tr, %txs11
  %t11_0row = mul i64 %srcW, 0
  %t11_0off = add i64 %t11_0row, 0
  %t11_0idx = add i64 %tb11, %t11_0off
  %t11_0ptr = getelementptr i8, ptr %src, i64 %t11_0idx
  %t11_0raw = load i8, ptr %t11_0ptr, align 1
  %t11_0 = zext i8 %t11_0raw to i32
  %t11_1row = mul i64 %srcW, 0
  %t11_1off = add i64 %t11_1row, 1
  %t11_1idx = add i64 %tb11, %t11_1off
  %t11_1ptr = getelementptr i8, ptr %src, i64 %t11_1idx
  %t11_1raw = load i8, ptr %t11_1ptr, align 1
  %t11_1 = zext i8 %t11_1raw to i32
  %t11_2row = mul i64 %srcW, 0
  %t11_2off = add i64 %t11_2row, 2
  %t11_2idx = add i64 %tb11, %t11_2off
  %t11_2ptr = getelementptr i8, ptr %src, i64 %t11_2idx
  %t11_2raw = load i8, ptr %t11_2ptr, align 1
  %t11_2 = zext i8 %t11_2raw to i32
  %t11_3row = mul i64 %srcW, 1
  %t11_3off = add i64 %t11_3row, 0
  %t11_3idx = add i64 %tb11, %t11_3off
  %t11_3ptr = getelementptr i8, ptr %src, i64 %t11_3idx
  %t11_3raw = load i8, ptr %t11_3ptr, align 1
  %t11_3 = zext i8 %t11_3raw to i32
  %t11_4row = mul i64 %srcW, 1
  %t11_4off = add i64 %t11_4row, 1
  %t11_4idx = add i64 %tb11, %t11_4off
  %t11_4ptr = getelementptr i8, ptr %src, i64 %t11_4idx
  %t11_4raw = load i8, ptr %t11_4ptr, align 1
  %t11_4 = zext i8 %t11_4raw to i32
  %t11_5row = mul i64 %srcW, 1
  %t11_5off = add i64 %t11_5row, 2
  %t11_5idx = add i64 %tb11, %t11_5off
  %t11_5ptr = getelementptr i8, ptr %src, i64 %t11_5idx
  %t11_5raw = load i8, ptr %t11_5ptr, align 1
  %t11_5 = zext i8 %t11_5raw to i32
  %t11_6row = mul i64 %srcW, 2
  %t11_6off = add i64 %t11_6row, 0
  %t11_6idx = add i64 %tb11, %t11_6off
  %t11_6ptr = getelementptr i8, ptr %src, i64 %t11_6idx
  %t11_6raw = load i8, ptr %t11_6ptr, align 1
  %t11_6 = zext i8 %t11_6raw to i32
  %t11_7row = mul i64 %srcW, 2
  %t11_7off = add i64 %t11_7row, 1
  %t11_7idx = add i64 %tb11, %t11_7off
  %t11_7ptr = getelementptr i8, ptr %src, i64 %t11_7idx
  %t11_7raw = load i8, ptr %t11_7ptr, align 1
  %t11_7 = zext i8 %t11_7raw to i32
  %t11_8row = mul i64 %srcW, 2
  %t11_8off = add i64 %t11_8row, 2
  %t11_8idx = add i64 %tb11, %t11_8off
  %t11_8ptr = getelementptr i8, ptr %src, i64 %t11_8idx
  %t11_8raw = load i8, ptr %t11_8ptr, align 1
  %t11_8 = zext i8 %t11_8raw to i32
  %ts11_1 = add i32 %t11_0, %t11_1
  %ts11_2 = add i32 %ts11_1, %t11_2
  %ts11_3 = add i32 %ts11_2, %t11_3
  %ts11_4 = add i32 %ts11_3, %t11_4
  %ts11_5 = add i32 %ts11_4, %t11_5
  %ts11_6 = add i32 %ts11_5, %t11_6
  %ts11_7 = add i32 %ts11_6, %t11_7
  %ts11_8 = add i32 %ts11_7, %t11_8
  %ta11 = add i32 %ts11_8, 4
  %tm11 = mul i32 %ta11, 7282
  %tv11 = lshr i32 %tm11, 16
  %third11 = insertelement <16 x i32> %third10, i32 %tv11, i64 11
  %tx12 = add i64 %bxi, 12
  %txs12 = mul i64 %tx12, 3
  %tb12 = add i64 %tr, %txs12
  %t12_0row = mul i64 %srcW, 0
  %t12_0off = add i64 %t12_0row, 0
  %t12_0idx = add i64 %tb12, %t12_0off
  %t12_0ptr = getelementptr i8, ptr %src, i64 %t12_0idx
  %t12_0raw = load i8, ptr %t12_0ptr, align 1
  %t12_0 = zext i8 %t12_0raw to i32
  %t12_1row = mul i64 %srcW, 0
  %t12_1off = add i64 %t12_1row, 1
  %t12_1idx = add i64 %tb12, %t12_1off
  %t12_1ptr = getelementptr i8, ptr %src, i64 %t12_1idx
  %t12_1raw = load i8, ptr %t12_1ptr, align 1
  %t12_1 = zext i8 %t12_1raw to i32
  %t12_2row = mul i64 %srcW, 0
  %t12_2off = add i64 %t12_2row, 2
  %t12_2idx = add i64 %tb12, %t12_2off
  %t12_2ptr = getelementptr i8, ptr %src, i64 %t12_2idx
  %t12_2raw = load i8, ptr %t12_2ptr, align 1
  %t12_2 = zext i8 %t12_2raw to i32
  %t12_3row = mul i64 %srcW, 1
  %t12_3off = add i64 %t12_3row, 0
  %t12_3idx = add i64 %tb12, %t12_3off
  %t12_3ptr = getelementptr i8, ptr %src, i64 %t12_3idx
  %t12_3raw = load i8, ptr %t12_3ptr, align 1
  %t12_3 = zext i8 %t12_3raw to i32
  %t12_4row = mul i64 %srcW, 1
  %t12_4off = add i64 %t12_4row, 1
  %t12_4idx = add i64 %tb12, %t12_4off
  %t12_4ptr = getelementptr i8, ptr %src, i64 %t12_4idx
  %t12_4raw = load i8, ptr %t12_4ptr, align 1
  %t12_4 = zext i8 %t12_4raw to i32
  %t12_5row = mul i64 %srcW, 1
  %t12_5off = add i64 %t12_5row, 2
  %t12_5idx = add i64 %tb12, %t12_5off
  %t12_5ptr = getelementptr i8, ptr %src, i64 %t12_5idx
  %t12_5raw = load i8, ptr %t12_5ptr, align 1
  %t12_5 = zext i8 %t12_5raw to i32
  %t12_6row = mul i64 %srcW, 2
  %t12_6off = add i64 %t12_6row, 0
  %t12_6idx = add i64 %tb12, %t12_6off
  %t12_6ptr = getelementptr i8, ptr %src, i64 %t12_6idx
  %t12_6raw = load i8, ptr %t12_6ptr, align 1
  %t12_6 = zext i8 %t12_6raw to i32
  %t12_7row = mul i64 %srcW, 2
  %t12_7off = add i64 %t12_7row, 1
  %t12_7idx = add i64 %tb12, %t12_7off
  %t12_7ptr = getelementptr i8, ptr %src, i64 %t12_7idx
  %t12_7raw = load i8, ptr %t12_7ptr, align 1
  %t12_7 = zext i8 %t12_7raw to i32
  %t12_8row = mul i64 %srcW, 2
  %t12_8off = add i64 %t12_8row, 2
  %t12_8idx = add i64 %tb12, %t12_8off
  %t12_8ptr = getelementptr i8, ptr %src, i64 %t12_8idx
  %t12_8raw = load i8, ptr %t12_8ptr, align 1
  %t12_8 = zext i8 %t12_8raw to i32
  %ts12_1 = add i32 %t12_0, %t12_1
  %ts12_2 = add i32 %ts12_1, %t12_2
  %ts12_3 = add i32 %ts12_2, %t12_3
  %ts12_4 = add i32 %ts12_3, %t12_4
  %ts12_5 = add i32 %ts12_4, %t12_5
  %ts12_6 = add i32 %ts12_5, %t12_6
  %ts12_7 = add i32 %ts12_6, %t12_7
  %ts12_8 = add i32 %ts12_7, %t12_8
  %ta12 = add i32 %ts12_8, 4
  %tm12 = mul i32 %ta12, 7282
  %tv12 = lshr i32 %tm12, 16
  %third12 = insertelement <16 x i32> %third11, i32 %tv12, i64 12
  %tx13 = add i64 %bxi, 13
  %txs13 = mul i64 %tx13, 3
  %tb13 = add i64 %tr, %txs13
  %t13_0row = mul i64 %srcW, 0
  %t13_0off = add i64 %t13_0row, 0
  %t13_0idx = add i64 %tb13, %t13_0off
  %t13_0ptr = getelementptr i8, ptr %src, i64 %t13_0idx
  %t13_0raw = load i8, ptr %t13_0ptr, align 1
  %t13_0 = zext i8 %t13_0raw to i32
  %t13_1row = mul i64 %srcW, 0
  %t13_1off = add i64 %t13_1row, 1
  %t13_1idx = add i64 %tb13, %t13_1off
  %t13_1ptr = getelementptr i8, ptr %src, i64 %t13_1idx
  %t13_1raw = load i8, ptr %t13_1ptr, align 1
  %t13_1 = zext i8 %t13_1raw to i32
  %t13_2row = mul i64 %srcW, 0
  %t13_2off = add i64 %t13_2row, 2
  %t13_2idx = add i64 %tb13, %t13_2off
  %t13_2ptr = getelementptr i8, ptr %src, i64 %t13_2idx
  %t13_2raw = load i8, ptr %t13_2ptr, align 1
  %t13_2 = zext i8 %t13_2raw to i32
  %t13_3row = mul i64 %srcW, 1
  %t13_3off = add i64 %t13_3row, 0
  %t13_3idx = add i64 %tb13, %t13_3off
  %t13_3ptr = getelementptr i8, ptr %src, i64 %t13_3idx
  %t13_3raw = load i8, ptr %t13_3ptr, align 1
  %t13_3 = zext i8 %t13_3raw to i32
  %t13_4row = mul i64 %srcW, 1
  %t13_4off = add i64 %t13_4row, 1
  %t13_4idx = add i64 %tb13, %t13_4off
  %t13_4ptr = getelementptr i8, ptr %src, i64 %t13_4idx
  %t13_4raw = load i8, ptr %t13_4ptr, align 1
  %t13_4 = zext i8 %t13_4raw to i32
  %t13_5row = mul i64 %srcW, 1
  %t13_5off = add i64 %t13_5row, 2
  %t13_5idx = add i64 %tb13, %t13_5off
  %t13_5ptr = getelementptr i8, ptr %src, i64 %t13_5idx
  %t13_5raw = load i8, ptr %t13_5ptr, align 1
  %t13_5 = zext i8 %t13_5raw to i32
  %t13_6row = mul i64 %srcW, 2
  %t13_6off = add i64 %t13_6row, 0
  %t13_6idx = add i64 %tb13, %t13_6off
  %t13_6ptr = getelementptr i8, ptr %src, i64 %t13_6idx
  %t13_6raw = load i8, ptr %t13_6ptr, align 1
  %t13_6 = zext i8 %t13_6raw to i32
  %t13_7row = mul i64 %srcW, 2
  %t13_7off = add i64 %t13_7row, 1
  %t13_7idx = add i64 %tb13, %t13_7off
  %t13_7ptr = getelementptr i8, ptr %src, i64 %t13_7idx
  %t13_7raw = load i8, ptr %t13_7ptr, align 1
  %t13_7 = zext i8 %t13_7raw to i32
  %t13_8row = mul i64 %srcW, 2
  %t13_8off = add i64 %t13_8row, 2
  %t13_8idx = add i64 %tb13, %t13_8off
  %t13_8ptr = getelementptr i8, ptr %src, i64 %t13_8idx
  %t13_8raw = load i8, ptr %t13_8ptr, align 1
  %t13_8 = zext i8 %t13_8raw to i32
  %ts13_1 = add i32 %t13_0, %t13_1
  %ts13_2 = add i32 %ts13_1, %t13_2
  %ts13_3 = add i32 %ts13_2, %t13_3
  %ts13_4 = add i32 %ts13_3, %t13_4
  %ts13_5 = add i32 %ts13_4, %t13_5
  %ts13_6 = add i32 %ts13_5, %t13_6
  %ts13_7 = add i32 %ts13_6, %t13_7
  %ts13_8 = add i32 %ts13_7, %t13_8
  %ta13 = add i32 %ts13_8, 4
  %tm13 = mul i32 %ta13, 7282
  %tv13 = lshr i32 %tm13, 16
  %third13 = insertelement <16 x i32> %third12, i32 %tv13, i64 13
  %tx14 = add i64 %bxi, 14
  %txs14 = mul i64 %tx14, 3
  %tb14 = add i64 %tr, %txs14
  %t14_0row = mul i64 %srcW, 0
  %t14_0off = add i64 %t14_0row, 0
  %t14_0idx = add i64 %tb14, %t14_0off
  %t14_0ptr = getelementptr i8, ptr %src, i64 %t14_0idx
  %t14_0raw = load i8, ptr %t14_0ptr, align 1
  %t14_0 = zext i8 %t14_0raw to i32
  %t14_1row = mul i64 %srcW, 0
  %t14_1off = add i64 %t14_1row, 1
  %t14_1idx = add i64 %tb14, %t14_1off
  %t14_1ptr = getelementptr i8, ptr %src, i64 %t14_1idx
  %t14_1raw = load i8, ptr %t14_1ptr, align 1
  %t14_1 = zext i8 %t14_1raw to i32
  %t14_2row = mul i64 %srcW, 0
  %t14_2off = add i64 %t14_2row, 2
  %t14_2idx = add i64 %tb14, %t14_2off
  %t14_2ptr = getelementptr i8, ptr %src, i64 %t14_2idx
  %t14_2raw = load i8, ptr %t14_2ptr, align 1
  %t14_2 = zext i8 %t14_2raw to i32
  %t14_3row = mul i64 %srcW, 1
  %t14_3off = add i64 %t14_3row, 0
  %t14_3idx = add i64 %tb14, %t14_3off
  %t14_3ptr = getelementptr i8, ptr %src, i64 %t14_3idx
  %t14_3raw = load i8, ptr %t14_3ptr, align 1
  %t14_3 = zext i8 %t14_3raw to i32
  %t14_4row = mul i64 %srcW, 1
  %t14_4off = add i64 %t14_4row, 1
  %t14_4idx = add i64 %tb14, %t14_4off
  %t14_4ptr = getelementptr i8, ptr %src, i64 %t14_4idx
  %t14_4raw = load i8, ptr %t14_4ptr, align 1
  %t14_4 = zext i8 %t14_4raw to i32
  %t14_5row = mul i64 %srcW, 1
  %t14_5off = add i64 %t14_5row, 2
  %t14_5idx = add i64 %tb14, %t14_5off
  %t14_5ptr = getelementptr i8, ptr %src, i64 %t14_5idx
  %t14_5raw = load i8, ptr %t14_5ptr, align 1
  %t14_5 = zext i8 %t14_5raw to i32
  %t14_6row = mul i64 %srcW, 2
  %t14_6off = add i64 %t14_6row, 0
  %t14_6idx = add i64 %tb14, %t14_6off
  %t14_6ptr = getelementptr i8, ptr %src, i64 %t14_6idx
  %t14_6raw = load i8, ptr %t14_6ptr, align 1
  %t14_6 = zext i8 %t14_6raw to i32
  %t14_7row = mul i64 %srcW, 2
  %t14_7off = add i64 %t14_7row, 1
  %t14_7idx = add i64 %tb14, %t14_7off
  %t14_7ptr = getelementptr i8, ptr %src, i64 %t14_7idx
  %t14_7raw = load i8, ptr %t14_7ptr, align 1
  %t14_7 = zext i8 %t14_7raw to i32
  %t14_8row = mul i64 %srcW, 2
  %t14_8off = add i64 %t14_8row, 2
  %t14_8idx = add i64 %tb14, %t14_8off
  %t14_8ptr = getelementptr i8, ptr %src, i64 %t14_8idx
  %t14_8raw = load i8, ptr %t14_8ptr, align 1
  %t14_8 = zext i8 %t14_8raw to i32
  %ts14_1 = add i32 %t14_0, %t14_1
  %ts14_2 = add i32 %ts14_1, %t14_2
  %ts14_3 = add i32 %ts14_2, %t14_3
  %ts14_4 = add i32 %ts14_3, %t14_4
  %ts14_5 = add i32 %ts14_4, %t14_5
  %ts14_6 = add i32 %ts14_5, %t14_6
  %ts14_7 = add i32 %ts14_6, %t14_7
  %ts14_8 = add i32 %ts14_7, %t14_8
  %ta14 = add i32 %ts14_8, 4
  %tm14 = mul i32 %ta14, 7282
  %tv14 = lshr i32 %tm14, 16
  %third14 = insertelement <16 x i32> %third13, i32 %tv14, i64 14
  %tx15 = add i64 %bxi, 15
  %txs15 = mul i64 %tx15, 3
  %tb15 = add i64 %tr, %txs15
  %t15_0row = mul i64 %srcW, 0
  %t15_0off = add i64 %t15_0row, 0
  %t15_0idx = add i64 %tb15, %t15_0off
  %t15_0ptr = getelementptr i8, ptr %src, i64 %t15_0idx
  %t15_0raw = load i8, ptr %t15_0ptr, align 1
  %t15_0 = zext i8 %t15_0raw to i32
  %t15_1row = mul i64 %srcW, 0
  %t15_1off = add i64 %t15_1row, 1
  %t15_1idx = add i64 %tb15, %t15_1off
  %t15_1ptr = getelementptr i8, ptr %src, i64 %t15_1idx
  %t15_1raw = load i8, ptr %t15_1ptr, align 1
  %t15_1 = zext i8 %t15_1raw to i32
  %t15_2row = mul i64 %srcW, 0
  %t15_2off = add i64 %t15_2row, 2
  %t15_2idx = add i64 %tb15, %t15_2off
  %t15_2ptr = getelementptr i8, ptr %src, i64 %t15_2idx
  %t15_2raw = load i8, ptr %t15_2ptr, align 1
  %t15_2 = zext i8 %t15_2raw to i32
  %t15_3row = mul i64 %srcW, 1
  %t15_3off = add i64 %t15_3row, 0
  %t15_3idx = add i64 %tb15, %t15_3off
  %t15_3ptr = getelementptr i8, ptr %src, i64 %t15_3idx
  %t15_3raw = load i8, ptr %t15_3ptr, align 1
  %t15_3 = zext i8 %t15_3raw to i32
  %t15_4row = mul i64 %srcW, 1
  %t15_4off = add i64 %t15_4row, 1
  %t15_4idx = add i64 %tb15, %t15_4off
  %t15_4ptr = getelementptr i8, ptr %src, i64 %t15_4idx
  %t15_4raw = load i8, ptr %t15_4ptr, align 1
  %t15_4 = zext i8 %t15_4raw to i32
  %t15_5row = mul i64 %srcW, 1
  %t15_5off = add i64 %t15_5row, 2
  %t15_5idx = add i64 %tb15, %t15_5off
  %t15_5ptr = getelementptr i8, ptr %src, i64 %t15_5idx
  %t15_5raw = load i8, ptr %t15_5ptr, align 1
  %t15_5 = zext i8 %t15_5raw to i32
  %t15_6row = mul i64 %srcW, 2
  %t15_6off = add i64 %t15_6row, 0
  %t15_6idx = add i64 %tb15, %t15_6off
  %t15_6ptr = getelementptr i8, ptr %src, i64 %t15_6idx
  %t15_6raw = load i8, ptr %t15_6ptr, align 1
  %t15_6 = zext i8 %t15_6raw to i32
  %t15_7row = mul i64 %srcW, 2
  %t15_7off = add i64 %t15_7row, 1
  %t15_7idx = add i64 %tb15, %t15_7off
  %t15_7ptr = getelementptr i8, ptr %src, i64 %t15_7idx
  %t15_7raw = load i8, ptr %t15_7ptr, align 1
  %t15_7 = zext i8 %t15_7raw to i32
  %t15_8row = mul i64 %srcW, 2
  %t15_8off = add i64 %t15_8row, 2
  %t15_8idx = add i64 %tb15, %t15_8off
  %t15_8ptr = getelementptr i8, ptr %src, i64 %t15_8idx
  %t15_8raw = load i8, ptr %t15_8ptr, align 1
  %t15_8 = zext i8 %t15_8raw to i32
  %ts15_1 = add i32 %t15_0, %t15_1
  %ts15_2 = add i32 %ts15_1, %t15_2
  %ts15_3 = add i32 %ts15_2, %t15_3
  %ts15_4 = add i32 %ts15_3, %t15_4
  %ts15_5 = add i32 %ts15_4, %t15_5
  %ts15_6 = add i32 %ts15_5, %t15_6
  %ts15_7 = add i32 %ts15_6, %t15_7
  %ts15_8 = add i32 %ts15_7, %t15_8
  %ta15 = add i32 %ts15_8, 4
  %tm15 = mul i32 %ta15, 7282
  %tv15 = lshr i32 %tm15, 16
  %third15 = insertelement <16 x i32> %third14, i32 %tv15, i64 15
  br label %reduce
q8:
  %qyprod = mul i64 %dy, %srcH
  %qynum = shl i64 %qyprod, 8
  %qyq = udiv i64 %qynum, %dstH
  %qyraw0 = lshr i64 %qyq, 8
  %qylast = sub i64 %srcH, 1
  %qyin = icmp ult i64 %qyraw0, %srcH
  %qy0 = select i1 %qyin, i64 %qyraw0, i64 %qylast
  %qynext = add i64 %qy0, 1
  %qymore = icmp ult i64 %qynext, %srcH
  %qy1 = select i1 %qymore, i64 %qynext, i64 %qy0
  %qyfrac64 = and i64 %qyq, 255
  %qyf = trunc i64 %qyfrac64 to i32
  %qyinv = sub i32 256, %qyf
  %qr0 = mul i64 %qy0, %srcW
  %qr1 = mul i64 %qy1, %srcW
  %qdx0 = add i64 %bxi, 0
  %qx0prod = mul i64 %qdx0, %srcW
  %qx0num = shl i64 %qx0prod, 8
  %qx0q = udiv i64 %qx0num, %dstW
  %qx0raw0 = lshr i64 %qx0q, 8
  %qx0last = sub i64 %srcW, 1
  %qx0in = icmp ult i64 %qx0raw0, %srcW
  %qx00 = select i1 %qx0in, i64 %qx0raw0, i64 %qx0last
  %qx0next = add i64 %qx00, 1
  %qx0more = icmp ult i64 %qx0next, %srcW
  %qx01 = select i1 %qx0more, i64 %qx0next, i64 %qx00
  %qx0frac64 = and i64 %qx0q, 255
  %qx0f = trunc i64 %qx0frac64 to i32
  %qx0inv = sub i32 256, %qx0f
  %qp0_00idx = add i64 %qr0, %qx00
  %qp0_00ptr = getelementptr i8, ptr %src, i64 %qp0_00idx
  %qp0_00raw = load i8, ptr %qp0_00ptr, align 1
  %qp0_00 = zext i8 %qp0_00raw to i32
  %qp0_00w = mul i32 %qp0_00, %qx0inv
  %qp0_01idx = add i64 %qr0, %qx01
  %qp0_01ptr = getelementptr i8, ptr %src, i64 %qp0_01idx
  %qp0_01raw = load i8, ptr %qp0_01ptr, align 1
  %qp0_01 = zext i8 %qp0_01raw to i32
  %qp0_01w = mul i32 %qp0_01, %qx0f
  %qp0_10idx = add i64 %qr1, %qx00
  %qp0_10ptr = getelementptr i8, ptr %src, i64 %qp0_10idx
  %qp0_10raw = load i8, ptr %qp0_10ptr, align 1
  %qp0_10 = zext i8 %qp0_10raw to i32
  %qp0_10w = mul i32 %qp0_10, %qx0inv
  %qp0_11idx = add i64 %qr1, %qx01
  %qp0_11ptr = getelementptr i8, ptr %src, i64 %qp0_11idx
  %qp0_11raw = load i8, ptr %qp0_11ptr, align 1
  %qp0_11 = zext i8 %qp0_11raw to i32
  %qp0_11w = mul i32 %qp0_11, %qx0f
  %qt0 = add i32 %qp0_00w, %qp0_01w
  %qb0 = add i32 %qp0_10w, %qp0_11w
  %qtw0 = mul i32 %qt0, %qyinv
  %qbw0 = mul i32 %qb0, %qyf
  %qs0 = add i32 %qtw0, %qbw0
  %qa0 = add i32 %qs0, 32768
  %qv0 = lshr i32 %qa0, 16
  %q8v0 = insertelement <16 x i32> poison, i32 %qv0, i64 0
  %qdx1 = add i64 %bxi, 1
  %qx1prod = mul i64 %qdx1, %srcW
  %qx1num = shl i64 %qx1prod, 8
  %qx1q = udiv i64 %qx1num, %dstW
  %qx1raw0 = lshr i64 %qx1q, 8
  %qx1last = sub i64 %srcW, 1
  %qx1in = icmp ult i64 %qx1raw0, %srcW
  %qx10 = select i1 %qx1in, i64 %qx1raw0, i64 %qx1last
  %qx1next = add i64 %qx10, 1
  %qx1more = icmp ult i64 %qx1next, %srcW
  %qx11 = select i1 %qx1more, i64 %qx1next, i64 %qx10
  %qx1frac64 = and i64 %qx1q, 255
  %qx1f = trunc i64 %qx1frac64 to i32
  %qx1inv = sub i32 256, %qx1f
  %qp1_00idx = add i64 %qr0, %qx10
  %qp1_00ptr = getelementptr i8, ptr %src, i64 %qp1_00idx
  %qp1_00raw = load i8, ptr %qp1_00ptr, align 1
  %qp1_00 = zext i8 %qp1_00raw to i32
  %qp1_00w = mul i32 %qp1_00, %qx1inv
  %qp1_01idx = add i64 %qr0, %qx11
  %qp1_01ptr = getelementptr i8, ptr %src, i64 %qp1_01idx
  %qp1_01raw = load i8, ptr %qp1_01ptr, align 1
  %qp1_01 = zext i8 %qp1_01raw to i32
  %qp1_01w = mul i32 %qp1_01, %qx1f
  %qp1_10idx = add i64 %qr1, %qx10
  %qp1_10ptr = getelementptr i8, ptr %src, i64 %qp1_10idx
  %qp1_10raw = load i8, ptr %qp1_10ptr, align 1
  %qp1_10 = zext i8 %qp1_10raw to i32
  %qp1_10w = mul i32 %qp1_10, %qx1inv
  %qp1_11idx = add i64 %qr1, %qx11
  %qp1_11ptr = getelementptr i8, ptr %src, i64 %qp1_11idx
  %qp1_11raw = load i8, ptr %qp1_11ptr, align 1
  %qp1_11 = zext i8 %qp1_11raw to i32
  %qp1_11w = mul i32 %qp1_11, %qx1f
  %qt1 = add i32 %qp1_00w, %qp1_01w
  %qb1 = add i32 %qp1_10w, %qp1_11w
  %qtw1 = mul i32 %qt1, %qyinv
  %qbw1 = mul i32 %qb1, %qyf
  %qs1 = add i32 %qtw1, %qbw1
  %qa1 = add i32 %qs1, 32768
  %qv1 = lshr i32 %qa1, 16
  %q8v1 = insertelement <16 x i32> %q8v0, i32 %qv1, i64 1
  %qdx2 = add i64 %bxi, 2
  %qx2prod = mul i64 %qdx2, %srcW
  %qx2num = shl i64 %qx2prod, 8
  %qx2q = udiv i64 %qx2num, %dstW
  %qx2raw0 = lshr i64 %qx2q, 8
  %qx2last = sub i64 %srcW, 1
  %qx2in = icmp ult i64 %qx2raw0, %srcW
  %qx20 = select i1 %qx2in, i64 %qx2raw0, i64 %qx2last
  %qx2next = add i64 %qx20, 1
  %qx2more = icmp ult i64 %qx2next, %srcW
  %qx21 = select i1 %qx2more, i64 %qx2next, i64 %qx20
  %qx2frac64 = and i64 %qx2q, 255
  %qx2f = trunc i64 %qx2frac64 to i32
  %qx2inv = sub i32 256, %qx2f
  %qp2_00idx = add i64 %qr0, %qx20
  %qp2_00ptr = getelementptr i8, ptr %src, i64 %qp2_00idx
  %qp2_00raw = load i8, ptr %qp2_00ptr, align 1
  %qp2_00 = zext i8 %qp2_00raw to i32
  %qp2_00w = mul i32 %qp2_00, %qx2inv
  %qp2_01idx = add i64 %qr0, %qx21
  %qp2_01ptr = getelementptr i8, ptr %src, i64 %qp2_01idx
  %qp2_01raw = load i8, ptr %qp2_01ptr, align 1
  %qp2_01 = zext i8 %qp2_01raw to i32
  %qp2_01w = mul i32 %qp2_01, %qx2f
  %qp2_10idx = add i64 %qr1, %qx20
  %qp2_10ptr = getelementptr i8, ptr %src, i64 %qp2_10idx
  %qp2_10raw = load i8, ptr %qp2_10ptr, align 1
  %qp2_10 = zext i8 %qp2_10raw to i32
  %qp2_10w = mul i32 %qp2_10, %qx2inv
  %qp2_11idx = add i64 %qr1, %qx21
  %qp2_11ptr = getelementptr i8, ptr %src, i64 %qp2_11idx
  %qp2_11raw = load i8, ptr %qp2_11ptr, align 1
  %qp2_11 = zext i8 %qp2_11raw to i32
  %qp2_11w = mul i32 %qp2_11, %qx2f
  %qt2 = add i32 %qp2_00w, %qp2_01w
  %qb2 = add i32 %qp2_10w, %qp2_11w
  %qtw2 = mul i32 %qt2, %qyinv
  %qbw2 = mul i32 %qb2, %qyf
  %qs2 = add i32 %qtw2, %qbw2
  %qa2 = add i32 %qs2, 32768
  %qv2 = lshr i32 %qa2, 16
  %q8v2 = insertelement <16 x i32> %q8v1, i32 %qv2, i64 2
  %qdx3 = add i64 %bxi, 3
  %qx3prod = mul i64 %qdx3, %srcW
  %qx3num = shl i64 %qx3prod, 8
  %qx3q = udiv i64 %qx3num, %dstW
  %qx3raw0 = lshr i64 %qx3q, 8
  %qx3last = sub i64 %srcW, 1
  %qx3in = icmp ult i64 %qx3raw0, %srcW
  %qx30 = select i1 %qx3in, i64 %qx3raw0, i64 %qx3last
  %qx3next = add i64 %qx30, 1
  %qx3more = icmp ult i64 %qx3next, %srcW
  %qx31 = select i1 %qx3more, i64 %qx3next, i64 %qx30
  %qx3frac64 = and i64 %qx3q, 255
  %qx3f = trunc i64 %qx3frac64 to i32
  %qx3inv = sub i32 256, %qx3f
  %qp3_00idx = add i64 %qr0, %qx30
  %qp3_00ptr = getelementptr i8, ptr %src, i64 %qp3_00idx
  %qp3_00raw = load i8, ptr %qp3_00ptr, align 1
  %qp3_00 = zext i8 %qp3_00raw to i32
  %qp3_00w = mul i32 %qp3_00, %qx3inv
  %qp3_01idx = add i64 %qr0, %qx31
  %qp3_01ptr = getelementptr i8, ptr %src, i64 %qp3_01idx
  %qp3_01raw = load i8, ptr %qp3_01ptr, align 1
  %qp3_01 = zext i8 %qp3_01raw to i32
  %qp3_01w = mul i32 %qp3_01, %qx3f
  %qp3_10idx = add i64 %qr1, %qx30
  %qp3_10ptr = getelementptr i8, ptr %src, i64 %qp3_10idx
  %qp3_10raw = load i8, ptr %qp3_10ptr, align 1
  %qp3_10 = zext i8 %qp3_10raw to i32
  %qp3_10w = mul i32 %qp3_10, %qx3inv
  %qp3_11idx = add i64 %qr1, %qx31
  %qp3_11ptr = getelementptr i8, ptr %src, i64 %qp3_11idx
  %qp3_11raw = load i8, ptr %qp3_11ptr, align 1
  %qp3_11 = zext i8 %qp3_11raw to i32
  %qp3_11w = mul i32 %qp3_11, %qx3f
  %qt3 = add i32 %qp3_00w, %qp3_01w
  %qb3 = add i32 %qp3_10w, %qp3_11w
  %qtw3 = mul i32 %qt3, %qyinv
  %qbw3 = mul i32 %qb3, %qyf
  %qs3 = add i32 %qtw3, %qbw3
  %qa3 = add i32 %qs3, 32768
  %qv3 = lshr i32 %qa3, 16
  %q8v3 = insertelement <16 x i32> %q8v2, i32 %qv3, i64 3
  %qdx4 = add i64 %bxi, 4
  %qx4prod = mul i64 %qdx4, %srcW
  %qx4num = shl i64 %qx4prod, 8
  %qx4q = udiv i64 %qx4num, %dstW
  %qx4raw0 = lshr i64 %qx4q, 8
  %qx4last = sub i64 %srcW, 1
  %qx4in = icmp ult i64 %qx4raw0, %srcW
  %qx40 = select i1 %qx4in, i64 %qx4raw0, i64 %qx4last
  %qx4next = add i64 %qx40, 1
  %qx4more = icmp ult i64 %qx4next, %srcW
  %qx41 = select i1 %qx4more, i64 %qx4next, i64 %qx40
  %qx4frac64 = and i64 %qx4q, 255
  %qx4f = trunc i64 %qx4frac64 to i32
  %qx4inv = sub i32 256, %qx4f
  %qp4_00idx = add i64 %qr0, %qx40
  %qp4_00ptr = getelementptr i8, ptr %src, i64 %qp4_00idx
  %qp4_00raw = load i8, ptr %qp4_00ptr, align 1
  %qp4_00 = zext i8 %qp4_00raw to i32
  %qp4_00w = mul i32 %qp4_00, %qx4inv
  %qp4_01idx = add i64 %qr0, %qx41
  %qp4_01ptr = getelementptr i8, ptr %src, i64 %qp4_01idx
  %qp4_01raw = load i8, ptr %qp4_01ptr, align 1
  %qp4_01 = zext i8 %qp4_01raw to i32
  %qp4_01w = mul i32 %qp4_01, %qx4f
  %qp4_10idx = add i64 %qr1, %qx40
  %qp4_10ptr = getelementptr i8, ptr %src, i64 %qp4_10idx
  %qp4_10raw = load i8, ptr %qp4_10ptr, align 1
  %qp4_10 = zext i8 %qp4_10raw to i32
  %qp4_10w = mul i32 %qp4_10, %qx4inv
  %qp4_11idx = add i64 %qr1, %qx41
  %qp4_11ptr = getelementptr i8, ptr %src, i64 %qp4_11idx
  %qp4_11raw = load i8, ptr %qp4_11ptr, align 1
  %qp4_11 = zext i8 %qp4_11raw to i32
  %qp4_11w = mul i32 %qp4_11, %qx4f
  %qt4 = add i32 %qp4_00w, %qp4_01w
  %qb4 = add i32 %qp4_10w, %qp4_11w
  %qtw4 = mul i32 %qt4, %qyinv
  %qbw4 = mul i32 %qb4, %qyf
  %qs4 = add i32 %qtw4, %qbw4
  %qa4 = add i32 %qs4, 32768
  %qv4 = lshr i32 %qa4, 16
  %q8v4 = insertelement <16 x i32> %q8v3, i32 %qv4, i64 4
  %qdx5 = add i64 %bxi, 5
  %qx5prod = mul i64 %qdx5, %srcW
  %qx5num = shl i64 %qx5prod, 8
  %qx5q = udiv i64 %qx5num, %dstW
  %qx5raw0 = lshr i64 %qx5q, 8
  %qx5last = sub i64 %srcW, 1
  %qx5in = icmp ult i64 %qx5raw0, %srcW
  %qx50 = select i1 %qx5in, i64 %qx5raw0, i64 %qx5last
  %qx5next = add i64 %qx50, 1
  %qx5more = icmp ult i64 %qx5next, %srcW
  %qx51 = select i1 %qx5more, i64 %qx5next, i64 %qx50
  %qx5frac64 = and i64 %qx5q, 255
  %qx5f = trunc i64 %qx5frac64 to i32
  %qx5inv = sub i32 256, %qx5f
  %qp5_00idx = add i64 %qr0, %qx50
  %qp5_00ptr = getelementptr i8, ptr %src, i64 %qp5_00idx
  %qp5_00raw = load i8, ptr %qp5_00ptr, align 1
  %qp5_00 = zext i8 %qp5_00raw to i32
  %qp5_00w = mul i32 %qp5_00, %qx5inv
  %qp5_01idx = add i64 %qr0, %qx51
  %qp5_01ptr = getelementptr i8, ptr %src, i64 %qp5_01idx
  %qp5_01raw = load i8, ptr %qp5_01ptr, align 1
  %qp5_01 = zext i8 %qp5_01raw to i32
  %qp5_01w = mul i32 %qp5_01, %qx5f
  %qp5_10idx = add i64 %qr1, %qx50
  %qp5_10ptr = getelementptr i8, ptr %src, i64 %qp5_10idx
  %qp5_10raw = load i8, ptr %qp5_10ptr, align 1
  %qp5_10 = zext i8 %qp5_10raw to i32
  %qp5_10w = mul i32 %qp5_10, %qx5inv
  %qp5_11idx = add i64 %qr1, %qx51
  %qp5_11ptr = getelementptr i8, ptr %src, i64 %qp5_11idx
  %qp5_11raw = load i8, ptr %qp5_11ptr, align 1
  %qp5_11 = zext i8 %qp5_11raw to i32
  %qp5_11w = mul i32 %qp5_11, %qx5f
  %qt5 = add i32 %qp5_00w, %qp5_01w
  %qb5 = add i32 %qp5_10w, %qp5_11w
  %qtw5 = mul i32 %qt5, %qyinv
  %qbw5 = mul i32 %qb5, %qyf
  %qs5 = add i32 %qtw5, %qbw5
  %qa5 = add i32 %qs5, 32768
  %qv5 = lshr i32 %qa5, 16
  %q8v5 = insertelement <16 x i32> %q8v4, i32 %qv5, i64 5
  %qdx6 = add i64 %bxi, 6
  %qx6prod = mul i64 %qdx6, %srcW
  %qx6num = shl i64 %qx6prod, 8
  %qx6q = udiv i64 %qx6num, %dstW
  %qx6raw0 = lshr i64 %qx6q, 8
  %qx6last = sub i64 %srcW, 1
  %qx6in = icmp ult i64 %qx6raw0, %srcW
  %qx60 = select i1 %qx6in, i64 %qx6raw0, i64 %qx6last
  %qx6next = add i64 %qx60, 1
  %qx6more = icmp ult i64 %qx6next, %srcW
  %qx61 = select i1 %qx6more, i64 %qx6next, i64 %qx60
  %qx6frac64 = and i64 %qx6q, 255
  %qx6f = trunc i64 %qx6frac64 to i32
  %qx6inv = sub i32 256, %qx6f
  %qp6_00idx = add i64 %qr0, %qx60
  %qp6_00ptr = getelementptr i8, ptr %src, i64 %qp6_00idx
  %qp6_00raw = load i8, ptr %qp6_00ptr, align 1
  %qp6_00 = zext i8 %qp6_00raw to i32
  %qp6_00w = mul i32 %qp6_00, %qx6inv
  %qp6_01idx = add i64 %qr0, %qx61
  %qp6_01ptr = getelementptr i8, ptr %src, i64 %qp6_01idx
  %qp6_01raw = load i8, ptr %qp6_01ptr, align 1
  %qp6_01 = zext i8 %qp6_01raw to i32
  %qp6_01w = mul i32 %qp6_01, %qx6f
  %qp6_10idx = add i64 %qr1, %qx60
  %qp6_10ptr = getelementptr i8, ptr %src, i64 %qp6_10idx
  %qp6_10raw = load i8, ptr %qp6_10ptr, align 1
  %qp6_10 = zext i8 %qp6_10raw to i32
  %qp6_10w = mul i32 %qp6_10, %qx6inv
  %qp6_11idx = add i64 %qr1, %qx61
  %qp6_11ptr = getelementptr i8, ptr %src, i64 %qp6_11idx
  %qp6_11raw = load i8, ptr %qp6_11ptr, align 1
  %qp6_11 = zext i8 %qp6_11raw to i32
  %qp6_11w = mul i32 %qp6_11, %qx6f
  %qt6 = add i32 %qp6_00w, %qp6_01w
  %qb6 = add i32 %qp6_10w, %qp6_11w
  %qtw6 = mul i32 %qt6, %qyinv
  %qbw6 = mul i32 %qb6, %qyf
  %qs6 = add i32 %qtw6, %qbw6
  %qa6 = add i32 %qs6, 32768
  %qv6 = lshr i32 %qa6, 16
  %q8v6 = insertelement <16 x i32> %q8v5, i32 %qv6, i64 6
  %qdx7 = add i64 %bxi, 7
  %qx7prod = mul i64 %qdx7, %srcW
  %qx7num = shl i64 %qx7prod, 8
  %qx7q = udiv i64 %qx7num, %dstW
  %qx7raw0 = lshr i64 %qx7q, 8
  %qx7last = sub i64 %srcW, 1
  %qx7in = icmp ult i64 %qx7raw0, %srcW
  %qx70 = select i1 %qx7in, i64 %qx7raw0, i64 %qx7last
  %qx7next = add i64 %qx70, 1
  %qx7more = icmp ult i64 %qx7next, %srcW
  %qx71 = select i1 %qx7more, i64 %qx7next, i64 %qx70
  %qx7frac64 = and i64 %qx7q, 255
  %qx7f = trunc i64 %qx7frac64 to i32
  %qx7inv = sub i32 256, %qx7f
  %qp7_00idx = add i64 %qr0, %qx70
  %qp7_00ptr = getelementptr i8, ptr %src, i64 %qp7_00idx
  %qp7_00raw = load i8, ptr %qp7_00ptr, align 1
  %qp7_00 = zext i8 %qp7_00raw to i32
  %qp7_00w = mul i32 %qp7_00, %qx7inv
  %qp7_01idx = add i64 %qr0, %qx71
  %qp7_01ptr = getelementptr i8, ptr %src, i64 %qp7_01idx
  %qp7_01raw = load i8, ptr %qp7_01ptr, align 1
  %qp7_01 = zext i8 %qp7_01raw to i32
  %qp7_01w = mul i32 %qp7_01, %qx7f
  %qp7_10idx = add i64 %qr1, %qx70
  %qp7_10ptr = getelementptr i8, ptr %src, i64 %qp7_10idx
  %qp7_10raw = load i8, ptr %qp7_10ptr, align 1
  %qp7_10 = zext i8 %qp7_10raw to i32
  %qp7_10w = mul i32 %qp7_10, %qx7inv
  %qp7_11idx = add i64 %qr1, %qx71
  %qp7_11ptr = getelementptr i8, ptr %src, i64 %qp7_11idx
  %qp7_11raw = load i8, ptr %qp7_11ptr, align 1
  %qp7_11 = zext i8 %qp7_11raw to i32
  %qp7_11w = mul i32 %qp7_11, %qx7f
  %qt7 = add i32 %qp7_00w, %qp7_01w
  %qb7 = add i32 %qp7_10w, %qp7_11w
  %qtw7 = mul i32 %qt7, %qyinv
  %qbw7 = mul i32 %qb7, %qyf
  %qs7 = add i32 %qtw7, %qbw7
  %qa7 = add i32 %qs7, 32768
  %qv7 = lshr i32 %qa7, 16
  %q8v7 = insertelement <16 x i32> %q8v6, i32 %qv7, i64 7
  %qdx8 = add i64 %bxi, 8
  %qx8prod = mul i64 %qdx8, %srcW
  %qx8num = shl i64 %qx8prod, 8
  %qx8q = udiv i64 %qx8num, %dstW
  %qx8raw0 = lshr i64 %qx8q, 8
  %qx8last = sub i64 %srcW, 1
  %qx8in = icmp ult i64 %qx8raw0, %srcW
  %qx80 = select i1 %qx8in, i64 %qx8raw0, i64 %qx8last
  %qx8next = add i64 %qx80, 1
  %qx8more = icmp ult i64 %qx8next, %srcW
  %qx81 = select i1 %qx8more, i64 %qx8next, i64 %qx80
  %qx8frac64 = and i64 %qx8q, 255
  %qx8f = trunc i64 %qx8frac64 to i32
  %qx8inv = sub i32 256, %qx8f
  %qp8_00idx = add i64 %qr0, %qx80
  %qp8_00ptr = getelementptr i8, ptr %src, i64 %qp8_00idx
  %qp8_00raw = load i8, ptr %qp8_00ptr, align 1
  %qp8_00 = zext i8 %qp8_00raw to i32
  %qp8_00w = mul i32 %qp8_00, %qx8inv
  %qp8_01idx = add i64 %qr0, %qx81
  %qp8_01ptr = getelementptr i8, ptr %src, i64 %qp8_01idx
  %qp8_01raw = load i8, ptr %qp8_01ptr, align 1
  %qp8_01 = zext i8 %qp8_01raw to i32
  %qp8_01w = mul i32 %qp8_01, %qx8f
  %qp8_10idx = add i64 %qr1, %qx80
  %qp8_10ptr = getelementptr i8, ptr %src, i64 %qp8_10idx
  %qp8_10raw = load i8, ptr %qp8_10ptr, align 1
  %qp8_10 = zext i8 %qp8_10raw to i32
  %qp8_10w = mul i32 %qp8_10, %qx8inv
  %qp8_11idx = add i64 %qr1, %qx81
  %qp8_11ptr = getelementptr i8, ptr %src, i64 %qp8_11idx
  %qp8_11raw = load i8, ptr %qp8_11ptr, align 1
  %qp8_11 = zext i8 %qp8_11raw to i32
  %qp8_11w = mul i32 %qp8_11, %qx8f
  %qt8 = add i32 %qp8_00w, %qp8_01w
  %qb8 = add i32 %qp8_10w, %qp8_11w
  %qtw8 = mul i32 %qt8, %qyinv
  %qbw8 = mul i32 %qb8, %qyf
  %qs8 = add i32 %qtw8, %qbw8
  %qa8 = add i32 %qs8, 32768
  %qv8 = lshr i32 %qa8, 16
  %q8v8 = insertelement <16 x i32> %q8v7, i32 %qv8, i64 8
  %qdx9 = add i64 %bxi, 9
  %qx9prod = mul i64 %qdx9, %srcW
  %qx9num = shl i64 %qx9prod, 8
  %qx9q = udiv i64 %qx9num, %dstW
  %qx9raw0 = lshr i64 %qx9q, 8
  %qx9last = sub i64 %srcW, 1
  %qx9in = icmp ult i64 %qx9raw0, %srcW
  %qx90 = select i1 %qx9in, i64 %qx9raw0, i64 %qx9last
  %qx9next = add i64 %qx90, 1
  %qx9more = icmp ult i64 %qx9next, %srcW
  %qx91 = select i1 %qx9more, i64 %qx9next, i64 %qx90
  %qx9frac64 = and i64 %qx9q, 255
  %qx9f = trunc i64 %qx9frac64 to i32
  %qx9inv = sub i32 256, %qx9f
  %qp9_00idx = add i64 %qr0, %qx90
  %qp9_00ptr = getelementptr i8, ptr %src, i64 %qp9_00idx
  %qp9_00raw = load i8, ptr %qp9_00ptr, align 1
  %qp9_00 = zext i8 %qp9_00raw to i32
  %qp9_00w = mul i32 %qp9_00, %qx9inv
  %qp9_01idx = add i64 %qr0, %qx91
  %qp9_01ptr = getelementptr i8, ptr %src, i64 %qp9_01idx
  %qp9_01raw = load i8, ptr %qp9_01ptr, align 1
  %qp9_01 = zext i8 %qp9_01raw to i32
  %qp9_01w = mul i32 %qp9_01, %qx9f
  %qp9_10idx = add i64 %qr1, %qx90
  %qp9_10ptr = getelementptr i8, ptr %src, i64 %qp9_10idx
  %qp9_10raw = load i8, ptr %qp9_10ptr, align 1
  %qp9_10 = zext i8 %qp9_10raw to i32
  %qp9_10w = mul i32 %qp9_10, %qx9inv
  %qp9_11idx = add i64 %qr1, %qx91
  %qp9_11ptr = getelementptr i8, ptr %src, i64 %qp9_11idx
  %qp9_11raw = load i8, ptr %qp9_11ptr, align 1
  %qp9_11 = zext i8 %qp9_11raw to i32
  %qp9_11w = mul i32 %qp9_11, %qx9f
  %qt9 = add i32 %qp9_00w, %qp9_01w
  %qb9 = add i32 %qp9_10w, %qp9_11w
  %qtw9 = mul i32 %qt9, %qyinv
  %qbw9 = mul i32 %qb9, %qyf
  %qs9 = add i32 %qtw9, %qbw9
  %qa9 = add i32 %qs9, 32768
  %qv9 = lshr i32 %qa9, 16
  %q8v9 = insertelement <16 x i32> %q8v8, i32 %qv9, i64 9
  %qdx10 = add i64 %bxi, 10
  %qx10prod = mul i64 %qdx10, %srcW
  %qx10num = shl i64 %qx10prod, 8
  %qx10q = udiv i64 %qx10num, %dstW
  %qx10raw0 = lshr i64 %qx10q, 8
  %qx10last = sub i64 %srcW, 1
  %qx10in = icmp ult i64 %qx10raw0, %srcW
  %qx100 = select i1 %qx10in, i64 %qx10raw0, i64 %qx10last
  %qx10next = add i64 %qx100, 1
  %qx10more = icmp ult i64 %qx10next, %srcW
  %qx101 = select i1 %qx10more, i64 %qx10next, i64 %qx100
  %qx10frac64 = and i64 %qx10q, 255
  %qx10f = trunc i64 %qx10frac64 to i32
  %qx10inv = sub i32 256, %qx10f
  %qp10_00idx = add i64 %qr0, %qx100
  %qp10_00ptr = getelementptr i8, ptr %src, i64 %qp10_00idx
  %qp10_00raw = load i8, ptr %qp10_00ptr, align 1
  %qp10_00 = zext i8 %qp10_00raw to i32
  %qp10_00w = mul i32 %qp10_00, %qx10inv
  %qp10_01idx = add i64 %qr0, %qx101
  %qp10_01ptr = getelementptr i8, ptr %src, i64 %qp10_01idx
  %qp10_01raw = load i8, ptr %qp10_01ptr, align 1
  %qp10_01 = zext i8 %qp10_01raw to i32
  %qp10_01w = mul i32 %qp10_01, %qx10f
  %qp10_10idx = add i64 %qr1, %qx100
  %qp10_10ptr = getelementptr i8, ptr %src, i64 %qp10_10idx
  %qp10_10raw = load i8, ptr %qp10_10ptr, align 1
  %qp10_10 = zext i8 %qp10_10raw to i32
  %qp10_10w = mul i32 %qp10_10, %qx10inv
  %qp10_11idx = add i64 %qr1, %qx101
  %qp10_11ptr = getelementptr i8, ptr %src, i64 %qp10_11idx
  %qp10_11raw = load i8, ptr %qp10_11ptr, align 1
  %qp10_11 = zext i8 %qp10_11raw to i32
  %qp10_11w = mul i32 %qp10_11, %qx10f
  %qt10 = add i32 %qp10_00w, %qp10_01w
  %qb10 = add i32 %qp10_10w, %qp10_11w
  %qtw10 = mul i32 %qt10, %qyinv
  %qbw10 = mul i32 %qb10, %qyf
  %qs10 = add i32 %qtw10, %qbw10
  %qa10 = add i32 %qs10, 32768
  %qv10 = lshr i32 %qa10, 16
  %q8v10 = insertelement <16 x i32> %q8v9, i32 %qv10, i64 10
  %qdx11 = add i64 %bxi, 11
  %qx11prod = mul i64 %qdx11, %srcW
  %qx11num = shl i64 %qx11prod, 8
  %qx11q = udiv i64 %qx11num, %dstW
  %qx11raw0 = lshr i64 %qx11q, 8
  %qx11last = sub i64 %srcW, 1
  %qx11in = icmp ult i64 %qx11raw0, %srcW
  %qx110 = select i1 %qx11in, i64 %qx11raw0, i64 %qx11last
  %qx11next = add i64 %qx110, 1
  %qx11more = icmp ult i64 %qx11next, %srcW
  %qx111 = select i1 %qx11more, i64 %qx11next, i64 %qx110
  %qx11frac64 = and i64 %qx11q, 255
  %qx11f = trunc i64 %qx11frac64 to i32
  %qx11inv = sub i32 256, %qx11f
  %qp11_00idx = add i64 %qr0, %qx110
  %qp11_00ptr = getelementptr i8, ptr %src, i64 %qp11_00idx
  %qp11_00raw = load i8, ptr %qp11_00ptr, align 1
  %qp11_00 = zext i8 %qp11_00raw to i32
  %qp11_00w = mul i32 %qp11_00, %qx11inv
  %qp11_01idx = add i64 %qr0, %qx111
  %qp11_01ptr = getelementptr i8, ptr %src, i64 %qp11_01idx
  %qp11_01raw = load i8, ptr %qp11_01ptr, align 1
  %qp11_01 = zext i8 %qp11_01raw to i32
  %qp11_01w = mul i32 %qp11_01, %qx11f
  %qp11_10idx = add i64 %qr1, %qx110
  %qp11_10ptr = getelementptr i8, ptr %src, i64 %qp11_10idx
  %qp11_10raw = load i8, ptr %qp11_10ptr, align 1
  %qp11_10 = zext i8 %qp11_10raw to i32
  %qp11_10w = mul i32 %qp11_10, %qx11inv
  %qp11_11idx = add i64 %qr1, %qx111
  %qp11_11ptr = getelementptr i8, ptr %src, i64 %qp11_11idx
  %qp11_11raw = load i8, ptr %qp11_11ptr, align 1
  %qp11_11 = zext i8 %qp11_11raw to i32
  %qp11_11w = mul i32 %qp11_11, %qx11f
  %qt11 = add i32 %qp11_00w, %qp11_01w
  %qb11 = add i32 %qp11_10w, %qp11_11w
  %qtw11 = mul i32 %qt11, %qyinv
  %qbw11 = mul i32 %qb11, %qyf
  %qs11 = add i32 %qtw11, %qbw11
  %qa11 = add i32 %qs11, 32768
  %qv11 = lshr i32 %qa11, 16
  %q8v11 = insertelement <16 x i32> %q8v10, i32 %qv11, i64 11
  %qdx12 = add i64 %bxi, 12
  %qx12prod = mul i64 %qdx12, %srcW
  %qx12num = shl i64 %qx12prod, 8
  %qx12q = udiv i64 %qx12num, %dstW
  %qx12raw0 = lshr i64 %qx12q, 8
  %qx12last = sub i64 %srcW, 1
  %qx12in = icmp ult i64 %qx12raw0, %srcW
  %qx120 = select i1 %qx12in, i64 %qx12raw0, i64 %qx12last
  %qx12next = add i64 %qx120, 1
  %qx12more = icmp ult i64 %qx12next, %srcW
  %qx121 = select i1 %qx12more, i64 %qx12next, i64 %qx120
  %qx12frac64 = and i64 %qx12q, 255
  %qx12f = trunc i64 %qx12frac64 to i32
  %qx12inv = sub i32 256, %qx12f
  %qp12_00idx = add i64 %qr0, %qx120
  %qp12_00ptr = getelementptr i8, ptr %src, i64 %qp12_00idx
  %qp12_00raw = load i8, ptr %qp12_00ptr, align 1
  %qp12_00 = zext i8 %qp12_00raw to i32
  %qp12_00w = mul i32 %qp12_00, %qx12inv
  %qp12_01idx = add i64 %qr0, %qx121
  %qp12_01ptr = getelementptr i8, ptr %src, i64 %qp12_01idx
  %qp12_01raw = load i8, ptr %qp12_01ptr, align 1
  %qp12_01 = zext i8 %qp12_01raw to i32
  %qp12_01w = mul i32 %qp12_01, %qx12f
  %qp12_10idx = add i64 %qr1, %qx120
  %qp12_10ptr = getelementptr i8, ptr %src, i64 %qp12_10idx
  %qp12_10raw = load i8, ptr %qp12_10ptr, align 1
  %qp12_10 = zext i8 %qp12_10raw to i32
  %qp12_10w = mul i32 %qp12_10, %qx12inv
  %qp12_11idx = add i64 %qr1, %qx121
  %qp12_11ptr = getelementptr i8, ptr %src, i64 %qp12_11idx
  %qp12_11raw = load i8, ptr %qp12_11ptr, align 1
  %qp12_11 = zext i8 %qp12_11raw to i32
  %qp12_11w = mul i32 %qp12_11, %qx12f
  %qt12 = add i32 %qp12_00w, %qp12_01w
  %qb12 = add i32 %qp12_10w, %qp12_11w
  %qtw12 = mul i32 %qt12, %qyinv
  %qbw12 = mul i32 %qb12, %qyf
  %qs12 = add i32 %qtw12, %qbw12
  %qa12 = add i32 %qs12, 32768
  %qv12 = lshr i32 %qa12, 16
  %q8v12 = insertelement <16 x i32> %q8v11, i32 %qv12, i64 12
  %qdx13 = add i64 %bxi, 13
  %qx13prod = mul i64 %qdx13, %srcW
  %qx13num = shl i64 %qx13prod, 8
  %qx13q = udiv i64 %qx13num, %dstW
  %qx13raw0 = lshr i64 %qx13q, 8
  %qx13last = sub i64 %srcW, 1
  %qx13in = icmp ult i64 %qx13raw0, %srcW
  %qx130 = select i1 %qx13in, i64 %qx13raw0, i64 %qx13last
  %qx13next = add i64 %qx130, 1
  %qx13more = icmp ult i64 %qx13next, %srcW
  %qx131 = select i1 %qx13more, i64 %qx13next, i64 %qx130
  %qx13frac64 = and i64 %qx13q, 255
  %qx13f = trunc i64 %qx13frac64 to i32
  %qx13inv = sub i32 256, %qx13f
  %qp13_00idx = add i64 %qr0, %qx130
  %qp13_00ptr = getelementptr i8, ptr %src, i64 %qp13_00idx
  %qp13_00raw = load i8, ptr %qp13_00ptr, align 1
  %qp13_00 = zext i8 %qp13_00raw to i32
  %qp13_00w = mul i32 %qp13_00, %qx13inv
  %qp13_01idx = add i64 %qr0, %qx131
  %qp13_01ptr = getelementptr i8, ptr %src, i64 %qp13_01idx
  %qp13_01raw = load i8, ptr %qp13_01ptr, align 1
  %qp13_01 = zext i8 %qp13_01raw to i32
  %qp13_01w = mul i32 %qp13_01, %qx13f
  %qp13_10idx = add i64 %qr1, %qx130
  %qp13_10ptr = getelementptr i8, ptr %src, i64 %qp13_10idx
  %qp13_10raw = load i8, ptr %qp13_10ptr, align 1
  %qp13_10 = zext i8 %qp13_10raw to i32
  %qp13_10w = mul i32 %qp13_10, %qx13inv
  %qp13_11idx = add i64 %qr1, %qx131
  %qp13_11ptr = getelementptr i8, ptr %src, i64 %qp13_11idx
  %qp13_11raw = load i8, ptr %qp13_11ptr, align 1
  %qp13_11 = zext i8 %qp13_11raw to i32
  %qp13_11w = mul i32 %qp13_11, %qx13f
  %qt13 = add i32 %qp13_00w, %qp13_01w
  %qb13 = add i32 %qp13_10w, %qp13_11w
  %qtw13 = mul i32 %qt13, %qyinv
  %qbw13 = mul i32 %qb13, %qyf
  %qs13 = add i32 %qtw13, %qbw13
  %qa13 = add i32 %qs13, 32768
  %qv13 = lshr i32 %qa13, 16
  %q8v13 = insertelement <16 x i32> %q8v12, i32 %qv13, i64 13
  %qdx14 = add i64 %bxi, 14
  %qx14prod = mul i64 %qdx14, %srcW
  %qx14num = shl i64 %qx14prod, 8
  %qx14q = udiv i64 %qx14num, %dstW
  %qx14raw0 = lshr i64 %qx14q, 8
  %qx14last = sub i64 %srcW, 1
  %qx14in = icmp ult i64 %qx14raw0, %srcW
  %qx140 = select i1 %qx14in, i64 %qx14raw0, i64 %qx14last
  %qx14next = add i64 %qx140, 1
  %qx14more = icmp ult i64 %qx14next, %srcW
  %qx141 = select i1 %qx14more, i64 %qx14next, i64 %qx140
  %qx14frac64 = and i64 %qx14q, 255
  %qx14f = trunc i64 %qx14frac64 to i32
  %qx14inv = sub i32 256, %qx14f
  %qp14_00idx = add i64 %qr0, %qx140
  %qp14_00ptr = getelementptr i8, ptr %src, i64 %qp14_00idx
  %qp14_00raw = load i8, ptr %qp14_00ptr, align 1
  %qp14_00 = zext i8 %qp14_00raw to i32
  %qp14_00w = mul i32 %qp14_00, %qx14inv
  %qp14_01idx = add i64 %qr0, %qx141
  %qp14_01ptr = getelementptr i8, ptr %src, i64 %qp14_01idx
  %qp14_01raw = load i8, ptr %qp14_01ptr, align 1
  %qp14_01 = zext i8 %qp14_01raw to i32
  %qp14_01w = mul i32 %qp14_01, %qx14f
  %qp14_10idx = add i64 %qr1, %qx140
  %qp14_10ptr = getelementptr i8, ptr %src, i64 %qp14_10idx
  %qp14_10raw = load i8, ptr %qp14_10ptr, align 1
  %qp14_10 = zext i8 %qp14_10raw to i32
  %qp14_10w = mul i32 %qp14_10, %qx14inv
  %qp14_11idx = add i64 %qr1, %qx141
  %qp14_11ptr = getelementptr i8, ptr %src, i64 %qp14_11idx
  %qp14_11raw = load i8, ptr %qp14_11ptr, align 1
  %qp14_11 = zext i8 %qp14_11raw to i32
  %qp14_11w = mul i32 %qp14_11, %qx14f
  %qt14 = add i32 %qp14_00w, %qp14_01w
  %qb14 = add i32 %qp14_10w, %qp14_11w
  %qtw14 = mul i32 %qt14, %qyinv
  %qbw14 = mul i32 %qb14, %qyf
  %qs14 = add i32 %qtw14, %qbw14
  %qa14 = add i32 %qs14, 32768
  %qv14 = lshr i32 %qa14, 16
  %q8v14 = insertelement <16 x i32> %q8v13, i32 %qv14, i64 14
  %qdx15 = add i64 %bxi, 15
  %qx15prod = mul i64 %qdx15, %srcW
  %qx15num = shl i64 %qx15prod, 8
  %qx15q = udiv i64 %qx15num, %dstW
  %qx15raw0 = lshr i64 %qx15q, 8
  %qx15last = sub i64 %srcW, 1
  %qx15in = icmp ult i64 %qx15raw0, %srcW
  %qx150 = select i1 %qx15in, i64 %qx15raw0, i64 %qx15last
  %qx15next = add i64 %qx150, 1
  %qx15more = icmp ult i64 %qx15next, %srcW
  %qx151 = select i1 %qx15more, i64 %qx15next, i64 %qx150
  %qx15frac64 = and i64 %qx15q, 255
  %qx15f = trunc i64 %qx15frac64 to i32
  %qx15inv = sub i32 256, %qx15f
  %qp15_00idx = add i64 %qr0, %qx150
  %qp15_00ptr = getelementptr i8, ptr %src, i64 %qp15_00idx
  %qp15_00raw = load i8, ptr %qp15_00ptr, align 1
  %qp15_00 = zext i8 %qp15_00raw to i32
  %qp15_00w = mul i32 %qp15_00, %qx15inv
  %qp15_01idx = add i64 %qr0, %qx151
  %qp15_01ptr = getelementptr i8, ptr %src, i64 %qp15_01idx
  %qp15_01raw = load i8, ptr %qp15_01ptr, align 1
  %qp15_01 = zext i8 %qp15_01raw to i32
  %qp15_01w = mul i32 %qp15_01, %qx15f
  %qp15_10idx = add i64 %qr1, %qx150
  %qp15_10ptr = getelementptr i8, ptr %src, i64 %qp15_10idx
  %qp15_10raw = load i8, ptr %qp15_10ptr, align 1
  %qp15_10 = zext i8 %qp15_10raw to i32
  %qp15_10w = mul i32 %qp15_10, %qx15inv
  %qp15_11idx = add i64 %qr1, %qx151
  %qp15_11ptr = getelementptr i8, ptr %src, i64 %qp15_11idx
  %qp15_11raw = load i8, ptr %qp15_11ptr, align 1
  %qp15_11 = zext i8 %qp15_11raw to i32
  %qp15_11w = mul i32 %qp15_11, %qx15f
  %qt15 = add i32 %qp15_00w, %qp15_01w
  %qb15 = add i32 %qp15_10w, %qp15_11w
  %qtw15 = mul i32 %qt15, %qyinv
  %qbw15 = mul i32 %qb15, %qyf
  %qs15 = add i32 %qtw15, %qbw15
  %qa15 = add i32 %qs15, 32768
  %qv15 = lshr i32 %qa15, 16
  %q8v15 = insertelement <16 x i32> %q8v14, i32 %qv15, i64 15
  br label %reduce
reduce:
  %r = phi <16 x i32> [ %r1, %same ], [ %r2, %half ], [ %third15, %third ], [ %q8v15, %q8 ]
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

define weak_odr dso_local void @lean_native_luma_acceptance_16x16_u16le(ptr noalias noundef readonly %src, i64 noundef %srcW, i64 noundef %srcH, ptr noalias noundef readonly %dst, i64 noundef %dstW, i64 noundef %dstH, ptr noalias noundef writeonly %outMetrics4) #0 {
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
  %oneW = icmp eq i64 %srcW, %dstW
  %oneH = icmp eq i64 %srcH, %dstH
  %one = and i1 %oneW, %oneH
  %twoWsize = mul i64 %dstW, 2
  %twoW = icmp eq i64 %srcW, %twoWsize
  %twoHsize = mul i64 %dstH, 2
  %twoH = icmp eq i64 %srcH, %twoHsize
  %two = and i1 %twoW, %twoH
  %threeWsize = mul i64 %dstW, 3
  %threeW = icmp eq i64 %srcW, %threeWsize
  %threeHsize = mul i64 %dstH, 3
  %threeH = icmp eq i64 %srcH, %threeHsize
  %three = and i1 %threeW, %threeH
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
  %dp = getelementptr i16, ptr %dst, i64 %di
  %db = load <16 x i16>, ptr %dp, align 1
  %draw = zext <16 x i16> %db to <16 x i32>
  %dshift = lshr <16 x i32> %draw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %d = and <16 x i32> %dshift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  br i1 %one, label %same, label %choose2
same:
  %sp = getelementptr i16, ptr %src, i64 %di
  %sb = load <16 x i16>, ptr %sp, align 1
  %r1raw = zext <16 x i16> %sb to <16 x i32>
  %r1shift = lshr <16 x i32> %r1raw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %r1 = and <16 x i32> %r1shift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  br label %reduce
half:
  %sr = mul i64 %dy, %srcW
  %si0 = add i64 %sr, %bxi
  %si = shl i64 %si0, 1
  %si1 = add i64 %si, %srcW
  %p0 = getelementptr i16, ptr %src, i64 %si
  %p1 = getelementptr i16, ptr %src, i64 %si1
  %a = load <32 x i16>, ptr %p0, align 1
  %b = load <32 x i16>, ptr %p1, align 1
  %ae8 = shufflevector <32 x i16> %a, <32 x i16> poison, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %aeraw = zext <16 x i16> %ae8 to <16 x i32>
  %aeshift = lshr <16 x i32> %aeraw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %ae = and <16 x i32> %aeshift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %ao8 = shufflevector <32 x i16> %a, <32 x i16> poison, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %aoraw = zext <16 x i16> %ao8 to <16 x i32>
  %aoshift = lshr <16 x i32> %aoraw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %ao = and <16 x i32> %aoshift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %be8 = shufflevector <32 x i16> %b, <32 x i16> poison, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>
  %beraw = zext <16 x i16> %be8 to <16 x i32>
  %beshift = lshr <16 x i32> %beraw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %be = and <16 x i32> %beshift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %bo8 = shufflevector <32 x i16> %b, <32 x i16> poison, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>
  %boraw = zext <16 x i16> %bo8 to <16 x i32>
  %boshift = lshr <16 x i32> %boraw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %bo = and <16 x i32> %boshift, <i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255, i32 255>
  %ab = add <16 x i32> %ae, %ao
  %bb = add <16 x i32> %be, %bo
  %sum = add <16 x i32> %ab, %bb
  %rounded = add <16 x i32> %sum, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %r2 = lshr <16 x i32> %rounded, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  br label %reduce
choose2:
  br i1 %two, label %half, label %choose3
choose3:
  br i1 %three, label %third, label %q8
third:
  %ty = mul i64 %dy, 3
  %tr = mul i64 %ty, %srcW
  %tx0 = add i64 %bxi, 0
  %txs0 = mul i64 %tx0, 3
  %tb0 = add i64 %tr, %txs0
  %t0_0row = mul i64 %srcW, 0
  %t0_0off = add i64 %t0_0row, 0
  %t0_0idx = add i64 %tb0, %t0_0off
  %t0_0ptr = getelementptr i16, ptr %src, i64 %t0_0idx
  %t0_0raw = load i16, ptr %t0_0ptr, align 1
  %t0_0wide = zext i16 %t0_0raw to i32
  %t0_0shift = lshr i32 %t0_0wide, 2
  %t0_0 = and i32 %t0_0shift, 255
  %t0_1row = mul i64 %srcW, 0
  %t0_1off = add i64 %t0_1row, 1
  %t0_1idx = add i64 %tb0, %t0_1off
  %t0_1ptr = getelementptr i16, ptr %src, i64 %t0_1idx
  %t0_1raw = load i16, ptr %t0_1ptr, align 1
  %t0_1wide = zext i16 %t0_1raw to i32
  %t0_1shift = lshr i32 %t0_1wide, 2
  %t0_1 = and i32 %t0_1shift, 255
  %t0_2row = mul i64 %srcW, 0
  %t0_2off = add i64 %t0_2row, 2
  %t0_2idx = add i64 %tb0, %t0_2off
  %t0_2ptr = getelementptr i16, ptr %src, i64 %t0_2idx
  %t0_2raw = load i16, ptr %t0_2ptr, align 1
  %t0_2wide = zext i16 %t0_2raw to i32
  %t0_2shift = lshr i32 %t0_2wide, 2
  %t0_2 = and i32 %t0_2shift, 255
  %t0_3row = mul i64 %srcW, 1
  %t0_3off = add i64 %t0_3row, 0
  %t0_3idx = add i64 %tb0, %t0_3off
  %t0_3ptr = getelementptr i16, ptr %src, i64 %t0_3idx
  %t0_3raw = load i16, ptr %t0_3ptr, align 1
  %t0_3wide = zext i16 %t0_3raw to i32
  %t0_3shift = lshr i32 %t0_3wide, 2
  %t0_3 = and i32 %t0_3shift, 255
  %t0_4row = mul i64 %srcW, 1
  %t0_4off = add i64 %t0_4row, 1
  %t0_4idx = add i64 %tb0, %t0_4off
  %t0_4ptr = getelementptr i16, ptr %src, i64 %t0_4idx
  %t0_4raw = load i16, ptr %t0_4ptr, align 1
  %t0_4wide = zext i16 %t0_4raw to i32
  %t0_4shift = lshr i32 %t0_4wide, 2
  %t0_4 = and i32 %t0_4shift, 255
  %t0_5row = mul i64 %srcW, 1
  %t0_5off = add i64 %t0_5row, 2
  %t0_5idx = add i64 %tb0, %t0_5off
  %t0_5ptr = getelementptr i16, ptr %src, i64 %t0_5idx
  %t0_5raw = load i16, ptr %t0_5ptr, align 1
  %t0_5wide = zext i16 %t0_5raw to i32
  %t0_5shift = lshr i32 %t0_5wide, 2
  %t0_5 = and i32 %t0_5shift, 255
  %t0_6row = mul i64 %srcW, 2
  %t0_6off = add i64 %t0_6row, 0
  %t0_6idx = add i64 %tb0, %t0_6off
  %t0_6ptr = getelementptr i16, ptr %src, i64 %t0_6idx
  %t0_6raw = load i16, ptr %t0_6ptr, align 1
  %t0_6wide = zext i16 %t0_6raw to i32
  %t0_6shift = lshr i32 %t0_6wide, 2
  %t0_6 = and i32 %t0_6shift, 255
  %t0_7row = mul i64 %srcW, 2
  %t0_7off = add i64 %t0_7row, 1
  %t0_7idx = add i64 %tb0, %t0_7off
  %t0_7ptr = getelementptr i16, ptr %src, i64 %t0_7idx
  %t0_7raw = load i16, ptr %t0_7ptr, align 1
  %t0_7wide = zext i16 %t0_7raw to i32
  %t0_7shift = lshr i32 %t0_7wide, 2
  %t0_7 = and i32 %t0_7shift, 255
  %t0_8row = mul i64 %srcW, 2
  %t0_8off = add i64 %t0_8row, 2
  %t0_8idx = add i64 %tb0, %t0_8off
  %t0_8ptr = getelementptr i16, ptr %src, i64 %t0_8idx
  %t0_8raw = load i16, ptr %t0_8ptr, align 1
  %t0_8wide = zext i16 %t0_8raw to i32
  %t0_8shift = lshr i32 %t0_8wide, 2
  %t0_8 = and i32 %t0_8shift, 255
  %ts0_1 = add i32 %t0_0, %t0_1
  %ts0_2 = add i32 %ts0_1, %t0_2
  %ts0_3 = add i32 %ts0_2, %t0_3
  %ts0_4 = add i32 %ts0_3, %t0_4
  %ts0_5 = add i32 %ts0_4, %t0_5
  %ts0_6 = add i32 %ts0_5, %t0_6
  %ts0_7 = add i32 %ts0_6, %t0_7
  %ts0_8 = add i32 %ts0_7, %t0_8
  %ta0 = add i32 %ts0_8, 4
  %tm0 = mul i32 %ta0, 7282
  %tv0 = lshr i32 %tm0, 16
  %third0 = insertelement <16 x i32> poison, i32 %tv0, i64 0
  %tx1 = add i64 %bxi, 1
  %txs1 = mul i64 %tx1, 3
  %tb1 = add i64 %tr, %txs1
  %t1_0row = mul i64 %srcW, 0
  %t1_0off = add i64 %t1_0row, 0
  %t1_0idx = add i64 %tb1, %t1_0off
  %t1_0ptr = getelementptr i16, ptr %src, i64 %t1_0idx
  %t1_0raw = load i16, ptr %t1_0ptr, align 1
  %t1_0wide = zext i16 %t1_0raw to i32
  %t1_0shift = lshr i32 %t1_0wide, 2
  %t1_0 = and i32 %t1_0shift, 255
  %t1_1row = mul i64 %srcW, 0
  %t1_1off = add i64 %t1_1row, 1
  %t1_1idx = add i64 %tb1, %t1_1off
  %t1_1ptr = getelementptr i16, ptr %src, i64 %t1_1idx
  %t1_1raw = load i16, ptr %t1_1ptr, align 1
  %t1_1wide = zext i16 %t1_1raw to i32
  %t1_1shift = lshr i32 %t1_1wide, 2
  %t1_1 = and i32 %t1_1shift, 255
  %t1_2row = mul i64 %srcW, 0
  %t1_2off = add i64 %t1_2row, 2
  %t1_2idx = add i64 %tb1, %t1_2off
  %t1_2ptr = getelementptr i16, ptr %src, i64 %t1_2idx
  %t1_2raw = load i16, ptr %t1_2ptr, align 1
  %t1_2wide = zext i16 %t1_2raw to i32
  %t1_2shift = lshr i32 %t1_2wide, 2
  %t1_2 = and i32 %t1_2shift, 255
  %t1_3row = mul i64 %srcW, 1
  %t1_3off = add i64 %t1_3row, 0
  %t1_3idx = add i64 %tb1, %t1_3off
  %t1_3ptr = getelementptr i16, ptr %src, i64 %t1_3idx
  %t1_3raw = load i16, ptr %t1_3ptr, align 1
  %t1_3wide = zext i16 %t1_3raw to i32
  %t1_3shift = lshr i32 %t1_3wide, 2
  %t1_3 = and i32 %t1_3shift, 255
  %t1_4row = mul i64 %srcW, 1
  %t1_4off = add i64 %t1_4row, 1
  %t1_4idx = add i64 %tb1, %t1_4off
  %t1_4ptr = getelementptr i16, ptr %src, i64 %t1_4idx
  %t1_4raw = load i16, ptr %t1_4ptr, align 1
  %t1_4wide = zext i16 %t1_4raw to i32
  %t1_4shift = lshr i32 %t1_4wide, 2
  %t1_4 = and i32 %t1_4shift, 255
  %t1_5row = mul i64 %srcW, 1
  %t1_5off = add i64 %t1_5row, 2
  %t1_5idx = add i64 %tb1, %t1_5off
  %t1_5ptr = getelementptr i16, ptr %src, i64 %t1_5idx
  %t1_5raw = load i16, ptr %t1_5ptr, align 1
  %t1_5wide = zext i16 %t1_5raw to i32
  %t1_5shift = lshr i32 %t1_5wide, 2
  %t1_5 = and i32 %t1_5shift, 255
  %t1_6row = mul i64 %srcW, 2
  %t1_6off = add i64 %t1_6row, 0
  %t1_6idx = add i64 %tb1, %t1_6off
  %t1_6ptr = getelementptr i16, ptr %src, i64 %t1_6idx
  %t1_6raw = load i16, ptr %t1_6ptr, align 1
  %t1_6wide = zext i16 %t1_6raw to i32
  %t1_6shift = lshr i32 %t1_6wide, 2
  %t1_6 = and i32 %t1_6shift, 255
  %t1_7row = mul i64 %srcW, 2
  %t1_7off = add i64 %t1_7row, 1
  %t1_7idx = add i64 %tb1, %t1_7off
  %t1_7ptr = getelementptr i16, ptr %src, i64 %t1_7idx
  %t1_7raw = load i16, ptr %t1_7ptr, align 1
  %t1_7wide = zext i16 %t1_7raw to i32
  %t1_7shift = lshr i32 %t1_7wide, 2
  %t1_7 = and i32 %t1_7shift, 255
  %t1_8row = mul i64 %srcW, 2
  %t1_8off = add i64 %t1_8row, 2
  %t1_8idx = add i64 %tb1, %t1_8off
  %t1_8ptr = getelementptr i16, ptr %src, i64 %t1_8idx
  %t1_8raw = load i16, ptr %t1_8ptr, align 1
  %t1_8wide = zext i16 %t1_8raw to i32
  %t1_8shift = lshr i32 %t1_8wide, 2
  %t1_8 = and i32 %t1_8shift, 255
  %ts1_1 = add i32 %t1_0, %t1_1
  %ts1_2 = add i32 %ts1_1, %t1_2
  %ts1_3 = add i32 %ts1_2, %t1_3
  %ts1_4 = add i32 %ts1_3, %t1_4
  %ts1_5 = add i32 %ts1_4, %t1_5
  %ts1_6 = add i32 %ts1_5, %t1_6
  %ts1_7 = add i32 %ts1_6, %t1_7
  %ts1_8 = add i32 %ts1_7, %t1_8
  %ta1 = add i32 %ts1_8, 4
  %tm1 = mul i32 %ta1, 7282
  %tv1 = lshr i32 %tm1, 16
  %third1 = insertelement <16 x i32> %third0, i32 %tv1, i64 1
  %tx2 = add i64 %bxi, 2
  %txs2 = mul i64 %tx2, 3
  %tb2 = add i64 %tr, %txs2
  %t2_0row = mul i64 %srcW, 0
  %t2_0off = add i64 %t2_0row, 0
  %t2_0idx = add i64 %tb2, %t2_0off
  %t2_0ptr = getelementptr i16, ptr %src, i64 %t2_0idx
  %t2_0raw = load i16, ptr %t2_0ptr, align 1
  %t2_0wide = zext i16 %t2_0raw to i32
  %t2_0shift = lshr i32 %t2_0wide, 2
  %t2_0 = and i32 %t2_0shift, 255
  %t2_1row = mul i64 %srcW, 0
  %t2_1off = add i64 %t2_1row, 1
  %t2_1idx = add i64 %tb2, %t2_1off
  %t2_1ptr = getelementptr i16, ptr %src, i64 %t2_1idx
  %t2_1raw = load i16, ptr %t2_1ptr, align 1
  %t2_1wide = zext i16 %t2_1raw to i32
  %t2_1shift = lshr i32 %t2_1wide, 2
  %t2_1 = and i32 %t2_1shift, 255
  %t2_2row = mul i64 %srcW, 0
  %t2_2off = add i64 %t2_2row, 2
  %t2_2idx = add i64 %tb2, %t2_2off
  %t2_2ptr = getelementptr i16, ptr %src, i64 %t2_2idx
  %t2_2raw = load i16, ptr %t2_2ptr, align 1
  %t2_2wide = zext i16 %t2_2raw to i32
  %t2_2shift = lshr i32 %t2_2wide, 2
  %t2_2 = and i32 %t2_2shift, 255
  %t2_3row = mul i64 %srcW, 1
  %t2_3off = add i64 %t2_3row, 0
  %t2_3idx = add i64 %tb2, %t2_3off
  %t2_3ptr = getelementptr i16, ptr %src, i64 %t2_3idx
  %t2_3raw = load i16, ptr %t2_3ptr, align 1
  %t2_3wide = zext i16 %t2_3raw to i32
  %t2_3shift = lshr i32 %t2_3wide, 2
  %t2_3 = and i32 %t2_3shift, 255
  %t2_4row = mul i64 %srcW, 1
  %t2_4off = add i64 %t2_4row, 1
  %t2_4idx = add i64 %tb2, %t2_4off
  %t2_4ptr = getelementptr i16, ptr %src, i64 %t2_4idx
  %t2_4raw = load i16, ptr %t2_4ptr, align 1
  %t2_4wide = zext i16 %t2_4raw to i32
  %t2_4shift = lshr i32 %t2_4wide, 2
  %t2_4 = and i32 %t2_4shift, 255
  %t2_5row = mul i64 %srcW, 1
  %t2_5off = add i64 %t2_5row, 2
  %t2_5idx = add i64 %tb2, %t2_5off
  %t2_5ptr = getelementptr i16, ptr %src, i64 %t2_5idx
  %t2_5raw = load i16, ptr %t2_5ptr, align 1
  %t2_5wide = zext i16 %t2_5raw to i32
  %t2_5shift = lshr i32 %t2_5wide, 2
  %t2_5 = and i32 %t2_5shift, 255
  %t2_6row = mul i64 %srcW, 2
  %t2_6off = add i64 %t2_6row, 0
  %t2_6idx = add i64 %tb2, %t2_6off
  %t2_6ptr = getelementptr i16, ptr %src, i64 %t2_6idx
  %t2_6raw = load i16, ptr %t2_6ptr, align 1
  %t2_6wide = zext i16 %t2_6raw to i32
  %t2_6shift = lshr i32 %t2_6wide, 2
  %t2_6 = and i32 %t2_6shift, 255
  %t2_7row = mul i64 %srcW, 2
  %t2_7off = add i64 %t2_7row, 1
  %t2_7idx = add i64 %tb2, %t2_7off
  %t2_7ptr = getelementptr i16, ptr %src, i64 %t2_7idx
  %t2_7raw = load i16, ptr %t2_7ptr, align 1
  %t2_7wide = zext i16 %t2_7raw to i32
  %t2_7shift = lshr i32 %t2_7wide, 2
  %t2_7 = and i32 %t2_7shift, 255
  %t2_8row = mul i64 %srcW, 2
  %t2_8off = add i64 %t2_8row, 2
  %t2_8idx = add i64 %tb2, %t2_8off
  %t2_8ptr = getelementptr i16, ptr %src, i64 %t2_8idx
  %t2_8raw = load i16, ptr %t2_8ptr, align 1
  %t2_8wide = zext i16 %t2_8raw to i32
  %t2_8shift = lshr i32 %t2_8wide, 2
  %t2_8 = and i32 %t2_8shift, 255
  %ts2_1 = add i32 %t2_0, %t2_1
  %ts2_2 = add i32 %ts2_1, %t2_2
  %ts2_3 = add i32 %ts2_2, %t2_3
  %ts2_4 = add i32 %ts2_3, %t2_4
  %ts2_5 = add i32 %ts2_4, %t2_5
  %ts2_6 = add i32 %ts2_5, %t2_6
  %ts2_7 = add i32 %ts2_6, %t2_7
  %ts2_8 = add i32 %ts2_7, %t2_8
  %ta2 = add i32 %ts2_8, 4
  %tm2 = mul i32 %ta2, 7282
  %tv2 = lshr i32 %tm2, 16
  %third2 = insertelement <16 x i32> %third1, i32 %tv2, i64 2
  %tx3 = add i64 %bxi, 3
  %txs3 = mul i64 %tx3, 3
  %tb3 = add i64 %tr, %txs3
  %t3_0row = mul i64 %srcW, 0
  %t3_0off = add i64 %t3_0row, 0
  %t3_0idx = add i64 %tb3, %t3_0off
  %t3_0ptr = getelementptr i16, ptr %src, i64 %t3_0idx
  %t3_0raw = load i16, ptr %t3_0ptr, align 1
  %t3_0wide = zext i16 %t3_0raw to i32
  %t3_0shift = lshr i32 %t3_0wide, 2
  %t3_0 = and i32 %t3_0shift, 255
  %t3_1row = mul i64 %srcW, 0
  %t3_1off = add i64 %t3_1row, 1
  %t3_1idx = add i64 %tb3, %t3_1off
  %t3_1ptr = getelementptr i16, ptr %src, i64 %t3_1idx
  %t3_1raw = load i16, ptr %t3_1ptr, align 1
  %t3_1wide = zext i16 %t3_1raw to i32
  %t3_1shift = lshr i32 %t3_1wide, 2
  %t3_1 = and i32 %t3_1shift, 255
  %t3_2row = mul i64 %srcW, 0
  %t3_2off = add i64 %t3_2row, 2
  %t3_2idx = add i64 %tb3, %t3_2off
  %t3_2ptr = getelementptr i16, ptr %src, i64 %t3_2idx
  %t3_2raw = load i16, ptr %t3_2ptr, align 1
  %t3_2wide = zext i16 %t3_2raw to i32
  %t3_2shift = lshr i32 %t3_2wide, 2
  %t3_2 = and i32 %t3_2shift, 255
  %t3_3row = mul i64 %srcW, 1
  %t3_3off = add i64 %t3_3row, 0
  %t3_3idx = add i64 %tb3, %t3_3off
  %t3_3ptr = getelementptr i16, ptr %src, i64 %t3_3idx
  %t3_3raw = load i16, ptr %t3_3ptr, align 1
  %t3_3wide = zext i16 %t3_3raw to i32
  %t3_3shift = lshr i32 %t3_3wide, 2
  %t3_3 = and i32 %t3_3shift, 255
  %t3_4row = mul i64 %srcW, 1
  %t3_4off = add i64 %t3_4row, 1
  %t3_4idx = add i64 %tb3, %t3_4off
  %t3_4ptr = getelementptr i16, ptr %src, i64 %t3_4idx
  %t3_4raw = load i16, ptr %t3_4ptr, align 1
  %t3_4wide = zext i16 %t3_4raw to i32
  %t3_4shift = lshr i32 %t3_4wide, 2
  %t3_4 = and i32 %t3_4shift, 255
  %t3_5row = mul i64 %srcW, 1
  %t3_5off = add i64 %t3_5row, 2
  %t3_5idx = add i64 %tb3, %t3_5off
  %t3_5ptr = getelementptr i16, ptr %src, i64 %t3_5idx
  %t3_5raw = load i16, ptr %t3_5ptr, align 1
  %t3_5wide = zext i16 %t3_5raw to i32
  %t3_5shift = lshr i32 %t3_5wide, 2
  %t3_5 = and i32 %t3_5shift, 255
  %t3_6row = mul i64 %srcW, 2
  %t3_6off = add i64 %t3_6row, 0
  %t3_6idx = add i64 %tb3, %t3_6off
  %t3_6ptr = getelementptr i16, ptr %src, i64 %t3_6idx
  %t3_6raw = load i16, ptr %t3_6ptr, align 1
  %t3_6wide = zext i16 %t3_6raw to i32
  %t3_6shift = lshr i32 %t3_6wide, 2
  %t3_6 = and i32 %t3_6shift, 255
  %t3_7row = mul i64 %srcW, 2
  %t3_7off = add i64 %t3_7row, 1
  %t3_7idx = add i64 %tb3, %t3_7off
  %t3_7ptr = getelementptr i16, ptr %src, i64 %t3_7idx
  %t3_7raw = load i16, ptr %t3_7ptr, align 1
  %t3_7wide = zext i16 %t3_7raw to i32
  %t3_7shift = lshr i32 %t3_7wide, 2
  %t3_7 = and i32 %t3_7shift, 255
  %t3_8row = mul i64 %srcW, 2
  %t3_8off = add i64 %t3_8row, 2
  %t3_8idx = add i64 %tb3, %t3_8off
  %t3_8ptr = getelementptr i16, ptr %src, i64 %t3_8idx
  %t3_8raw = load i16, ptr %t3_8ptr, align 1
  %t3_8wide = zext i16 %t3_8raw to i32
  %t3_8shift = lshr i32 %t3_8wide, 2
  %t3_8 = and i32 %t3_8shift, 255
  %ts3_1 = add i32 %t3_0, %t3_1
  %ts3_2 = add i32 %ts3_1, %t3_2
  %ts3_3 = add i32 %ts3_2, %t3_3
  %ts3_4 = add i32 %ts3_3, %t3_4
  %ts3_5 = add i32 %ts3_4, %t3_5
  %ts3_6 = add i32 %ts3_5, %t3_6
  %ts3_7 = add i32 %ts3_6, %t3_7
  %ts3_8 = add i32 %ts3_7, %t3_8
  %ta3 = add i32 %ts3_8, 4
  %tm3 = mul i32 %ta3, 7282
  %tv3 = lshr i32 %tm3, 16
  %third3 = insertelement <16 x i32> %third2, i32 %tv3, i64 3
  %tx4 = add i64 %bxi, 4
  %txs4 = mul i64 %tx4, 3
  %tb4 = add i64 %tr, %txs4
  %t4_0row = mul i64 %srcW, 0
  %t4_0off = add i64 %t4_0row, 0
  %t4_0idx = add i64 %tb4, %t4_0off
  %t4_0ptr = getelementptr i16, ptr %src, i64 %t4_0idx
  %t4_0raw = load i16, ptr %t4_0ptr, align 1
  %t4_0wide = zext i16 %t4_0raw to i32
  %t4_0shift = lshr i32 %t4_0wide, 2
  %t4_0 = and i32 %t4_0shift, 255
  %t4_1row = mul i64 %srcW, 0
  %t4_1off = add i64 %t4_1row, 1
  %t4_1idx = add i64 %tb4, %t4_1off
  %t4_1ptr = getelementptr i16, ptr %src, i64 %t4_1idx
  %t4_1raw = load i16, ptr %t4_1ptr, align 1
  %t4_1wide = zext i16 %t4_1raw to i32
  %t4_1shift = lshr i32 %t4_1wide, 2
  %t4_1 = and i32 %t4_1shift, 255
  %t4_2row = mul i64 %srcW, 0
  %t4_2off = add i64 %t4_2row, 2
  %t4_2idx = add i64 %tb4, %t4_2off
  %t4_2ptr = getelementptr i16, ptr %src, i64 %t4_2idx
  %t4_2raw = load i16, ptr %t4_2ptr, align 1
  %t4_2wide = zext i16 %t4_2raw to i32
  %t4_2shift = lshr i32 %t4_2wide, 2
  %t4_2 = and i32 %t4_2shift, 255
  %t4_3row = mul i64 %srcW, 1
  %t4_3off = add i64 %t4_3row, 0
  %t4_3idx = add i64 %tb4, %t4_3off
  %t4_3ptr = getelementptr i16, ptr %src, i64 %t4_3idx
  %t4_3raw = load i16, ptr %t4_3ptr, align 1
  %t4_3wide = zext i16 %t4_3raw to i32
  %t4_3shift = lshr i32 %t4_3wide, 2
  %t4_3 = and i32 %t4_3shift, 255
  %t4_4row = mul i64 %srcW, 1
  %t4_4off = add i64 %t4_4row, 1
  %t4_4idx = add i64 %tb4, %t4_4off
  %t4_4ptr = getelementptr i16, ptr %src, i64 %t4_4idx
  %t4_4raw = load i16, ptr %t4_4ptr, align 1
  %t4_4wide = zext i16 %t4_4raw to i32
  %t4_4shift = lshr i32 %t4_4wide, 2
  %t4_4 = and i32 %t4_4shift, 255
  %t4_5row = mul i64 %srcW, 1
  %t4_5off = add i64 %t4_5row, 2
  %t4_5idx = add i64 %tb4, %t4_5off
  %t4_5ptr = getelementptr i16, ptr %src, i64 %t4_5idx
  %t4_5raw = load i16, ptr %t4_5ptr, align 1
  %t4_5wide = zext i16 %t4_5raw to i32
  %t4_5shift = lshr i32 %t4_5wide, 2
  %t4_5 = and i32 %t4_5shift, 255
  %t4_6row = mul i64 %srcW, 2
  %t4_6off = add i64 %t4_6row, 0
  %t4_6idx = add i64 %tb4, %t4_6off
  %t4_6ptr = getelementptr i16, ptr %src, i64 %t4_6idx
  %t4_6raw = load i16, ptr %t4_6ptr, align 1
  %t4_6wide = zext i16 %t4_6raw to i32
  %t4_6shift = lshr i32 %t4_6wide, 2
  %t4_6 = and i32 %t4_6shift, 255
  %t4_7row = mul i64 %srcW, 2
  %t4_7off = add i64 %t4_7row, 1
  %t4_7idx = add i64 %tb4, %t4_7off
  %t4_7ptr = getelementptr i16, ptr %src, i64 %t4_7idx
  %t4_7raw = load i16, ptr %t4_7ptr, align 1
  %t4_7wide = zext i16 %t4_7raw to i32
  %t4_7shift = lshr i32 %t4_7wide, 2
  %t4_7 = and i32 %t4_7shift, 255
  %t4_8row = mul i64 %srcW, 2
  %t4_8off = add i64 %t4_8row, 2
  %t4_8idx = add i64 %tb4, %t4_8off
  %t4_8ptr = getelementptr i16, ptr %src, i64 %t4_8idx
  %t4_8raw = load i16, ptr %t4_8ptr, align 1
  %t4_8wide = zext i16 %t4_8raw to i32
  %t4_8shift = lshr i32 %t4_8wide, 2
  %t4_8 = and i32 %t4_8shift, 255
  %ts4_1 = add i32 %t4_0, %t4_1
  %ts4_2 = add i32 %ts4_1, %t4_2
  %ts4_3 = add i32 %ts4_2, %t4_3
  %ts4_4 = add i32 %ts4_3, %t4_4
  %ts4_5 = add i32 %ts4_4, %t4_5
  %ts4_6 = add i32 %ts4_5, %t4_6
  %ts4_7 = add i32 %ts4_6, %t4_7
  %ts4_8 = add i32 %ts4_7, %t4_8
  %ta4 = add i32 %ts4_8, 4
  %tm4 = mul i32 %ta4, 7282
  %tv4 = lshr i32 %tm4, 16
  %third4 = insertelement <16 x i32> %third3, i32 %tv4, i64 4
  %tx5 = add i64 %bxi, 5
  %txs5 = mul i64 %tx5, 3
  %tb5 = add i64 %tr, %txs5
  %t5_0row = mul i64 %srcW, 0
  %t5_0off = add i64 %t5_0row, 0
  %t5_0idx = add i64 %tb5, %t5_0off
  %t5_0ptr = getelementptr i16, ptr %src, i64 %t5_0idx
  %t5_0raw = load i16, ptr %t5_0ptr, align 1
  %t5_0wide = zext i16 %t5_0raw to i32
  %t5_0shift = lshr i32 %t5_0wide, 2
  %t5_0 = and i32 %t5_0shift, 255
  %t5_1row = mul i64 %srcW, 0
  %t5_1off = add i64 %t5_1row, 1
  %t5_1idx = add i64 %tb5, %t5_1off
  %t5_1ptr = getelementptr i16, ptr %src, i64 %t5_1idx
  %t5_1raw = load i16, ptr %t5_1ptr, align 1
  %t5_1wide = zext i16 %t5_1raw to i32
  %t5_1shift = lshr i32 %t5_1wide, 2
  %t5_1 = and i32 %t5_1shift, 255
  %t5_2row = mul i64 %srcW, 0
  %t5_2off = add i64 %t5_2row, 2
  %t5_2idx = add i64 %tb5, %t5_2off
  %t5_2ptr = getelementptr i16, ptr %src, i64 %t5_2idx
  %t5_2raw = load i16, ptr %t5_2ptr, align 1
  %t5_2wide = zext i16 %t5_2raw to i32
  %t5_2shift = lshr i32 %t5_2wide, 2
  %t5_2 = and i32 %t5_2shift, 255
  %t5_3row = mul i64 %srcW, 1
  %t5_3off = add i64 %t5_3row, 0
  %t5_3idx = add i64 %tb5, %t5_3off
  %t5_3ptr = getelementptr i16, ptr %src, i64 %t5_3idx
  %t5_3raw = load i16, ptr %t5_3ptr, align 1
  %t5_3wide = zext i16 %t5_3raw to i32
  %t5_3shift = lshr i32 %t5_3wide, 2
  %t5_3 = and i32 %t5_3shift, 255
  %t5_4row = mul i64 %srcW, 1
  %t5_4off = add i64 %t5_4row, 1
  %t5_4idx = add i64 %tb5, %t5_4off
  %t5_4ptr = getelementptr i16, ptr %src, i64 %t5_4idx
  %t5_4raw = load i16, ptr %t5_4ptr, align 1
  %t5_4wide = zext i16 %t5_4raw to i32
  %t5_4shift = lshr i32 %t5_4wide, 2
  %t5_4 = and i32 %t5_4shift, 255
  %t5_5row = mul i64 %srcW, 1
  %t5_5off = add i64 %t5_5row, 2
  %t5_5idx = add i64 %tb5, %t5_5off
  %t5_5ptr = getelementptr i16, ptr %src, i64 %t5_5idx
  %t5_5raw = load i16, ptr %t5_5ptr, align 1
  %t5_5wide = zext i16 %t5_5raw to i32
  %t5_5shift = lshr i32 %t5_5wide, 2
  %t5_5 = and i32 %t5_5shift, 255
  %t5_6row = mul i64 %srcW, 2
  %t5_6off = add i64 %t5_6row, 0
  %t5_6idx = add i64 %tb5, %t5_6off
  %t5_6ptr = getelementptr i16, ptr %src, i64 %t5_6idx
  %t5_6raw = load i16, ptr %t5_6ptr, align 1
  %t5_6wide = zext i16 %t5_6raw to i32
  %t5_6shift = lshr i32 %t5_6wide, 2
  %t5_6 = and i32 %t5_6shift, 255
  %t5_7row = mul i64 %srcW, 2
  %t5_7off = add i64 %t5_7row, 1
  %t5_7idx = add i64 %tb5, %t5_7off
  %t5_7ptr = getelementptr i16, ptr %src, i64 %t5_7idx
  %t5_7raw = load i16, ptr %t5_7ptr, align 1
  %t5_7wide = zext i16 %t5_7raw to i32
  %t5_7shift = lshr i32 %t5_7wide, 2
  %t5_7 = and i32 %t5_7shift, 255
  %t5_8row = mul i64 %srcW, 2
  %t5_8off = add i64 %t5_8row, 2
  %t5_8idx = add i64 %tb5, %t5_8off
  %t5_8ptr = getelementptr i16, ptr %src, i64 %t5_8idx
  %t5_8raw = load i16, ptr %t5_8ptr, align 1
  %t5_8wide = zext i16 %t5_8raw to i32
  %t5_8shift = lshr i32 %t5_8wide, 2
  %t5_8 = and i32 %t5_8shift, 255
  %ts5_1 = add i32 %t5_0, %t5_1
  %ts5_2 = add i32 %ts5_1, %t5_2
  %ts5_3 = add i32 %ts5_2, %t5_3
  %ts5_4 = add i32 %ts5_3, %t5_4
  %ts5_5 = add i32 %ts5_4, %t5_5
  %ts5_6 = add i32 %ts5_5, %t5_6
  %ts5_7 = add i32 %ts5_6, %t5_7
  %ts5_8 = add i32 %ts5_7, %t5_8
  %ta5 = add i32 %ts5_8, 4
  %tm5 = mul i32 %ta5, 7282
  %tv5 = lshr i32 %tm5, 16
  %third5 = insertelement <16 x i32> %third4, i32 %tv5, i64 5
  %tx6 = add i64 %bxi, 6
  %txs6 = mul i64 %tx6, 3
  %tb6 = add i64 %tr, %txs6
  %t6_0row = mul i64 %srcW, 0
  %t6_0off = add i64 %t6_0row, 0
  %t6_0idx = add i64 %tb6, %t6_0off
  %t6_0ptr = getelementptr i16, ptr %src, i64 %t6_0idx
  %t6_0raw = load i16, ptr %t6_0ptr, align 1
  %t6_0wide = zext i16 %t6_0raw to i32
  %t6_0shift = lshr i32 %t6_0wide, 2
  %t6_0 = and i32 %t6_0shift, 255
  %t6_1row = mul i64 %srcW, 0
  %t6_1off = add i64 %t6_1row, 1
  %t6_1idx = add i64 %tb6, %t6_1off
  %t6_1ptr = getelementptr i16, ptr %src, i64 %t6_1idx
  %t6_1raw = load i16, ptr %t6_1ptr, align 1
  %t6_1wide = zext i16 %t6_1raw to i32
  %t6_1shift = lshr i32 %t6_1wide, 2
  %t6_1 = and i32 %t6_1shift, 255
  %t6_2row = mul i64 %srcW, 0
  %t6_2off = add i64 %t6_2row, 2
  %t6_2idx = add i64 %tb6, %t6_2off
  %t6_2ptr = getelementptr i16, ptr %src, i64 %t6_2idx
  %t6_2raw = load i16, ptr %t6_2ptr, align 1
  %t6_2wide = zext i16 %t6_2raw to i32
  %t6_2shift = lshr i32 %t6_2wide, 2
  %t6_2 = and i32 %t6_2shift, 255
  %t6_3row = mul i64 %srcW, 1
  %t6_3off = add i64 %t6_3row, 0
  %t6_3idx = add i64 %tb6, %t6_3off
  %t6_3ptr = getelementptr i16, ptr %src, i64 %t6_3idx
  %t6_3raw = load i16, ptr %t6_3ptr, align 1
  %t6_3wide = zext i16 %t6_3raw to i32
  %t6_3shift = lshr i32 %t6_3wide, 2
  %t6_3 = and i32 %t6_3shift, 255
  %t6_4row = mul i64 %srcW, 1
  %t6_4off = add i64 %t6_4row, 1
  %t6_4idx = add i64 %tb6, %t6_4off
  %t6_4ptr = getelementptr i16, ptr %src, i64 %t6_4idx
  %t6_4raw = load i16, ptr %t6_4ptr, align 1
  %t6_4wide = zext i16 %t6_4raw to i32
  %t6_4shift = lshr i32 %t6_4wide, 2
  %t6_4 = and i32 %t6_4shift, 255
  %t6_5row = mul i64 %srcW, 1
  %t6_5off = add i64 %t6_5row, 2
  %t6_5idx = add i64 %tb6, %t6_5off
  %t6_5ptr = getelementptr i16, ptr %src, i64 %t6_5idx
  %t6_5raw = load i16, ptr %t6_5ptr, align 1
  %t6_5wide = zext i16 %t6_5raw to i32
  %t6_5shift = lshr i32 %t6_5wide, 2
  %t6_5 = and i32 %t6_5shift, 255
  %t6_6row = mul i64 %srcW, 2
  %t6_6off = add i64 %t6_6row, 0
  %t6_6idx = add i64 %tb6, %t6_6off
  %t6_6ptr = getelementptr i16, ptr %src, i64 %t6_6idx
  %t6_6raw = load i16, ptr %t6_6ptr, align 1
  %t6_6wide = zext i16 %t6_6raw to i32
  %t6_6shift = lshr i32 %t6_6wide, 2
  %t6_6 = and i32 %t6_6shift, 255
  %t6_7row = mul i64 %srcW, 2
  %t6_7off = add i64 %t6_7row, 1
  %t6_7idx = add i64 %tb6, %t6_7off
  %t6_7ptr = getelementptr i16, ptr %src, i64 %t6_7idx
  %t6_7raw = load i16, ptr %t6_7ptr, align 1
  %t6_7wide = zext i16 %t6_7raw to i32
  %t6_7shift = lshr i32 %t6_7wide, 2
  %t6_7 = and i32 %t6_7shift, 255
  %t6_8row = mul i64 %srcW, 2
  %t6_8off = add i64 %t6_8row, 2
  %t6_8idx = add i64 %tb6, %t6_8off
  %t6_8ptr = getelementptr i16, ptr %src, i64 %t6_8idx
  %t6_8raw = load i16, ptr %t6_8ptr, align 1
  %t6_8wide = zext i16 %t6_8raw to i32
  %t6_8shift = lshr i32 %t6_8wide, 2
  %t6_8 = and i32 %t6_8shift, 255
  %ts6_1 = add i32 %t6_0, %t6_1
  %ts6_2 = add i32 %ts6_1, %t6_2
  %ts6_3 = add i32 %ts6_2, %t6_3
  %ts6_4 = add i32 %ts6_3, %t6_4
  %ts6_5 = add i32 %ts6_4, %t6_5
  %ts6_6 = add i32 %ts6_5, %t6_6
  %ts6_7 = add i32 %ts6_6, %t6_7
  %ts6_8 = add i32 %ts6_7, %t6_8
  %ta6 = add i32 %ts6_8, 4
  %tm6 = mul i32 %ta6, 7282
  %tv6 = lshr i32 %tm6, 16
  %third6 = insertelement <16 x i32> %third5, i32 %tv6, i64 6
  %tx7 = add i64 %bxi, 7
  %txs7 = mul i64 %tx7, 3
  %tb7 = add i64 %tr, %txs7
  %t7_0row = mul i64 %srcW, 0
  %t7_0off = add i64 %t7_0row, 0
  %t7_0idx = add i64 %tb7, %t7_0off
  %t7_0ptr = getelementptr i16, ptr %src, i64 %t7_0idx
  %t7_0raw = load i16, ptr %t7_0ptr, align 1
  %t7_0wide = zext i16 %t7_0raw to i32
  %t7_0shift = lshr i32 %t7_0wide, 2
  %t7_0 = and i32 %t7_0shift, 255
  %t7_1row = mul i64 %srcW, 0
  %t7_1off = add i64 %t7_1row, 1
  %t7_1idx = add i64 %tb7, %t7_1off
  %t7_1ptr = getelementptr i16, ptr %src, i64 %t7_1idx
  %t7_1raw = load i16, ptr %t7_1ptr, align 1
  %t7_1wide = zext i16 %t7_1raw to i32
  %t7_1shift = lshr i32 %t7_1wide, 2
  %t7_1 = and i32 %t7_1shift, 255
  %t7_2row = mul i64 %srcW, 0
  %t7_2off = add i64 %t7_2row, 2
  %t7_2idx = add i64 %tb7, %t7_2off
  %t7_2ptr = getelementptr i16, ptr %src, i64 %t7_2idx
  %t7_2raw = load i16, ptr %t7_2ptr, align 1
  %t7_2wide = zext i16 %t7_2raw to i32
  %t7_2shift = lshr i32 %t7_2wide, 2
  %t7_2 = and i32 %t7_2shift, 255
  %t7_3row = mul i64 %srcW, 1
  %t7_3off = add i64 %t7_3row, 0
  %t7_3idx = add i64 %tb7, %t7_3off
  %t7_3ptr = getelementptr i16, ptr %src, i64 %t7_3idx
  %t7_3raw = load i16, ptr %t7_3ptr, align 1
  %t7_3wide = zext i16 %t7_3raw to i32
  %t7_3shift = lshr i32 %t7_3wide, 2
  %t7_3 = and i32 %t7_3shift, 255
  %t7_4row = mul i64 %srcW, 1
  %t7_4off = add i64 %t7_4row, 1
  %t7_4idx = add i64 %tb7, %t7_4off
  %t7_4ptr = getelementptr i16, ptr %src, i64 %t7_4idx
  %t7_4raw = load i16, ptr %t7_4ptr, align 1
  %t7_4wide = zext i16 %t7_4raw to i32
  %t7_4shift = lshr i32 %t7_4wide, 2
  %t7_4 = and i32 %t7_4shift, 255
  %t7_5row = mul i64 %srcW, 1
  %t7_5off = add i64 %t7_5row, 2
  %t7_5idx = add i64 %tb7, %t7_5off
  %t7_5ptr = getelementptr i16, ptr %src, i64 %t7_5idx
  %t7_5raw = load i16, ptr %t7_5ptr, align 1
  %t7_5wide = zext i16 %t7_5raw to i32
  %t7_5shift = lshr i32 %t7_5wide, 2
  %t7_5 = and i32 %t7_5shift, 255
  %t7_6row = mul i64 %srcW, 2
  %t7_6off = add i64 %t7_6row, 0
  %t7_6idx = add i64 %tb7, %t7_6off
  %t7_6ptr = getelementptr i16, ptr %src, i64 %t7_6idx
  %t7_6raw = load i16, ptr %t7_6ptr, align 1
  %t7_6wide = zext i16 %t7_6raw to i32
  %t7_6shift = lshr i32 %t7_6wide, 2
  %t7_6 = and i32 %t7_6shift, 255
  %t7_7row = mul i64 %srcW, 2
  %t7_7off = add i64 %t7_7row, 1
  %t7_7idx = add i64 %tb7, %t7_7off
  %t7_7ptr = getelementptr i16, ptr %src, i64 %t7_7idx
  %t7_7raw = load i16, ptr %t7_7ptr, align 1
  %t7_7wide = zext i16 %t7_7raw to i32
  %t7_7shift = lshr i32 %t7_7wide, 2
  %t7_7 = and i32 %t7_7shift, 255
  %t7_8row = mul i64 %srcW, 2
  %t7_8off = add i64 %t7_8row, 2
  %t7_8idx = add i64 %tb7, %t7_8off
  %t7_8ptr = getelementptr i16, ptr %src, i64 %t7_8idx
  %t7_8raw = load i16, ptr %t7_8ptr, align 1
  %t7_8wide = zext i16 %t7_8raw to i32
  %t7_8shift = lshr i32 %t7_8wide, 2
  %t7_8 = and i32 %t7_8shift, 255
  %ts7_1 = add i32 %t7_0, %t7_1
  %ts7_2 = add i32 %ts7_1, %t7_2
  %ts7_3 = add i32 %ts7_2, %t7_3
  %ts7_4 = add i32 %ts7_3, %t7_4
  %ts7_5 = add i32 %ts7_4, %t7_5
  %ts7_6 = add i32 %ts7_5, %t7_6
  %ts7_7 = add i32 %ts7_6, %t7_7
  %ts7_8 = add i32 %ts7_7, %t7_8
  %ta7 = add i32 %ts7_8, 4
  %tm7 = mul i32 %ta7, 7282
  %tv7 = lshr i32 %tm7, 16
  %third7 = insertelement <16 x i32> %third6, i32 %tv7, i64 7
  %tx8 = add i64 %bxi, 8
  %txs8 = mul i64 %tx8, 3
  %tb8 = add i64 %tr, %txs8
  %t8_0row = mul i64 %srcW, 0
  %t8_0off = add i64 %t8_0row, 0
  %t8_0idx = add i64 %tb8, %t8_0off
  %t8_0ptr = getelementptr i16, ptr %src, i64 %t8_0idx
  %t8_0raw = load i16, ptr %t8_0ptr, align 1
  %t8_0wide = zext i16 %t8_0raw to i32
  %t8_0shift = lshr i32 %t8_0wide, 2
  %t8_0 = and i32 %t8_0shift, 255
  %t8_1row = mul i64 %srcW, 0
  %t8_1off = add i64 %t8_1row, 1
  %t8_1idx = add i64 %tb8, %t8_1off
  %t8_1ptr = getelementptr i16, ptr %src, i64 %t8_1idx
  %t8_1raw = load i16, ptr %t8_1ptr, align 1
  %t8_1wide = zext i16 %t8_1raw to i32
  %t8_1shift = lshr i32 %t8_1wide, 2
  %t8_1 = and i32 %t8_1shift, 255
  %t8_2row = mul i64 %srcW, 0
  %t8_2off = add i64 %t8_2row, 2
  %t8_2idx = add i64 %tb8, %t8_2off
  %t8_2ptr = getelementptr i16, ptr %src, i64 %t8_2idx
  %t8_2raw = load i16, ptr %t8_2ptr, align 1
  %t8_2wide = zext i16 %t8_2raw to i32
  %t8_2shift = lshr i32 %t8_2wide, 2
  %t8_2 = and i32 %t8_2shift, 255
  %t8_3row = mul i64 %srcW, 1
  %t8_3off = add i64 %t8_3row, 0
  %t8_3idx = add i64 %tb8, %t8_3off
  %t8_3ptr = getelementptr i16, ptr %src, i64 %t8_3idx
  %t8_3raw = load i16, ptr %t8_3ptr, align 1
  %t8_3wide = zext i16 %t8_3raw to i32
  %t8_3shift = lshr i32 %t8_3wide, 2
  %t8_3 = and i32 %t8_3shift, 255
  %t8_4row = mul i64 %srcW, 1
  %t8_4off = add i64 %t8_4row, 1
  %t8_4idx = add i64 %tb8, %t8_4off
  %t8_4ptr = getelementptr i16, ptr %src, i64 %t8_4idx
  %t8_4raw = load i16, ptr %t8_4ptr, align 1
  %t8_4wide = zext i16 %t8_4raw to i32
  %t8_4shift = lshr i32 %t8_4wide, 2
  %t8_4 = and i32 %t8_4shift, 255
  %t8_5row = mul i64 %srcW, 1
  %t8_5off = add i64 %t8_5row, 2
  %t8_5idx = add i64 %tb8, %t8_5off
  %t8_5ptr = getelementptr i16, ptr %src, i64 %t8_5idx
  %t8_5raw = load i16, ptr %t8_5ptr, align 1
  %t8_5wide = zext i16 %t8_5raw to i32
  %t8_5shift = lshr i32 %t8_5wide, 2
  %t8_5 = and i32 %t8_5shift, 255
  %t8_6row = mul i64 %srcW, 2
  %t8_6off = add i64 %t8_6row, 0
  %t8_6idx = add i64 %tb8, %t8_6off
  %t8_6ptr = getelementptr i16, ptr %src, i64 %t8_6idx
  %t8_6raw = load i16, ptr %t8_6ptr, align 1
  %t8_6wide = zext i16 %t8_6raw to i32
  %t8_6shift = lshr i32 %t8_6wide, 2
  %t8_6 = and i32 %t8_6shift, 255
  %t8_7row = mul i64 %srcW, 2
  %t8_7off = add i64 %t8_7row, 1
  %t8_7idx = add i64 %tb8, %t8_7off
  %t8_7ptr = getelementptr i16, ptr %src, i64 %t8_7idx
  %t8_7raw = load i16, ptr %t8_7ptr, align 1
  %t8_7wide = zext i16 %t8_7raw to i32
  %t8_7shift = lshr i32 %t8_7wide, 2
  %t8_7 = and i32 %t8_7shift, 255
  %t8_8row = mul i64 %srcW, 2
  %t8_8off = add i64 %t8_8row, 2
  %t8_8idx = add i64 %tb8, %t8_8off
  %t8_8ptr = getelementptr i16, ptr %src, i64 %t8_8idx
  %t8_8raw = load i16, ptr %t8_8ptr, align 1
  %t8_8wide = zext i16 %t8_8raw to i32
  %t8_8shift = lshr i32 %t8_8wide, 2
  %t8_8 = and i32 %t8_8shift, 255
  %ts8_1 = add i32 %t8_0, %t8_1
  %ts8_2 = add i32 %ts8_1, %t8_2
  %ts8_3 = add i32 %ts8_2, %t8_3
  %ts8_4 = add i32 %ts8_3, %t8_4
  %ts8_5 = add i32 %ts8_4, %t8_5
  %ts8_6 = add i32 %ts8_5, %t8_6
  %ts8_7 = add i32 %ts8_6, %t8_7
  %ts8_8 = add i32 %ts8_7, %t8_8
  %ta8 = add i32 %ts8_8, 4
  %tm8 = mul i32 %ta8, 7282
  %tv8 = lshr i32 %tm8, 16
  %third8 = insertelement <16 x i32> %third7, i32 %tv8, i64 8
  %tx9 = add i64 %bxi, 9
  %txs9 = mul i64 %tx9, 3
  %tb9 = add i64 %tr, %txs9
  %t9_0row = mul i64 %srcW, 0
  %t9_0off = add i64 %t9_0row, 0
  %t9_0idx = add i64 %tb9, %t9_0off
  %t9_0ptr = getelementptr i16, ptr %src, i64 %t9_0idx
  %t9_0raw = load i16, ptr %t9_0ptr, align 1
  %t9_0wide = zext i16 %t9_0raw to i32
  %t9_0shift = lshr i32 %t9_0wide, 2
  %t9_0 = and i32 %t9_0shift, 255
  %t9_1row = mul i64 %srcW, 0
  %t9_1off = add i64 %t9_1row, 1
  %t9_1idx = add i64 %tb9, %t9_1off
  %t9_1ptr = getelementptr i16, ptr %src, i64 %t9_1idx
  %t9_1raw = load i16, ptr %t9_1ptr, align 1
  %t9_1wide = zext i16 %t9_1raw to i32
  %t9_1shift = lshr i32 %t9_1wide, 2
  %t9_1 = and i32 %t9_1shift, 255
  %t9_2row = mul i64 %srcW, 0
  %t9_2off = add i64 %t9_2row, 2
  %t9_2idx = add i64 %tb9, %t9_2off
  %t9_2ptr = getelementptr i16, ptr %src, i64 %t9_2idx
  %t9_2raw = load i16, ptr %t9_2ptr, align 1
  %t9_2wide = zext i16 %t9_2raw to i32
  %t9_2shift = lshr i32 %t9_2wide, 2
  %t9_2 = and i32 %t9_2shift, 255
  %t9_3row = mul i64 %srcW, 1
  %t9_3off = add i64 %t9_3row, 0
  %t9_3idx = add i64 %tb9, %t9_3off
  %t9_3ptr = getelementptr i16, ptr %src, i64 %t9_3idx
  %t9_3raw = load i16, ptr %t9_3ptr, align 1
  %t9_3wide = zext i16 %t9_3raw to i32
  %t9_3shift = lshr i32 %t9_3wide, 2
  %t9_3 = and i32 %t9_3shift, 255
  %t9_4row = mul i64 %srcW, 1
  %t9_4off = add i64 %t9_4row, 1
  %t9_4idx = add i64 %tb9, %t9_4off
  %t9_4ptr = getelementptr i16, ptr %src, i64 %t9_4idx
  %t9_4raw = load i16, ptr %t9_4ptr, align 1
  %t9_4wide = zext i16 %t9_4raw to i32
  %t9_4shift = lshr i32 %t9_4wide, 2
  %t9_4 = and i32 %t9_4shift, 255
  %t9_5row = mul i64 %srcW, 1
  %t9_5off = add i64 %t9_5row, 2
  %t9_5idx = add i64 %tb9, %t9_5off
  %t9_5ptr = getelementptr i16, ptr %src, i64 %t9_5idx
  %t9_5raw = load i16, ptr %t9_5ptr, align 1
  %t9_5wide = zext i16 %t9_5raw to i32
  %t9_5shift = lshr i32 %t9_5wide, 2
  %t9_5 = and i32 %t9_5shift, 255
  %t9_6row = mul i64 %srcW, 2
  %t9_6off = add i64 %t9_6row, 0
  %t9_6idx = add i64 %tb9, %t9_6off
  %t9_6ptr = getelementptr i16, ptr %src, i64 %t9_6idx
  %t9_6raw = load i16, ptr %t9_6ptr, align 1
  %t9_6wide = zext i16 %t9_6raw to i32
  %t9_6shift = lshr i32 %t9_6wide, 2
  %t9_6 = and i32 %t9_6shift, 255
  %t9_7row = mul i64 %srcW, 2
  %t9_7off = add i64 %t9_7row, 1
  %t9_7idx = add i64 %tb9, %t9_7off
  %t9_7ptr = getelementptr i16, ptr %src, i64 %t9_7idx
  %t9_7raw = load i16, ptr %t9_7ptr, align 1
  %t9_7wide = zext i16 %t9_7raw to i32
  %t9_7shift = lshr i32 %t9_7wide, 2
  %t9_7 = and i32 %t9_7shift, 255
  %t9_8row = mul i64 %srcW, 2
  %t9_8off = add i64 %t9_8row, 2
  %t9_8idx = add i64 %tb9, %t9_8off
  %t9_8ptr = getelementptr i16, ptr %src, i64 %t9_8idx
  %t9_8raw = load i16, ptr %t9_8ptr, align 1
  %t9_8wide = zext i16 %t9_8raw to i32
  %t9_8shift = lshr i32 %t9_8wide, 2
  %t9_8 = and i32 %t9_8shift, 255
  %ts9_1 = add i32 %t9_0, %t9_1
  %ts9_2 = add i32 %ts9_1, %t9_2
  %ts9_3 = add i32 %ts9_2, %t9_3
  %ts9_4 = add i32 %ts9_3, %t9_4
  %ts9_5 = add i32 %ts9_4, %t9_5
  %ts9_6 = add i32 %ts9_5, %t9_6
  %ts9_7 = add i32 %ts9_6, %t9_7
  %ts9_8 = add i32 %ts9_7, %t9_8
  %ta9 = add i32 %ts9_8, 4
  %tm9 = mul i32 %ta9, 7282
  %tv9 = lshr i32 %tm9, 16
  %third9 = insertelement <16 x i32> %third8, i32 %tv9, i64 9
  %tx10 = add i64 %bxi, 10
  %txs10 = mul i64 %tx10, 3
  %tb10 = add i64 %tr, %txs10
  %t10_0row = mul i64 %srcW, 0
  %t10_0off = add i64 %t10_0row, 0
  %t10_0idx = add i64 %tb10, %t10_0off
  %t10_0ptr = getelementptr i16, ptr %src, i64 %t10_0idx
  %t10_0raw = load i16, ptr %t10_0ptr, align 1
  %t10_0wide = zext i16 %t10_0raw to i32
  %t10_0shift = lshr i32 %t10_0wide, 2
  %t10_0 = and i32 %t10_0shift, 255
  %t10_1row = mul i64 %srcW, 0
  %t10_1off = add i64 %t10_1row, 1
  %t10_1idx = add i64 %tb10, %t10_1off
  %t10_1ptr = getelementptr i16, ptr %src, i64 %t10_1idx
  %t10_1raw = load i16, ptr %t10_1ptr, align 1
  %t10_1wide = zext i16 %t10_1raw to i32
  %t10_1shift = lshr i32 %t10_1wide, 2
  %t10_1 = and i32 %t10_1shift, 255
  %t10_2row = mul i64 %srcW, 0
  %t10_2off = add i64 %t10_2row, 2
  %t10_2idx = add i64 %tb10, %t10_2off
  %t10_2ptr = getelementptr i16, ptr %src, i64 %t10_2idx
  %t10_2raw = load i16, ptr %t10_2ptr, align 1
  %t10_2wide = zext i16 %t10_2raw to i32
  %t10_2shift = lshr i32 %t10_2wide, 2
  %t10_2 = and i32 %t10_2shift, 255
  %t10_3row = mul i64 %srcW, 1
  %t10_3off = add i64 %t10_3row, 0
  %t10_3idx = add i64 %tb10, %t10_3off
  %t10_3ptr = getelementptr i16, ptr %src, i64 %t10_3idx
  %t10_3raw = load i16, ptr %t10_3ptr, align 1
  %t10_3wide = zext i16 %t10_3raw to i32
  %t10_3shift = lshr i32 %t10_3wide, 2
  %t10_3 = and i32 %t10_3shift, 255
  %t10_4row = mul i64 %srcW, 1
  %t10_4off = add i64 %t10_4row, 1
  %t10_4idx = add i64 %tb10, %t10_4off
  %t10_4ptr = getelementptr i16, ptr %src, i64 %t10_4idx
  %t10_4raw = load i16, ptr %t10_4ptr, align 1
  %t10_4wide = zext i16 %t10_4raw to i32
  %t10_4shift = lshr i32 %t10_4wide, 2
  %t10_4 = and i32 %t10_4shift, 255
  %t10_5row = mul i64 %srcW, 1
  %t10_5off = add i64 %t10_5row, 2
  %t10_5idx = add i64 %tb10, %t10_5off
  %t10_5ptr = getelementptr i16, ptr %src, i64 %t10_5idx
  %t10_5raw = load i16, ptr %t10_5ptr, align 1
  %t10_5wide = zext i16 %t10_5raw to i32
  %t10_5shift = lshr i32 %t10_5wide, 2
  %t10_5 = and i32 %t10_5shift, 255
  %t10_6row = mul i64 %srcW, 2
  %t10_6off = add i64 %t10_6row, 0
  %t10_6idx = add i64 %tb10, %t10_6off
  %t10_6ptr = getelementptr i16, ptr %src, i64 %t10_6idx
  %t10_6raw = load i16, ptr %t10_6ptr, align 1
  %t10_6wide = zext i16 %t10_6raw to i32
  %t10_6shift = lshr i32 %t10_6wide, 2
  %t10_6 = and i32 %t10_6shift, 255
  %t10_7row = mul i64 %srcW, 2
  %t10_7off = add i64 %t10_7row, 1
  %t10_7idx = add i64 %tb10, %t10_7off
  %t10_7ptr = getelementptr i16, ptr %src, i64 %t10_7idx
  %t10_7raw = load i16, ptr %t10_7ptr, align 1
  %t10_7wide = zext i16 %t10_7raw to i32
  %t10_7shift = lshr i32 %t10_7wide, 2
  %t10_7 = and i32 %t10_7shift, 255
  %t10_8row = mul i64 %srcW, 2
  %t10_8off = add i64 %t10_8row, 2
  %t10_8idx = add i64 %tb10, %t10_8off
  %t10_8ptr = getelementptr i16, ptr %src, i64 %t10_8idx
  %t10_8raw = load i16, ptr %t10_8ptr, align 1
  %t10_8wide = zext i16 %t10_8raw to i32
  %t10_8shift = lshr i32 %t10_8wide, 2
  %t10_8 = and i32 %t10_8shift, 255
  %ts10_1 = add i32 %t10_0, %t10_1
  %ts10_2 = add i32 %ts10_1, %t10_2
  %ts10_3 = add i32 %ts10_2, %t10_3
  %ts10_4 = add i32 %ts10_3, %t10_4
  %ts10_5 = add i32 %ts10_4, %t10_5
  %ts10_6 = add i32 %ts10_5, %t10_6
  %ts10_7 = add i32 %ts10_6, %t10_7
  %ts10_8 = add i32 %ts10_7, %t10_8
  %ta10 = add i32 %ts10_8, 4
  %tm10 = mul i32 %ta10, 7282
  %tv10 = lshr i32 %tm10, 16
  %third10 = insertelement <16 x i32> %third9, i32 %tv10, i64 10
  %tx11 = add i64 %bxi, 11
  %txs11 = mul i64 %tx11, 3
  %tb11 = add i64 %tr, %txs11
  %t11_0row = mul i64 %srcW, 0
  %t11_0off = add i64 %t11_0row, 0
  %t11_0idx = add i64 %tb11, %t11_0off
  %t11_0ptr = getelementptr i16, ptr %src, i64 %t11_0idx
  %t11_0raw = load i16, ptr %t11_0ptr, align 1
  %t11_0wide = zext i16 %t11_0raw to i32
  %t11_0shift = lshr i32 %t11_0wide, 2
  %t11_0 = and i32 %t11_0shift, 255
  %t11_1row = mul i64 %srcW, 0
  %t11_1off = add i64 %t11_1row, 1
  %t11_1idx = add i64 %tb11, %t11_1off
  %t11_1ptr = getelementptr i16, ptr %src, i64 %t11_1idx
  %t11_1raw = load i16, ptr %t11_1ptr, align 1
  %t11_1wide = zext i16 %t11_1raw to i32
  %t11_1shift = lshr i32 %t11_1wide, 2
  %t11_1 = and i32 %t11_1shift, 255
  %t11_2row = mul i64 %srcW, 0
  %t11_2off = add i64 %t11_2row, 2
  %t11_2idx = add i64 %tb11, %t11_2off
  %t11_2ptr = getelementptr i16, ptr %src, i64 %t11_2idx
  %t11_2raw = load i16, ptr %t11_2ptr, align 1
  %t11_2wide = zext i16 %t11_2raw to i32
  %t11_2shift = lshr i32 %t11_2wide, 2
  %t11_2 = and i32 %t11_2shift, 255
  %t11_3row = mul i64 %srcW, 1
  %t11_3off = add i64 %t11_3row, 0
  %t11_3idx = add i64 %tb11, %t11_3off
  %t11_3ptr = getelementptr i16, ptr %src, i64 %t11_3idx
  %t11_3raw = load i16, ptr %t11_3ptr, align 1
  %t11_3wide = zext i16 %t11_3raw to i32
  %t11_3shift = lshr i32 %t11_3wide, 2
  %t11_3 = and i32 %t11_3shift, 255
  %t11_4row = mul i64 %srcW, 1
  %t11_4off = add i64 %t11_4row, 1
  %t11_4idx = add i64 %tb11, %t11_4off
  %t11_4ptr = getelementptr i16, ptr %src, i64 %t11_4idx
  %t11_4raw = load i16, ptr %t11_4ptr, align 1
  %t11_4wide = zext i16 %t11_4raw to i32
  %t11_4shift = lshr i32 %t11_4wide, 2
  %t11_4 = and i32 %t11_4shift, 255
  %t11_5row = mul i64 %srcW, 1
  %t11_5off = add i64 %t11_5row, 2
  %t11_5idx = add i64 %tb11, %t11_5off
  %t11_5ptr = getelementptr i16, ptr %src, i64 %t11_5idx
  %t11_5raw = load i16, ptr %t11_5ptr, align 1
  %t11_5wide = zext i16 %t11_5raw to i32
  %t11_5shift = lshr i32 %t11_5wide, 2
  %t11_5 = and i32 %t11_5shift, 255
  %t11_6row = mul i64 %srcW, 2
  %t11_6off = add i64 %t11_6row, 0
  %t11_6idx = add i64 %tb11, %t11_6off
  %t11_6ptr = getelementptr i16, ptr %src, i64 %t11_6idx
  %t11_6raw = load i16, ptr %t11_6ptr, align 1
  %t11_6wide = zext i16 %t11_6raw to i32
  %t11_6shift = lshr i32 %t11_6wide, 2
  %t11_6 = and i32 %t11_6shift, 255
  %t11_7row = mul i64 %srcW, 2
  %t11_7off = add i64 %t11_7row, 1
  %t11_7idx = add i64 %tb11, %t11_7off
  %t11_7ptr = getelementptr i16, ptr %src, i64 %t11_7idx
  %t11_7raw = load i16, ptr %t11_7ptr, align 1
  %t11_7wide = zext i16 %t11_7raw to i32
  %t11_7shift = lshr i32 %t11_7wide, 2
  %t11_7 = and i32 %t11_7shift, 255
  %t11_8row = mul i64 %srcW, 2
  %t11_8off = add i64 %t11_8row, 2
  %t11_8idx = add i64 %tb11, %t11_8off
  %t11_8ptr = getelementptr i16, ptr %src, i64 %t11_8idx
  %t11_8raw = load i16, ptr %t11_8ptr, align 1
  %t11_8wide = zext i16 %t11_8raw to i32
  %t11_8shift = lshr i32 %t11_8wide, 2
  %t11_8 = and i32 %t11_8shift, 255
  %ts11_1 = add i32 %t11_0, %t11_1
  %ts11_2 = add i32 %ts11_1, %t11_2
  %ts11_3 = add i32 %ts11_2, %t11_3
  %ts11_4 = add i32 %ts11_3, %t11_4
  %ts11_5 = add i32 %ts11_4, %t11_5
  %ts11_6 = add i32 %ts11_5, %t11_6
  %ts11_7 = add i32 %ts11_6, %t11_7
  %ts11_8 = add i32 %ts11_7, %t11_8
  %ta11 = add i32 %ts11_8, 4
  %tm11 = mul i32 %ta11, 7282
  %tv11 = lshr i32 %tm11, 16
  %third11 = insertelement <16 x i32> %third10, i32 %tv11, i64 11
  %tx12 = add i64 %bxi, 12
  %txs12 = mul i64 %tx12, 3
  %tb12 = add i64 %tr, %txs12
  %t12_0row = mul i64 %srcW, 0
  %t12_0off = add i64 %t12_0row, 0
  %t12_0idx = add i64 %tb12, %t12_0off
  %t12_0ptr = getelementptr i16, ptr %src, i64 %t12_0idx
  %t12_0raw = load i16, ptr %t12_0ptr, align 1
  %t12_0wide = zext i16 %t12_0raw to i32
  %t12_0shift = lshr i32 %t12_0wide, 2
  %t12_0 = and i32 %t12_0shift, 255
  %t12_1row = mul i64 %srcW, 0
  %t12_1off = add i64 %t12_1row, 1
  %t12_1idx = add i64 %tb12, %t12_1off
  %t12_1ptr = getelementptr i16, ptr %src, i64 %t12_1idx
  %t12_1raw = load i16, ptr %t12_1ptr, align 1
  %t12_1wide = zext i16 %t12_1raw to i32
  %t12_1shift = lshr i32 %t12_1wide, 2
  %t12_1 = and i32 %t12_1shift, 255
  %t12_2row = mul i64 %srcW, 0
  %t12_2off = add i64 %t12_2row, 2
  %t12_2idx = add i64 %tb12, %t12_2off
  %t12_2ptr = getelementptr i16, ptr %src, i64 %t12_2idx
  %t12_2raw = load i16, ptr %t12_2ptr, align 1
  %t12_2wide = zext i16 %t12_2raw to i32
  %t12_2shift = lshr i32 %t12_2wide, 2
  %t12_2 = and i32 %t12_2shift, 255
  %t12_3row = mul i64 %srcW, 1
  %t12_3off = add i64 %t12_3row, 0
  %t12_3idx = add i64 %tb12, %t12_3off
  %t12_3ptr = getelementptr i16, ptr %src, i64 %t12_3idx
  %t12_3raw = load i16, ptr %t12_3ptr, align 1
  %t12_3wide = zext i16 %t12_3raw to i32
  %t12_3shift = lshr i32 %t12_3wide, 2
  %t12_3 = and i32 %t12_3shift, 255
  %t12_4row = mul i64 %srcW, 1
  %t12_4off = add i64 %t12_4row, 1
  %t12_4idx = add i64 %tb12, %t12_4off
  %t12_4ptr = getelementptr i16, ptr %src, i64 %t12_4idx
  %t12_4raw = load i16, ptr %t12_4ptr, align 1
  %t12_4wide = zext i16 %t12_4raw to i32
  %t12_4shift = lshr i32 %t12_4wide, 2
  %t12_4 = and i32 %t12_4shift, 255
  %t12_5row = mul i64 %srcW, 1
  %t12_5off = add i64 %t12_5row, 2
  %t12_5idx = add i64 %tb12, %t12_5off
  %t12_5ptr = getelementptr i16, ptr %src, i64 %t12_5idx
  %t12_5raw = load i16, ptr %t12_5ptr, align 1
  %t12_5wide = zext i16 %t12_5raw to i32
  %t12_5shift = lshr i32 %t12_5wide, 2
  %t12_5 = and i32 %t12_5shift, 255
  %t12_6row = mul i64 %srcW, 2
  %t12_6off = add i64 %t12_6row, 0
  %t12_6idx = add i64 %tb12, %t12_6off
  %t12_6ptr = getelementptr i16, ptr %src, i64 %t12_6idx
  %t12_6raw = load i16, ptr %t12_6ptr, align 1
  %t12_6wide = zext i16 %t12_6raw to i32
  %t12_6shift = lshr i32 %t12_6wide, 2
  %t12_6 = and i32 %t12_6shift, 255
  %t12_7row = mul i64 %srcW, 2
  %t12_7off = add i64 %t12_7row, 1
  %t12_7idx = add i64 %tb12, %t12_7off
  %t12_7ptr = getelementptr i16, ptr %src, i64 %t12_7idx
  %t12_7raw = load i16, ptr %t12_7ptr, align 1
  %t12_7wide = zext i16 %t12_7raw to i32
  %t12_7shift = lshr i32 %t12_7wide, 2
  %t12_7 = and i32 %t12_7shift, 255
  %t12_8row = mul i64 %srcW, 2
  %t12_8off = add i64 %t12_8row, 2
  %t12_8idx = add i64 %tb12, %t12_8off
  %t12_8ptr = getelementptr i16, ptr %src, i64 %t12_8idx
  %t12_8raw = load i16, ptr %t12_8ptr, align 1
  %t12_8wide = zext i16 %t12_8raw to i32
  %t12_8shift = lshr i32 %t12_8wide, 2
  %t12_8 = and i32 %t12_8shift, 255
  %ts12_1 = add i32 %t12_0, %t12_1
  %ts12_2 = add i32 %ts12_1, %t12_2
  %ts12_3 = add i32 %ts12_2, %t12_3
  %ts12_4 = add i32 %ts12_3, %t12_4
  %ts12_5 = add i32 %ts12_4, %t12_5
  %ts12_6 = add i32 %ts12_5, %t12_6
  %ts12_7 = add i32 %ts12_6, %t12_7
  %ts12_8 = add i32 %ts12_7, %t12_8
  %ta12 = add i32 %ts12_8, 4
  %tm12 = mul i32 %ta12, 7282
  %tv12 = lshr i32 %tm12, 16
  %third12 = insertelement <16 x i32> %third11, i32 %tv12, i64 12
  %tx13 = add i64 %bxi, 13
  %txs13 = mul i64 %tx13, 3
  %tb13 = add i64 %tr, %txs13
  %t13_0row = mul i64 %srcW, 0
  %t13_0off = add i64 %t13_0row, 0
  %t13_0idx = add i64 %tb13, %t13_0off
  %t13_0ptr = getelementptr i16, ptr %src, i64 %t13_0idx
  %t13_0raw = load i16, ptr %t13_0ptr, align 1
  %t13_0wide = zext i16 %t13_0raw to i32
  %t13_0shift = lshr i32 %t13_0wide, 2
  %t13_0 = and i32 %t13_0shift, 255
  %t13_1row = mul i64 %srcW, 0
  %t13_1off = add i64 %t13_1row, 1
  %t13_1idx = add i64 %tb13, %t13_1off
  %t13_1ptr = getelementptr i16, ptr %src, i64 %t13_1idx
  %t13_1raw = load i16, ptr %t13_1ptr, align 1
  %t13_1wide = zext i16 %t13_1raw to i32
  %t13_1shift = lshr i32 %t13_1wide, 2
  %t13_1 = and i32 %t13_1shift, 255
  %t13_2row = mul i64 %srcW, 0
  %t13_2off = add i64 %t13_2row, 2
  %t13_2idx = add i64 %tb13, %t13_2off
  %t13_2ptr = getelementptr i16, ptr %src, i64 %t13_2idx
  %t13_2raw = load i16, ptr %t13_2ptr, align 1
  %t13_2wide = zext i16 %t13_2raw to i32
  %t13_2shift = lshr i32 %t13_2wide, 2
  %t13_2 = and i32 %t13_2shift, 255
  %t13_3row = mul i64 %srcW, 1
  %t13_3off = add i64 %t13_3row, 0
  %t13_3idx = add i64 %tb13, %t13_3off
  %t13_3ptr = getelementptr i16, ptr %src, i64 %t13_3idx
  %t13_3raw = load i16, ptr %t13_3ptr, align 1
  %t13_3wide = zext i16 %t13_3raw to i32
  %t13_3shift = lshr i32 %t13_3wide, 2
  %t13_3 = and i32 %t13_3shift, 255
  %t13_4row = mul i64 %srcW, 1
  %t13_4off = add i64 %t13_4row, 1
  %t13_4idx = add i64 %tb13, %t13_4off
  %t13_4ptr = getelementptr i16, ptr %src, i64 %t13_4idx
  %t13_4raw = load i16, ptr %t13_4ptr, align 1
  %t13_4wide = zext i16 %t13_4raw to i32
  %t13_4shift = lshr i32 %t13_4wide, 2
  %t13_4 = and i32 %t13_4shift, 255
  %t13_5row = mul i64 %srcW, 1
  %t13_5off = add i64 %t13_5row, 2
  %t13_5idx = add i64 %tb13, %t13_5off
  %t13_5ptr = getelementptr i16, ptr %src, i64 %t13_5idx
  %t13_5raw = load i16, ptr %t13_5ptr, align 1
  %t13_5wide = zext i16 %t13_5raw to i32
  %t13_5shift = lshr i32 %t13_5wide, 2
  %t13_5 = and i32 %t13_5shift, 255
  %t13_6row = mul i64 %srcW, 2
  %t13_6off = add i64 %t13_6row, 0
  %t13_6idx = add i64 %tb13, %t13_6off
  %t13_6ptr = getelementptr i16, ptr %src, i64 %t13_6idx
  %t13_6raw = load i16, ptr %t13_6ptr, align 1
  %t13_6wide = zext i16 %t13_6raw to i32
  %t13_6shift = lshr i32 %t13_6wide, 2
  %t13_6 = and i32 %t13_6shift, 255
  %t13_7row = mul i64 %srcW, 2
  %t13_7off = add i64 %t13_7row, 1
  %t13_7idx = add i64 %tb13, %t13_7off
  %t13_7ptr = getelementptr i16, ptr %src, i64 %t13_7idx
  %t13_7raw = load i16, ptr %t13_7ptr, align 1
  %t13_7wide = zext i16 %t13_7raw to i32
  %t13_7shift = lshr i32 %t13_7wide, 2
  %t13_7 = and i32 %t13_7shift, 255
  %t13_8row = mul i64 %srcW, 2
  %t13_8off = add i64 %t13_8row, 2
  %t13_8idx = add i64 %tb13, %t13_8off
  %t13_8ptr = getelementptr i16, ptr %src, i64 %t13_8idx
  %t13_8raw = load i16, ptr %t13_8ptr, align 1
  %t13_8wide = zext i16 %t13_8raw to i32
  %t13_8shift = lshr i32 %t13_8wide, 2
  %t13_8 = and i32 %t13_8shift, 255
  %ts13_1 = add i32 %t13_0, %t13_1
  %ts13_2 = add i32 %ts13_1, %t13_2
  %ts13_3 = add i32 %ts13_2, %t13_3
  %ts13_4 = add i32 %ts13_3, %t13_4
  %ts13_5 = add i32 %ts13_4, %t13_5
  %ts13_6 = add i32 %ts13_5, %t13_6
  %ts13_7 = add i32 %ts13_6, %t13_7
  %ts13_8 = add i32 %ts13_7, %t13_8
  %ta13 = add i32 %ts13_8, 4
  %tm13 = mul i32 %ta13, 7282
  %tv13 = lshr i32 %tm13, 16
  %third13 = insertelement <16 x i32> %third12, i32 %tv13, i64 13
  %tx14 = add i64 %bxi, 14
  %txs14 = mul i64 %tx14, 3
  %tb14 = add i64 %tr, %txs14
  %t14_0row = mul i64 %srcW, 0
  %t14_0off = add i64 %t14_0row, 0
  %t14_0idx = add i64 %tb14, %t14_0off
  %t14_0ptr = getelementptr i16, ptr %src, i64 %t14_0idx
  %t14_0raw = load i16, ptr %t14_0ptr, align 1
  %t14_0wide = zext i16 %t14_0raw to i32
  %t14_0shift = lshr i32 %t14_0wide, 2
  %t14_0 = and i32 %t14_0shift, 255
  %t14_1row = mul i64 %srcW, 0
  %t14_1off = add i64 %t14_1row, 1
  %t14_1idx = add i64 %tb14, %t14_1off
  %t14_1ptr = getelementptr i16, ptr %src, i64 %t14_1idx
  %t14_1raw = load i16, ptr %t14_1ptr, align 1
  %t14_1wide = zext i16 %t14_1raw to i32
  %t14_1shift = lshr i32 %t14_1wide, 2
  %t14_1 = and i32 %t14_1shift, 255
  %t14_2row = mul i64 %srcW, 0
  %t14_2off = add i64 %t14_2row, 2
  %t14_2idx = add i64 %tb14, %t14_2off
  %t14_2ptr = getelementptr i16, ptr %src, i64 %t14_2idx
  %t14_2raw = load i16, ptr %t14_2ptr, align 1
  %t14_2wide = zext i16 %t14_2raw to i32
  %t14_2shift = lshr i32 %t14_2wide, 2
  %t14_2 = and i32 %t14_2shift, 255
  %t14_3row = mul i64 %srcW, 1
  %t14_3off = add i64 %t14_3row, 0
  %t14_3idx = add i64 %tb14, %t14_3off
  %t14_3ptr = getelementptr i16, ptr %src, i64 %t14_3idx
  %t14_3raw = load i16, ptr %t14_3ptr, align 1
  %t14_3wide = zext i16 %t14_3raw to i32
  %t14_3shift = lshr i32 %t14_3wide, 2
  %t14_3 = and i32 %t14_3shift, 255
  %t14_4row = mul i64 %srcW, 1
  %t14_4off = add i64 %t14_4row, 1
  %t14_4idx = add i64 %tb14, %t14_4off
  %t14_4ptr = getelementptr i16, ptr %src, i64 %t14_4idx
  %t14_4raw = load i16, ptr %t14_4ptr, align 1
  %t14_4wide = zext i16 %t14_4raw to i32
  %t14_4shift = lshr i32 %t14_4wide, 2
  %t14_4 = and i32 %t14_4shift, 255
  %t14_5row = mul i64 %srcW, 1
  %t14_5off = add i64 %t14_5row, 2
  %t14_5idx = add i64 %tb14, %t14_5off
  %t14_5ptr = getelementptr i16, ptr %src, i64 %t14_5idx
  %t14_5raw = load i16, ptr %t14_5ptr, align 1
  %t14_5wide = zext i16 %t14_5raw to i32
  %t14_5shift = lshr i32 %t14_5wide, 2
  %t14_5 = and i32 %t14_5shift, 255
  %t14_6row = mul i64 %srcW, 2
  %t14_6off = add i64 %t14_6row, 0
  %t14_6idx = add i64 %tb14, %t14_6off
  %t14_6ptr = getelementptr i16, ptr %src, i64 %t14_6idx
  %t14_6raw = load i16, ptr %t14_6ptr, align 1
  %t14_6wide = zext i16 %t14_6raw to i32
  %t14_6shift = lshr i32 %t14_6wide, 2
  %t14_6 = and i32 %t14_6shift, 255
  %t14_7row = mul i64 %srcW, 2
  %t14_7off = add i64 %t14_7row, 1
  %t14_7idx = add i64 %tb14, %t14_7off
  %t14_7ptr = getelementptr i16, ptr %src, i64 %t14_7idx
  %t14_7raw = load i16, ptr %t14_7ptr, align 1
  %t14_7wide = zext i16 %t14_7raw to i32
  %t14_7shift = lshr i32 %t14_7wide, 2
  %t14_7 = and i32 %t14_7shift, 255
  %t14_8row = mul i64 %srcW, 2
  %t14_8off = add i64 %t14_8row, 2
  %t14_8idx = add i64 %tb14, %t14_8off
  %t14_8ptr = getelementptr i16, ptr %src, i64 %t14_8idx
  %t14_8raw = load i16, ptr %t14_8ptr, align 1
  %t14_8wide = zext i16 %t14_8raw to i32
  %t14_8shift = lshr i32 %t14_8wide, 2
  %t14_8 = and i32 %t14_8shift, 255
  %ts14_1 = add i32 %t14_0, %t14_1
  %ts14_2 = add i32 %ts14_1, %t14_2
  %ts14_3 = add i32 %ts14_2, %t14_3
  %ts14_4 = add i32 %ts14_3, %t14_4
  %ts14_5 = add i32 %ts14_4, %t14_5
  %ts14_6 = add i32 %ts14_5, %t14_6
  %ts14_7 = add i32 %ts14_6, %t14_7
  %ts14_8 = add i32 %ts14_7, %t14_8
  %ta14 = add i32 %ts14_8, 4
  %tm14 = mul i32 %ta14, 7282
  %tv14 = lshr i32 %tm14, 16
  %third14 = insertelement <16 x i32> %third13, i32 %tv14, i64 14
  %tx15 = add i64 %bxi, 15
  %txs15 = mul i64 %tx15, 3
  %tb15 = add i64 %tr, %txs15
  %t15_0row = mul i64 %srcW, 0
  %t15_0off = add i64 %t15_0row, 0
  %t15_0idx = add i64 %tb15, %t15_0off
  %t15_0ptr = getelementptr i16, ptr %src, i64 %t15_0idx
  %t15_0raw = load i16, ptr %t15_0ptr, align 1
  %t15_0wide = zext i16 %t15_0raw to i32
  %t15_0shift = lshr i32 %t15_0wide, 2
  %t15_0 = and i32 %t15_0shift, 255
  %t15_1row = mul i64 %srcW, 0
  %t15_1off = add i64 %t15_1row, 1
  %t15_1idx = add i64 %tb15, %t15_1off
  %t15_1ptr = getelementptr i16, ptr %src, i64 %t15_1idx
  %t15_1raw = load i16, ptr %t15_1ptr, align 1
  %t15_1wide = zext i16 %t15_1raw to i32
  %t15_1shift = lshr i32 %t15_1wide, 2
  %t15_1 = and i32 %t15_1shift, 255
  %t15_2row = mul i64 %srcW, 0
  %t15_2off = add i64 %t15_2row, 2
  %t15_2idx = add i64 %tb15, %t15_2off
  %t15_2ptr = getelementptr i16, ptr %src, i64 %t15_2idx
  %t15_2raw = load i16, ptr %t15_2ptr, align 1
  %t15_2wide = zext i16 %t15_2raw to i32
  %t15_2shift = lshr i32 %t15_2wide, 2
  %t15_2 = and i32 %t15_2shift, 255
  %t15_3row = mul i64 %srcW, 1
  %t15_3off = add i64 %t15_3row, 0
  %t15_3idx = add i64 %tb15, %t15_3off
  %t15_3ptr = getelementptr i16, ptr %src, i64 %t15_3idx
  %t15_3raw = load i16, ptr %t15_3ptr, align 1
  %t15_3wide = zext i16 %t15_3raw to i32
  %t15_3shift = lshr i32 %t15_3wide, 2
  %t15_3 = and i32 %t15_3shift, 255
  %t15_4row = mul i64 %srcW, 1
  %t15_4off = add i64 %t15_4row, 1
  %t15_4idx = add i64 %tb15, %t15_4off
  %t15_4ptr = getelementptr i16, ptr %src, i64 %t15_4idx
  %t15_4raw = load i16, ptr %t15_4ptr, align 1
  %t15_4wide = zext i16 %t15_4raw to i32
  %t15_4shift = lshr i32 %t15_4wide, 2
  %t15_4 = and i32 %t15_4shift, 255
  %t15_5row = mul i64 %srcW, 1
  %t15_5off = add i64 %t15_5row, 2
  %t15_5idx = add i64 %tb15, %t15_5off
  %t15_5ptr = getelementptr i16, ptr %src, i64 %t15_5idx
  %t15_5raw = load i16, ptr %t15_5ptr, align 1
  %t15_5wide = zext i16 %t15_5raw to i32
  %t15_5shift = lshr i32 %t15_5wide, 2
  %t15_5 = and i32 %t15_5shift, 255
  %t15_6row = mul i64 %srcW, 2
  %t15_6off = add i64 %t15_6row, 0
  %t15_6idx = add i64 %tb15, %t15_6off
  %t15_6ptr = getelementptr i16, ptr %src, i64 %t15_6idx
  %t15_6raw = load i16, ptr %t15_6ptr, align 1
  %t15_6wide = zext i16 %t15_6raw to i32
  %t15_6shift = lshr i32 %t15_6wide, 2
  %t15_6 = and i32 %t15_6shift, 255
  %t15_7row = mul i64 %srcW, 2
  %t15_7off = add i64 %t15_7row, 1
  %t15_7idx = add i64 %tb15, %t15_7off
  %t15_7ptr = getelementptr i16, ptr %src, i64 %t15_7idx
  %t15_7raw = load i16, ptr %t15_7ptr, align 1
  %t15_7wide = zext i16 %t15_7raw to i32
  %t15_7shift = lshr i32 %t15_7wide, 2
  %t15_7 = and i32 %t15_7shift, 255
  %t15_8row = mul i64 %srcW, 2
  %t15_8off = add i64 %t15_8row, 2
  %t15_8idx = add i64 %tb15, %t15_8off
  %t15_8ptr = getelementptr i16, ptr %src, i64 %t15_8idx
  %t15_8raw = load i16, ptr %t15_8ptr, align 1
  %t15_8wide = zext i16 %t15_8raw to i32
  %t15_8shift = lshr i32 %t15_8wide, 2
  %t15_8 = and i32 %t15_8shift, 255
  %ts15_1 = add i32 %t15_0, %t15_1
  %ts15_2 = add i32 %ts15_1, %t15_2
  %ts15_3 = add i32 %ts15_2, %t15_3
  %ts15_4 = add i32 %ts15_3, %t15_4
  %ts15_5 = add i32 %ts15_4, %t15_5
  %ts15_6 = add i32 %ts15_5, %t15_6
  %ts15_7 = add i32 %ts15_6, %t15_7
  %ts15_8 = add i32 %ts15_7, %t15_8
  %ta15 = add i32 %ts15_8, 4
  %tm15 = mul i32 %ta15, 7282
  %tv15 = lshr i32 %tm15, 16
  %third15 = insertelement <16 x i32> %third14, i32 %tv15, i64 15
  br label %reduce
q8:
  %qyprod = mul i64 %dy, %srcH
  %qynum = shl i64 %qyprod, 8
  %qyq = udiv i64 %qynum, %dstH
  %qyraw0 = lshr i64 %qyq, 8
  %qylast = sub i64 %srcH, 1
  %qyin = icmp ult i64 %qyraw0, %srcH
  %qy0 = select i1 %qyin, i64 %qyraw0, i64 %qylast
  %qynext = add i64 %qy0, 1
  %qymore = icmp ult i64 %qynext, %srcH
  %qy1 = select i1 %qymore, i64 %qynext, i64 %qy0
  %qyfrac64 = and i64 %qyq, 255
  %qyf = trunc i64 %qyfrac64 to i32
  %qyinv = sub i32 256, %qyf
  %qr0 = mul i64 %qy0, %srcW
  %qr1 = mul i64 %qy1, %srcW
  %qdx0 = add i64 %bxi, 0
  %qx0prod = mul i64 %qdx0, %srcW
  %qx0num = shl i64 %qx0prod, 8
  %qx0q = udiv i64 %qx0num, %dstW
  %qx0raw0 = lshr i64 %qx0q, 8
  %qx0last = sub i64 %srcW, 1
  %qx0in = icmp ult i64 %qx0raw0, %srcW
  %qx00 = select i1 %qx0in, i64 %qx0raw0, i64 %qx0last
  %qx0next = add i64 %qx00, 1
  %qx0more = icmp ult i64 %qx0next, %srcW
  %qx01 = select i1 %qx0more, i64 %qx0next, i64 %qx00
  %qx0frac64 = and i64 %qx0q, 255
  %qx0f = trunc i64 %qx0frac64 to i32
  %qx0inv = sub i32 256, %qx0f
  %qp0_00idx = add i64 %qr0, %qx00
  %qp0_00ptr = getelementptr i16, ptr %src, i64 %qp0_00idx
  %qp0_00raw = load i16, ptr %qp0_00ptr, align 1
  %qp0_00wide = zext i16 %qp0_00raw to i32
  %qp0_00shift = lshr i32 %qp0_00wide, 2
  %qp0_00 = and i32 %qp0_00shift, 255
  %qp0_00w = mul i32 %qp0_00, %qx0inv
  %qp0_01idx = add i64 %qr0, %qx01
  %qp0_01ptr = getelementptr i16, ptr %src, i64 %qp0_01idx
  %qp0_01raw = load i16, ptr %qp0_01ptr, align 1
  %qp0_01wide = zext i16 %qp0_01raw to i32
  %qp0_01shift = lshr i32 %qp0_01wide, 2
  %qp0_01 = and i32 %qp0_01shift, 255
  %qp0_01w = mul i32 %qp0_01, %qx0f
  %qp0_10idx = add i64 %qr1, %qx00
  %qp0_10ptr = getelementptr i16, ptr %src, i64 %qp0_10idx
  %qp0_10raw = load i16, ptr %qp0_10ptr, align 1
  %qp0_10wide = zext i16 %qp0_10raw to i32
  %qp0_10shift = lshr i32 %qp0_10wide, 2
  %qp0_10 = and i32 %qp0_10shift, 255
  %qp0_10w = mul i32 %qp0_10, %qx0inv
  %qp0_11idx = add i64 %qr1, %qx01
  %qp0_11ptr = getelementptr i16, ptr %src, i64 %qp0_11idx
  %qp0_11raw = load i16, ptr %qp0_11ptr, align 1
  %qp0_11wide = zext i16 %qp0_11raw to i32
  %qp0_11shift = lshr i32 %qp0_11wide, 2
  %qp0_11 = and i32 %qp0_11shift, 255
  %qp0_11w = mul i32 %qp0_11, %qx0f
  %qt0 = add i32 %qp0_00w, %qp0_01w
  %qb0 = add i32 %qp0_10w, %qp0_11w
  %qtw0 = mul i32 %qt0, %qyinv
  %qbw0 = mul i32 %qb0, %qyf
  %qs0 = add i32 %qtw0, %qbw0
  %qa0 = add i32 %qs0, 32768
  %qv0 = lshr i32 %qa0, 16
  %q8v0 = insertelement <16 x i32> poison, i32 %qv0, i64 0
  %qdx1 = add i64 %bxi, 1
  %qx1prod = mul i64 %qdx1, %srcW
  %qx1num = shl i64 %qx1prod, 8
  %qx1q = udiv i64 %qx1num, %dstW
  %qx1raw0 = lshr i64 %qx1q, 8
  %qx1last = sub i64 %srcW, 1
  %qx1in = icmp ult i64 %qx1raw0, %srcW
  %qx10 = select i1 %qx1in, i64 %qx1raw0, i64 %qx1last
  %qx1next = add i64 %qx10, 1
  %qx1more = icmp ult i64 %qx1next, %srcW
  %qx11 = select i1 %qx1more, i64 %qx1next, i64 %qx10
  %qx1frac64 = and i64 %qx1q, 255
  %qx1f = trunc i64 %qx1frac64 to i32
  %qx1inv = sub i32 256, %qx1f
  %qp1_00idx = add i64 %qr0, %qx10
  %qp1_00ptr = getelementptr i16, ptr %src, i64 %qp1_00idx
  %qp1_00raw = load i16, ptr %qp1_00ptr, align 1
  %qp1_00wide = zext i16 %qp1_00raw to i32
  %qp1_00shift = lshr i32 %qp1_00wide, 2
  %qp1_00 = and i32 %qp1_00shift, 255
  %qp1_00w = mul i32 %qp1_00, %qx1inv
  %qp1_01idx = add i64 %qr0, %qx11
  %qp1_01ptr = getelementptr i16, ptr %src, i64 %qp1_01idx
  %qp1_01raw = load i16, ptr %qp1_01ptr, align 1
  %qp1_01wide = zext i16 %qp1_01raw to i32
  %qp1_01shift = lshr i32 %qp1_01wide, 2
  %qp1_01 = and i32 %qp1_01shift, 255
  %qp1_01w = mul i32 %qp1_01, %qx1f
  %qp1_10idx = add i64 %qr1, %qx10
  %qp1_10ptr = getelementptr i16, ptr %src, i64 %qp1_10idx
  %qp1_10raw = load i16, ptr %qp1_10ptr, align 1
  %qp1_10wide = zext i16 %qp1_10raw to i32
  %qp1_10shift = lshr i32 %qp1_10wide, 2
  %qp1_10 = and i32 %qp1_10shift, 255
  %qp1_10w = mul i32 %qp1_10, %qx1inv
  %qp1_11idx = add i64 %qr1, %qx11
  %qp1_11ptr = getelementptr i16, ptr %src, i64 %qp1_11idx
  %qp1_11raw = load i16, ptr %qp1_11ptr, align 1
  %qp1_11wide = zext i16 %qp1_11raw to i32
  %qp1_11shift = lshr i32 %qp1_11wide, 2
  %qp1_11 = and i32 %qp1_11shift, 255
  %qp1_11w = mul i32 %qp1_11, %qx1f
  %qt1 = add i32 %qp1_00w, %qp1_01w
  %qb1 = add i32 %qp1_10w, %qp1_11w
  %qtw1 = mul i32 %qt1, %qyinv
  %qbw1 = mul i32 %qb1, %qyf
  %qs1 = add i32 %qtw1, %qbw1
  %qa1 = add i32 %qs1, 32768
  %qv1 = lshr i32 %qa1, 16
  %q8v1 = insertelement <16 x i32> %q8v0, i32 %qv1, i64 1
  %qdx2 = add i64 %bxi, 2
  %qx2prod = mul i64 %qdx2, %srcW
  %qx2num = shl i64 %qx2prod, 8
  %qx2q = udiv i64 %qx2num, %dstW
  %qx2raw0 = lshr i64 %qx2q, 8
  %qx2last = sub i64 %srcW, 1
  %qx2in = icmp ult i64 %qx2raw0, %srcW
  %qx20 = select i1 %qx2in, i64 %qx2raw0, i64 %qx2last
  %qx2next = add i64 %qx20, 1
  %qx2more = icmp ult i64 %qx2next, %srcW
  %qx21 = select i1 %qx2more, i64 %qx2next, i64 %qx20
  %qx2frac64 = and i64 %qx2q, 255
  %qx2f = trunc i64 %qx2frac64 to i32
  %qx2inv = sub i32 256, %qx2f
  %qp2_00idx = add i64 %qr0, %qx20
  %qp2_00ptr = getelementptr i16, ptr %src, i64 %qp2_00idx
  %qp2_00raw = load i16, ptr %qp2_00ptr, align 1
  %qp2_00wide = zext i16 %qp2_00raw to i32
  %qp2_00shift = lshr i32 %qp2_00wide, 2
  %qp2_00 = and i32 %qp2_00shift, 255
  %qp2_00w = mul i32 %qp2_00, %qx2inv
  %qp2_01idx = add i64 %qr0, %qx21
  %qp2_01ptr = getelementptr i16, ptr %src, i64 %qp2_01idx
  %qp2_01raw = load i16, ptr %qp2_01ptr, align 1
  %qp2_01wide = zext i16 %qp2_01raw to i32
  %qp2_01shift = lshr i32 %qp2_01wide, 2
  %qp2_01 = and i32 %qp2_01shift, 255
  %qp2_01w = mul i32 %qp2_01, %qx2f
  %qp2_10idx = add i64 %qr1, %qx20
  %qp2_10ptr = getelementptr i16, ptr %src, i64 %qp2_10idx
  %qp2_10raw = load i16, ptr %qp2_10ptr, align 1
  %qp2_10wide = zext i16 %qp2_10raw to i32
  %qp2_10shift = lshr i32 %qp2_10wide, 2
  %qp2_10 = and i32 %qp2_10shift, 255
  %qp2_10w = mul i32 %qp2_10, %qx2inv
  %qp2_11idx = add i64 %qr1, %qx21
  %qp2_11ptr = getelementptr i16, ptr %src, i64 %qp2_11idx
  %qp2_11raw = load i16, ptr %qp2_11ptr, align 1
  %qp2_11wide = zext i16 %qp2_11raw to i32
  %qp2_11shift = lshr i32 %qp2_11wide, 2
  %qp2_11 = and i32 %qp2_11shift, 255
  %qp2_11w = mul i32 %qp2_11, %qx2f
  %qt2 = add i32 %qp2_00w, %qp2_01w
  %qb2 = add i32 %qp2_10w, %qp2_11w
  %qtw2 = mul i32 %qt2, %qyinv
  %qbw2 = mul i32 %qb2, %qyf
  %qs2 = add i32 %qtw2, %qbw2
  %qa2 = add i32 %qs2, 32768
  %qv2 = lshr i32 %qa2, 16
  %q8v2 = insertelement <16 x i32> %q8v1, i32 %qv2, i64 2
  %qdx3 = add i64 %bxi, 3
  %qx3prod = mul i64 %qdx3, %srcW
  %qx3num = shl i64 %qx3prod, 8
  %qx3q = udiv i64 %qx3num, %dstW
  %qx3raw0 = lshr i64 %qx3q, 8
  %qx3last = sub i64 %srcW, 1
  %qx3in = icmp ult i64 %qx3raw0, %srcW
  %qx30 = select i1 %qx3in, i64 %qx3raw0, i64 %qx3last
  %qx3next = add i64 %qx30, 1
  %qx3more = icmp ult i64 %qx3next, %srcW
  %qx31 = select i1 %qx3more, i64 %qx3next, i64 %qx30
  %qx3frac64 = and i64 %qx3q, 255
  %qx3f = trunc i64 %qx3frac64 to i32
  %qx3inv = sub i32 256, %qx3f
  %qp3_00idx = add i64 %qr0, %qx30
  %qp3_00ptr = getelementptr i16, ptr %src, i64 %qp3_00idx
  %qp3_00raw = load i16, ptr %qp3_00ptr, align 1
  %qp3_00wide = zext i16 %qp3_00raw to i32
  %qp3_00shift = lshr i32 %qp3_00wide, 2
  %qp3_00 = and i32 %qp3_00shift, 255
  %qp3_00w = mul i32 %qp3_00, %qx3inv
  %qp3_01idx = add i64 %qr0, %qx31
  %qp3_01ptr = getelementptr i16, ptr %src, i64 %qp3_01idx
  %qp3_01raw = load i16, ptr %qp3_01ptr, align 1
  %qp3_01wide = zext i16 %qp3_01raw to i32
  %qp3_01shift = lshr i32 %qp3_01wide, 2
  %qp3_01 = and i32 %qp3_01shift, 255
  %qp3_01w = mul i32 %qp3_01, %qx3f
  %qp3_10idx = add i64 %qr1, %qx30
  %qp3_10ptr = getelementptr i16, ptr %src, i64 %qp3_10idx
  %qp3_10raw = load i16, ptr %qp3_10ptr, align 1
  %qp3_10wide = zext i16 %qp3_10raw to i32
  %qp3_10shift = lshr i32 %qp3_10wide, 2
  %qp3_10 = and i32 %qp3_10shift, 255
  %qp3_10w = mul i32 %qp3_10, %qx3inv
  %qp3_11idx = add i64 %qr1, %qx31
  %qp3_11ptr = getelementptr i16, ptr %src, i64 %qp3_11idx
  %qp3_11raw = load i16, ptr %qp3_11ptr, align 1
  %qp3_11wide = zext i16 %qp3_11raw to i32
  %qp3_11shift = lshr i32 %qp3_11wide, 2
  %qp3_11 = and i32 %qp3_11shift, 255
  %qp3_11w = mul i32 %qp3_11, %qx3f
  %qt3 = add i32 %qp3_00w, %qp3_01w
  %qb3 = add i32 %qp3_10w, %qp3_11w
  %qtw3 = mul i32 %qt3, %qyinv
  %qbw3 = mul i32 %qb3, %qyf
  %qs3 = add i32 %qtw3, %qbw3
  %qa3 = add i32 %qs3, 32768
  %qv3 = lshr i32 %qa3, 16
  %q8v3 = insertelement <16 x i32> %q8v2, i32 %qv3, i64 3
  %qdx4 = add i64 %bxi, 4
  %qx4prod = mul i64 %qdx4, %srcW
  %qx4num = shl i64 %qx4prod, 8
  %qx4q = udiv i64 %qx4num, %dstW
  %qx4raw0 = lshr i64 %qx4q, 8
  %qx4last = sub i64 %srcW, 1
  %qx4in = icmp ult i64 %qx4raw0, %srcW
  %qx40 = select i1 %qx4in, i64 %qx4raw0, i64 %qx4last
  %qx4next = add i64 %qx40, 1
  %qx4more = icmp ult i64 %qx4next, %srcW
  %qx41 = select i1 %qx4more, i64 %qx4next, i64 %qx40
  %qx4frac64 = and i64 %qx4q, 255
  %qx4f = trunc i64 %qx4frac64 to i32
  %qx4inv = sub i32 256, %qx4f
  %qp4_00idx = add i64 %qr0, %qx40
  %qp4_00ptr = getelementptr i16, ptr %src, i64 %qp4_00idx
  %qp4_00raw = load i16, ptr %qp4_00ptr, align 1
  %qp4_00wide = zext i16 %qp4_00raw to i32
  %qp4_00shift = lshr i32 %qp4_00wide, 2
  %qp4_00 = and i32 %qp4_00shift, 255
  %qp4_00w = mul i32 %qp4_00, %qx4inv
  %qp4_01idx = add i64 %qr0, %qx41
  %qp4_01ptr = getelementptr i16, ptr %src, i64 %qp4_01idx
  %qp4_01raw = load i16, ptr %qp4_01ptr, align 1
  %qp4_01wide = zext i16 %qp4_01raw to i32
  %qp4_01shift = lshr i32 %qp4_01wide, 2
  %qp4_01 = and i32 %qp4_01shift, 255
  %qp4_01w = mul i32 %qp4_01, %qx4f
  %qp4_10idx = add i64 %qr1, %qx40
  %qp4_10ptr = getelementptr i16, ptr %src, i64 %qp4_10idx
  %qp4_10raw = load i16, ptr %qp4_10ptr, align 1
  %qp4_10wide = zext i16 %qp4_10raw to i32
  %qp4_10shift = lshr i32 %qp4_10wide, 2
  %qp4_10 = and i32 %qp4_10shift, 255
  %qp4_10w = mul i32 %qp4_10, %qx4inv
  %qp4_11idx = add i64 %qr1, %qx41
  %qp4_11ptr = getelementptr i16, ptr %src, i64 %qp4_11idx
  %qp4_11raw = load i16, ptr %qp4_11ptr, align 1
  %qp4_11wide = zext i16 %qp4_11raw to i32
  %qp4_11shift = lshr i32 %qp4_11wide, 2
  %qp4_11 = and i32 %qp4_11shift, 255
  %qp4_11w = mul i32 %qp4_11, %qx4f
  %qt4 = add i32 %qp4_00w, %qp4_01w
  %qb4 = add i32 %qp4_10w, %qp4_11w
  %qtw4 = mul i32 %qt4, %qyinv
  %qbw4 = mul i32 %qb4, %qyf
  %qs4 = add i32 %qtw4, %qbw4
  %qa4 = add i32 %qs4, 32768
  %qv4 = lshr i32 %qa4, 16
  %q8v4 = insertelement <16 x i32> %q8v3, i32 %qv4, i64 4
  %qdx5 = add i64 %bxi, 5
  %qx5prod = mul i64 %qdx5, %srcW
  %qx5num = shl i64 %qx5prod, 8
  %qx5q = udiv i64 %qx5num, %dstW
  %qx5raw0 = lshr i64 %qx5q, 8
  %qx5last = sub i64 %srcW, 1
  %qx5in = icmp ult i64 %qx5raw0, %srcW
  %qx50 = select i1 %qx5in, i64 %qx5raw0, i64 %qx5last
  %qx5next = add i64 %qx50, 1
  %qx5more = icmp ult i64 %qx5next, %srcW
  %qx51 = select i1 %qx5more, i64 %qx5next, i64 %qx50
  %qx5frac64 = and i64 %qx5q, 255
  %qx5f = trunc i64 %qx5frac64 to i32
  %qx5inv = sub i32 256, %qx5f
  %qp5_00idx = add i64 %qr0, %qx50
  %qp5_00ptr = getelementptr i16, ptr %src, i64 %qp5_00idx
  %qp5_00raw = load i16, ptr %qp5_00ptr, align 1
  %qp5_00wide = zext i16 %qp5_00raw to i32
  %qp5_00shift = lshr i32 %qp5_00wide, 2
  %qp5_00 = and i32 %qp5_00shift, 255
  %qp5_00w = mul i32 %qp5_00, %qx5inv
  %qp5_01idx = add i64 %qr0, %qx51
  %qp5_01ptr = getelementptr i16, ptr %src, i64 %qp5_01idx
  %qp5_01raw = load i16, ptr %qp5_01ptr, align 1
  %qp5_01wide = zext i16 %qp5_01raw to i32
  %qp5_01shift = lshr i32 %qp5_01wide, 2
  %qp5_01 = and i32 %qp5_01shift, 255
  %qp5_01w = mul i32 %qp5_01, %qx5f
  %qp5_10idx = add i64 %qr1, %qx50
  %qp5_10ptr = getelementptr i16, ptr %src, i64 %qp5_10idx
  %qp5_10raw = load i16, ptr %qp5_10ptr, align 1
  %qp5_10wide = zext i16 %qp5_10raw to i32
  %qp5_10shift = lshr i32 %qp5_10wide, 2
  %qp5_10 = and i32 %qp5_10shift, 255
  %qp5_10w = mul i32 %qp5_10, %qx5inv
  %qp5_11idx = add i64 %qr1, %qx51
  %qp5_11ptr = getelementptr i16, ptr %src, i64 %qp5_11idx
  %qp5_11raw = load i16, ptr %qp5_11ptr, align 1
  %qp5_11wide = zext i16 %qp5_11raw to i32
  %qp5_11shift = lshr i32 %qp5_11wide, 2
  %qp5_11 = and i32 %qp5_11shift, 255
  %qp5_11w = mul i32 %qp5_11, %qx5f
  %qt5 = add i32 %qp5_00w, %qp5_01w
  %qb5 = add i32 %qp5_10w, %qp5_11w
  %qtw5 = mul i32 %qt5, %qyinv
  %qbw5 = mul i32 %qb5, %qyf
  %qs5 = add i32 %qtw5, %qbw5
  %qa5 = add i32 %qs5, 32768
  %qv5 = lshr i32 %qa5, 16
  %q8v5 = insertelement <16 x i32> %q8v4, i32 %qv5, i64 5
  %qdx6 = add i64 %bxi, 6
  %qx6prod = mul i64 %qdx6, %srcW
  %qx6num = shl i64 %qx6prod, 8
  %qx6q = udiv i64 %qx6num, %dstW
  %qx6raw0 = lshr i64 %qx6q, 8
  %qx6last = sub i64 %srcW, 1
  %qx6in = icmp ult i64 %qx6raw0, %srcW
  %qx60 = select i1 %qx6in, i64 %qx6raw0, i64 %qx6last
  %qx6next = add i64 %qx60, 1
  %qx6more = icmp ult i64 %qx6next, %srcW
  %qx61 = select i1 %qx6more, i64 %qx6next, i64 %qx60
  %qx6frac64 = and i64 %qx6q, 255
  %qx6f = trunc i64 %qx6frac64 to i32
  %qx6inv = sub i32 256, %qx6f
  %qp6_00idx = add i64 %qr0, %qx60
  %qp6_00ptr = getelementptr i16, ptr %src, i64 %qp6_00idx
  %qp6_00raw = load i16, ptr %qp6_00ptr, align 1
  %qp6_00wide = zext i16 %qp6_00raw to i32
  %qp6_00shift = lshr i32 %qp6_00wide, 2
  %qp6_00 = and i32 %qp6_00shift, 255
  %qp6_00w = mul i32 %qp6_00, %qx6inv
  %qp6_01idx = add i64 %qr0, %qx61
  %qp6_01ptr = getelementptr i16, ptr %src, i64 %qp6_01idx
  %qp6_01raw = load i16, ptr %qp6_01ptr, align 1
  %qp6_01wide = zext i16 %qp6_01raw to i32
  %qp6_01shift = lshr i32 %qp6_01wide, 2
  %qp6_01 = and i32 %qp6_01shift, 255
  %qp6_01w = mul i32 %qp6_01, %qx6f
  %qp6_10idx = add i64 %qr1, %qx60
  %qp6_10ptr = getelementptr i16, ptr %src, i64 %qp6_10idx
  %qp6_10raw = load i16, ptr %qp6_10ptr, align 1
  %qp6_10wide = zext i16 %qp6_10raw to i32
  %qp6_10shift = lshr i32 %qp6_10wide, 2
  %qp6_10 = and i32 %qp6_10shift, 255
  %qp6_10w = mul i32 %qp6_10, %qx6inv
  %qp6_11idx = add i64 %qr1, %qx61
  %qp6_11ptr = getelementptr i16, ptr %src, i64 %qp6_11idx
  %qp6_11raw = load i16, ptr %qp6_11ptr, align 1
  %qp6_11wide = zext i16 %qp6_11raw to i32
  %qp6_11shift = lshr i32 %qp6_11wide, 2
  %qp6_11 = and i32 %qp6_11shift, 255
  %qp6_11w = mul i32 %qp6_11, %qx6f
  %qt6 = add i32 %qp6_00w, %qp6_01w
  %qb6 = add i32 %qp6_10w, %qp6_11w
  %qtw6 = mul i32 %qt6, %qyinv
  %qbw6 = mul i32 %qb6, %qyf
  %qs6 = add i32 %qtw6, %qbw6
  %qa6 = add i32 %qs6, 32768
  %qv6 = lshr i32 %qa6, 16
  %q8v6 = insertelement <16 x i32> %q8v5, i32 %qv6, i64 6
  %qdx7 = add i64 %bxi, 7
  %qx7prod = mul i64 %qdx7, %srcW
  %qx7num = shl i64 %qx7prod, 8
  %qx7q = udiv i64 %qx7num, %dstW
  %qx7raw0 = lshr i64 %qx7q, 8
  %qx7last = sub i64 %srcW, 1
  %qx7in = icmp ult i64 %qx7raw0, %srcW
  %qx70 = select i1 %qx7in, i64 %qx7raw0, i64 %qx7last
  %qx7next = add i64 %qx70, 1
  %qx7more = icmp ult i64 %qx7next, %srcW
  %qx71 = select i1 %qx7more, i64 %qx7next, i64 %qx70
  %qx7frac64 = and i64 %qx7q, 255
  %qx7f = trunc i64 %qx7frac64 to i32
  %qx7inv = sub i32 256, %qx7f
  %qp7_00idx = add i64 %qr0, %qx70
  %qp7_00ptr = getelementptr i16, ptr %src, i64 %qp7_00idx
  %qp7_00raw = load i16, ptr %qp7_00ptr, align 1
  %qp7_00wide = zext i16 %qp7_00raw to i32
  %qp7_00shift = lshr i32 %qp7_00wide, 2
  %qp7_00 = and i32 %qp7_00shift, 255
  %qp7_00w = mul i32 %qp7_00, %qx7inv
  %qp7_01idx = add i64 %qr0, %qx71
  %qp7_01ptr = getelementptr i16, ptr %src, i64 %qp7_01idx
  %qp7_01raw = load i16, ptr %qp7_01ptr, align 1
  %qp7_01wide = zext i16 %qp7_01raw to i32
  %qp7_01shift = lshr i32 %qp7_01wide, 2
  %qp7_01 = and i32 %qp7_01shift, 255
  %qp7_01w = mul i32 %qp7_01, %qx7f
  %qp7_10idx = add i64 %qr1, %qx70
  %qp7_10ptr = getelementptr i16, ptr %src, i64 %qp7_10idx
  %qp7_10raw = load i16, ptr %qp7_10ptr, align 1
  %qp7_10wide = zext i16 %qp7_10raw to i32
  %qp7_10shift = lshr i32 %qp7_10wide, 2
  %qp7_10 = and i32 %qp7_10shift, 255
  %qp7_10w = mul i32 %qp7_10, %qx7inv
  %qp7_11idx = add i64 %qr1, %qx71
  %qp7_11ptr = getelementptr i16, ptr %src, i64 %qp7_11idx
  %qp7_11raw = load i16, ptr %qp7_11ptr, align 1
  %qp7_11wide = zext i16 %qp7_11raw to i32
  %qp7_11shift = lshr i32 %qp7_11wide, 2
  %qp7_11 = and i32 %qp7_11shift, 255
  %qp7_11w = mul i32 %qp7_11, %qx7f
  %qt7 = add i32 %qp7_00w, %qp7_01w
  %qb7 = add i32 %qp7_10w, %qp7_11w
  %qtw7 = mul i32 %qt7, %qyinv
  %qbw7 = mul i32 %qb7, %qyf
  %qs7 = add i32 %qtw7, %qbw7
  %qa7 = add i32 %qs7, 32768
  %qv7 = lshr i32 %qa7, 16
  %q8v7 = insertelement <16 x i32> %q8v6, i32 %qv7, i64 7
  %qdx8 = add i64 %bxi, 8
  %qx8prod = mul i64 %qdx8, %srcW
  %qx8num = shl i64 %qx8prod, 8
  %qx8q = udiv i64 %qx8num, %dstW
  %qx8raw0 = lshr i64 %qx8q, 8
  %qx8last = sub i64 %srcW, 1
  %qx8in = icmp ult i64 %qx8raw0, %srcW
  %qx80 = select i1 %qx8in, i64 %qx8raw0, i64 %qx8last
  %qx8next = add i64 %qx80, 1
  %qx8more = icmp ult i64 %qx8next, %srcW
  %qx81 = select i1 %qx8more, i64 %qx8next, i64 %qx80
  %qx8frac64 = and i64 %qx8q, 255
  %qx8f = trunc i64 %qx8frac64 to i32
  %qx8inv = sub i32 256, %qx8f
  %qp8_00idx = add i64 %qr0, %qx80
  %qp8_00ptr = getelementptr i16, ptr %src, i64 %qp8_00idx
  %qp8_00raw = load i16, ptr %qp8_00ptr, align 1
  %qp8_00wide = zext i16 %qp8_00raw to i32
  %qp8_00shift = lshr i32 %qp8_00wide, 2
  %qp8_00 = and i32 %qp8_00shift, 255
  %qp8_00w = mul i32 %qp8_00, %qx8inv
  %qp8_01idx = add i64 %qr0, %qx81
  %qp8_01ptr = getelementptr i16, ptr %src, i64 %qp8_01idx
  %qp8_01raw = load i16, ptr %qp8_01ptr, align 1
  %qp8_01wide = zext i16 %qp8_01raw to i32
  %qp8_01shift = lshr i32 %qp8_01wide, 2
  %qp8_01 = and i32 %qp8_01shift, 255
  %qp8_01w = mul i32 %qp8_01, %qx8f
  %qp8_10idx = add i64 %qr1, %qx80
  %qp8_10ptr = getelementptr i16, ptr %src, i64 %qp8_10idx
  %qp8_10raw = load i16, ptr %qp8_10ptr, align 1
  %qp8_10wide = zext i16 %qp8_10raw to i32
  %qp8_10shift = lshr i32 %qp8_10wide, 2
  %qp8_10 = and i32 %qp8_10shift, 255
  %qp8_10w = mul i32 %qp8_10, %qx8inv
  %qp8_11idx = add i64 %qr1, %qx81
  %qp8_11ptr = getelementptr i16, ptr %src, i64 %qp8_11idx
  %qp8_11raw = load i16, ptr %qp8_11ptr, align 1
  %qp8_11wide = zext i16 %qp8_11raw to i32
  %qp8_11shift = lshr i32 %qp8_11wide, 2
  %qp8_11 = and i32 %qp8_11shift, 255
  %qp8_11w = mul i32 %qp8_11, %qx8f
  %qt8 = add i32 %qp8_00w, %qp8_01w
  %qb8 = add i32 %qp8_10w, %qp8_11w
  %qtw8 = mul i32 %qt8, %qyinv
  %qbw8 = mul i32 %qb8, %qyf
  %qs8 = add i32 %qtw8, %qbw8
  %qa8 = add i32 %qs8, 32768
  %qv8 = lshr i32 %qa8, 16
  %q8v8 = insertelement <16 x i32> %q8v7, i32 %qv8, i64 8
  %qdx9 = add i64 %bxi, 9
  %qx9prod = mul i64 %qdx9, %srcW
  %qx9num = shl i64 %qx9prod, 8
  %qx9q = udiv i64 %qx9num, %dstW
  %qx9raw0 = lshr i64 %qx9q, 8
  %qx9last = sub i64 %srcW, 1
  %qx9in = icmp ult i64 %qx9raw0, %srcW
  %qx90 = select i1 %qx9in, i64 %qx9raw0, i64 %qx9last
  %qx9next = add i64 %qx90, 1
  %qx9more = icmp ult i64 %qx9next, %srcW
  %qx91 = select i1 %qx9more, i64 %qx9next, i64 %qx90
  %qx9frac64 = and i64 %qx9q, 255
  %qx9f = trunc i64 %qx9frac64 to i32
  %qx9inv = sub i32 256, %qx9f
  %qp9_00idx = add i64 %qr0, %qx90
  %qp9_00ptr = getelementptr i16, ptr %src, i64 %qp9_00idx
  %qp9_00raw = load i16, ptr %qp9_00ptr, align 1
  %qp9_00wide = zext i16 %qp9_00raw to i32
  %qp9_00shift = lshr i32 %qp9_00wide, 2
  %qp9_00 = and i32 %qp9_00shift, 255
  %qp9_00w = mul i32 %qp9_00, %qx9inv
  %qp9_01idx = add i64 %qr0, %qx91
  %qp9_01ptr = getelementptr i16, ptr %src, i64 %qp9_01idx
  %qp9_01raw = load i16, ptr %qp9_01ptr, align 1
  %qp9_01wide = zext i16 %qp9_01raw to i32
  %qp9_01shift = lshr i32 %qp9_01wide, 2
  %qp9_01 = and i32 %qp9_01shift, 255
  %qp9_01w = mul i32 %qp9_01, %qx9f
  %qp9_10idx = add i64 %qr1, %qx90
  %qp9_10ptr = getelementptr i16, ptr %src, i64 %qp9_10idx
  %qp9_10raw = load i16, ptr %qp9_10ptr, align 1
  %qp9_10wide = zext i16 %qp9_10raw to i32
  %qp9_10shift = lshr i32 %qp9_10wide, 2
  %qp9_10 = and i32 %qp9_10shift, 255
  %qp9_10w = mul i32 %qp9_10, %qx9inv
  %qp9_11idx = add i64 %qr1, %qx91
  %qp9_11ptr = getelementptr i16, ptr %src, i64 %qp9_11idx
  %qp9_11raw = load i16, ptr %qp9_11ptr, align 1
  %qp9_11wide = zext i16 %qp9_11raw to i32
  %qp9_11shift = lshr i32 %qp9_11wide, 2
  %qp9_11 = and i32 %qp9_11shift, 255
  %qp9_11w = mul i32 %qp9_11, %qx9f
  %qt9 = add i32 %qp9_00w, %qp9_01w
  %qb9 = add i32 %qp9_10w, %qp9_11w
  %qtw9 = mul i32 %qt9, %qyinv
  %qbw9 = mul i32 %qb9, %qyf
  %qs9 = add i32 %qtw9, %qbw9
  %qa9 = add i32 %qs9, 32768
  %qv9 = lshr i32 %qa9, 16
  %q8v9 = insertelement <16 x i32> %q8v8, i32 %qv9, i64 9
  %qdx10 = add i64 %bxi, 10
  %qx10prod = mul i64 %qdx10, %srcW
  %qx10num = shl i64 %qx10prod, 8
  %qx10q = udiv i64 %qx10num, %dstW
  %qx10raw0 = lshr i64 %qx10q, 8
  %qx10last = sub i64 %srcW, 1
  %qx10in = icmp ult i64 %qx10raw0, %srcW
  %qx100 = select i1 %qx10in, i64 %qx10raw0, i64 %qx10last
  %qx10next = add i64 %qx100, 1
  %qx10more = icmp ult i64 %qx10next, %srcW
  %qx101 = select i1 %qx10more, i64 %qx10next, i64 %qx100
  %qx10frac64 = and i64 %qx10q, 255
  %qx10f = trunc i64 %qx10frac64 to i32
  %qx10inv = sub i32 256, %qx10f
  %qp10_00idx = add i64 %qr0, %qx100
  %qp10_00ptr = getelementptr i16, ptr %src, i64 %qp10_00idx
  %qp10_00raw = load i16, ptr %qp10_00ptr, align 1
  %qp10_00wide = zext i16 %qp10_00raw to i32
  %qp10_00shift = lshr i32 %qp10_00wide, 2
  %qp10_00 = and i32 %qp10_00shift, 255
  %qp10_00w = mul i32 %qp10_00, %qx10inv
  %qp10_01idx = add i64 %qr0, %qx101
  %qp10_01ptr = getelementptr i16, ptr %src, i64 %qp10_01idx
  %qp10_01raw = load i16, ptr %qp10_01ptr, align 1
  %qp10_01wide = zext i16 %qp10_01raw to i32
  %qp10_01shift = lshr i32 %qp10_01wide, 2
  %qp10_01 = and i32 %qp10_01shift, 255
  %qp10_01w = mul i32 %qp10_01, %qx10f
  %qp10_10idx = add i64 %qr1, %qx100
  %qp10_10ptr = getelementptr i16, ptr %src, i64 %qp10_10idx
  %qp10_10raw = load i16, ptr %qp10_10ptr, align 1
  %qp10_10wide = zext i16 %qp10_10raw to i32
  %qp10_10shift = lshr i32 %qp10_10wide, 2
  %qp10_10 = and i32 %qp10_10shift, 255
  %qp10_10w = mul i32 %qp10_10, %qx10inv
  %qp10_11idx = add i64 %qr1, %qx101
  %qp10_11ptr = getelementptr i16, ptr %src, i64 %qp10_11idx
  %qp10_11raw = load i16, ptr %qp10_11ptr, align 1
  %qp10_11wide = zext i16 %qp10_11raw to i32
  %qp10_11shift = lshr i32 %qp10_11wide, 2
  %qp10_11 = and i32 %qp10_11shift, 255
  %qp10_11w = mul i32 %qp10_11, %qx10f
  %qt10 = add i32 %qp10_00w, %qp10_01w
  %qb10 = add i32 %qp10_10w, %qp10_11w
  %qtw10 = mul i32 %qt10, %qyinv
  %qbw10 = mul i32 %qb10, %qyf
  %qs10 = add i32 %qtw10, %qbw10
  %qa10 = add i32 %qs10, 32768
  %qv10 = lshr i32 %qa10, 16
  %q8v10 = insertelement <16 x i32> %q8v9, i32 %qv10, i64 10
  %qdx11 = add i64 %bxi, 11
  %qx11prod = mul i64 %qdx11, %srcW
  %qx11num = shl i64 %qx11prod, 8
  %qx11q = udiv i64 %qx11num, %dstW
  %qx11raw0 = lshr i64 %qx11q, 8
  %qx11last = sub i64 %srcW, 1
  %qx11in = icmp ult i64 %qx11raw0, %srcW
  %qx110 = select i1 %qx11in, i64 %qx11raw0, i64 %qx11last
  %qx11next = add i64 %qx110, 1
  %qx11more = icmp ult i64 %qx11next, %srcW
  %qx111 = select i1 %qx11more, i64 %qx11next, i64 %qx110
  %qx11frac64 = and i64 %qx11q, 255
  %qx11f = trunc i64 %qx11frac64 to i32
  %qx11inv = sub i32 256, %qx11f
  %qp11_00idx = add i64 %qr0, %qx110
  %qp11_00ptr = getelementptr i16, ptr %src, i64 %qp11_00idx
  %qp11_00raw = load i16, ptr %qp11_00ptr, align 1
  %qp11_00wide = zext i16 %qp11_00raw to i32
  %qp11_00shift = lshr i32 %qp11_00wide, 2
  %qp11_00 = and i32 %qp11_00shift, 255
  %qp11_00w = mul i32 %qp11_00, %qx11inv
  %qp11_01idx = add i64 %qr0, %qx111
  %qp11_01ptr = getelementptr i16, ptr %src, i64 %qp11_01idx
  %qp11_01raw = load i16, ptr %qp11_01ptr, align 1
  %qp11_01wide = zext i16 %qp11_01raw to i32
  %qp11_01shift = lshr i32 %qp11_01wide, 2
  %qp11_01 = and i32 %qp11_01shift, 255
  %qp11_01w = mul i32 %qp11_01, %qx11f
  %qp11_10idx = add i64 %qr1, %qx110
  %qp11_10ptr = getelementptr i16, ptr %src, i64 %qp11_10idx
  %qp11_10raw = load i16, ptr %qp11_10ptr, align 1
  %qp11_10wide = zext i16 %qp11_10raw to i32
  %qp11_10shift = lshr i32 %qp11_10wide, 2
  %qp11_10 = and i32 %qp11_10shift, 255
  %qp11_10w = mul i32 %qp11_10, %qx11inv
  %qp11_11idx = add i64 %qr1, %qx111
  %qp11_11ptr = getelementptr i16, ptr %src, i64 %qp11_11idx
  %qp11_11raw = load i16, ptr %qp11_11ptr, align 1
  %qp11_11wide = zext i16 %qp11_11raw to i32
  %qp11_11shift = lshr i32 %qp11_11wide, 2
  %qp11_11 = and i32 %qp11_11shift, 255
  %qp11_11w = mul i32 %qp11_11, %qx11f
  %qt11 = add i32 %qp11_00w, %qp11_01w
  %qb11 = add i32 %qp11_10w, %qp11_11w
  %qtw11 = mul i32 %qt11, %qyinv
  %qbw11 = mul i32 %qb11, %qyf
  %qs11 = add i32 %qtw11, %qbw11
  %qa11 = add i32 %qs11, 32768
  %qv11 = lshr i32 %qa11, 16
  %q8v11 = insertelement <16 x i32> %q8v10, i32 %qv11, i64 11
  %qdx12 = add i64 %bxi, 12
  %qx12prod = mul i64 %qdx12, %srcW
  %qx12num = shl i64 %qx12prod, 8
  %qx12q = udiv i64 %qx12num, %dstW
  %qx12raw0 = lshr i64 %qx12q, 8
  %qx12last = sub i64 %srcW, 1
  %qx12in = icmp ult i64 %qx12raw0, %srcW
  %qx120 = select i1 %qx12in, i64 %qx12raw0, i64 %qx12last
  %qx12next = add i64 %qx120, 1
  %qx12more = icmp ult i64 %qx12next, %srcW
  %qx121 = select i1 %qx12more, i64 %qx12next, i64 %qx120
  %qx12frac64 = and i64 %qx12q, 255
  %qx12f = trunc i64 %qx12frac64 to i32
  %qx12inv = sub i32 256, %qx12f
  %qp12_00idx = add i64 %qr0, %qx120
  %qp12_00ptr = getelementptr i16, ptr %src, i64 %qp12_00idx
  %qp12_00raw = load i16, ptr %qp12_00ptr, align 1
  %qp12_00wide = zext i16 %qp12_00raw to i32
  %qp12_00shift = lshr i32 %qp12_00wide, 2
  %qp12_00 = and i32 %qp12_00shift, 255
  %qp12_00w = mul i32 %qp12_00, %qx12inv
  %qp12_01idx = add i64 %qr0, %qx121
  %qp12_01ptr = getelementptr i16, ptr %src, i64 %qp12_01idx
  %qp12_01raw = load i16, ptr %qp12_01ptr, align 1
  %qp12_01wide = zext i16 %qp12_01raw to i32
  %qp12_01shift = lshr i32 %qp12_01wide, 2
  %qp12_01 = and i32 %qp12_01shift, 255
  %qp12_01w = mul i32 %qp12_01, %qx12f
  %qp12_10idx = add i64 %qr1, %qx120
  %qp12_10ptr = getelementptr i16, ptr %src, i64 %qp12_10idx
  %qp12_10raw = load i16, ptr %qp12_10ptr, align 1
  %qp12_10wide = zext i16 %qp12_10raw to i32
  %qp12_10shift = lshr i32 %qp12_10wide, 2
  %qp12_10 = and i32 %qp12_10shift, 255
  %qp12_10w = mul i32 %qp12_10, %qx12inv
  %qp12_11idx = add i64 %qr1, %qx121
  %qp12_11ptr = getelementptr i16, ptr %src, i64 %qp12_11idx
  %qp12_11raw = load i16, ptr %qp12_11ptr, align 1
  %qp12_11wide = zext i16 %qp12_11raw to i32
  %qp12_11shift = lshr i32 %qp12_11wide, 2
  %qp12_11 = and i32 %qp12_11shift, 255
  %qp12_11w = mul i32 %qp12_11, %qx12f
  %qt12 = add i32 %qp12_00w, %qp12_01w
  %qb12 = add i32 %qp12_10w, %qp12_11w
  %qtw12 = mul i32 %qt12, %qyinv
  %qbw12 = mul i32 %qb12, %qyf
  %qs12 = add i32 %qtw12, %qbw12
  %qa12 = add i32 %qs12, 32768
  %qv12 = lshr i32 %qa12, 16
  %q8v12 = insertelement <16 x i32> %q8v11, i32 %qv12, i64 12
  %qdx13 = add i64 %bxi, 13
  %qx13prod = mul i64 %qdx13, %srcW
  %qx13num = shl i64 %qx13prod, 8
  %qx13q = udiv i64 %qx13num, %dstW
  %qx13raw0 = lshr i64 %qx13q, 8
  %qx13last = sub i64 %srcW, 1
  %qx13in = icmp ult i64 %qx13raw0, %srcW
  %qx130 = select i1 %qx13in, i64 %qx13raw0, i64 %qx13last
  %qx13next = add i64 %qx130, 1
  %qx13more = icmp ult i64 %qx13next, %srcW
  %qx131 = select i1 %qx13more, i64 %qx13next, i64 %qx130
  %qx13frac64 = and i64 %qx13q, 255
  %qx13f = trunc i64 %qx13frac64 to i32
  %qx13inv = sub i32 256, %qx13f
  %qp13_00idx = add i64 %qr0, %qx130
  %qp13_00ptr = getelementptr i16, ptr %src, i64 %qp13_00idx
  %qp13_00raw = load i16, ptr %qp13_00ptr, align 1
  %qp13_00wide = zext i16 %qp13_00raw to i32
  %qp13_00shift = lshr i32 %qp13_00wide, 2
  %qp13_00 = and i32 %qp13_00shift, 255
  %qp13_00w = mul i32 %qp13_00, %qx13inv
  %qp13_01idx = add i64 %qr0, %qx131
  %qp13_01ptr = getelementptr i16, ptr %src, i64 %qp13_01idx
  %qp13_01raw = load i16, ptr %qp13_01ptr, align 1
  %qp13_01wide = zext i16 %qp13_01raw to i32
  %qp13_01shift = lshr i32 %qp13_01wide, 2
  %qp13_01 = and i32 %qp13_01shift, 255
  %qp13_01w = mul i32 %qp13_01, %qx13f
  %qp13_10idx = add i64 %qr1, %qx130
  %qp13_10ptr = getelementptr i16, ptr %src, i64 %qp13_10idx
  %qp13_10raw = load i16, ptr %qp13_10ptr, align 1
  %qp13_10wide = zext i16 %qp13_10raw to i32
  %qp13_10shift = lshr i32 %qp13_10wide, 2
  %qp13_10 = and i32 %qp13_10shift, 255
  %qp13_10w = mul i32 %qp13_10, %qx13inv
  %qp13_11idx = add i64 %qr1, %qx131
  %qp13_11ptr = getelementptr i16, ptr %src, i64 %qp13_11idx
  %qp13_11raw = load i16, ptr %qp13_11ptr, align 1
  %qp13_11wide = zext i16 %qp13_11raw to i32
  %qp13_11shift = lshr i32 %qp13_11wide, 2
  %qp13_11 = and i32 %qp13_11shift, 255
  %qp13_11w = mul i32 %qp13_11, %qx13f
  %qt13 = add i32 %qp13_00w, %qp13_01w
  %qb13 = add i32 %qp13_10w, %qp13_11w
  %qtw13 = mul i32 %qt13, %qyinv
  %qbw13 = mul i32 %qb13, %qyf
  %qs13 = add i32 %qtw13, %qbw13
  %qa13 = add i32 %qs13, 32768
  %qv13 = lshr i32 %qa13, 16
  %q8v13 = insertelement <16 x i32> %q8v12, i32 %qv13, i64 13
  %qdx14 = add i64 %bxi, 14
  %qx14prod = mul i64 %qdx14, %srcW
  %qx14num = shl i64 %qx14prod, 8
  %qx14q = udiv i64 %qx14num, %dstW
  %qx14raw0 = lshr i64 %qx14q, 8
  %qx14last = sub i64 %srcW, 1
  %qx14in = icmp ult i64 %qx14raw0, %srcW
  %qx140 = select i1 %qx14in, i64 %qx14raw0, i64 %qx14last
  %qx14next = add i64 %qx140, 1
  %qx14more = icmp ult i64 %qx14next, %srcW
  %qx141 = select i1 %qx14more, i64 %qx14next, i64 %qx140
  %qx14frac64 = and i64 %qx14q, 255
  %qx14f = trunc i64 %qx14frac64 to i32
  %qx14inv = sub i32 256, %qx14f
  %qp14_00idx = add i64 %qr0, %qx140
  %qp14_00ptr = getelementptr i16, ptr %src, i64 %qp14_00idx
  %qp14_00raw = load i16, ptr %qp14_00ptr, align 1
  %qp14_00wide = zext i16 %qp14_00raw to i32
  %qp14_00shift = lshr i32 %qp14_00wide, 2
  %qp14_00 = and i32 %qp14_00shift, 255
  %qp14_00w = mul i32 %qp14_00, %qx14inv
  %qp14_01idx = add i64 %qr0, %qx141
  %qp14_01ptr = getelementptr i16, ptr %src, i64 %qp14_01idx
  %qp14_01raw = load i16, ptr %qp14_01ptr, align 1
  %qp14_01wide = zext i16 %qp14_01raw to i32
  %qp14_01shift = lshr i32 %qp14_01wide, 2
  %qp14_01 = and i32 %qp14_01shift, 255
  %qp14_01w = mul i32 %qp14_01, %qx14f
  %qp14_10idx = add i64 %qr1, %qx140
  %qp14_10ptr = getelementptr i16, ptr %src, i64 %qp14_10idx
  %qp14_10raw = load i16, ptr %qp14_10ptr, align 1
  %qp14_10wide = zext i16 %qp14_10raw to i32
  %qp14_10shift = lshr i32 %qp14_10wide, 2
  %qp14_10 = and i32 %qp14_10shift, 255
  %qp14_10w = mul i32 %qp14_10, %qx14inv
  %qp14_11idx = add i64 %qr1, %qx141
  %qp14_11ptr = getelementptr i16, ptr %src, i64 %qp14_11idx
  %qp14_11raw = load i16, ptr %qp14_11ptr, align 1
  %qp14_11wide = zext i16 %qp14_11raw to i32
  %qp14_11shift = lshr i32 %qp14_11wide, 2
  %qp14_11 = and i32 %qp14_11shift, 255
  %qp14_11w = mul i32 %qp14_11, %qx14f
  %qt14 = add i32 %qp14_00w, %qp14_01w
  %qb14 = add i32 %qp14_10w, %qp14_11w
  %qtw14 = mul i32 %qt14, %qyinv
  %qbw14 = mul i32 %qb14, %qyf
  %qs14 = add i32 %qtw14, %qbw14
  %qa14 = add i32 %qs14, 32768
  %qv14 = lshr i32 %qa14, 16
  %q8v14 = insertelement <16 x i32> %q8v13, i32 %qv14, i64 14
  %qdx15 = add i64 %bxi, 15
  %qx15prod = mul i64 %qdx15, %srcW
  %qx15num = shl i64 %qx15prod, 8
  %qx15q = udiv i64 %qx15num, %dstW
  %qx15raw0 = lshr i64 %qx15q, 8
  %qx15last = sub i64 %srcW, 1
  %qx15in = icmp ult i64 %qx15raw0, %srcW
  %qx150 = select i1 %qx15in, i64 %qx15raw0, i64 %qx15last
  %qx15next = add i64 %qx150, 1
  %qx15more = icmp ult i64 %qx15next, %srcW
  %qx151 = select i1 %qx15more, i64 %qx15next, i64 %qx150
  %qx15frac64 = and i64 %qx15q, 255
  %qx15f = trunc i64 %qx15frac64 to i32
  %qx15inv = sub i32 256, %qx15f
  %qp15_00idx = add i64 %qr0, %qx150
  %qp15_00ptr = getelementptr i16, ptr %src, i64 %qp15_00idx
  %qp15_00raw = load i16, ptr %qp15_00ptr, align 1
  %qp15_00wide = zext i16 %qp15_00raw to i32
  %qp15_00shift = lshr i32 %qp15_00wide, 2
  %qp15_00 = and i32 %qp15_00shift, 255
  %qp15_00w = mul i32 %qp15_00, %qx15inv
  %qp15_01idx = add i64 %qr0, %qx151
  %qp15_01ptr = getelementptr i16, ptr %src, i64 %qp15_01idx
  %qp15_01raw = load i16, ptr %qp15_01ptr, align 1
  %qp15_01wide = zext i16 %qp15_01raw to i32
  %qp15_01shift = lshr i32 %qp15_01wide, 2
  %qp15_01 = and i32 %qp15_01shift, 255
  %qp15_01w = mul i32 %qp15_01, %qx15f
  %qp15_10idx = add i64 %qr1, %qx150
  %qp15_10ptr = getelementptr i16, ptr %src, i64 %qp15_10idx
  %qp15_10raw = load i16, ptr %qp15_10ptr, align 1
  %qp15_10wide = zext i16 %qp15_10raw to i32
  %qp15_10shift = lshr i32 %qp15_10wide, 2
  %qp15_10 = and i32 %qp15_10shift, 255
  %qp15_10w = mul i32 %qp15_10, %qx15inv
  %qp15_11idx = add i64 %qr1, %qx151
  %qp15_11ptr = getelementptr i16, ptr %src, i64 %qp15_11idx
  %qp15_11raw = load i16, ptr %qp15_11ptr, align 1
  %qp15_11wide = zext i16 %qp15_11raw to i32
  %qp15_11shift = lshr i32 %qp15_11wide, 2
  %qp15_11 = and i32 %qp15_11shift, 255
  %qp15_11w = mul i32 %qp15_11, %qx15f
  %qt15 = add i32 %qp15_00w, %qp15_01w
  %qb15 = add i32 %qp15_10w, %qp15_11w
  %qtw15 = mul i32 %qt15, %qyinv
  %qbw15 = mul i32 %qb15, %qyf
  %qs15 = add i32 %qtw15, %qbw15
  %qa15 = add i32 %qs15, 32768
  %qv15 = lshr i32 %qa15, 16
  %q8v15 = insertelement <16 x i32> %q8v14, i32 %qv15, i64 15
  br label %reduce
reduce:
  %r = phi <16 x i32> [ %r1, %same ], [ %r2, %half ], [ %third15, %third ], [ %q8v15, %q8 ]
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

declare <4 x i32> @llvm.umin.v4i32(<4 x i32>, <4 x i32>)

define weak_odr dso_local i64 @lean_native_luma_stats_u16le(ptr noalias noundef readonly %src, i64 noundef %nPixels, i64 noundef %step) #0 {
entry:
  %has_px = icmp ugt i64 %nPixels, 0
  %step_pos = icmp ugt i64 %step, 0
  %ok = and i1 %has_px, %step_pos
  br i1 %ok, label %dispatch, label %exit.zero
dispatch:
  %contiguous = icmp eq i64 %step, 1
  br i1 %contiguous, label %vec16.check, label %stride.check
stride.check:
  %strided = icmp eq i64 %step, 16
  br i1 %strided, label %vec4.check, label %scalar.check
vec16.check:
  %vec16.idx = phi i64 [ 0, %dispatch ], [ %vec16.idx.next, %vec16.body ]
  %vec16.sum = phi i64 [ 0, %dispatch ], [ %vec16.sum.next, %vec16.body ]
  %vec16.sumSq = phi i64 [ 0, %dispatch ], [ %vec16.sumSq.next, %vec16.body ]
  %vec16.cnt = phi i64 [ 0, %dispatch ], [ %vec16.cnt.next, %vec16.body ]
  %vec16.remaining = sub i64 %nPixels, %vec16.idx
  %vec16.enough = icmp uge i64 %vec16.remaining, 16
  br i1 %vec16.enough, label %vec16.body, label %scalar.check
vec16.body:
  %vp = getelementptr i16, ptr %src, i64 %vec16.idx
  %vb = load <16 x i16>, ptr %vp, align 1
  %vraw = zext <16 x i16> %vb to <16 x i32>
  %v16 = lshr <16 x i32> %vraw, <i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2, i32 2>
  %vec16.sq = mul nuw <16 x i32> %v16, %v16
  %vec16.sum.r = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %v16)
  %vec16.sum.wide = zext i32 %vec16.sum.r to i64
  %vec16.sum.next = add i64 %vec16.sum, %vec16.sum.wide
  %vec16.sumSq.r = call i32 @llvm.vector.reduce.add.v16i32(<16 x i32> %vec16.sq)
  %vec16.sumSq.wide = zext i32 %vec16.sumSq.r to i64
  %vec16.sumSq.next = add i64 %vec16.sumSq, %vec16.sumSq.wide
  %vec16.cnt.next = add nuw i64 %vec16.cnt, 16
  %vec16.idx.next = add nuw i64 %vec16.idx, 16
  br label %vec16.check
vec4.check:
  %vec4.idx = phi i64 [ 0, %stride.check ], [ %vec4.idx.next, %vec4.body ]
  %vec4.sum = phi i64 [ 0, %stride.check ], [ %vec4.sum.next, %vec4.body ]
  %vec4.sumSq = phi i64 [ 0, %stride.check ], [ %vec4.sumSq.next, %vec4.body ]
  %vec4.cnt = phi i64 [ 0, %stride.check ], [ %vec4.cnt.next, %vec4.body ]
  %vec4.remaining = sub i64 %nPixels, %vec4.idx
  %vec4.enough = icmp uge i64 %vec4.remaining, 49
  br i1 %vec4.enough, label %vec4.body, label %scalar.check
vec4.body:
  %si0 = add i64 %vec4.idx, 0
  %sp0 = getelementptr i16, ptr %src, i64 %si0
  %sb0 = load i16, ptr %sp0, align 1
  %sr0 = zext i16 %sb0 to i32
  %sv0 = lshr i32 %sr0, 2
  %pack0 = insertelement <4 x i32> poison, i32 %sv0, i32 0
  %si1 = add i64 %vec4.idx, 16
  %sp1 = getelementptr i16, ptr %src, i64 %si1
  %sb1 = load i16, ptr %sp1, align 1
  %sr1 = zext i16 %sb1 to i32
  %sv1 = lshr i32 %sr1, 2
  %pack1 = insertelement <4 x i32> %pack0, i32 %sv1, i32 1
  %si2 = add i64 %vec4.idx, 32
  %sp2 = getelementptr i16, ptr %src, i64 %si2
  %sb2 = load i16, ptr %sp2, align 1
  %sr2 = zext i16 %sb2 to i32
  %sv2 = lshr i32 %sr2, 2
  %pack2 = insertelement <4 x i32> %pack1, i32 %sv2, i32 2
  %si3 = add i64 %vec4.idx, 48
  %sp3 = getelementptr i16, ptr %src, i64 %si3
  %sb3 = load i16, ptr %sp3, align 1
  %sr3 = zext i16 %sb3 to i32
  %sv3 = lshr i32 %sr3, 2
  %pack3 = insertelement <4 x i32> %pack2, i32 %sv3, i32 3
  %vec4.sq = mul nuw <4 x i32> %pack3, %pack3
  %vec4.sum.r = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %pack3)
  %vec4.sum.wide = zext i32 %vec4.sum.r to i64
  %vec4.sum.next = add i64 %vec4.sum, %vec4.sum.wide
  %vec4.sumSq.r = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %vec4.sq)
  %vec4.sumSq.wide = zext i32 %vec4.sumSq.r to i64
  %vec4.sumSq.next = add i64 %vec4.sumSq, %vec4.sumSq.wide
  %vec4.cnt.next = add nuw i64 %vec4.cnt, 4
  %vec4.advance = add i64 %vec4.idx, 64
  %vec4.more = icmp ugt i64 %vec4.remaining, 64
  %vec4.idx.next = select i1 %vec4.more, i64 %vec4.advance, i64 %nPixels
  br label %vec4.check
scalar.check:
  %initial.idx = phi i64 [ 0, %stride.check ], [ %vec16.idx, %vec16.check ], [ %vec4.idx, %vec4.check ]
  %initial.sum = phi i64 [ 0, %stride.check ], [ %vec16.sum, %vec16.check ], [ %vec4.sum, %vec4.check ]
  %initial.sumSq = phi i64 [ 0, %stride.check ], [ %vec16.sumSq, %vec16.check ], [ %vec4.sumSq, %vec4.check ]
  %initial.cnt = phi i64 [ 0, %stride.check ], [ %vec16.cnt, %vec16.check ], [ %vec4.cnt, %vec4.check ]
  %tail = icmp ult i64 %initial.idx, %nPixels
  br i1 %tail, label %loop.body, label %compute.out
loop.body:
  %idx = phi i64 [ %initial.idx, %scalar.check ], [ %idx_next, %loop.body ]
  %sum = phi i64 [ %initial.sum, %scalar.check ], [ %sum_next, %loop.body ]
  %sumSq = phi i64 [ %initial.sumSq, %scalar.check ], [ %sumSq_next, %loop.body ]
  %cnt = phi i64 [ %initial.cnt, %scalar.check ], [ %cnt_next, %loop.body ]
  %p = getelementptr i16, ptr %src, i64 %idx
  %b = load i16, ptr %p, align 1
  %raw = zext i16 %b to i64
  %v = lshr i64 %raw, 2
  %v2 = mul nuw i64 %v, %v
  %sum_next = add i64 %sum, %v
  %sumSq_next = add i64 %sumSq, %v2
  %cnt_next = add nuw i64 %cnt, 1
  %idx_next = add i64 %idx, %step
  %remaining = sub i64 %nPixels, %idx
  %more = icmp ult i64 %step, %remaining
  br i1 %more, label %loop.body, label %compute.out
compute.out:
  %final.sum = phi i64 [ %initial.sum, %scalar.check ], [ %sum_next, %loop.body ]
  %final.sumSq = phi i64 [ %initial.sumSq, %scalar.check ], [ %sumSq_next, %loop.body ]
  %final.cnt = phi i64 [ %initial.cnt, %scalar.check ], [ %cnt_next, %loop.body ]
  %mean = udiv i64 %final.sum, %final.cnt
  %meanSq = udiv i64 %final.sumSq, %final.cnt
  %sq = mul nuw i64 %mean, %mean
  %gt = icmp ugt i64 %meanSq, %sq
  %diff = sub i64 %meanSq, %sq
  %var = select i1 %gt, i64 %diff, i64 0
  %var_hi = shl i64 %var, 32
  %mean_lo = and i64 %mean, 4294967295
  %packed = or i64 %var_hi, %mean_lo
  ret i64 %packed
exit.zero:
  ret i64 0
}

define weak_odr dso_local void @lean_native_swscale_bilinear_q8_u16le(ptr %src, ptr %dst, i64 %sw, i64 %sh, i64 %dw, i64 %dh) #0 {
entry:
  %sw0 = icmp eq i64 %sw, 0
  %sh0 = icmp eq i64 %sh, 0
  %dw0 = icmp eq i64 %dw, 0
  %dh0 = icmp eq i64 %dh, 0
  %s0 = or i1 %sw0, %sh0
  %d0 = or i1 %dw0, %dh0
  %empty = or i1 %s0, %d0
  br i1 %empty, label %exit, label %identity
identity:
  %samew = icmp eq i64 %sw, %dw
  %sameh = icmp eq i64 %sh, %dh
  %same = and i1 %samew, %sameh
  br i1 %same, label %copy, label %dispatch
copy:
  %pixels = mul i64 %sw, %sh
  %bytes = shl i64 %pixels, 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %bytes, i1 false)
  br label %exit
dispatch:
  %w2 = mul i64 %dw, 2
  %h2 = mul i64 %dh, 2
  %w3 = mul i64 %dw, 3
  %h3 = mul i64 %dh, 3
  %eqw2 = icmp eq i64 %sw, %w2
  %eqh2 = icmp eq i64 %sh, %h2
  %eq2 = and i1 %eqw2, %eqh2
  %eqw3 = icmp eq i64 %sw, %w3
  %eqh3 = icmp eq i64 %sh, %h3
  %eq3 = and i1 %eqw3, %eqh3
  %vlim = and i64 %dw, -4
  br i1 %eq2, label %b2row, label %check3
check3:
  br i1 %eq3, label %b3row, label %check3to2
b2row:
  %y2 = phi i64 [ 0, %dispatch ], [ %yn2, %b2end ]
  %r2a = mul i64 %y2, %sw
  %r2 = shl i64 %r2a, 1
  %dr2 = mul i64 %y2, %dw
  br label %b2veccond
b2veccond:
  %x2v = phi i64 [ 0, %b2row ], [ %x2vn, %b2vec ]
  %more2v = icmp ult i64 %x2v, %vlim
  br i1 %more2v, label %b2vec, label %b2cond
b2vec:
  %sx2v = shl i64 %x2v, 1
  %i2v = add i64 %r2, %sx2v
  %j2v = add i64 %i2v, %sw
  %p2v = getelementptr i16, ptr %src, i64 %i2v
  %q2v = getelementptr i16, ptr %src, i64 %j2v
  %a2v = load <8 x i16>, ptr %p2v, align 1
  %b2v = load <8 x i16>, ptr %q2v, align 1
  %a2wide = zext <8 x i16> %a2v to <8 x i32>
  %b2wide = zext <8 x i16> %b2v to <8 x i32>
  %a0 = shufflevector <8 x i32> %a2wide, <8 x i32> poison, <4 x i32> <i32 0, i32 2, i32 4, i32 6>
  %a1 = shufflevector <8 x i32> %a2wide, <8 x i32> poison, <4 x i32> <i32 1, i32 3, i32 5, i32 7>
  %b0 = shufflevector <8 x i32> %b2wide, <8 x i32> poison, <4 x i32> <i32 0, i32 2, i32 4, i32 6>
  %b1 = shufflevector <8 x i32> %b2wide, <8 x i32> poison, <4 x i32> <i32 1, i32 3, i32 5, i32 7>
  %va = add <4 x i32> %a0, %a1
  %vb = add <4 x i32> %b0, %b1
  %vs = add <4 x i32> %va, %vb
  %vr = add <4 x i32> %vs, <i32 2, i32 2, i32 2, i32 2>
  %vo = lshr <4 x i32> %vr, <i32 2, i32 2, i32 2, i32 2>
  %vt = trunc <4 x i32> %vo to <4 x i16>
  %di2v = add i64 %dr2, %x2v
  %dp2v = getelementptr i16, ptr %dst, i64 %di2v
  store <4 x i16> %vt, ptr %dp2v, align 1
  %x2vn = add i64 %x2v, 4
  br label %b2veccond
b2cond:
  %x2 = phi i64 [ %x2v, %b2veccond ], [ %xn2, %b2body ]
  %more2 = icmp ult i64 %x2, %dw
  br i1 %more2, label %b2body, label %b2end
b2body:
  %sx2 = shl i64 %x2, 1
  %base2 = add i64 %r2, %sx2
%row2_0 = mul i64 %sw, 0
%base2_0 = add i64 %base2, %row2_0
%i2_0_0 = add i64 %base2_0, 0
  %p2_0_0 = getelementptr i16, ptr %src, i64 %i2_0_0
  %b2_0_0 = load i16, ptr %p2_0_0, align 1
  %v2_0_0 = zext i16 %b2_0_0 to i32
%i2_0_1 = add i64 %base2_0, 1
  %p2_0_1 = getelementptr i16, ptr %src, i64 %i2_0_1
  %b2_0_1 = load i16, ptr %p2_0_1, align 1
  %v2_0_1 = zext i16 %b2_0_1 to i32
%row2_1 = mul i64 %sw, 1
%base2_1 = add i64 %base2, %row2_1
%i2_1_0 = add i64 %base2_1, 0
  %p2_1_0 = getelementptr i16, ptr %src, i64 %i2_1_0
  %b2_1_0 = load i16, ptr %p2_1_0, align 1
  %v2_1_0 = zext i16 %b2_1_0 to i32
%i2_1_1 = add i64 %base2_1, 1
  %p2_1_1 = getelementptr i16, ptr %src, i64 %i2_1_1
  %b2_1_1 = load i16, ptr %p2_1_1, align 1
  %v2_1_1 = zext i16 %b2_1_1 to i32
%sum2_0 = add i32 %v2_0_0, %v2_0_1
%sum2_1 = add i32 %sum2_0, %v2_1_0
%sum2_2 = add i32 %sum2_1, %v2_1_1
%round2 = add i32 %sum2_2, 2
%out2 = lshr i32 %round2, 2
  %tr2 = trunc i32 %out2 to i16
%di2 = add i64 %dr2, %x2
  %dp2 = getelementptr i16, ptr %dst, i64 %di2
  store i16 %tr2, ptr %dp2, align 1
  %xn2 = add i64 %x2, 1
br label %b2cond
b2end:
  %yn2 = add i64 %y2, 1
  %ymore2 = icmp ult i64 %yn2, %dh
  br i1 %ymore2, label %b2row, label %exit
b3row:
  %y3 = phi i64 [ 0, %check3 ], [ %yn3, %b3end ]
  %r3a = mul i64 %y3, %sw
  %r3 = mul i64 %r3a, 3
  %dr3 = mul i64 %y3, %dw
  br label %b3veccond
b3veccond:
  %x3v = phi i64 [ 0, %b3row ], [ %x3vn, %b3vec ]
  %more3v = icmp ult i64 %x3v, %vlim
  br i1 %more3v, label %b3vec, label %b3cond
b3vec:
  %sx3v = mul i64 %x3v, 3
  %base3v = add i64 %r3, %sx3v
  %row3v0 = mul i64 %sw, 0
  %i3v0 = add i64 %base3v, %row3v0
  %p3v0 = getelementptr i16, ptr %src, i64 %i3v0
  %q3v0 = getelementptr i16, ptr %p3v0, i64 8
  %lo3v0 = load <8 x i16>, ptr %p3v0, align 1
  %hi3v0 = load <4 x i16>, ptr %q3v0, align 1
  %lw3v0 = zext <8 x i16> %lo3v0 to <8 x i32>
  %hw3v0 = zext <4 x i16> %hi3v0 to <4 x i32>
  %hp3v0 = shufflevector <4 x i32> %hw3v0, <4 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 poison, i32 poison, i32 poison, i32 poison>
  %c3v00 = shufflevector <8 x i32> %lw3v0, <8 x i32> %hp3v0, <4 x i32> <i32 0, i32 3, i32 6, i32 9>
  %c3v01 = shufflevector <8 x i32> %lw3v0, <8 x i32> %hp3v0, <4 x i32> <i32 1, i32 4, i32 7, i32 10>
  %c3v02 = shufflevector <8 x i32> %lw3v0, <8 x i32> %hp3v0, <4 x i32> <i32 2, i32 5, i32 8, i32 11>
  %row3v1 = mul i64 %sw, 1
  %i3v1 = add i64 %base3v, %row3v1
  %p3v1 = getelementptr i16, ptr %src, i64 %i3v1
  %q3v1 = getelementptr i16, ptr %p3v1, i64 8
  %lo3v1 = load <8 x i16>, ptr %p3v1, align 1
  %hi3v1 = load <4 x i16>, ptr %q3v1, align 1
  %lw3v1 = zext <8 x i16> %lo3v1 to <8 x i32>
  %hw3v1 = zext <4 x i16> %hi3v1 to <4 x i32>
  %hp3v1 = shufflevector <4 x i32> %hw3v1, <4 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 poison, i32 poison, i32 poison, i32 poison>
  %c3v10 = shufflevector <8 x i32> %lw3v1, <8 x i32> %hp3v1, <4 x i32> <i32 0, i32 3, i32 6, i32 9>
  %c3v11 = shufflevector <8 x i32> %lw3v1, <8 x i32> %hp3v1, <4 x i32> <i32 1, i32 4, i32 7, i32 10>
  %c3v12 = shufflevector <8 x i32> %lw3v1, <8 x i32> %hp3v1, <4 x i32> <i32 2, i32 5, i32 8, i32 11>
  %row3v2 = mul i64 %sw, 2
  %i3v2 = add i64 %base3v, %row3v2
  %p3v2 = getelementptr i16, ptr %src, i64 %i3v2
  %q3v2 = getelementptr i16, ptr %p3v2, i64 8
  %lo3v2 = load <8 x i16>, ptr %p3v2, align 1
  %hi3v2 = load <4 x i16>, ptr %q3v2, align 1
  %lw3v2 = zext <8 x i16> %lo3v2 to <8 x i32>
  %hw3v2 = zext <4 x i16> %hi3v2 to <4 x i32>
  %hp3v2 = shufflevector <4 x i32> %hw3v2, <4 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 poison, i32 poison, i32 poison, i32 poison>
  %c3v20 = shufflevector <8 x i32> %lw3v2, <8 x i32> %hp3v2, <4 x i32> <i32 0, i32 3, i32 6, i32 9>
  %c3v21 = shufflevector <8 x i32> %lw3v2, <8 x i32> %hp3v2, <4 x i32> <i32 1, i32 4, i32 7, i32 10>
  %c3v22 = shufflevector <8 x i32> %lw3v2, <8 x i32> %hp3v2, <4 x i32> <i32 2, i32 5, i32 8, i32 11>
  %s3v1 = add <4 x i32> %c3v00, %c3v01
  %s3v2 = add <4 x i32> %s3v1, %c3v02
  %s3v3 = add <4 x i32> %s3v2, %c3v10
  %s3v4 = add <4 x i32> %s3v3, %c3v11
  %s3v5 = add <4 x i32> %s3v4, %c3v12
  %s3v6 = add <4 x i32> %s3v5, %c3v20
  %s3v7 = add <4 x i32> %s3v6, %c3v21
  %s3v8 = add <4 x i32> %s3v7, %c3v22
  %vr3 = add <4 x i32> %s3v8, <i32 4, i32 4, i32 4, i32 4>
  %vo3 = udiv <4 x i32> %vr3, <i32 9, i32 9, i32 9, i32 9>
  %vt3 = trunc <4 x i32> %vo3 to <4 x i16>
  %di3v = add i64 %dr3, %x3v
  %dp3v = getelementptr i16, ptr %dst, i64 %di3v
  store <4 x i16> %vt3, ptr %dp3v, align 1
  %x3vn = add i64 %x3v, 4
  br label %b3veccond
b3cond:
  %x3 = phi i64 [ %x3v, %b3veccond ], [ %xn3, %b3body ]
  %more3 = icmp ult i64 %x3, %dw
  br i1 %more3, label %b3body, label %b3end
b3body:
  %sx3 = mul i64 %x3, 3
  %base3 = add i64 %r3, %sx3
%row3_0 = mul i64 %sw, 0
%base3_0 = add i64 %base3, %row3_0
%i3_0_0 = add i64 %base3_0, 0
  %p3_0_0 = getelementptr i16, ptr %src, i64 %i3_0_0
  %b3_0_0 = load i16, ptr %p3_0_0, align 1
  %v3_0_0 = zext i16 %b3_0_0 to i32
%i3_0_1 = add i64 %base3_0, 1
  %p3_0_1 = getelementptr i16, ptr %src, i64 %i3_0_1
  %b3_0_1 = load i16, ptr %p3_0_1, align 1
  %v3_0_1 = zext i16 %b3_0_1 to i32
%i3_0_2 = add i64 %base3_0, 2
  %p3_0_2 = getelementptr i16, ptr %src, i64 %i3_0_2
  %b3_0_2 = load i16, ptr %p3_0_2, align 1
  %v3_0_2 = zext i16 %b3_0_2 to i32
%row3_1 = mul i64 %sw, 1
%base3_1 = add i64 %base3, %row3_1
%i3_1_0 = add i64 %base3_1, 0
  %p3_1_0 = getelementptr i16, ptr %src, i64 %i3_1_0
  %b3_1_0 = load i16, ptr %p3_1_0, align 1
  %v3_1_0 = zext i16 %b3_1_0 to i32
%i3_1_1 = add i64 %base3_1, 1
  %p3_1_1 = getelementptr i16, ptr %src, i64 %i3_1_1
  %b3_1_1 = load i16, ptr %p3_1_1, align 1
  %v3_1_1 = zext i16 %b3_1_1 to i32
%i3_1_2 = add i64 %base3_1, 2
  %p3_1_2 = getelementptr i16, ptr %src, i64 %i3_1_2
  %b3_1_2 = load i16, ptr %p3_1_2, align 1
  %v3_1_2 = zext i16 %b3_1_2 to i32
%row3_2 = mul i64 %sw, 2
%base3_2 = add i64 %base3, %row3_2
%i3_2_0 = add i64 %base3_2, 0
  %p3_2_0 = getelementptr i16, ptr %src, i64 %i3_2_0
  %b3_2_0 = load i16, ptr %p3_2_0, align 1
  %v3_2_0 = zext i16 %b3_2_0 to i32
%i3_2_1 = add i64 %base3_2, 1
  %p3_2_1 = getelementptr i16, ptr %src, i64 %i3_2_1
  %b3_2_1 = load i16, ptr %p3_2_1, align 1
  %v3_2_1 = zext i16 %b3_2_1 to i32
%i3_2_2 = add i64 %base3_2, 2
  %p3_2_2 = getelementptr i16, ptr %src, i64 %i3_2_2
  %b3_2_2 = load i16, ptr %p3_2_2, align 1
  %v3_2_2 = zext i16 %b3_2_2 to i32
%sum3_0 = add i32 %v3_0_0, %v3_0_1
%sum3_1 = add i32 %sum3_0, %v3_0_2
%sum3_2 = add i32 %sum3_1, %v3_1_0
%sum3_3 = add i32 %sum3_2, %v3_1_1
%sum3_4 = add i32 %sum3_3, %v3_1_2
%sum3_5 = add i32 %sum3_4, %v3_2_0
%sum3_6 = add i32 %sum3_5, %v3_2_1
%sum3_7 = add i32 %sum3_6, %v3_2_2
%round3 = add i32 %sum3_7, 4
  %out3 = udiv i32 %round3, 9
  %tr3 = trunc i32 %out3 to i16
%di3 = add i64 %dr3, %x3
  %dp3 = getelementptr i16, ptr %dst, i64 %di3
  store i16 %tr3, ptr %dp3, align 1
  %xn3 = add i64 %x3, 1
  br label %b3cond
b3end:
  %yn3 = add i64 %y3, 1
  %ymore3 = icmp ult i64 %yn3, %dh
  br i1 %ymore3, label %b3row, label %exit
check3to2:
  %sw_wide = zext i64 %sw to i128
  %sh_wide = zext i64 %sh to i128
  %dw_wide = zext i64 %dw to i128
  %dh_wide = zext i64 %dh to i128
  %sw2 = shl i128 %sw_wide, 1
  %sh2 = shl i128 %sh_wide, 1
  %dw3 = mul i128 %dw_wide, 3
  %dh3 = mul i128 %dh_wide, 3
  %ratio_w = icmp eq i128 %sw2, %dw3
  %ratio_h = icmp eq i128 %sh2, %dh3
  %min_w = icmp uge i64 %sw, 3
  %min_h = icmp uge i64 %sh, 3
  %ratio = and i1 %ratio_w, %ratio_h
  %min_dims = and i1 %min_w, %min_h
  %is3to2 = and i1 %ratio, %min_dims
  br i1 %is3to2, label %b3to2row, label %qsetup
b3to2row:
  %bdy = phi i64 [ 0, %check3to2 ], [ %bnextY, %browEnd ]
  %byhalf = lshr i64 %bdy, 1
  %bsy0 = add i64 %bdy, %byhalf
  %byp = and i64 %bdy, 1
  %bsy1 = add i64 %bsy0, %byp
  %br0 = mul i64 %bsy0, %sw
  %br1 = mul i64 %bsy1, %sw
  %bdr = mul i64 %bdy, %dw
  br label %bveccond
bveccond:
  %bx = phi i64 [ 0, %b3to2row ], [ %bxnext, %bvec ]
  %bsx = phi i64 [ 0, %b3to2row ], [ %bsxnext, %bvec ]
  %bmore = icmp ult i64 %bx, %vlim
  br i1 %bmore, label %bvec, label %btailcheck
bvec:
  %bvi0 = add i64 %br0, %bsx
  %bvp0 = getelementptr i16, ptr %src, i64 %bvi0
  %bva0 = load <6 x i16>, ptr %bvp0, align 1
  %bvz0 = zext <6 x i16> %bva0 to <6 x i32>
  %bvi1 = add i64 %br1, %bsx
  %bvp1 = getelementptr i16, ptr %src, i64 %bvi1
  %bva1 = load <6 x i16>, ptr %bvp1, align 1
  %bvz1 = zext <6 x i16> %bva1 to <6 x i32>
  %bvs = add <6 x i32> %bvz0, %bvz1
  %bvc0 = shufflevector <6 x i32> %bvs, <6 x i32> poison, <4 x i32> <i32 0, i32 1, i32 3, i32 4>
  %bvc1 = shufflevector <6 x i32> %bvs, <6 x i32> poison, <4 x i32> <i32 0, i32 2, i32 3, i32 5>
  %bvsum = add <4 x i32> %bvc0, %bvc1
  %bvrnd = add <4 x i32> %bvsum, <i32 2, i32 2, i32 2, i32 2>
  %bvavg = lshr <4 x i32> %bvrnd, <i32 2, i32 2, i32 2, i32 2>
  %bvover = icmp ugt <4 x i32> %bvavg, <i32 1023, i32 1023, i32 1023, i32 1023>
  %bvclip = select <4 x i1> %bvover, <4 x i32> <i32 1023, i32 1023, i32 1023, i32 1023>, <4 x i32> %bvavg
  %bvout = trunc <4 x i32> %bvclip to <4 x i16>
  %bvdi = add i64 %bdr, %bx
  %bvdp = getelementptr i16, ptr %dst, i64 %bvdi
  store <4 x i16> %bvout, ptr %bvdp, align 1
  %bxnext = add i64 %bx, 4
  %bsxnext = add i64 %bsx, 6
  br label %bveccond
btailcheck:
  %btail = icmp ult i64 %bx, %dw
  br i1 %btail, label %bpair, label %browEnd
bpair:
  %bpi0 = add i64 %br0, %bsx
  %bpp0 = getelementptr i16, ptr %src, i64 %bpi0
  %bpa0 = load <3 x i16>, ptr %bpp0, align 1
  %bpz0 = zext <3 x i16> %bpa0 to <3 x i32>
  %bpi1 = add i64 %br1, %bsx
  %bpp1 = getelementptr i16, ptr %src, i64 %bpi1
  %bpa1 = load <3 x i16>, ptr %bpp1, align 1
  %bpz1 = zext <3 x i16> %bpa1 to <3 x i32>
  %bps = add <3 x i32> %bpz0, %bpz1
  %bpc0 = shufflevector <3 x i32> %bps, <3 x i32> poison, <2 x i32> <i32 0, i32 1>
  %bpc1 = shufflevector <3 x i32> %bps, <3 x i32> poison, <2 x i32> <i32 0, i32 2>
  %bpsum = add <2 x i32> %bpc0, %bpc1
  %bprnd = add <2 x i32> %bpsum, <i32 2, i32 2>
  %bpavg = lshr <2 x i32> %bprnd, <i32 2, i32 2>
  %bpover = icmp ugt <2 x i32> %bpavg, <i32 1023, i32 1023>
  %bpclip = select <2 x i1> %bpover, <2 x i32> <i32 1023, i32 1023>, <2 x i32> %bpavg
  %bpout = trunc <2 x i32> %bpclip to <2 x i16>
  %bpdi = add i64 %bdr, %bx
  %bpdp = getelementptr i16, ptr %dst, i64 %bpdi
  store <2 x i16> %bpout, ptr %bpdp, align 1
  br label %browEnd
browEnd:
  %bnextY = add i64 %bdy, 1
  %bmoreY = icmp ult i64 %bnextY, %dh
  br i1 %bmoreY, label %b3to2row, label %exit
qsetup:
  %srcW = add i64 %sw, 0
  %srcH = add i64 %sh, 0
  %srcStride = add i64 %sw, 0
  %dstW = add i64 %dw, 0
  %dstH = add i64 %dh, 0
  %sx0_tab = alloca [4096 x i64], align 16
  %sx1_tab = alloca [4096 x i64], align 16
  %fx_tab = alloca [4096 x i32], align 16
  %lastX = sub i64 %srcW, 1
  %lastY = sub i64 %srcH, 1
  %scaleX = shl i64 %srcW, 8
  %scaleY = shl i64 %srcH, 8
  %use_tab = icmp ule i64 %dstW, 4096
  br label %check.tab
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
  %va00_0 = getelementptr i16, ptr %src, i64 %vi00_0
  %vb00_0 = load i16, ptr %va00_0, align 1
  %vp00_0 = zext i16 %vb00_0 to i32
  %v00_0 = insertelement <4 x i32> poison, i32 %vp00_0, i64 0
  %vi01_0 = add i64 %r0, %vsx1_0
  %va01_0 = getelementptr i16, ptr %src, i64 %vi01_0
  %vb01_0 = load i16, ptr %va01_0, align 1
  %vp01_0 = zext i16 %vb01_0 to i32
  %v01_0 = insertelement <4 x i32> poison, i32 %vp01_0, i64 0
  %vi10_0 = add i64 %r1, %vsx0_0
  %va10_0 = getelementptr i16, ptr %src, i64 %vi10_0
  %vb10_0 = load i16, ptr %va10_0, align 1
  %vp10_0 = zext i16 %vb10_0 to i32
  %v10_0 = insertelement <4 x i32> poison, i32 %vp10_0, i64 0
  %vi11_0 = add i64 %r1, %vsx1_0
  %va11_0 = getelementptr i16, ptr %src, i64 %vi11_0
  %vb11_0 = load i16, ptr %va11_0, align 1
  %vp11_0 = zext i16 %vb11_0 to i32
  %v11_0 = insertelement <4 x i32> poison, i32 %vp11_0, i64 0
  %vx1 = add i64 %dx4, 1
  %vsx0p1 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx1
  %vsx0_1 = load i64, ptr %vsx0p1, align 8
  %vsx1p1 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx1
  %vsx1_1 = load i64, ptr %vsx1p1, align 8
  %vi00_1 = add i64 %r0, %vsx0_1
  %va00_1 = getelementptr i16, ptr %src, i64 %vi00_1
  %vb00_1 = load i16, ptr %va00_1, align 1
  %vp00_1 = zext i16 %vb00_1 to i32
  %v00_1 = insertelement <4 x i32> %v00_0, i32 %vp00_1, i64 1
  %vi01_1 = add i64 %r0, %vsx1_1
  %va01_1 = getelementptr i16, ptr %src, i64 %vi01_1
  %vb01_1 = load i16, ptr %va01_1, align 1
  %vp01_1 = zext i16 %vb01_1 to i32
  %v01_1 = insertelement <4 x i32> %v01_0, i32 %vp01_1, i64 1
  %vi10_1 = add i64 %r1, %vsx0_1
  %va10_1 = getelementptr i16, ptr %src, i64 %vi10_1
  %vb10_1 = load i16, ptr %va10_1, align 1
  %vp10_1 = zext i16 %vb10_1 to i32
  %v10_1 = insertelement <4 x i32> %v10_0, i32 %vp10_1, i64 1
  %vi11_1 = add i64 %r1, %vsx1_1
  %va11_1 = getelementptr i16, ptr %src, i64 %vi11_1
  %vb11_1 = load i16, ptr %va11_1, align 1
  %vp11_1 = zext i16 %vb11_1 to i32
  %v11_1 = insertelement <4 x i32> %v11_0, i32 %vp11_1, i64 1
  %vx2 = add i64 %dx4, 2
  %vsx0p2 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx2
  %vsx0_2 = load i64, ptr %vsx0p2, align 8
  %vsx1p2 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx2
  %vsx1_2 = load i64, ptr %vsx1p2, align 8
  %vi00_2 = add i64 %r0, %vsx0_2
  %va00_2 = getelementptr i16, ptr %src, i64 %vi00_2
  %vb00_2 = load i16, ptr %va00_2, align 1
  %vp00_2 = zext i16 %vb00_2 to i32
  %v00_2 = insertelement <4 x i32> %v00_1, i32 %vp00_2, i64 2
  %vi01_2 = add i64 %r0, %vsx1_2
  %va01_2 = getelementptr i16, ptr %src, i64 %vi01_2
  %vb01_2 = load i16, ptr %va01_2, align 1
  %vp01_2 = zext i16 %vb01_2 to i32
  %v01_2 = insertelement <4 x i32> %v01_1, i32 %vp01_2, i64 2
  %vi10_2 = add i64 %r1, %vsx0_2
  %va10_2 = getelementptr i16, ptr %src, i64 %vi10_2
  %vb10_2 = load i16, ptr %va10_2, align 1
  %vp10_2 = zext i16 %vb10_2 to i32
  %v10_2 = insertelement <4 x i32> %v10_1, i32 %vp10_2, i64 2
  %vi11_2 = add i64 %r1, %vsx1_2
  %va11_2 = getelementptr i16, ptr %src, i64 %vi11_2
  %vb11_2 = load i16, ptr %va11_2, align 1
  %vp11_2 = zext i16 %vb11_2 to i32
  %v11_2 = insertelement <4 x i32> %v11_1, i32 %vp11_2, i64 2
  %vx3 = add i64 %dx4, 3
  %vsx0p3 = getelementptr inbounds [4096 x i64], ptr %sx0_tab, i64 0, i64 %vx3
  %vsx0_3 = load i64, ptr %vsx0p3, align 8
  %vsx1p3 = getelementptr inbounds [4096 x i64], ptr %sx1_tab, i64 0, i64 %vx3
  %vsx1_3 = load i64, ptr %vsx1p3, align 8
  %vi00_3 = add i64 %r0, %vsx0_3
  %va00_3 = getelementptr i16, ptr %src, i64 %vi00_3
  %vb00_3 = load i16, ptr %va00_3, align 1
  %vp00_3 = zext i16 %vb00_3 to i32
  %v00_3 = insertelement <4 x i32> %v00_2, i32 %vp00_3, i64 3
  %vi01_3 = add i64 %r0, %vsx1_3
  %va01_3 = getelementptr i16, ptr %src, i64 %vi01_3
  %vb01_3 = load i16, ptr %va01_3, align 1
  %vp01_3 = zext i16 %vb01_3 to i32
  %v01_3 = insertelement <4 x i32> %v01_2, i32 %vp01_3, i64 3
  %vi10_3 = add i64 %r1, %vsx0_3
  %va10_3 = getelementptr i16, ptr %src, i64 %vi10_3
  %vb10_3 = load i16, ptr %va10_3, align 1
  %vp10_3 = zext i16 %vb10_3 to i32
  %v10_3 = insertelement <4 x i32> %v10_2, i32 %vp10_3, i64 3
  %vi11_3 = add i64 %r1, %vsx1_3
  %va11_3 = getelementptr i16, ptr %src, i64 %vi11_3
  %vb11_3 = load i16, ptr %va11_3, align 1
  %vp11_3 = zext i16 %vb11_3 to i32
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
  %clamped4 = call <4 x i32> @llvm.umin.v4i32(<4 x i32> %res4, <4 x i32> <i32 1023, i32 1023, i32 1023, i32 1023>)
  %bytes4 = trunc <4 x i32> %clamped4 to <4 x i16>
  %di4 = add i64 %dr, %dx4
  %dp4 = getelementptr i16, ptr %dst, i64 %di4
  store <4 x i16> %bytes4, ptr %dp4, align 1
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
  %a00 = getelementptr i16, ptr %src, i64 %i00
  %b00 = load i16, ptr %a00, align 1
  %p00 = zext i16 %b00 to i32
  %w00 = mul i32 %p00, %ifx
  %i01 = add i64 %r0, %sx1
  %a01 = getelementptr i16, ptr %src, i64 %i01
  %b01 = load i16, ptr %a01, align 1
  %p01 = zext i16 %b01 to i32
  %w01 = mul i32 %p01, %fx
  %i10 = add i64 %r1, %sx0
  %a10 = getelementptr i16, ptr %src, i64 %i10
  %b10 = load i16, ptr %a10, align 1
  %p10 = zext i16 %b10 to i32
  %w10 = mul i32 %p10, %ifx
  %i11 = add i64 %r1, %sx1
  %a11 = getelementptr i16, ptr %src, i64 %i11
  %b11 = load i16, ptr %a11, align 1
  %p11 = zext i16 %b11 to i32
  %w11 = mul i32 %p11, %fx
  %top = add i32 %w00, %w01
  %bot = add i32 %w10, %w11
  %wt = mul i32 %top, %ify
  %wb = mul i32 %bot, %fy
  %sum = add i32 %wt, %wb
  %rounded = add i32 %sum, 32768
  %value = lshr i32 %rounded, 16
  %over = icmp ugt i32 %value, 1023
  %clamped = select i1 %over, i32 1023, i32 %value
  %byte = trunc i32 %clamped to i16
  %di = add i64 %dr, %dx
  %dp = getelementptr i16, ptr %dst, i64 %di
  store i16 %byte, ptr %dp, align 1
  %nextX = add i64 %dx, 1
  %moreX = icmp ult i64 %nextX, %dstW
  br i1 %moreX, label %col, label %rowEnd
rowEnd:
  %nextY = add i64 %dy, 1
  %moreY = icmp ult i64 %nextY, %dstH
  br i1 %moreY, label %row, label %exit
exit:
  ret void
}
define weak_odr dso_local void @lean_native_extract_u16le_msb8(ptr %src, ptr %dst, i64 %n) #0 {
entry:
  %lim = and i64 %n, -16
  br label %vcond
vcond:
  %vi = phi i64 [ 0, %entry ], [ %vin, %vbody ]
  %vm = icmp ult i64 %vi, %lim
  br i1 %vm, label %vbody, label %cond
vbody:
  %vp = getelementptr i16, ptr %src, i64 %vi
  %vd = getelementptr i8, ptr %dst, i64 %vi
  %vb = load <16 x i16>, ptr %vp, align 1
%vs = lshr <16 x i16> %vb, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>
%vt = trunc <16 x i16> %vs to <16 x i8>
  store <16 x i8> %vt, ptr %vd, align 1
  %vin = add i64 %vi, 16
  br label %vcond
cond:
  %i = phi i64 [ %vi, %vcond ], [ %in, %body ]
  %more = icmp ult i64 %i, %n
  br i1 %more, label %body, label %exit
body:
  %p = getelementptr i16, ptr %src, i64 %i
  %d = getelementptr i8, ptr %dst, i64 %i
  %b = load i16, ptr %p, align 1
  %s = lshr i16 %b, 2
  %t = trunc i16 %s to i8
  store i8 %t, ptr %d, align 1
  %in = add i64 %i, 1
  br label %cond
exit:
  ret void
}

; Packed Y/U/V filter: source and destination may alias exactly.
declare <16 x i8> @llvm.umax.v16i8(<16 x i8>, <16 x i8>)
declare <16 x i8> @llvm.umin.v16i8(<16 x i8>, <16 x i8>)
define weak_odr dso_local void @lean_native_apply_filters_yuv420p_u8(ptr %src, ptr %dst, i64 %y_len, i64 %uv_len, i64 %flags) #0 {
entry:
  %yf = and i64 %flags, 2
  %cf = and i64 %flags, 1
  %tonemap = icmp ne i64 %yf, 0
  %csc = icmp ne i64 %cf, 0
  %same_ptr = icmp eq ptr %src, %dst
  %yvlen = and i64 %y_len, -16
  %cvlen = and i64 %uv_len, -16
  %su = getelementptr i8, ptr %src, i64 %y_len
  %sv = getelementptr i8, ptr %su, i64 %uv_len
  %du = getelementptr i8, ptr %dst, i64 %y_len
  %dv = getelementptr i8, ptr %du, i64 %uv_len
  br i1 %tonemap, label %yvcheck, label %ypass
ypass:
  br i1 %same_ptr, label %cdispatch, label %ycopycheck
ycopycheck:
  %y_pos = icmp ugt i64 %y_len, 0
  br i1 %y_pos, label %ycopy, label %cdispatch
ycopy:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %y_len, i1 false)
  br label %cdispatch
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
  store <16 x i8> %yhi, ptr %ydp, align 1
  %yn = add i64 %yi, 16
  br label %yvcheck
yscheck:
  %ysi = phi i64 [ %yi, %yvcheck ], [ %ysn, %ysbody ]
  %ysmore = icmp ult i64 %ysi, %y_len
  br i1 %ysmore, label %ysbody, label %cdispatch
ysbody:
  %yssp = getelementptr i8, ptr %src, i64 %ysi
  %ysdp = getelementptr i8, ptr %dst, i64 %ysi
  %ysb = load i8, ptr %yssp, align 1
  %yslow = icmp ult i8 %ysb, 16
  %yslo = select i1 %yslow, i8 16, i8 %ysb
  %yshigh = icmp ugt i8 %yslo, 235
  %yshi = select i1 %yshigh, i8 235, i8 %yslo
  store i8 %yshi, ptr %ysdp, align 1
  %ysn = add i64 %ysi, 1
  br label %yscheck
cdispatch:
  br i1 %csc, label %cvcheck, label %cpass
cpass:
  br i1 %same_ptr, label %done, label %ccopycheck
ccopycheck:
  %uv2_len = shl i64 %uv_len, 1
  %uv_pos = icmp ugt i64 %uv2_len, 0
  br i1 %uv_pos, label %ccopy, label %done
ccopy:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %du, ptr align 1 %su, i64 %uv2_len, i1 false)
  br label %done
cvcheck:
  %cvi = phi i64 [ 0, %cdispatch ], [ %cvn, %cvbody ]
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
  store <16 x i8> %cvubyte, ptr %cvudp, align 1
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
  store <16 x i8> %cvvbyte, ptr %cvvdp, align 1
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
  store i8 %csubyte, ptr %csudp, align 1
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
  store i8 %csvbyte, ptr %csvdp, align 1
  %csn = add i64 %csi, 1
  br label %cscheck
done:
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
