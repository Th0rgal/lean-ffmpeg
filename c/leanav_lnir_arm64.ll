; ModuleID = 'LeanAV.DSP.Kernels.optimized'
source_filename = "LeanAV.DSP.Kernels.lean"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

; --- LeanNative Runtime Intrinsics & C ABI Entrypoints ---
declare i1 @llvm.expect.i1(i1, i1) #2
declare <16 x i8> @llvm.aarch64.neon.pmull64(i64, i64) #2
declare <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64(<2 x i64>, <2 x i64>, <2 x i64>) #2
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
  %rc_next = add nsw i32 %rc, %c32
  store i32 %rc_next, ptr %obj, align 4
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
  %rc_next = sub nsw i32 %rc, %c32
  store i32 %rc_next, ptr %obj, align 4
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
  %rc_dec = sub nsw i32 %rc, 1
  store i32 %rc_dec, ptr %arr, align 4
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

; LNIRDecl: swscale_luma_gain_bias_simd (assurance=VerifiedKernelProof, isGpuCand=true)
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
  store i64 %ld_13, ptr %slot_v5, align 8
  %ldp_15 = load ptr, ptr %slot_v111, align 8
  store ptr %ldp_15, ptr %slot_v6, align 8
  br label %loop_hdr_16
loop_hdr_16:
  %ld_20 = load i64, ptr %slot_v5, align 8
  %loop_cmp_21 = icmp ult i64 %ld_20, %ld_14
  br i1 %loop_cmp_21, label %loop_body_17, label %loop_exit_19
loop_body_17:
  %ldp_22 = load ptr, ptr %slot_v112, align 8
  %ld_23 = load i64, ptr %slot_v5, align 8
  %rld_gep_24 = getelementptr inbounds i64, ptr %ldp_22, i64 %ld_23
  %rld_val_25 = load i64, ptr %rld_gep_24, align 8
  store i64 %rld_val_25, ptr %slot_v8, align 8
  %ld_26 = load i64, ptr %slot_v8, align 8
  %ld_27 = load i64, ptr %slot_v1, align 8
  %ld_28 = load i64, ptr %slot_v2, align 8
  %fma_mul_29 = mul i64 %ld_26, %ld_27
  %fma_add_30 = add i64 %fma_mul_29, %ld_28
  store i64 %fma_add_30, ptr %slot_v9, align 8
  %ldp_31 = load ptr, ptr %slot_v112, align 8
  %ld_32 = load i64, ptr %slot_v5, align 8
  %ld_33 = load i64, ptr %slot_v9, align 8
  %rst_gep_34 = getelementptr inbounds i64, ptr %ldp_31, i64 %ld_32
  store i64 %ld_33, ptr %rst_gep_34, align 8
  %ldp_35 = load ptr, ptr %slot_v6, align 8
  store ptr %ldp_35, ptr %slot_v6, align 8
  br label %loop_latch_18
loop_latch_18:
  %ld_36 = load i64, ptr %slot_v5, align 8
  %loop_next_37 = add nuw nsw i64 %ld_36, 1
  store i64 %loop_next_37, ptr %slot_v5, align 8
  br label %loop_hdr_16, !llvm.loop !0
loop_exit_19:
  %ldp_38 = load ptr, ptr %slot_v6, align 8
  ret ptr %ldp_38
}

; LNIRDecl: flac_lpc_autocorr_dot_simd (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %p_in1_18 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_14
  %v_in1_19 = load i64, ptr %p_in1_18, align 8
  %zm_mul_20 = mul i64 %v_in0_17, %v_in1_19
  %p_out_21 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %zm_mul_20, ptr %p_out_21, align 8
  %par_iv_next_22 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_22, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_23 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_23
}

; LNIRDecl: opus_celt_pvq_mix_saxpy_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %p_in1_18 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_14
  %v_in1_19 = load i64, ptr %p_in1_18, align 8
  %sax_mul_20 = mul i64 %v_in0_17, 4
  %sax_add_21 = add i64 %sax_mul_20, %v_in1_19
  %p_out_22 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %sax_add_21, ptr %p_out_22, align 8
  %par_iv_next_23 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_23, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_24 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_24
}

; LNIRDecl: av1_wiener_3tap_sym_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %ldp_18 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_19 = getelementptr inbounds i64, ptr %ldp_18, i64 3
  %cs_at_20 = getelementptr inbounds i64, ptr %cs_ptr_19, i64 %par_iv_14
  %cs_value_21 = load i64, ptr %cs_at_20, align 8
  %ldp_22 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_23 = getelementptr inbounds i64, ptr %ldp_22, i64 3
  %cs_at_24 = getelementptr inbounds i64, ptr %cs_ptr_23, i64 %par_iv_14
  %cs_value_25 = load i64, ptr %cs_at_24, align 8
  %ldp_26 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_27 = getelementptr inbounds i64, ptr %ldp_26, i64 3
  %cs_at_28 = getelementptr inbounds i64, ptr %cs_ptr_27, i64 %par_iv_14
  %cs_value_29 = load i64, ptr %cs_at_28, align 8
  %alu_30 = mul i64 %cs_value_25, 10
  %fma_mul_31 = mul i64 %cs_value_21, 3
  %fma_add_32 = add i64 %fma_mul_31, %alu_30
  %fma_mul_33 = mul i64 %cs_value_29, 3
  %fma_add_34 = add i64 %fma_mul_33, %fma_add_32
  %p_out_35 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %fma_add_34, ptr %p_out_35, align 8
  %par_iv_next_36 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_36, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_37 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_37
}

; LNIRDecl: av1_cdef_fma_blend_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v4, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %ldp_18 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_19 = getelementptr inbounds i64, ptr %ldp_18, i64 3
  %cs_at_20 = getelementptr inbounds i64, ptr %cs_ptr_19, i64 %par_iv_14
  %cs_value_21 = load i64, ptr %cs_at_20, align 8
  %ldp_22 = load ptr, ptr %slot_v1, align 8
  %cs_ptr_23 = getelementptr inbounds i64, ptr %ldp_22, i64 3
  %cs_at_24 = getelementptr inbounds i64, ptr %cs_ptr_23, i64 %par_iv_14
  %cs_value_25 = load i64, ptr %cs_at_24, align 8
  %ldp_26 = load ptr, ptr %slot_v2, align 8
  %cs_ptr_27 = getelementptr inbounds i64, ptr %ldp_26, i64 3
  %cs_at_28 = getelementptr inbounds i64, ptr %cs_ptr_27, i64 %par_iv_14
  %cs_value_29 = load i64, ptr %cs_at_28, align 8
  %fma_mul_30 = mul i64 %cs_value_21, %cs_value_25
  %fma_add_31 = add i64 %fma_mul_30, %cs_value_29
  %p_out_32 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %fma_add_31, ptr %p_out_32, align 8
  %par_iv_next_33 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_33, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_34 = load ptr, ptr %slot_v4, align 8
  ret ptr %ldp_34
}

; LNIRDecl: h264_idct_tuple_accum_sroa (assurance=VerifiedKernelProof, isGpuCand=false)
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
  store i64 %ld_0, ptr %slot_v3, align 8
  %ld_2 = load i64, ptr %slot_v1, align 8
  store i64 %ld_2, ptr %slot_v4, align 8
  br label %loop_hdr_3
loop_hdr_3:
  %ld_7 = load i64, ptr %slot_v3, align 8
  %loop_cmp_8 = icmp ult i64 %ld_7, %ld_1
  br i1 %loop_cmp_8, label %loop_body_4, label %loop_exit_6
loop_body_4:
  %ld_9 = load i64, ptr %slot_v4, align 8
  %ld_10 = load i64, ptr %slot_v3, align 8
  %alu_11 = add i64 %ld_9, %ld_10
  store i64 %alu_11, ptr %slot_v5, align 8
  %ld_12 = load i64, ptr %slot_v3, align 8
  %alu_13 = shl i64 %ld_12, 1
  store i64 %alu_13, ptr %slot_v6, align 8
  %ld_14 = load i64, ptr %slot_v5, align 8
  store i64 %ld_14, ptr %slot_v8, align 8
  %ld_15 = load i64, ptr %slot_v6, align 8
  store i64 %ld_15, ptr %slot_v9, align 8
  %ld_16 = load i64, ptr %slot_v8, align 8
  %ld_17 = load i64, ptr %slot_v9, align 8
  %alu_18 = add i64 %ld_16, %ld_17
  store i64 %alu_18, ptr %slot_v10, align 8
  %ld_19 = load i64, ptr %slot_v10, align 8
  store i64 %ld_19, ptr %slot_v4, align 8
  br label %loop_latch_5
loop_latch_5:
  %ld_20 = load i64, ptr %slot_v3, align 8
  %loop_next_21 = add nuw nsw i64 %ld_20, 1
  store i64 %loop_next_21, ptr %slot_v3, align 8
  br label %loop_hdr_3, !llvm.loop !6
loop_exit_6:
  %ld_22 = load i64, ptr %slot_v4, align 8
  ret i64 %ld_22
}

; LNIRDecl: bframe_bipred_blend_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %p_in1_18 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_14
  %v_in1_19 = load i64, ptr %p_in1_18, align 8
  %sax_mul_20 = mul i64 %v_in0_17, 1
  %sax_add_21 = add i64 %sax_mul_20, %v_in1_19
  %p_out_22 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %sax_add_21, ptr %p_out_22, align 8
  %par_iv_next_23 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_23, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_24 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_24
}

; LNIRDecl: hevc_sao_band_offset_add_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %p_in1_18 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_14
  %v_in1_19 = load i64, ptr %p_in1_18, align 8
  %za_add_20 = add i64 %v_in0_17, %v_in1_19
  %p_out_21 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %za_add_20, ptr %p_out_21, align 8
  %par_iv_next_22 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_22, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_23 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_23
}

; LNIRDecl: aac_imdct_window_mul_gpu (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v3, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %p_in1_18 = getelementptr inbounds i64, ptr %par_in1_data_9, i64 %par_iv_14
  %v_in1_19 = load i64, ptr %p_in1_18, align 8
  %zm_mul_20 = mul i64 %v_in0_17, %v_in1_19
  %p_out_21 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %zm_mul_20, ptr %p_out_21, align 8
  %par_iv_next_22 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_22, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_23 = load ptr, ptr %slot_v3, align 8
  ret ptr %ldp_23
}

; LNIRDecl: prores_qscale_map_simd (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %msa_mul_18 = mul i64 %v_in0_17, 16
  %msa_add_19 = add i64 %msa_mul_18, 8
  %p_out_20 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %msa_add_19, ptr %p_out_20, align 8
  %par_iv_next_21 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_21, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_22 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_22
}

; LNIRDecl: boxblur_div9_recip_shift_simd (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %ldp_18 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_19 = getelementptr inbounds i64, ptr %ldp_18, i64 3
  %cs_at_20 = getelementptr inbounds i64, ptr %cs_ptr_19, i64 %par_iv_14
  %cs_value_21 = load i64, ptr %cs_at_20, align 8
  %alu_22 = add i64 %cs_value_21, 4
  %alu_23 = mul i64 %alu_22, 7282
  %alu_24 = lshr i64 %alu_23, 16
  %p_out_25 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %alu_24, ptr %p_out_25, align 8
  %par_iv_next_26 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_26, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_27 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_27
}

; LNIRDecl: pq10_studio_clamp_select_simd (assurance=VerifiedKernelProof, isGpuCand=true)
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
  %par_out_6 = call ptr @lean_native_ensure_exclusive(ptr %ldp_4)
  store ptr %par_out_6, ptr %slot_v2, align 8
  %par_out_data_7 = getelementptr inbounds i64, ptr %par_out_6, i64 3
  %par_in0_data_8 = getelementptr inbounds i64, ptr %ldp_4, i64 3
  %par_in1_data_9 = getelementptr inbounds i64, ptr %ldp_5, i64 3
  %par_iv_slot_13 = alloca i64, align 8
  store i64 0, ptr %par_iv_slot_13, align 8
  br label %par_cond_10
par_cond_10:
  %par_iv_14 = load i64, ptr %par_iv_slot_13, align 8
  %par_cmp_15 = icmp ult i64 %par_iv_14, %ld_3
  br i1 %par_cmp_15, label %par_body_11, label %par_exit_12
par_body_11:
  %p_in0_16 = getelementptr inbounds i64, ptr %par_in0_data_8, i64 %par_iv_14
  %v_in0_17 = load i64, ptr %p_in0_16, align 8
  %ldp_18 = load ptr, ptr %slot_v0, align 8
  %cs_ptr_19 = getelementptr inbounds i64, ptr %ldp_18, i64 3
  %cs_at_20 = getelementptr inbounds i64, ptr %cs_ptr_19, i64 %par_iv_14
  %cs_value_21 = load i64, ptr %cs_at_20, align 8
  %cmp_lt_23 = icmp ult i64 %cs_value_21, 64
  %alu_22 = zext i1 %cmp_lt_23 to i64
  %cmp_lt_25 = icmp ult i64 940, %cs_value_21
  %alu_24 = zext i1 %cmp_lt_25 to i64
  %sel_cond_26 = icmp ne i64 %alu_24, 0
  %sel_27 = select i1 %sel_cond_26, i64 940, i64 %cs_value_21
  %sel_cond_28 = icmp ne i64 %alu_22, 0
  %sel_29 = select i1 %sel_cond_28, i64 64, i64 %sel_27
  %p_out_30 = getelementptr inbounds i64, ptr %par_out_data_7, i64 %par_iv_14
  store i64 %sel_29, ptr %p_out_30, align 8
  %par_iv_next_31 = add nuw nsw i64 %par_iv_14, 1
  store i64 %par_iv_next_31, ptr %par_iv_slot_13, align 8
  br label %par_cond_10, !llvm.loop !0
par_exit_12:
  %ldp_32 = load ptr, ptr %slot_v2, align 8
  ret ptr %ldp_32
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

attributes #0 = { nounwind uwtable "target-cpu"="apple-m3" "target-features"="+neon,+aes,+sha3" }
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
!8 = !{!"llvm.loop.vectorize.scalable.enable", i1 false}
