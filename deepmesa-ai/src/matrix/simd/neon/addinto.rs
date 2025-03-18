use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::simd::neon::kernel::SimdKernelNeon;
use crate::matrix::simd::neon::vaddq::vadd_vaddq;
use crate::matrix::simd::neon::vaddqxn::vadd_vaddqxn;
use crate::matrix::simd::neon::vdup::vdup_vld1q_dup;
use crate::matrix::simd::neon::vload::vload_vld1q;
use crate::matrix::simd::neon::vstore::vstore_vst1q;
use crate::matrix::simd::traits::SimdAddInto;
use crate::matrix::simd::vecbuf::SimdVecBuffer;
use crate::matrix::traits::ElementType;
use crate::matrix::traits::MatrixElement;
use core::arch::aarch64::*;
use core::ptr;

macro_rules! impl_simd_add_into {
    ($t:ident) => {
        impl SimdAddInto<$t, $t> for $t {
            unsafe fn simd_add_into(ptr: *const $t, rhs: $t, dst: *mut $t, len: usize) {
                let s = SimdMetaData::simd_neon::<$t>(len);
                vdup_vld1q_dup!($t, v_rhs, rhs);
                let mut idx: usize = 0;

                while idx < s.bat_f * s.bat_sz * s.vec_sz {
                    let ptr_idx = ptr.add(idx);
                    let dst_idx = dst.add(idx);
                    vload_vld1q!($t, x4, v_lhs, ptr_idx);
                    vadd_vaddq!($t, x4, v_lhs, v_rhs, v_res);
                    vstore_vst1q!($t, x4, dst_idx, v_res);
                    idx += s.vec_sz * s.bat_sz;
                }

                if s.pbat_sz > 0 {
                    let ptr_idx = ptr.add(idx);
                    let dst_idx = dst.add(idx);
                    match s.pbat_sz {
                        1 => {
                            vload_vld1q!($t, x1, v_lhs, ptr_idx);
                            vadd_vaddq!($t, x1, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x1, dst_idx, v_res);
                            idx += s.vec_sz;
                        }
                        2 => {
                            vload_vld1q!($t, x2, v_lhs, ptr_idx);
                            vadd_vaddq!($t, x2, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x2, dst_idx, v_res);
                            idx += s.vec_sz * 2;
                        }
                        3 => {
                            vload_vld1q!($t, x3, v_lhs, ptr_idx);
                            vadd_vaddq!($t, x3, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x3, dst_idx, v_res);
                            idx += s.vec_sz * 3;
                        }
                        _ => {
                            panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                        }
                    }
                }
                if s.pvec_sz > 0 {
                    let mut ptr_idx = ptr.add(idx);
                    let mut dst_idx = dst.add(idx);
                    for _ in 0..s.pvec_sz {
                        *dst_idx = *ptr_idx + rhs;
                        ptr_idx = ptr_idx.add(1);
                        dst_idx = dst_idx.add(1);
                    }
                }
            }
        }

        impl SimdAddInto<$t, *const $t> for $t {
            unsafe fn simd_add_into(ptr: *const $t, rhs: *const $t, dst: *mut $t, len: usize) {
                let s = SimdMetaData::simd_neon::<$t>(len);

                let mut idx: usize = 0;
                while idx < s.bat_f * s.bat_sz * s.vec_sz {
                    let ptr_idx = ptr.add(idx);
                    let prhs_idx = rhs.add(idx);
                    let pdst_idx = dst.add(idx);
                    vload_vld1q!($t, x4, v_lhs, ptr_idx);
                    vload_vld1q!($t, x4, v_rhs, prhs_idx);
                    vadd_vaddqxn!($t, x4, v_lhs, v_rhs, v_res);
                    vstore_vst1q!($t, x4, pdst_idx, v_res);
                    idx += s.vec_sz * s.bat_sz;
                }

                if s.pbat_sz > 0 {
                    let ptr_idx = ptr.add(idx);
                    let prhs_idx = rhs.add(idx);
                    let pdst_idx = dst.add(idx);
                    match s.pbat_sz {
                        1 => {
                            vload_vld1q!($t, x1, v_lhs, ptr_idx);
                            vload_vld1q!($t, x1, v_rhs, prhs_idx);
                            vadd_vaddqxn!($t, x1, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x1, pdst_idx, v_res);
                            idx += s.vec_sz;
                        }
                        2 => {
                            vload_vld1q!($t, x2, v_lhs, ptr_idx);
                            vload_vld1q!($t, x2, v_rhs, prhs_idx);
                            vadd_vaddqxn!($t, x2, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x2, pdst_idx, v_res);
                            idx += s.vec_sz * 2;
                        }
                        3 => {
                            vload_vld1q!($t, x3, v_lhs, ptr_idx);
                            vload_vld1q!($t, x3, v_rhs, prhs_idx);
                            vadd_vaddqxn!($t, x3, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x3, pdst_idx, v_res);
                            idx += s.vec_sz * 3;
                        }
                        _ => {
                            panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                        }
                    }
                }
                if s.pvec_sz > 0 {
                    let mut ptr_idx = ptr.add(idx);
                    let mut prhs_idx = rhs.add(idx);
                    let mut pdst_idx = dst.add(idx);
                    for _ in 0..s.pvec_sz {
                        *pdst_idx = *ptr_idx + *prhs_idx;
                        ptr_idx = ptr_idx.add(1);
                        prhs_idx = prhs_idx.add(1);
                        pdst_idx = pdst_idx.add(1);
                    }
                }
            }
        }
    };
}

impl_simd_add_into!(u8);
impl_simd_add_into!(u16);
impl_simd_add_into!(u32);
impl_simd_add_into!(i8);
impl_simd_add_into!(i16);
impl_simd_add_into!(i32);
impl_simd_add_into!(f32);
impl_simd_add_into!(f64);
