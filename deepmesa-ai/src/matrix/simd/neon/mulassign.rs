use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::simd::neon::vdup::vdup_vld1q_dup;
use crate::matrix::simd::neon::vload::vload_vld1q;
use crate::matrix::simd::neon::vmulq::vmul_vmulq;
use crate::matrix::simd::neon::vmulqxn::vmul_vmulqxn;
use crate::matrix::simd::neon::vstore::vstore_vst1q;
use crate::matrix::simd::traits::SimdMulAssign;
use core::arch::aarch64::*;
use core::ptr;

macro_rules! impl_simd_mul_assign {
    ($t:ident) => {
        impl SimdMulAssign<$t, $t> for $t {
            unsafe fn simd_mul_assign(ptr: *mut $t, val: $t, len: usize) {
                let s = SimdMetaData::simd_neon::<$t>(len);
                vdup_vld1q_dup!($t, v_rhs, val);
                let mut idx: usize = 0;

                while idx < s.bat_f * s.bat_sz * s.vec_sz {
                    let ptr_idx = ptr.add(idx);
                    vload_vld1q!($t, x4, v_lhs, ptr_idx);
                    vmul_vmulq!($t, x4, v_lhs, v_rhs, v_res);
                    vstore_vst1q!($t, x4, ptr_idx, v_res);
                    idx += s.vec_sz * s.bat_sz;
                }

                if s.pbat_sz > 0 {
                    let ptr_idx = ptr.add(idx);
                    match s.pbat_sz {
                        1 => {
                            vload_vld1q!($t, x1, v_lhs, ptr_idx);
                            vmul_vmulq!($t, x1, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x1, ptr_idx, v_res);
                            idx += s.vec_sz;
                        }
                        2 => {
                            vload_vld1q!($t, x2, v_lhs, ptr_idx);
                            vmul_vmulq!($t, x2, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x2, ptr_idx, v_res);
                            idx += s.vec_sz * 2;
                        }
                        3 => {
                            vload_vld1q!($t, x3, v_lhs, ptr_idx);
                            vmul_vmulq!($t, x3, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x3, ptr_idx, v_res);
                            idx += s.vec_sz * 3;
                        }
                        _ => {
                            panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                        }
                    }
                }
                if s.pvec_sz > 0 {
                    let mut ptr_idx = ptr.add(idx);
                    for _ in 0..s.pvec_sz {
                        *ptr_idx *= val;
                        ptr_idx = ptr_idx.add(1);
                    }
                }
            }
        }

        impl SimdMulAssign<$t, *const $t> for $t {
            unsafe fn simd_mul_assign(ptr: *mut $t, rhs: *const $t, len: usize) {
                let s = SimdMetaData::simd_neon::<$t>(len);
                let mut idx: usize = 0;
                while idx < s.bat_f * s.bat_sz * s.vec_sz {
                    let ptr_idx = ptr.add(idx);
                    let prhs_idx = rhs.add(idx);
                    vload_vld1q!($t, x4, v_lhs, ptr_idx);
                    vload_vld1q!($t, x4, v_rhs, prhs_idx);
                    vmul_vmulqxn!($t, x4, v_lhs, v_rhs, v_res);
                    vstore_vst1q!($t, x4, ptr_idx, v_res);
                    idx += s.vec_sz * s.bat_sz;
                }

                if s.pbat_sz > 0 {
                    let ptr_idx = ptr.add(idx);
                    let prhs_idx = rhs.add(idx);
                    match s.pbat_sz {
                        1 => {
                            vload_vld1q!($t, x1, v_lhs, ptr_idx);
                            vload_vld1q!($t, x1, v_rhs, prhs_idx);
                            vmul_vmulqxn!($t, x1, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x1, ptr_idx, v_res);
                            idx += s.vec_sz;
                        }
                        2 => {
                            vload_vld1q!($t, x2, v_lhs, ptr_idx);
                            vload_vld1q!($t, x2, v_rhs, prhs_idx);
                            vmul_vmulqxn!($t, x2, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x2, ptr_idx, v_res);
                            idx += s.vec_sz * 2;
                        }
                        3 => {
                            vload_vld1q!($t, x3, v_lhs, ptr_idx);
                            vload_vld1q!($t, x3, v_rhs, prhs_idx);
                            vmul_vmulqxn!($t, x3, v_lhs, v_rhs, v_res);
                            vstore_vst1q!($t, x3, ptr_idx, v_res);
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
                    for _ in 0..s.pvec_sz {
                        *ptr_idx *= *prhs_idx;
                        ptr_idx = ptr_idx.add(1);
                        prhs_idx = prhs_idx.add(1);
                    }
                }
            }
        }
    };
}

impl_simd_mul_assign!(u8);
impl_simd_mul_assign!(u16);
impl_simd_mul_assign!(u32);
impl_simd_mul_assign!(i8);
impl_simd_mul_assign!(i16);
impl_simd_mul_assign!(i32);
impl_simd_mul_assign!(f32);
impl_simd_mul_assign!(f64);
