//SIMD for arm64 Neon - simdneon. This doesn't support Arm SVE.

use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::SyncDirection;
use crate::matrix::simd::neon::partial_vec_load_mul_store;
use crate::matrix::simd::neon::vdup::vdup_vld1q_dup;
use crate::matrix::simd::neon::vec_load_mul_store;
use crate::matrix::simd::SimdVecBuffer;
use crate::matrix::simd::{SimdMetaData, SimdOperation};
use crate::matrix::traits::MatrixElement;
use std::arch::aarch64::*;
use std::marker::PhantomData;
use std::ptr;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_mul_assign_not_supported {
    ($t:ty) => {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        impl SimdOperation for $t {
            unsafe fn mul_assign(_ptr: *const $t, _len: usize, _val: $t) {
                panic!("SIMD mul_assign is not supported for $t");
            }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_mul_assign {
    ($t:ident) => {
        unsafe fn mul_assign(ptr: *const $t, len: usize, val: $t) {
            let s = SimdMetaData::simd_neon::<$t>(len);
            vdup_vld1q_dup!($t, v_rhs, val);
            let mut idx: usize = 0;
            while idx < s.bat_f * s.bat_sz {
                let ptr_idx = ptr.add(idx);
                vec_load_mul_store!($t, x4, ptr_idx, v_rhs);
                idx += s.bat_sz;
            }

            if s.pbat_sz > 0 {
                let ptr_idx = ptr.add(idx);
                match s.pbat_sz {
                    1 => {
                        vec_load_mul_store!($t, x1, ptr_idx, v_rhs);
                        idx += s.vec_sz;
                    }
                    2 => {
                        vec_load_mul_store!($t, x2, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    3 => {
                        vec_load_mul_store!($t, x3, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    _ => {
                        panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                    }
                }
            }
            if s.pvec_sz > 0 {
                let ptr_idx = ptr.add(idx);
                partial_vec_load_mul_store!($t, ptr_idx, v_rhs, s.pvec_sz);
            }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u8 {
    impl_simd_operation_mul_assign!(u8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u16 {
    impl_simd_operation_mul_assign!(u16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u32 {
    impl_simd_operation_mul_assign!(u32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i8 {
    impl_simd_operation_mul_assign!(i8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i16 {
    impl_simd_operation_mul_assign!(i16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i32 {
    impl_simd_operation_mul_assign!(i32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f32 {
    impl_simd_operation_mul_assign!(f32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f64 {
    impl_simd_operation_mul_assign!(f64);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(u64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(u128);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(i64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(i128);

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) struct SimdNeonKernel<T: MatrixElement> {
    _phantom: PhantomData<T>,
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl<T> SimdNeonKernel<T>
where
    T: MatrixElement<Output = T> + SimdOperation,
{
    //TODO: Handle ColMajor, RowMajor and Dual Index Matrices
    pub(in crate::matrix::simd) fn scale_row(m: &mut Matrix<T>, row: usize, val: T) {
        if m.is_transpose {
            unsafe {
                //Get the pointer to the raw data and operate on that
                let ptr = cmd_ptr_t!(m.cmd, row, 0);
                let len = m.cmd.col_stride;
                T::mul_assign(ptr, len, val);
                m.sync_row(row, SyncDirection::CmdToRmd);
            }
        } else {
            unsafe {
                let ptr = rmd_ptr!(m.rmd, row, 0);
                let len = m.rmd.row_stride;
                T::mul_assign(ptr, len, val);
                m.sync_row(row, SyncDirection::RmdToCmd);
            }
        }
    }
}
