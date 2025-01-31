//SIMD for arm64 Neon - simdneon. This doesn't support Arm SVE.

use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::SyncDirection;
use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::simd::neon::partial_vec_load_add_store;
use crate::matrix::simd::neon::partial_vec_load_mul_store;
use crate::matrix::simd::neon::vdup::vdup_vld1q_dup;
use crate::matrix::simd::neon::vec_load_add_store;
use crate::matrix::simd::neon::vec_load_mul_store;
use crate::matrix::simd::traits::SimdOperation;
use crate::matrix::simd::vecbuf::SimdVecBuffer;
use crate::matrix::traits::MatrixElement;
use std::arch::aarch64::*;
use std::marker::PhantomData;
use std::ptr;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_not_supported {
    ($t:ty) => {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        impl SimdOperation for $t {
            unsafe fn mul_assign(_ptr: *const $t, _len: usize, _val: $t) {
                panic!("SIMD mul_assign is not supported for $t");
            }
            unsafe fn add_assign(_ptr: *const $t, _len: usize, _val: $t) {
                panic!("SIMD add_assign is not supported for $t");
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

/*
Given a pointer to a contiguous set of memory that represents ONE ROW
in an RMD or ONE COL in a CMD:

do:

1. Start pointer: *ptr
2. n full_batches + k partial_batch + v partial_vec

*/

macro_rules! simd_op {
    ($t:ident,
     $fn_name:ident,
     $vec_dup_op: ident,
     $batch_vec_op: ident,
     $partial_vec_op: ident) => {
        unsafe fn $fn_name(ptr: *const $t, len: usize, val: $t) {
            let s = SimdMetaData::simd_neon::<$t>(len);
            $vec_dup_op!($t, v_rhs, val);
            let mut idx: usize = 0;
            while idx < s.bat_f * s.bat_sz {
                let ptr_idx = ptr.add(idx);
                $batch_vec_op!($t, x4, ptr_idx, v_rhs);
                idx += s.bat_sz;
            }

            if s.pbat_sz > 0 {
                let ptr_idx = ptr.add(idx);
                match s.pbat_sz {
                    1 => {
                        $batch_vec_op!($t, x1, ptr_idx, v_rhs);
                        idx += s.vec_sz;
                    }
                    2 => {
                        $batch_vec_op!($t, x2, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    3 => {
                        $batch_vec_op!($t, x3, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    _ => {
                        panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                    }
                }
            }
            if s.pvec_sz > 0 {
                let ptr_idx = ptr.add(idx);
                $partial_vec_op!($t, ptr_idx, v_rhs, s.pvec_sz);
            }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_add_assign {
    ($t:ident) => {
        simd_op!(
            $t,
            add_assign,
            vdup_vld1q_dup,
            vec_load_add_store,
            partial_vec_load_add_store
        );
    };
}
// #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
// macro_rules! impl_simd_operation_add_assign {
//     ($t:ident) => {
//         unsafe fn add_assign(ptr: *const $t, row_len: usize, val: $t) {
//             let s = SimdMetaData::simd_neon::<$t>(row_len);
//             vdup_vld1q_dup!($t, v_rhs, val);
//             let mut idx: usize = 0;
//             while idx < s.bat_f * s.bat_sz {
//                 let ptr_idx = ptr.add(idx);
//                 vec_load_add_store!($t, x4, ptr_idx, v_rhs);
//                 idx += s.bat_sz;
//             }

//             if s.pbat_sz > 0 {
//                 let ptr_idx = ptr.add(idx);
//                 match s.pbat_sz {
//                     1 => {
//                         vec_load_add_store!($t, x1, ptr_idx, v_rhs);
//                         idx += s.vec_sz;
//                     }
//                     2 => {
//                         vec_load_add_store!($t, x2, ptr_idx, v_rhs);
//                         idx += s.vec_sz * 2;
//                     }
//                     3 => {
//                         vec_load_add_store!($t, x3, ptr_idx, v_rhs);
//                         idx += s.vec_sz * 2;
//                     }
//                     _ => {
//                         panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
//                     }
//                 }
//             }
//             if s.pvec_sz > 0 {
//                 let ptr_idx = ptr.add(idx);
//                 partial_vec_load_add_store!($t, ptr_idx, v_rhs, s.pvec_sz);
//             }
//         }
//     };
// }

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u8 {
    impl_simd_operation_mul_assign!(u8);
    impl_simd_operation_add_assign!(u8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u16 {
    impl_simd_operation_mul_assign!(u16);
    impl_simd_operation_add_assign!(u16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u32 {
    impl_simd_operation_mul_assign!(u32);
    impl_simd_operation_add_assign!(u32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i8 {
    impl_simd_operation_mul_assign!(i8);
    impl_simd_operation_add_assign!(i8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i16 {
    impl_simd_operation_mul_assign!(i16);
    impl_simd_operation_add_assign!(i16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i32 {
    impl_simd_operation_mul_assign!(i32);
    impl_simd_operation_add_assign!(i32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f32 {
    impl_simd_operation_mul_assign!(f32);
    impl_simd_operation_add_assign!(f32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f64 {
    impl_simd_operation_mul_assign!(f64);
    impl_simd_operation_add_assign!(f64);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_not_supported!(u64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_not_supported!(u128);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_not_supported!(i64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_not_supported!(i128);

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
                match &mut m.data {
                    crate::matrix::matrix::MatrixData::ColMajor(cmd) => {
                        // //Get the pointer to the raw data and operate on that
                        let ptr = cmd_ptr_t!(cmd, row, 0);
                        let len = cmd.col_stride;
                        T::mul_assign(ptr, len, val);
                        //TODO:                         m.sync_row(row, SyncDirection::CmdToRmd);
                    }
                    _ => {}
                };
            }
        } else {
            unsafe {
                match &mut m.data {
                    crate::matrix::matrix::MatrixData::RowMajor(rmd) => {
                        let ptr = rmd_ptr!(rmd, row, 0);
                        let len = rmd.row_stride;
                        T::mul_assign(ptr, len, val);
                        //TODO                        m.sync_row(row, SyncDirection::RmdToCmd);
                    }
                    _ => {}
                }
            }
        }
    }
}

//#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
//use crate::matrix::simd::neon::neon::SimdNeonKernel;

#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
macro_rules! impl_simd_op_empty {
    ($t:ty) => {
        #[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
        impl SimdOperation for $t {}
    };
}

#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(u8);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(u16);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(u32);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(u64);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(u128);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(i8);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(i16);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(i32);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(i64);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(i128);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(f32);
#[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
impl_simd_op_empty!(f64);

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T> + SimdOperation,
{
    pub(in crate::matrix) fn scale_row_simd(&mut self, row: usize, scalar: T) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        {
            SimdNeonKernel::scale_row(self, row, scalar);
        }
    }
}

// #[cfg(test)]
// mod tests {

//     use crate::matrix::matrix::Matrix;
//     use crate::matrix::matrix::MatrixType;
//     //    #[test]
//     // fn test_scale_row_simd() {
//     //     let rows = 2;
//     //     let cols = 6;
//     //     let mut m: Matrix<u8> = Matrix::new(rows, cols, MatrixType::DualIndex, true);
//     //     m.fill(3);
//     //     m.set_simd_enabled(true);
//     //     assert_eq!(m.simd_enabled, true);
//     //     println!("Before Transpose");
//     //     println!("Before Scale: {:?}", m);
//     //     m.scale_row(1, 3);
//     //     println!("After Scale: {:?}", m);
//     //     m.transpose();
//     //     println!("After Transpose");
//     //     println!("Before Scale: {:?}", m);
//     //     m.transpose();
//     //     println!("Transposing Again:");
//     //     println!("Before Scale: {:?}", m);
//     //     // m.scale_row(1, 2);
//     //     // println!("After Scale: {:?}", m);
//     // }
// }
