use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::simd::neon::simd_op_into;
use crate::matrix::simd::neon::vdup::vdup_vld1q_dup;
use crate::matrix::simd::neon::SimdKernelNeon;
use crate::matrix::simd::traits::SimdPtrAddInto;
use crate::matrix::simd::vecbuf::SimdVecBuffer;
use crate::matrix::traits::ElementType;
use crate::matrix::traits::MatrixElement;
use core::arch::aarch64::*;
use core::ptr;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_add_into {
    ($type:ident, $x:ident, $ptr:ident, $dst:ident, $v_rhs:ident) => {
        crate::matrix::simd::neon::vload::vload_vld1q!($type, $x, v_lhs, $ptr);
        crate::matrix::simd::neon::vaddq::vadd_vaddq!($type, $x, v_lhs, $v_rhs, v_res);
        crate::matrix::simd::neon::vstore::vstore_vst1q!($type, $x, $dst, v_res);
    };
    ($t:ident, $ptr:ident, $dst: ident, $v_rhs:ident, $pvec_sz:expr) => {
        let mut sv_buf = SimdVecBuffer::<$t>::neon_vec();
        sv_buf.load($ptr, $pvec_sz);
        let buf_ptr = sv_buf.buf;
        vec_add_into!($t, x1, buf_ptr, $dst, $v_rhs);
        sv_buf.store($dst as *mut $t);
    };
}

macro_rules! dispatch_add_into {
    ($ptr: ident, $dst: ident, $val:ident, $len:ident, $(($t: ident, $e:ident)),*) => {
        match $val.element_type() {
            $(
                ElementType::$e(val) => {
                    $t::ptr_add_into($ptr as *const $t, $dst as *const $t, $len, val);
                }
            )*
                _ => {
                    panic!("Operation not supported");
                }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_add_into {
    ($t:ident) => {
        simd_op_into!($t, add_into, vdup_vld1q_dup, vec_add_into, vec_add_into);
    };
}

impl<T> SimdPtrAddInto<T> for SimdKernelNeon<T>
where
    T: MatrixElement,
{
    unsafe fn ptr_add_into(ptr: *const T, dst: *const T, len: usize, val: T) {
        dispatch_add_into!(
            ptr,
            dst,
            val,
            len,
            (u8, U8),
            (u16, U16),
            (u32, U32),
            (i8, I8),
            (i16, I16),
            (i32, I32),
            (f32, F32),
            (f64, F64)
        )
    }
}

macro_rules! impl_simd_ptr_into {
    ($($t:ident),*) => {
        $(
            impl SimdPtrAddInto for $t {
                unsafe fn ptr_add_into(ptr: *const Self, dst: *const Self, len: usize, val: Self) {
                    impl_simd_operation_add_into!($t);
                }
            }
        )*
    };
}

impl_simd_ptr_into!(u8, u16, u32, i8, i16, i32, f32, f64);
