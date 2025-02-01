pub(in crate::matrix) mod addassign;
pub(in crate::matrix) mod addinto;
pub(in crate::matrix) mod vaddq;
pub(in crate::matrix) mod vdup;
pub(in crate::matrix) mod vload;
pub(in crate::matrix) mod vmulq;
pub(in crate::matrix) mod vstore;
use crate::matrix::traits::MatrixElement;
use std::marker::PhantomData;

pub(in crate::matrix::simd) struct SimdKernelNeon<T>
where
    T: MatrixElement,
{
    _p: PhantomData<T>,
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_mul_assign {
    ($type:ident, $x:ident, $ptr:ident, $v_rhs:ident) => {
        crate::matrix::simd::neon::vload::vload_vld1q!($type, $x, v_lhs, $ptr);
        crate::matrix::simd::neon::vmulq::vmul_vmulq!($type, $x, v_lhs, $v_rhs, v_res);
        crate::matrix::simd::neon::vstore::vstore_vst1q!($type, $x, $ptr, v_res);
    };
    ($t:ident, $ptr:ident, $v_rhs:ident, $pvec_sz:expr) => {
        let mut sv_buf = SimdVecBuffer::<$t>::neon_vec();
        sv_buf.load($ptr, $pvec_sz);
        let buf_ptr = sv_buf.buf;
        vec_load_add_store!($t, x1, buf_ptr, $v_rhs);
        sv_buf.store($ptr as *mut $t);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use vec_mul_assign;

macro_rules! simd_op_assign {
    ($t:ident,
     $fn_name:ident,
     $vec_dup_op: ident,
     $vec_op_assign: ident,
     $vec_op_assign_partial: ident) => {
        unsafe fn $fn_name(ptr: *const $t, len: usize, val: $t) {
            let s = SimdMetaData::simd_neon::<$t>(len);
            $vec_dup_op!($t, v_rhs, val);
            let mut idx: usize = 0;
            while idx < s.bat_f * s.bat_sz {
                let ptr_idx = ptr.add(idx);
                $vec_op_assign!($t, x4, ptr_idx, v_rhs);
                idx += s.bat_sz;
            }

            if s.pbat_sz > 0 {
                let ptr_idx = ptr.add(idx);
                match s.pbat_sz {
                    1 => {
                        $vec_op_assign!($t, x1, ptr_idx, v_rhs);
                        idx += s.vec_sz;
                    }
                    2 => {
                        $vec_op_assign!($t, x2, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    3 => {
                        $vec_op_assign!($t, x3, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    _ => {
                        panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                    }
                }
            }
            if s.pvec_sz > 0 {
                let ptr_idx = ptr.add(idx);
                $vec_op_assign_partial!($t, ptr_idx, v_rhs, s.pvec_sz);
            }
        }
    };
}

pub(in crate::matrix::simd::neon) use simd_op_assign;

macro_rules! simd_op_into {
    ($t:ident,
     $fn_name:ident,
     $vec_dup_op: ident,
     $vec_op_into: ident,
     $vec_op_into_partial: ident) => {
        unsafe fn $fn_name(ptr: *const $t, dst: *const $t, len: usize, val: $t) {
            let s = SimdMetaData::simd_neon::<$t>(len);
            $vec_dup_op!($t, v_rhs, val);
            let mut idx: usize = 0;
            while idx < s.bat_f * s.bat_sz {
                let ptr_idx = ptr.add(idx);
                let dst_idx = dst.add(idx);
                $vec_op_into!($t, x4, ptr_idx, dst_idx, v_rhs);
                idx += s.bat_sz;
            }

            if s.pbat_sz > 0 {
                let ptr_idx = ptr.add(idx);
                let dst_idx = dst.add(idx);
                match s.pbat_sz {
                    1 => {
                        $vec_op_into!($t, x1, ptr_idx, dst_idx, v_rhs);
                        idx += s.vec_sz;
                    }
                    2 => {
                        $vec_op_into!($t, x2, ptr_idx, dst_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    3 => {
                        $vec_op_into!($t, x3, ptr_idx, dst_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    _ => {
                        panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                    }
                }
            }
            if s.pvec_sz > 0 {
                let ptr_idx = ptr.add(idx);
                let dst_idx = dst.add(idx);
                $vec_op_into_partial!($t, ptr_idx, dst_idx, v_rhs, s.pvec_sz);
            }
        }
    };
}

pub(in crate::matrix::simd::neon) use simd_op_into;
