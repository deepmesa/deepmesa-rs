pub(in crate::matrix) mod addassign;
pub(in crate::matrix) mod neon;
pub(in crate::matrix) mod rmd;
pub(in crate::matrix) mod vaddq;
pub(in crate::matrix) mod vdup;
pub(in crate::matrix) mod vload;
pub(in crate::matrix) mod vmulq;
pub(in crate::matrix) mod vstore;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_load_mul_store {
    ($t:ident, $x:ident, $ptr:ident, $v_rhs:ident) => {
        crate::matrix::simd::neon::vload::vload_vld1q!($t, $x, v_lhs, $ptr);
        crate::matrix::simd::neon::vmulq::vmul_vmulq!($t, $x, v_lhs, $v_rhs, v_res);
        crate::matrix::simd::neon::vstore::vstore_vst1q!($t, $x, $ptr, v_res);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_load_add_store {
    ($t:ident, $x:ident, $ptr:ident, $v_rhs:ident) => {
        crate::matrix::simd::neon::vload::vload_vld1q!($t, $x, v_lhs, $ptr);
        crate::matrix::simd::neon::vaddq::vadd_vaddq!($t, $x, v_lhs, $v_rhs, v_res);
        crate::matrix::simd::neon::vstore::vstore_vst1q!($t, $x, $ptr, v_res);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! partial_vec_load_mul_store {
    ($t:ident, $ptr:ident, $v_rhs:ident, $pvec_sz:expr) => {
        let mut sv_buf = SimdVecBuffer::<$t>::neon_vec();
        sv_buf.load($ptr, $pvec_sz);
        let buf_ptr = sv_buf.buf;
        vec_load_mul_store!($t, x1, buf_ptr, $v_rhs);
        sv_buf.store($ptr as *mut $t);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! partial_vec_load_add_store {
    ($t:ident, $ptr:ident, $v_rhs:ident, $pvec_sz:expr) => {
        let mut sv_buf = SimdVecBuffer::<$t>::neon_vec();
        sv_buf.load($ptr, $pvec_sz);
        let buf_ptr = sv_buf.buf;
        vec_load_add_store!($t, x1, buf_ptr, $v_rhs);
        sv_buf.store($ptr as *mut $t);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use vec_load_mul_store;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use partial_vec_load_mul_store;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use vec_load_add_store;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use partial_vec_load_add_store;
