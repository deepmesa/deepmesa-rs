pub(in crate::matrix) mod kernel;
pub(in crate::matrix) mod metadata;
pub(in crate::matrix) mod traits;
pub(in crate::matrix) mod vecbuf;

use core::mem;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix) mod neon;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) const SIMD_NEON_VEC_SIZE_BYTES: usize = 16;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) const SIMD_NEON_LOAD_SIZE_4: usize = 4;

pub(in crate::matrix) fn simd_align<T>(stride: usize, simd_vec_size: usize) -> usize {
    //lanes per vector
    let lanes = simd_vec_size / mem::size_of::<T>();
    let elem_per_vec = lanes;
    let vec_ct = (stride as f32 / lanes as f32).ceil() as usize;
    return vec_ct * elem_per_vec;
}

pub(in crate::matrix) fn simd_detect() -> usize {
    #[cfg(target_arch = "aarch64")]
    {
        use std::arch::is_aarch64_feature_detected;
        const SIMD_VEC_SIZE_NEON: usize = 16;
        if is_aarch64_feature_detected!("neon") {
            return SIMD_VEC_SIZE_NEON;
        }
    }

    return 0;
}
