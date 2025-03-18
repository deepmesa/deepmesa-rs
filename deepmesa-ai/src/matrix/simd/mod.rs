pub(in crate::matrix) mod kernel;
pub(in crate::matrix) mod metadata;
pub(in crate::matrix) mod traits;
pub(in crate::matrix) mod vecbuf;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub mod neon;

pub(in crate::matrix) fn simd_align<T>(stride: usize, simd_vec_size: usize) -> usize {
    //lanes per vector
    let lanes = simd_vec_size / core::mem::size_of::<T>();
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
