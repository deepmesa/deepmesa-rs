pub(in crate::matrix) mod metadata;
pub(in crate::matrix) mod traits;
pub(in crate::matrix) mod vecbuf;

use core::mem;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix) mod neon;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(super) const SIMD_NEON_VEC_SIZE_BYTES: usize = 16;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(super) const SIMD_NEON_LOAD_SIZE_4: usize = 4;

pub(in crate::matrix) fn simd_align<T>(
    stride: usize,
    simd_vec_size: usize,
    simd_batch_size: usize,
) -> usize {
    //lanes per vector
    let lanes = simd_vec_size / mem::size_of::<T>();
    let elem_per_vec = lanes;
    let vec_ct = (stride as f32 / lanes as f32).ceil() as usize;

    // let rem = stride % lanes;
    println!(
        "Elem Size: {:?}, vec_ct={:?}, lanes={:?}",
        mem::size_of::<T>(),
        vec_ct,
        lanes
    );
    return vec_ct * elem_per_vec;
    //    return stride + vec_ct + (lanes - rem);
    // if rem == 0 {
    //     return stride;
    // }
    //    return stride + (lanes - rem);
}

//OLD Code
// pub(crate) fn simd_align<T>(stride: usize, simd_vec_size: usize, simd_batch_size: usize) -> usize {
//     println!("Stride: {:?}", stride);
//     let lanes = (simd_vec_size / mem::size_of::<T>()); // * simd_batch_size;
//     let rem = stride % lanes;
//     if rem == 0 {
//         return stride;
//     }
//     return stride + (lanes - rem);
// }

pub(in crate::matrix) fn simd_detect() -> (usize, usize) {
    #[cfg(target_arch = "aarch64")]
    {
        use std::arch::is_aarch64_feature_detected;
        const SIMD_VEC_SIZE_NEON: usize = 16;
        const SIMD_BATCH_SIZE_NEON: usize = 4;
        if is_aarch64_feature_detected!("neon") {
            return (SIMD_VEC_SIZE_NEON, SIMD_BATCH_SIZE_NEON);
        }
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        use std::arch::is_x86_feature_detected;
        const SIMD_VEC_SIZE_AVX2: usize = 0;
        const SIMD_BATCH_SIZE_AVX2: usize = 0;

        //TODO: check specific features and return the correct
        // SIMD sizes
        return (SIMD_VEC_SIZE_AVX2, SIMD_BATCH_SIZE_AVX2);
    }

    return (0, 0);
}
