use crate::matrix::simd::SIMD_NEON_LOAD_SIZE_4;
use crate::matrix::simd::SIMD_NEON_VEC_SIZE_BYTES;

#[derive(Debug)]
pub struct SimdMetaData {
    //Size of a single SIMD Vector
    pub(super) vec_sz: usize,
    //Size of a SIMD batch (numbet of vectors loaded in one simd operation)
    pub(super) bat_sz: usize,
    //Size of a partial vector
    pub(super) pvec_sz: usize,
    //Number of full batches
    pub(super) bat_f: usize,
    //Size of a partial batch
    pub(super) pbat_sz: usize,
}

impl SimdMetaData {
    pub(in crate::matrix) fn new<T>(row_len: usize, vec_sz: usize, bat_sz: usize) -> SimdMetaData {
        let vec_f = row_len / vec_sz;
        let pvec_sz = row_len % vec_sz;
        let bat_f = vec_f / bat_sz;
        let pbat_sz = vec_f % bat_sz;
        debug_assert!(pbat_sz <= 3);

        SimdMetaData {
            vec_sz,
            bat_sz,
            bat_f,
            pvec_sz,
            pbat_sz,
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    pub(in crate::matrix) fn simd_neon<T>(row_len: usize) -> SimdMetaData {
        let elem_size = size_of::<T>();
        let vec_sz = SIMD_NEON_VEC_SIZE_BYTES / elem_size;
        let bat_sz = SIMD_NEON_LOAD_SIZE_4;
        return Self::new::<T>(row_len, vec_sz, bat_sz);
    }
}
