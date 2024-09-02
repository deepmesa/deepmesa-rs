//cross platform simd functions for matrix
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::matrix::matrix::Matrix;
use crate::matrix::traits::MatrixElement;
use core::mem;

pub(crate) fn simd_align<T>(stride: usize, simd_vec_size: usize, simd_batch_size: usize) -> usize {
    let lanes = (simd_vec_size / mem::size_of::<T>()) * simd_batch_size;
    let rem = stride % lanes;
    if rem == 0 {
        return stride;
    }
    return stride + (lanes - rem);
}

pub(crate) fn simd_detect() -> (usize, usize) {
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

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn scale_row_simd(&mut self, row: usize, scalar: T) {
        //this method detects the arch and calls the relevant simd method on matrix
        println!("In scale_row_simd");
        //        self.scale_row_simd_neon(row, scalar);
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::matrix::Matrix;
    #[test]
    fn test_scale_row_simd() {
        let row_size = 1024;
        let mut data: Vec<u8> = Vec::with_capacity(row_size);
        for _ in 0..4 {
            //TODO: Remove these magic values
            for i in 0..=u8::MAX {
                data.push(i);
            }
        }
        println!("ROW SRC LEN: {:?}", data.len());
        let mut m: Matrix<u8> = Matrix::from_val(1024, 1024, 0);
        for row_idx in 0..m.cols() {
            m.set_row(row_idx, &data);
        }
        let scalar = 2;
        m.scale_row_simd(3, scalar);
    }
}
