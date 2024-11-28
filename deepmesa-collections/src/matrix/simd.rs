//cross platform simd functions for matrix

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(crate) mod neon;

use crate::matrix::matrix::Matrix;
use crate::matrix::traits::MatrixElement;
extern crate alloc;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;
use core::mem;
use std::alloc::dealloc;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
use crate::matrix::simd::neon::SimdNeonKernel;

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

pub trait SimdOperation {
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe fn mul_assign(ptr: *const Self, len: usize, val: Self);
}

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

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(super) const SIMD_NEON_VEC_SIZE_BYTES: usize = 16;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(super) const SIMD_NEON_LOAD_SIZE_4: usize = 4;

pub(in crate::matrix) struct SimdVecBuffer<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix::simd) buf: *mut T,
    pub(in crate::matrix::simd) len: usize,
    pub(in crate::matrix::simd) lanes: usize,
}

impl<T> SimdVecBuffer<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix::simd) fn new(len: usize) -> SimdVecBuffer<T> {
        let layout = Layout::array::<T>(len).unwrap();
        unsafe {
            let data = alloc_zeroed(layout) as *mut T;
            SimdVecBuffer {
                len,
                buf: data as *mut T,
                lanes: 0,
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    pub(in crate::matrix::simd) fn neon_vec() -> SimdVecBuffer<T> {
        return Self::new(SIMD_NEON_VEC_SIZE_BYTES / size_of::<T>());
    }

    pub(in crate::matrix::simd) fn load(&mut self, ptr: *const T, ptr_len: usize) {
        debug_assert!(ptr_len < self.len);
        self.lanes = ptr_len;
        for idx in 0..self.lanes {
            unsafe {
                *(self.buf.add(idx)) = *(ptr.add(idx));
            }
        }
    }

    pub(in crate::matrix::simd) fn store(&self, ptr: *mut T) {
        for idx in 0..self.lanes {
            unsafe {
                *(ptr.add(idx)) = *(self.buf.add(idx));
            }
        }
    }
}

impl<T> Drop for SimdVecBuffer<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.len).unwrap();
        unsafe { dealloc(self.buf as *mut u8, layout) }
    }
}

#[derive(Debug)]
pub struct SimdMetaData {
    pub(super) vec_sz: usize,
    pub(super) bat_sz: usize,
    pub(super) pvec_sz: usize,
    pub(super) bat_f: usize,
    pub(super) pbat_sz: usize,
}

impl SimdMetaData {
    pub(super) fn new<T>(len: usize, vec_sz: usize, bat_sz: usize) -> SimdMetaData {
        let vec_f = len / vec_sz;
        let pvec_sz = len % vec_sz;
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
    pub(in crate::matrix::simd) fn simd_neon<T>(len: usize) -> SimdMetaData {
        let elem_size = size_of::<T>();
        let vec_sz = SIMD_NEON_VEC_SIZE_BYTES / elem_size;
        let bat_sz = SIMD_NEON_LOAD_SIZE_4;
        return Self::new::<T>(len, vec_sz, bat_sz);
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixType;
    #[test]
    fn test_scale_row_simd() {
        let rows = 2;
        let cols = 6;
        let mut m: Matrix<u8> = Matrix::new(rows, cols, MatrixType::DualIndex, true);
        m.fill(3);
        m.set_simd_enabled(true);
        assert_eq!(m.simd_enabled, true);
        println!("Before Transpose");
        println!("Before Scale: {:?}", m);
        m.scale_row(1, 3);
        println!("After Scale: {:?}", m);
        m.transpose();
        println!("After Transpose");
        println!("Before Scale: {:?}", m);
        m.transpose();
        println!("Transposing Again:");
        println!("Before Scale: {:?}", m);
        // m.scale_row(1, 2);
        // println!("After Scale: {:?}", m);
    }
}
