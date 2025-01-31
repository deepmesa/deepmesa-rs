use crate::matrix::simd::SIMD_NEON_VEC_SIZE_BYTES;
use crate::matrix::traits::MatrixElement;

extern crate alloc;
use core::alloc::Layout;
use std::alloc::alloc_zeroed;
use std::alloc::dealloc;

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
