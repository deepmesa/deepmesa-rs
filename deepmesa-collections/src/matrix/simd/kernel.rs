use crate::matrix::simd::traits::SimdAddAssign;
use crate::matrix::simd::traits::SimdAddInto;
use crate::matrix::traits::MatrixElement;
use std::marker::PhantomData;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
use crate::matrix::simd::neon::kernel::SimdKernelNeon;

pub struct SimdKernel<T>
where
    T: MatrixElement,
{
    _p: PhantomData<T>,
}

impl<T> SimdAddAssign<T, T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn simd_add_assign(ptr: *mut T, val: T, len: usize) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::simd_add_assign(ptr, val, len);
    }
}

impl<T> SimdAddAssign<T, *const T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn simd_add_assign(ptr: *mut T, val: *const T, len: usize) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::simd_add_assign(ptr, val, len);
    }
}

impl<T> SimdAddInto<T, T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn simd_add_into(ptr: *const T, rhs: T, dst: *mut T, len: usize) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::simd_add_into(ptr, rhs, dst, len);
    }
}

impl<T> SimdAddInto<T, *const T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn simd_add_into(ptr: *const T, rhs: *const T, dst: *mut T, len: usize) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::simd_add_into(ptr, rhs, dst, len);
    }
}
