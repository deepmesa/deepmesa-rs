use crate::matrix::simd::traits::SimdPtrAddAssign;
use crate::matrix::simd::traits::SimdPtrAddInto;
use crate::matrix::traits::MatrixElement;
use std::marker::PhantomData;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
use crate::matrix::simd::neon::SimdKernelNeon;

pub struct SimdKernel<T>
where
    T: MatrixElement,
{
    _p: PhantomData<T>,
}

impl<T> SimdPtrAddAssign<T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn ptr_add_assign(ptr: *const T, len: usize, val: T) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::ptr_add_assign(ptr, len, val);
    }
}

impl<T> SimdPtrAddInto<T> for SimdKernel<T>
where
    T: MatrixElement,
{
    unsafe fn ptr_add_into(ptr: *const T, dst: *const T, len: usize, val: T) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        SimdKernelNeon::ptr_add_into(ptr, dst, len, val);
    }
}
