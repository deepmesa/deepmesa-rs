pub trait SimdOperation {
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe fn mul_assign(ptr: *const Self, len: usize, val: Self);

    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    unsafe fn add_assign(ptr: *const Self, len: usize, val: Self);
}

pub(in crate::matrix) trait SimdAddAssign<Rhs = Self> {
    fn simd_add_assign(&mut self, rhs: Rhs);
}
