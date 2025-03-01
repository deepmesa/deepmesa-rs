pub(in crate::matrix) trait SimdAddAssign<T, Rhs = T> {
    unsafe fn simd_add_assign(ptr: *mut T, val: Rhs, len: usize);
}

pub(in crate::matrix) trait SimdMulAssign<T, Rhs = T> {
    unsafe fn simd_mul_assign(ptr: *mut T, val: Rhs, len: usize);
}

pub(in crate::matrix) trait SimdSubAssign<T, Rhs = T> {
    unsafe fn simd_sub_assign(ptr: *mut T, val: Rhs, len: usize);
}

pub(in crate::matrix) trait SimdAddInto<T, Rhs = T> {
    unsafe fn simd_add_into(ptr: *const T, val: Rhs, dst: *mut T, len: usize);
}

pub(in crate::matrix) trait SimdSubInto<T, Rhs = T> {
    unsafe fn simd_sub_into(ptr: *const T, val: Rhs, dst: *mut T, len: usize);
}

pub(in crate::matrix) trait SimdMulInto<T, Rhs = T> {
    unsafe fn simd_mul_into(ptr: *const T, val: Rhs, dst: *mut T, len: usize);
}
