pub(in crate::matrix) trait SimdAddAssign<T, Rhs = T> {
    unsafe fn simd_add_assign(ptr: *mut T, val: Rhs, len: usize);
}

pub(in crate::matrix) trait SimdAddInto<T, Rhs = T> {
    unsafe fn simd_add_into(ptr: *const T, val: Rhs, dst: *mut T, len: usize);
}

// pub(in crate::matrix) trait SimdPtrAddValAssign<T> {
//     unsafe fn ptr_add_val_assign(ptr: *const T, len: usize, val: T);
// }

// pub(in crate::matrix) trait SimdPtrAddPtrAssign<T> {
//     unsafe fn ptr_add_ptr_assign(ptr: *const T, rhs: *const T, len: usize);
// }

// pub(in crate::matrix) trait SimdPtrAddValInto<T> {
//     unsafe fn ptr_add_val_into(ptr: *const T, dst: *const T, len: usize, val: T);
// }
