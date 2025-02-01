pub(in crate::matrix) trait SimdPtrAddAssign<T = Self> {
    unsafe fn ptr_add_assign(ptr: *const T, len: usize, val: T);
}

pub(in crate::matrix) trait SimdPtrAddInto<T = Self> {
    unsafe fn ptr_add_into(ptr: *const T, dst: *const T, len: usize, val: T);
}
