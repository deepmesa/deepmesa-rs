#[macro_use]
pub(in crate::matrix) mod macros;
pub(in crate::matrix) mod cmd;
pub(in crate::matrix) mod did;
pub(in crate::matrix) mod rmd;
pub(in crate::matrix) mod simd;
#[cfg(test)]
pub(in crate::matrix) mod tests;

pub mod iter;
pub mod matmul;
pub mod matops;
pub mod matrix;
pub mod traits;
pub mod vector;

extern crate alloc;
use crate::matrix::traits::MatrixElement;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;

unsafe fn alloc_mem<T: MatrixElement>(len: usize) -> *mut T {
    let layout = Layout::array::<T>(len).unwrap();
    let data = alloc_zeroed(layout) as *mut T;
    return data;
}
