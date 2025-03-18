pub(in crate::matrix) mod macros;
pub(in crate::matrix) mod rm;
pub mod simd;

pub mod traits;
pub mod vector;

extern crate alloc;
use crate::matrix::traits::MatrixElement;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;

pub enum IterType {
    IterRows,
    IterCols,
}

use crate::matrix::rm::MatrixRowMajor;

/*
TODO:
* Iterators

*/

type Matrix<T> = MatrixRowMajor<T>;

unsafe fn alloc_mem<T: MatrixElement>(len: usize) -> *mut T {
    let layout = Layout::array::<T>(len).unwrap();
    let data = alloc_zeroed(layout) as *mut T;
    return data;
}
