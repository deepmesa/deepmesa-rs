pub(in crate::matrix) mod cm;
pub(in crate::matrix) mod cmd;
pub(in crate::matrix) mod did;
pub(in crate::matrix) mod macros;
pub(in crate::matrix) mod rm;
pub(in crate::matrix) mod rmd;
pub mod simd;

pub mod iter;
pub mod matmul;
pub mod matrix;
pub mod ops;
pub mod traits;
pub mod vector;

extern crate alloc;
use crate::matrix::traits::MatrixElement;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;
use cmd::data::ColMajorDataset;
use rmd::data::RowMajorDataset;
use std::marker::PhantomData;

unsafe fn alloc_mem<T: MatrixElement>(len: usize) -> *mut T {
    let layout = Layout::array::<T>(len).unwrap();
    let data = alloc_zeroed(layout) as *mut T;
    return data;
}
