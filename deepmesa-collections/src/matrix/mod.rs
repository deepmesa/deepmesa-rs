#[macro_use]
pub(in crate::matrix) mod macros;
pub(in crate::matrix) mod cmd;
pub(in crate::matrix) mod did;
pub(in crate::matrix) mod rmd;
pub(in crate::matrix) mod simd;

pub mod iter;
pub mod matmul;
pub mod matrix;
pub mod ops;
pub mod traits;
pub mod vector;

extern crate alloc;
use crate::matrix::traits::Dataset;
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

pub(in crate::matrix) struct DatasetRow<'a, D, T>
where
    D: Dataset<T>,
    T: MatrixElement,
{
    dataset: &'a D,
    row: usize,
    _p: PhantomData<T>,
}

impl<'a, D, T> DatasetRow<'a, D, T>
where
    D: Dataset<T>,
    T: MatrixElement,
{
    fn from_cmd(cmd: &'a ColMajorDataset<T>, row: usize) -> DatasetRow<'a, ColMajorDataset<T>, T> {
        return DatasetRow {
            dataset: cmd,
            row,
            _p: PhantomData,
        };
    }

    fn from_rmd(rmd: &'a RowMajorDataset<T>, row: usize) -> DatasetRow<'a, RowMajorDataset<T>, T> {
        return DatasetRow {
            dataset: rmd,
            row,
            _p: PhantomData,
        };
    }
}

pub(in crate::matrix) struct DatasetColumn<'a, D, T>
where
    D: Dataset<T>,
    T: MatrixElement,
{
    dataset: &'a D,
    col: usize,
    _p: PhantomData<T>,
}

impl<'a, D, T> DatasetColumn<'a, D, T>
where
    D: Dataset<T>,
    T: MatrixElement,
{
    fn from_cmd(
        cmd: &'a ColMajorDataset<T>,
        col: usize,
    ) -> DatasetColumn<'a, ColMajorDataset<T>, T> {
        return DatasetColumn {
            dataset: cmd,
            col,
            _p: PhantomData,
        };
    }

    fn from_rmd(
        rmd: &'a RowMajorDataset<T>,
        col: usize,
    ) -> DatasetColumn<'a, RowMajorDataset<T>, T> {
        return DatasetColumn {
            dataset: rmd,
            col,
            _p: PhantomData,
        };
    }
}
