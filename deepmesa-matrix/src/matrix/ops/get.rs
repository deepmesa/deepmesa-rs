use crate::matrix::macros::*;
use crate::matrix::matrix::{Matrix, MatrixData};
use crate::matrix::ops::macros::dispatch;
use crate::matrix::traits::{Get, MatrixElement};

impl<T> Get<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn get(&self, row: usize, col: usize) -> T {
        bounds_check_col!(col, self);
        bounds_check_row!(row, self);
        dispatch!(self, ds, return ds.get(row, col));
        // match &self.data {
        //     MatrixData::ColMajor(ds) => return ds.get(row, col),
        //     MatrixData::RowMajor(ds) => return ds.get(row, col),
        //     MatrixData::DualIndex(ds) => return ds.get(row, col),
        // }
    }
}
