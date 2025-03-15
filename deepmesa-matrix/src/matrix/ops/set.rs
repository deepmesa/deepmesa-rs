use crate::matrix::macros::*;
use crate::matrix::matrix::{Matrix, MatrixData};
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::traits::{MatrixElement, Set};
impl<T> Set<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        bounds_check_col!(col, self);
        bounds_check_row!(row, self);
        dispatch_mut!(self, ds, ds.set(row, col, val));

        // match &mut self.data {
        //     MatrixData::ColMajor(ds) => ds.set(row, col, val),
        //     MatrixData::RowMajor(ds) => ds.set(row, col, val),
        //     MatrixData::DualIndex(ds) => ds.set(row, col, val),
        // }
    }
}
