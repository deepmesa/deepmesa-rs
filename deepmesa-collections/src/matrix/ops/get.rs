use crate::matrix::matrix::{Matrix, MatrixData};
use crate::matrix::traits::{Get, MatrixElement};

macro_rules! m {
    ($self:ident, $ds:ident, $fn:expr) => {
        match &$self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

impl<T> Get<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn get(&self, row: usize, col: usize) -> T {
        bounds_check_col!(col, self);
        bounds_check_row!(row, self);
        m!(self, ds, return ds.get(row, col));
        // match &self.data {
        //     MatrixData::ColMajor(ds) => return ds.get(row, col),
        //     MatrixData::RowMajor(ds) => return ds.get(row, col),
        //     MatrixData::DualIndex(ds) => return ds.get(row, col),
        // }
    }
}
