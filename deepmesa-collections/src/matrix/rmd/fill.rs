use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for RowMajorDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {}
}
