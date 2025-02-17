use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        if self.is_transpose {
            unsafe {
                return rmd_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return rmd_get!(self, row, col);
            }
        }
    }
}
