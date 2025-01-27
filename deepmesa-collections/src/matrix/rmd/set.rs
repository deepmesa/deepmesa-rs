use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        match self.is_transpose {
            true => unsafe {
                rmd_assign_t!(self, row, col, val);
            },
            false => unsafe {
                rmd_assign!(self, row, col, val);
            },
        }
    }
}
