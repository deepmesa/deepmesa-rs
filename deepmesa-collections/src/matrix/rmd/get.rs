use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn get(&mut self, row: usize, col: usize) -> T {
        match self.is_transpose {
            true => unsafe {
                return rmd_get_t!(self, row, col);
            },
            false => unsafe {
                rmd_get!(self, row, col);
            },
        }
    }
}
