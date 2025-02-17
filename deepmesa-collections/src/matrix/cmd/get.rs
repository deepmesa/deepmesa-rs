use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        match self.is_transpose {
            true => unsafe {
                return cmd_get_t!(self, row, col);
            },
            false => unsafe {
                return cmd_get!(self, row, col);
            },
        }
    }
}
