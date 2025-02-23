use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < self.rows);
        debug_assert!(col < self.cols);
        if self.is_transpose {
            unsafe {
                return cmd_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return cmd_get!(self, row, col);
            }
        }
    }
}
