use super::data::ColMajorDataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        match self.is_transpose {
            true => unsafe {
                cmd_assign_t!(self, row, col, val);
            },
            false => unsafe {
                cmd_assign!(self, row, col, val);
            },
        }
    }
}
