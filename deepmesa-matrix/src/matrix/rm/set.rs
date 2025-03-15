use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        match self.is_transpose {
            true => unsafe {
                rm_assign_t!(self, row, col, val);
            },
            false => unsafe {
                rm_assign!(self, row, col, val);
            },
        }
    }
}
