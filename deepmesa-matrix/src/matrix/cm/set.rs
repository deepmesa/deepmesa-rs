use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        if self.is_transpose {
            unsafe {
                cm_assign_t!(self, row, col, val);
            }
        } else {
            unsafe {
                cm_assign!(self, row, col, val);
            }
        }
    }
}
