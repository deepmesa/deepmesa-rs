use crate::matrix::macros::bounds_check_col;
use crate::matrix::macros::bounds_check_row;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                rm_assign_t!(self, row, col, val);
            }
        } else {
            unsafe {
                rm_assign!(self, row, col, val);
            }
        }
    }
}
