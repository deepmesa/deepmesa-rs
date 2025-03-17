use crate::matrix::macros::bounds_check_col;
use crate::matrix::macros::bounds_check_row;

use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::traits::MatrixElement;

impl<T> MatrixColMajor<T>
where
    T: MatrixElement,
{
    pub fn set(&mut self, row: usize, col: usize, val: T) {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
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
