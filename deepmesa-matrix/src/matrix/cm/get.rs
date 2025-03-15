use crate::matrix::macros::bounds_check_col;
use crate::matrix::macros::bounds_check_row;

use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                return cm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return cm_get!(self, row, col);
            }
        }
    }
}
