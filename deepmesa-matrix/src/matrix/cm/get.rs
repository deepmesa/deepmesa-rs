use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < self.rows);
        debug_assert!(col < self.cols);
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
