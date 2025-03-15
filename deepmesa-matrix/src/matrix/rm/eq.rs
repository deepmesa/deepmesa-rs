use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq<MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &MatrixRowMajor<T>) -> bool {
        if self.rows != other.rows {
            return false;
        }

        if self.cols != other.cols {
            return false;
        }

        if self.is_transpose {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if rm_get_t!(self, row, col) != rm_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if rm_get_t!(self, row, col) != rm_get!(other, row, col) {
                        return false;
                    }
                });
            }
        } else {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if rm_get!(self, row, col) != rm_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if rm_get!(self, row, col) != rm_get!(other, row, col) {
                        return false;
                    }
                });
            }
        }
        return true;
    }
}
