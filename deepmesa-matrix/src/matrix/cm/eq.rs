use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::*;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq<MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &MatrixColMajor<T>) -> bool {
        if self.rows != other.rows {
            return false;
        }

        if self.cols != other.cols {
            return false;
        }

        if self.is_transpose {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cm_get_t!(self, row, col) != cm_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cm_get_t!(self, row, col) != cm_get!(other, row, col) {
                        return false;
                    }
                });
            }
        } else {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cm_get!(self, row, col) != cm_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cm_get!(self, row, col) != cm_get!(other, row, col) {
                        return false;
                    }
                });
            }
        }
        return true;
    }
}
