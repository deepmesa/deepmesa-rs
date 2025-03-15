use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::*;
use crate::matrix::matrix::MatrixDimension;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                cm_assign_t!(self, row, col, val);
            });
        } else {
            iterate_cols!(self, col, unsafe {
                cm_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> FillRow<&[T]> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, d: &[T]) {
        debug_assert_eq!(self.cols, d.len());
        if self.is_transpose {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                cm_assign_t!(self, row, col, val);
                idx += 1;
            });
        } else {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                cm_assign!(self, row, col, val);
                idx += 1;
            });
        }
    }
}

impl<T> FillRow<&Vec<T>> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, vec: &Vec<T>) {
        self.fill_row(row, &vec[..]);
    }
}

impl<T> FillRow<(&MatrixColMajor<T>, MatrixDimension)> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn fill_row(&mut self, row: usize, rhs: (&MatrixColMajor<T>, MatrixDimension)) {
        match rhs.1 {
            MatrixDimension::Row(rhs_row) => {
                self.fill_row_cm_row(row, rhs.0, rhs_row);
            }
            MatrixDimension::Col(rhs_col) => {
                self.fill_row_cm_col(row, rhs.0, rhs_col);
            }
        }
    }
}

impl<T> MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn fill_row_cm_row(&mut self, row: usize, rhs: &MatrixColMajor<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign_t!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign_t!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        }
    }

    fn fill_row_cm_col(&mut self, row: usize, rhs: &MatrixColMajor<T>, rhs_col: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign_t!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign_t!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cm_assign!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        }
    }
}
