use crate::matrix::macros::*;
use crate::matrix::matrix::MatrixDimension;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                rm_assign_t!(self, row, col, val);
            });
        } else {
            iterate_cols!(self, col, unsafe {
                rm_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> FillRow<&[T]> for MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, d: &[T]) {
        debug_assert_eq!(self.cols, d.len());
        if self.is_transpose {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                rm_assign_t!(self, row, col, val);
                idx += 1;
            });
        } else {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                rm_assign!(self, row, col, val);
                idx += 1;
            });
        }
    }
}

impl<T> FillRow<&Vec<T>> for MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, vec: &Vec<T>) {
        self.fill_row(row, &vec[..]);
    }
}

impl<T> FillRow<(&MatrixRowMajor<T>, MatrixDimension)> for MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, rhs: (&MatrixRowMajor<T>, MatrixDimension)) {
        match rhs.1 {
            MatrixDimension::Row(rhs_row) => {
                self.fill_row_rm_row(row, rhs.0, rhs_row);
            }
            MatrixDimension::Col(rhs_col) => {
                self.fill_row_rm_col(row, rhs.0, rhs_col);
            }
        }
    }
}

impl<T> MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn fill_row_rm_row(&mut self, row: usize, rhs: &MatrixRowMajor<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign_t!(self, row, col, rm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign_t!(self, row, col, rm_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign!(self, row, col, rm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign!(self, row, col, rm_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        }
    }

    fn fill_row_rm_col(&mut self, row: usize, rhs: &MatrixRowMajor<T>, rhs_col: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign_t!(self, row, col, rm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign_t!(self, row, col, rm_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign!(self, row, col, rm_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    rm_assign!(self, row, col, rm_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        }
    }
}
