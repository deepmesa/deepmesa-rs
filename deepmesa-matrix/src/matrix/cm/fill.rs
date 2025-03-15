use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::*;
use crate::matrix::traits::FillColumn;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        bounds_check_row!(row, self);
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
        bounds_check_row!(row, self);
        if self.cols != d.len() {
            panic!("Slice len {} should equal cols {}", d.len(), self.cols);
        }
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
        bounds_check_row!(row, self);
        if self.cols != vec.len() {
            panic!("Vector len {} should equal cols {}", vec.len(), self.cols);
        }

        self.fill_row(row, &vec[..]);
    }
}

impl<T> FillColumn<T> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, col: usize, val: T) {
        bounds_check_col!(col, self);
        if self.is_transpose {
            iterate_rows!(self, row, unsafe {
                cm_assign_t!(self, row, col, val);
            });
        } else {
            iterate_rows!(self, row, unsafe {
                cm_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> FillColumn<&[T]> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, col: usize, d: &[T]) {
        bounds_check_col!(col, self);
        if self.rows != d.len() {
            panic!("slice len {} should equal rows {}", d.len(), self.rows);
        }
        if self.is_transpose {
            let mut idx = 0;
            iterate_rows!(self, row, unsafe {
                let val = d[idx];
                cm_assign_t!(self, row, col, val);
                idx += 1;
            });
        } else {
            let mut idx = 0;
            iterate_rows!(self, row, unsafe {
                let val = d[idx];
                cm_assign!(self, row, col, val);
                idx += 1;
            });
        }
    }
}

impl<T> FillColumn<&Vec<T>> for MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, col: usize, vec: &Vec<T>) {
        bounds_check_col!(col, self);
        if self.rows != vec.len() {
            panic!("Vector len {} should equal rows {}", vec.len(), self.rows);
        }
        self.fill_column(col, &vec[..]);
    }
}

// impl<T> FillRow<(&MatrixColMajor<T>, MatrixDimension)> for MatrixColMajor<T>
// where
//     T: MatrixElement,
// {
//     fn fill_row(&mut self, row: usize, rhs: (&MatrixColMajor<T>, MatrixDimension)) {
//         match rhs.1 {
//             MatrixDimension::Row(rhs_row) => {
//                 self.fill_row_cm_row(row, rhs.0, rhs_row);
//             }
//             MatrixDimension::Col(rhs_col) => {
//                 self.fill_row_cm_col(row, rhs.0, rhs_col);
//             }
//         }
//     }
// }

// impl<T> MatrixColMajor<T>
// where
//     T: MatrixElement,
// {
//     fn fill_row_cm_row(&mut self, row: usize, rhs: &MatrixColMajor<T>, rhs_row: usize) {
//         if self.is_transpose {
//             if rhs.is_transpose {
//                 let mut rhs_col = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign_t!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
//                     rhs_col += 1;
//                 });
//             } else {
//                 let mut rhs_col = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign_t!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
//                     rhs_col += 1;
//                 });
//             }
//         } else {
//             if rhs.is_transpose {
//                 let mut rhs_col = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
//                     rhs_col += 1;
//                 });
//             } else {
//                 let mut rhs_col = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
//                     rhs_col += 1;
//                 });
//             }
//         }
//     }

//     fn fill_row_cm_col(&mut self, row: usize, rhs: &MatrixColMajor<T>, rhs_col: usize) {
//         if self.is_transpose {
//             if rhs.is_transpose {
//                 let mut rhs_row = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign_t!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
//                     rhs_row += 1;
//                 });
//             } else {
//                 let mut rhs_row = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign_t!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
//                     rhs_row += 1;
//                 });
//             }
//         } else {
//             if rhs.is_transpose {
//                 let mut rhs_row = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign!(self, row, col, cm_get_t!(rhs, rhs_row, rhs_col));
//                     rhs_row += 1;
//                 });
//             } else {
//                 let mut rhs_row = 0;
//                 iterate_cols!(self, col, unsafe {
//                     cm_assign!(self, row, col, cm_get!(rhs, rhs_row, rhs_col));
//                     rhs_row += 1;
//                 });
//             }
//         }
//     }
// }
