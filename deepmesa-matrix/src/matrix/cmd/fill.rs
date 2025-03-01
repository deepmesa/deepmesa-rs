use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::matrix::MatrixDimension;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for ColMajorDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                cmd_assign_t!(self, row, col, val);
            });
        } else {
            iterate_cols!(self, col, unsafe {
                cmd_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> FillRow<&[T]> for ColMajorDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, d: &[T]) {
        debug_assert_eq!(self.cols, d.len());
        if self.is_transpose {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                cmd_assign_t!(self, row, col, val);
                idx += 1;
            });
        } else {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                cmd_assign!(self, row, col, val);
                idx += 1;
            });
        }
    }
}

impl<T> FillRow<&Vec<T>> for ColMajorDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, vec: &Vec<T>) {
        self.fill_row(row, &vec[..]);
    }
}

impl<T> FillRow<(&RowMajorDataset<T>, MatrixDimension)> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn fill_row(&mut self, row: usize, rhs: (&RowMajorDataset<T>, MatrixDimension)) {
        match rhs.1 {
            MatrixDimension::Row(rhs_row) => {
                self.fill_row_rmd_row(row, rhs.0, rhs_row);
            }
            MatrixDimension::Col(rhs_col) => {
                self.fill_row_rmd_col(row, rhs.0, rhs_col);
            }
        }
    }
}

impl<T> FillRow<(&ColMajorDataset<T>, MatrixDimension)> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn fill_row(&mut self, row: usize, rhs: (&ColMajorDataset<T>, MatrixDimension)) {
        match rhs.1 {
            MatrixDimension::Row(rhs_row) => {
                self.fill_row_cmd_row(row, rhs.0, rhs_row);
            }
            MatrixDimension::Col(rhs_col) => {
                self.fill_row_cmd_col(row, rhs.0, rhs_col);
            }
        }
    }
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn fill_row_rmd_row(&mut self, row: usize, rhs: &RowMajorDataset<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, rmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, rmd_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, rmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, rmd_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        }
    }

    fn fill_row_rmd_col(&mut self, row: usize, rhs: &RowMajorDataset<T>, rhs_col: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, rmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, rmd_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, rmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, rmd_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        }
    }
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn fill_row_cmd_row(&mut self, row: usize, rhs: &ColMajorDataset<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, cmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, cmd_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, cmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, cmd_get!(rhs, rhs_row, rhs_col));
                    rhs_col += 1;
                });
            }
        }
    }

    fn fill_row_cmd_col(&mut self, row: usize, rhs: &ColMajorDataset<T>, rhs_col: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, cmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign_t!(self, row, col, cmd_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, cmd_get_t!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    cmd_assign!(self, row, col, cmd_get!(rhs, rhs_row, rhs_col));
                    rhs_row += 1;
                });
            }
        }
    }
}

// impl<'a, D, T> FillRow<&DatasetRow<'a, D, T>> for ColMajorDataset<T>
// where
//     D: Dataset<T>,
//     T: MatrixElement<Output = T>,
// {
//     fn fill_row(&mut self, row: usize, dr: &DatasetRow<'a, D, T>) {
//         debug_assert_eq!(self.cols, dr.dataset.cols());
//         if self.is_transpose {
//             let mut ds_col = 0;
//             iterate_cols!(self, col, unsafe {
//                 let val = dr.dataset.get(dr.row, ds_col);
//                 cmd_assign_t!(self, row, col, val);
//                 ds_col += 1;
//             });
//         } else {
//             let mut ds_col = 0;
//             iterate_cols!(self, col, unsafe {
//                 let val = dr.dataset.get(dr.row, ds_col);
//                 cmd_assign!(self, row, col, val);
//                 ds_col += 1;
//             });
//         }
//     }
// }

// impl<'a, D, T> FillRow<&DatasetColumn<'a, D, T>> for ColMajorDataset<T>
// where
//     D: Dataset<T>,
//     T: MatrixElement<Output = T>,
// {
//     fn fill_row(&mut self, row: usize, dc: &DatasetColumn<'a, D, T>) {
//         debug_assert_eq!(self.cols, dc.dataset.rows());
//         if self.is_transpose {
//             let mut ds_row = 0;
//             iterate_cols!(self, col, unsafe {
//                 let val = dc.dataset.get(ds_row, dc.col);
//                 cmd_assign_t!(self, row, col, val);
//                 ds_row += 1;
//             });
//         } else {
//             let mut ds_row = 0;
//             iterate_cols!(self, col, unsafe {
//                 let val = dc.dataset.get(ds_row, dc.col);
//                 cmd_assign!(self, row, col, val);
//                 ds_row += 1;
//             });
//         }
//     }
// }
