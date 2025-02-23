use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::matrix::MatrixDimension;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;

impl<T> FillRow<T> for DualIndexDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
            });
        } else {
            iterate_cols!(self, col, unsafe {
                rmd_assign!(self.rmd, row, col, val);
                cmd_assign!(self.cmd, row, col, val);
            });
        }
    }
}

impl<T> FillRow<&[T]> for DualIndexDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, d: &[T]) {
        debug_assert_eq!(self.cols, d.len());
        if self.is_transpose {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
                idx += 1;
            });
        } else {
            let mut idx = 0;
            iterate_cols!(self, col, unsafe {
                let val = d[idx];
                rmd_assign!(self.rmd, row, col, val);
                cmd_assign!(self.cmd, row, col, val);
                idx += 1;
            });
        }
    }
}

impl<T> FillRow<&Vec<T>> for DualIndexDataset<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, vec: &Vec<T>) {
        self.fill_row(row, &vec[..]);
    }
}

impl<T> FillRow<(&RowMajorDataset<T>, MatrixDimension)> for DualIndexDataset<T>
where
    T: MatrixElement<Output = T>,
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

impl<T> FillRow<(&ColMajorDataset<T>, MatrixDimension)> for DualIndexDataset<T>
where
    T: MatrixElement<Output = T>,
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

impl<T> DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn fill_row_rmd_row(&mut self, row: usize, rhs: &RowMajorDataset<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
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
                    let val = rmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = rmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            }
        }
    }
}

impl<T> DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn fill_row_cmd_row(&mut self, row: usize, rhs: &ColMajorDataset<T>, rhs_row: usize) {
        if self.is_transpose {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_col += 1;
                });
            } else {
                let mut rhs_col = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
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
                    let val = cmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            }
        } else {
            if rhs.is_transpose {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get_t!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            } else {
                let mut rhs_row = 0;
                iterate_cols!(self, col, unsafe {
                    let val = cmd_get!(rhs, rhs_row, rhs_col);
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                    rhs_row += 1;
                });
            }
        }
    }
}
