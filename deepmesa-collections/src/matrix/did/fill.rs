use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;
use crate::matrix::DatasetColumn;
use crate::matrix::DatasetRow;

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
        // debug_assert_eq!(self.cols, vec.len());
        // if self.is_transpose {
        //     let mut idx = 0;
        //     iterate_cols!(self, col, unsafe {
        //         let val = vec[idx];
        //         rmd_assign_t!(self.rmd, row, col, val);
        //         cmd_assign_t!(self.cmd, row, col, val);
        //         idx += 1;
        //     });
        // } else {
        //     let mut idx = 0;
        //     iterate_cols!(self, col, unsafe {
        //         let val = vec[idx];
        //         rmd_assign!(self.rmd, row, col, val);
        //         cmd_assign!(self.cmd, row, col, val);
        //         idx += 1;
        //     });
        // }
    }
}

impl<'a, D, T> FillRow<&DatasetRow<'a, D, T>> for DualIndexDataset<T>
where
    D: Dataset<T>,
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, dr: &DatasetRow<'a, D, T>) {
        debug_assert_eq!(self.cols, dr.dataset.cols());
        if self.is_transpose {
            let mut ds_col = 0;
            iterate_cols!(self, col, unsafe {
                let val = dr.dataset.get(dr.row, ds_col);
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
                ds_col += 1;
            });
        } else {
            let mut ds_col = 0;
            iterate_cols!(self, col, unsafe {
                let val = dr.dataset.get(dr.row, ds_col);
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
                ds_col += 1;
            });
        }
    }
}

impl<'a, D, T> FillRow<&DatasetColumn<'a, D, T>> for DualIndexDataset<T>
where
    D: Dataset<T>,
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, dc: &DatasetColumn<'a, D, T>) {
        debug_assert_eq!(self.cols, dc.dataset.rows());
        if self.is_transpose {
            let mut ds_row = 0;
            iterate_cols!(self, col, unsafe {
                let val = dc.dataset.get(ds_row, dc.col);
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
                ds_row += 1;
            });
        } else {
            let mut ds_row = 0;
            iterate_cols!(self, col, unsafe {
                let val = dc.dataset.get(ds_row, dc.col);
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
                ds_row += 1;
            });
        }
    }
}
