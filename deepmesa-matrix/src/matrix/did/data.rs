use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::macros::*;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

#[derive(Debug, Copy, Clone, PartialEq)]
pub(in crate::matrix) enum SyncDirection {
    CmdToRmd,
    RmdToCmd,
}

pub(in crate::matrix) struct DualIndexDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) rmd: RowMajorDataset<T>,
    pub(in crate::matrix) cmd: ColMajorDataset<T>,
    pub(in crate::matrix) is_transpose: bool,
    pub(in crate::matrix) rows: usize,
    pub(in crate::matrix) cols: usize,
}

impl<T> DualIndexDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
        simd_enabled: bool,
    ) -> DualIndexDataset<T> {
        if simd_optimized {
            return DualIndexDataset {
                rmd: RowMajorDataset::simd_optimized(rows, cols, simd_enabled),
                cmd: ColMajorDataset::simd_optimized(rows, cols, simd_enabled),
                rows,
                cols,
                is_transpose: false,
            };
        } else {
            return DualIndexDataset {
                rmd: RowMajorDataset::standard(rows, cols, simd_enabled),
                cmd: ColMajorDataset::standard(rows, cols, simd_enabled),
                rows,
                cols,
                is_transpose: false,
            };
        }
    }

    pub(in crate::matrix) fn from(dataset: &DualIndexDataset<T>) -> DualIndexDataset<T> {
        return DualIndexDataset::new(
            dataset.rows,
            dataset.cols,
            dataset.rmd.simd_optimized,
            dataset.rmd.simd_enabled,
        );
    }

    pub(in crate::matrix) fn set_simd_enabled(&mut self, simd_enabled: bool) {
        self.rmd.set_simd_enabled(simd_enabled);
        self.cmd.set_simd_enabled(simd_enabled);
    }

    pub(in crate::matrix) fn transpose(&mut self) {
        fn_transpose!(self);
        self.rmd.transpose();
        self.cmd.transpose();
    }

    pub(in crate::matrix) fn is_simd_optimized(&self) -> bool {
        return self.rmd.simd_optimized;
    }

    pub(in crate::matrix) fn sync(&mut self, dir: SyncDirection) {
        for row in 0..self.rows {
            self.sync_row(row, dir);
        }
    }

    pub(in crate::matrix) fn sync_row(&mut self, row: usize, dir: SyncDirection) {
        //TODO: Once partial Eq is implemented for &Matrix Type remove
        // this match and replace it with a !=
        if self.is_transpose {
            match dir {
                SyncDirection::CmdToRmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        rmd_assign_t!(self.rmd, row, col, val);
                    })
                }
                SyncDirection::RmdToCmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get_t!(self.rmd, row, col);
                        cmd_assign_t!(self.cmd, row, col, val);
                    })
                }
            }
        } else {
            match dir {
                SyncDirection::CmdToRmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        rmd_assign!(self.rmd, row, col, val);
                    })
                }
                SyncDirection::RmdToCmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get!(self.rmd, row, col);
                        cmd_assign!(self.cmd, row, col, val);
                    })
                }
            }
        }
    }
}

impl<T> Dataset<T> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    #[inline(always)]
    fn rows(&self) -> usize {
        return self.rows;
    }

    #[inline(always)]
    fn cols(&self) -> usize {
        return self.cols;
    }

    #[inline(always)]
    fn len(&self) -> usize {
        return self.rmd.rm_len;
    }

    #[inline(always)]
    fn data_ptr(&self) -> *const T {
        return self.rmd.rm_data;
    }

    #[inline(always)]
    fn is_simd_enabled(&self) -> bool {
        return self.rmd.simd_enabled;
    }

    // #[inline(always)]
    // fn get(&self, row: usize, col: usize) -> T {
    //     if self.is_transpose {
    //         unsafe {
    //             return rmd_get_t!(self.rmd, row, col);
    //         }
    //     } else {
    //         unsafe {
    //             return rmd_get!(self.rmd, row, col);
    //         }
    //     }
    // }
}

impl<T> Debug for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.rmd)?;
        Ok(())
    }
}
