use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

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
    pub(in crate::matrix) fn null() -> DualIndexDataset<T> {
        return DualIndexDataset {
            rmd: RowMajorDataset::null(),
            cmd: ColMajorDataset::null(),
            rows: 0,
            cols: 0,
            is_transpose: false,
        };
    }

    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
    ) -> DualIndexDataset<T> {
        if simd_optimized {
            return DualIndexDataset {
                rmd: RowMajorDataset::simd_optimized(rows, cols),
                cmd: ColMajorDataset::simd_optimized(rows, cols),
                rows,
                cols,
                is_transpose: false,
            };
        } else {
            return DualIndexDataset {
                rmd: RowMajorDataset::standard(rows, cols),
                cmd: ColMajorDataset::standard(rows, cols),
                rows,
                cols,
                is_transpose: false,
            };
        }
    }

    pub(in crate::matrix) fn transpose(&mut self) {
        fn_transpose!(self);
        self.rmd.transpose();
        self.cmd.transpose();
    }

    pub(in crate::matrix) fn is_simd_optimized(&self) -> bool {
        return self.rmd.simd_optimized;
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
    fn get(&self, row: usize, col: usize) -> T {
        if self.is_transpose {
            unsafe {
                return rmd_get_t!(self.rmd, row, col);
            }
        } else {
            unsafe {
                return rmd_get!(self.rmd, row, col);
            }
        }
    }
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
