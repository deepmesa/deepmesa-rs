use crate::matrix::traits::MatrixElement;

use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::rmd::data::RowMajorDataset;

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
