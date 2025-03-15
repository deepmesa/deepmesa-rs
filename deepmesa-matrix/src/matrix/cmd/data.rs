use crate::matrix::alloc_mem;
use crate::matrix::cmd::macros::*;
use crate::matrix::macros::*;
use crate::matrix::simd::simd_align;
use crate::matrix::simd::simd_detect;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
extern crate alloc;
use alloc::alloc::Layout;
use std::alloc::dealloc;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

pub(in crate::matrix) struct ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) cm_data: *mut T,
    // Number of rows in the Matrix
    pub(in crate::matrix) col_stride: usize,
    // Number of cols in the matrix
    pub(in crate::matrix) cols: usize,
    pub(in crate::matrix) rows: usize,
    pub(in crate::matrix) cm_len: usize,
    pub(in crate::matrix) col_pad: usize,
    pub(in crate::matrix) simd_optimized: bool,
    pub(in crate::matrix) is_transpose: bool,
    pub(in crate::matrix) simd_enabled: bool,
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
        simd_enabled: bool,
    ) -> ColMajorDataset<T> {
        if simd_optimized {
            return ColMajorDataset::simd_optimized(rows, cols, simd_enabled);
        } else {
            return ColMajorDataset::standard(rows, cols, simd_enabled);
        }
    }

    pub(in crate::matrix) fn from(dataset: &ColMajorDataset<T>) -> ColMajorDataset<T> {
        return ColMajorDataset::new(
            dataset.rows,
            dataset.cols,
            dataset.simd_optimized,
            dataset.simd_enabled,
        );
    }

    pub(in crate::matrix) fn standard(
        rows: usize,
        cols: usize,
        simd_enabled: bool,
    ) -> ColMajorDataset<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let ds = ColMajorDataset {
            cm_data: data,
            col_stride: rows,
            cols,
            rows,
            cm_len: len,
            col_pad: 0,
            simd_optimized: false,
            is_transpose: false,
            simd_enabled,
        };

        debug_assert!(ds.col_stride > 0);
        debug_assert!(!ds.cm_data.is_null());
        debug_assert!(ds.col_stride == rows);
        debug_assert!(ds.col_stride == rows + ds.col_pad);
        debug_assert!(cols * ds.col_stride == (rows + ds.col_pad) * cols);
        debug_assert!(ds.cm_len == (rows + ds.col_pad) * cols);
        debug_assert!(ds.cm_len == cols * ds.col_stride);

        return ds;
    }

    pub(in crate::matrix) fn simd_optimized(
        rows: usize,
        cols: usize,
        simd_enabled: bool,
    ) -> ColMajorDataset<T> {
        unsafe {
            let simd_vec_size = simd_detect();
            if simd_vec_size == 0 {
                return Self::standard(rows, cols, simd_enabled);
            }
            let data: *mut T;

            let col_stride = simd_align::<T>(rows, simd_vec_size);
            let cm_len = cols * col_stride;
            let col_pad = col_stride - rows;
            data = alloc_mem::<T>(cm_len);

            let ds = ColMajorDataset {
                cm_data: data,
                cols,
                rows,
                col_stride,
                cm_len,
                col_pad,
                simd_optimized: true,
                is_transpose: false,
                simd_enabled,
            };
            debug_assert!(ds.col_stride > 0);
            debug_assert!(!ds.cm_data.is_null());
            debug_assert!(ds.col_stride == rows + ds.col_pad);
            debug_assert!(cols * ds.col_stride == (rows + ds.col_pad) * cols);
            debug_assert!(ds.cm_len == (rows + ds.col_pad) * cols);
            debug_assert!(ds.cm_len == cols * ds.col_stride);

            return ds;
        }
    }

    pub(in crate::matrix) fn is_col_major(&self) -> bool {
        return true;
    }

    pub(in crate::matrix) fn set_simd_enabled(&mut self, simd_enabled: bool) {
        self.simd_enabled = simd_enabled;
    }

    pub(in crate::matrix) fn transpose(&mut self) {
        fn_transpose!(self);
    }

    pub(in crate::matrix) fn is_simd_optimized(&self) -> bool {
        return self.simd_optimized;
    }
}

impl<T> Dataset<T> for ColMajorDataset<T>
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
        return self.cm_len;
    }

    #[inline(always)]
    fn data_ptr(&self) -> *const T {
        return self.cm_data;
    }

    #[inline(always)]
    fn is_simd_enabled(&self) -> bool {
        return self.simd_enabled;
    }

    // #[inline(always)]
    // fn get(&self, row: usize, col: usize) -> T {
    //     if self.is_transpose {
    //         unsafe {
    //             return cmd_get_t!(self, row, col);
    //         }
    //     } else {
    //         unsafe {
    //             return cmd_get!(self, row, col);
    //         }
    //     }
    // }
}

impl<T> Drop for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.cm_len).unwrap();
        unsafe { dealloc(self.cm_data as *mut u8, layout) }
    }
}

impl<T> Debug for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let limit: usize;
        if self.is_transpose {
            limit = self.rows;
            write!(f, "[CMD:{}x{}]:", self.rows, self.col_stride)?;
        } else {
            limit = self.cols;
            write!(f, "[CMD:{}x{}]:", self.cols, self.col_stride)?;
        }

        let precision = f.precision().unwrap_or(1);
        for col in 0..limit {
            for row in 0..self.col_stride {
                write!(f, "{:.*?}", precision, unsafe { cmd_get!(self, row, col) })?;
                if row < self.col_stride - 1 {
                    write!(f, ",")?;
                }
            }
            if col < limit - 1 {
                write!(f, ";")?;
            }
        }

        Ok(())
    }
}
