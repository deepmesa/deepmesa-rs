use crate::matrix::alloc_mem;
use crate::matrix::simd::simd_align;
use crate::matrix::simd::simd_detect;
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
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) fn null() -> ColMajorDataset<T> {
        return ColMajorDataset {
            cm_data: core::ptr::null_mut(),
            col_stride: 0,
            cols: 0,
            rows: 0,
            cm_len: 0,
            col_pad: 0,
            simd_optimized: false,
            is_transpose: false,
        };
    }

    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
    ) -> ColMajorDataset<T> {
        if simd_optimized {
            return ColMajorDataset::simd_optimized(rows, cols);
        } else {
            return ColMajorDataset::standard(rows, cols);
        }
    }

    pub(in crate::matrix) fn standard(rows: usize, cols: usize) -> ColMajorDataset<T> {
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

    pub(in crate::matrix) fn simd_optimized(rows: usize, cols: usize) -> ColMajorDataset<T> {
        unsafe {
            let (simd_vec_size, simd_batch_size) = simd_detect();
            if simd_vec_size == 0 {
                return Self::standard(rows, cols);
            }
            let data: *mut T;

            let col_stride = simd_align::<T>(rows, simd_vec_size, simd_batch_size);
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

    pub(in crate::matrix) fn transpose(&mut self) {
        fn_transpose!(self);
    }

    pub(in crate::matrix) fn is_simd_optimized(&self) -> bool {
        return self.simd_optimized;
    }
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
        write!(f, "[CMD:{}x{}]:", self.cols, self.col_stride)?;
        let precision = f.precision().unwrap_or(1);
        for col in 0..self.cols {
            for row in 0..self.col_stride {
                write!(f, "{:.*?}", precision, unsafe { cmd_get!(self, row, col) })?;
                if row < self.col_stride - 1 {
                    write!(f, ",")?;
                }
            }
            write!(f, ";")?;
        }

        Ok(())
    }
}
