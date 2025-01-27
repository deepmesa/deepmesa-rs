use crate::matrix::alloc_mem;
use crate::matrix::simd::simd_align;
use crate::matrix::simd::simd_detect;
use crate::matrix::traits::MatrixElement;
use std::alloc::dealloc;
extern crate alloc;
use alloc::alloc::Layout;

use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

pub(in crate::matrix) struct RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) rm_data: *mut T,
    // Number of cols in the matrix
    pub(in crate::matrix) row_stride: usize,
    // Number of rows in the Matrix
    pub(in crate::matrix) rows: usize,
    pub(in crate::matrix) cols: usize,
    pub(in crate::matrix) rm_len: usize,
    pub(in crate::matrix) row_pad: usize,
    pub(in crate::matrix) simd_optimized: bool,
    pub(in crate::matrix) is_transpose: bool,
}

impl<T> RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) fn null() -> RowMajorDataset<T> {
        return RowMajorDataset {
            rm_data: core::ptr::null_mut(),
            rows: 0,
            cols: 0,
            row_stride: 0,
            rm_len: 0,
            row_pad: 0,
            simd_optimized: false,
            is_transpose: false,
        };
    }

    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
    ) -> RowMajorDataset<T> {
        if simd_optimized {
            return RowMajorDataset::simd_optimized(rows, cols);
        } else {
            return RowMajorDataset::standard(rows, cols);
        }
    }

    pub(in crate::matrix) fn standard(rows: usize, cols: usize) -> RowMajorDataset<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let ds = RowMajorDataset {
            rm_data: data,
            rows,
            cols,
            row_stride: cols,
            rm_len: len,
            row_pad: 0,
            simd_optimized: false,
            is_transpose: false,
        };

        debug_assert!(ds.row_stride > 0);
        debug_assert!(!ds.rm_data.is_null());
        debug_assert!(ds.row_stride == cols);
        debug_assert!(ds.row_stride == cols + ds.row_pad);
        debug_assert!(rows * ds.row_stride == (cols + ds.row_pad) * rows);
        debug_assert!(ds.rm_len == (cols + ds.row_pad) * rows);
        debug_assert!(ds.rm_len == rows * ds.row_stride);

        return ds;
    }

    pub(in crate::matrix) fn simd_optimized(rows: usize, cols: usize) -> RowMajorDataset<T> {
        unsafe {
            let (simd_vec_size, simd_batch_size) = simd_detect();
            if simd_vec_size == 0 {
                return Self::standard(rows, cols);
            }

            let data: *mut T;

            let row_stride = simd_align::<T>(cols, simd_vec_size, simd_batch_size);
            let rm_len = rows * row_stride;
            let row_pad = row_stride - cols;
            data = alloc_mem::<T>(rm_len);

            let ds = RowMajorDataset {
                rm_data: data,
                rows,
                cols,
                row_stride,
                rm_len,
                row_pad,
                simd_optimized: true,
                is_transpose: false,
            };
            debug_assert!(ds.row_stride > 0);
            debug_assert!(!ds.rm_data.is_null());
            debug_assert!(ds.row_stride == cols + ds.row_pad);
            debug_assert!(rows * ds.row_stride == (cols + ds.row_pad) * rows);
            debug_assert!(ds.rm_len == (cols + ds.row_pad) * rows);
            debug_assert!(ds.rm_len == rows * ds.row_stride);
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

impl<T> Drop for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.rm_len).unwrap();
        unsafe { dealloc(self.rm_data as *mut u8, layout) }
    }
}

impl<T> Debug for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[RMD:{}x{}]:", self.rows, self.row_stride)?;
        let precision = f.precision().unwrap_or(1);
        for row in 0..self.rows {
            for col in 0..self.row_stride {
                write!(f, "{:.*?}", precision, unsafe { rmd_get!(self, row, col) })?;
                if col < self.row_stride - 1 {
                    write!(f, ",")?;
                }
            }
            write!(f, ";")?;
        }

        Ok(())
    }
}
