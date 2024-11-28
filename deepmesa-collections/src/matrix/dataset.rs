#![allow(unused_variables)]
#![allow(dead_code)]

use std::alloc::dealloc;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
extern crate alloc;
use crate::matrix::simd::simd_align;
use crate::matrix::simd::simd_detect;
use crate::matrix::traits::MatrixElement;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;

pub(super) struct RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) rm_data: *mut T,
    // Number of cols in the matrix
    pub(super) row_stride: usize,
    // Number of rows in the Matrix
    pub(super) rows: usize,
    pub(super) rm_len: usize,
    pub(super) row_pad: usize,
    pub(super) simd_optimized: bool,
}

pub(super) struct ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) cm_data: *mut T,
    // Number of rows in the Matrix
    pub(super) col_stride: usize,
    // Number of cols in the matrix
    pub(super) cols: usize,
    pub(super) cm_len: usize,
    pub(super) col_pad: usize,
    pub(super) simd_optimized: bool,
}

// pub(super) struct MatrixDataset<T>
// where
//     T: MatrixElement,
// {
//     pub(super) cmd: *mut ColMajorDataset<T>,
//     pub(super) rmd: *mut RowMajorDataset<T>,
// }

// impl<T> MatrixDataset<T>
// where
//     T: MatrixElement,
// {
//     fn fill_diagonal(&mut self, transpose: bool) {}
// }

unsafe fn alloc_mem<T: MatrixElement>(len: usize) -> *mut T {
    let layout = Layout::array::<T>(len).unwrap();
    let data = alloc_zeroed(layout) as *mut T;
    return data;
}

impl<T> RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) fn null() -> RowMajorDataset<T> {
        return RowMajorDataset {
            rm_data: core::ptr::null_mut(),
            rows: 0,
            row_stride: 0,
            rm_len: 0,
            row_pad: 0,
            simd_optimized: false,
        };
    }

    pub(super) fn new(rows: usize, cols: usize, simd_optimized: bool) -> RowMajorDataset<T> {
        if simd_optimized {
            return RowMajorDataset::simd_optimized(rows, cols);
        } else {
            return RowMajorDataset::standard(rows, cols);
        }
    }

    pub(super) fn standard(rows: usize, cols: usize) -> RowMajorDataset<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let ds = RowMajorDataset {
            rm_data: data,
            rows,
            row_stride: cols,
            rm_len: len,
            row_pad: 0,
            simd_optimized: false,
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

    pub(super) fn simd_optimized(rows: usize, cols: usize) -> RowMajorDataset<T> {
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
                row_stride,
                rm_len,
                row_pad,
                simd_optimized: true,
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

    pub(super) fn is_simd_optimized(&self) -> bool {
        return self.simd_optimized;
    }
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) fn null() -> ColMajorDataset<T> {
        return ColMajorDataset {
            cm_data: core::ptr::null_mut(),
            col_stride: 0,
            cols: 0,
            cm_len: 0,
            col_pad: 0,
            simd_optimized: false,
        };
    }

    pub(super) fn new(rows: usize, cols: usize, simd_optimized: bool) -> ColMajorDataset<T> {
        if simd_optimized {
            return ColMajorDataset::simd_optimized(rows, cols);
        } else {
            return ColMajorDataset::standard(rows, cols);
        }
    }

    pub(super) fn standard(rows: usize, cols: usize) -> ColMajorDataset<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let ds = ColMajorDataset {
            cm_data: data,
            col_stride: rows,
            cols,
            cm_len: len,
            col_pad: 0,
            simd_optimized: false,
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

    pub(super) fn simd_optimized(rows: usize, cols: usize) -> ColMajorDataset<T> {
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
                col_stride,
                cm_len,
                col_pad,
                simd_optimized: true,
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

    pub(super) fn is_simd_optimized(&self) -> bool {
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

impl<T> Drop for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.cm_len).unwrap();
        unsafe { dealloc(self.cm_data as *mut u8, layout) }
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

#[cfg(test)]
mod tests {
    use super::RowMajorDataset;

    #[test]
    fn test_rm_index() {
        let rows = 2;
        let cols = 3;
        let rm_ds: RowMajorDataset<u64> = RowMajorDataset::new(rows, cols, false);
        let mut val = 0;
        for row in 0..rows {
            for col in 0..cols {
                unsafe { rmd_assign!(rm_ds, row, col, val) }
                val += 1;
            }
        }

        assert_eq!(format!("{:?}", rm_ds), "[RMD:2x3]:0,1,2;3,4,5;");
    }
}
