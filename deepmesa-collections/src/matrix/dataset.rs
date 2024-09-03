#![allow(unused_variables)]
#![allow(dead_code)]

use crate::matrix::simd::simd::*;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
extern crate alloc;
use crate::matrix::traits::MatrixElement;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::Layout;

pub(super) struct RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) rm_data: *mut T,
    pub(super) rows: usize,
    pub(super) row_stride: usize,
    pub(super) rm_len: usize,
    pub(super) row_pad: usize,
    pub(super) simd_enabled: bool,
}

pub(super) struct ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) cm_data: *mut T,
    pub(super) col_stride: usize,
    pub(super) cols: usize,
    pub(super) cm_len: usize,
    pub(super) col_pad: usize,
    pub(super) simd_enabled: bool,
}

unsafe fn alloc_mem<T: MatrixElement>(len: usize) -> *mut T {
    let layout = Layout::array::<T>(len).unwrap();
    let data = alloc_zeroed(layout) as *mut T;
    return data;
}

#[allow(unused_macros)]
macro_rules! rmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iptr {
    ($self:expr, $index:expr) => {
        $self.rm_data.add($index)
    };
}
#[allow(unused_macros)]
macro_rules! cmd_iptr {
    ($self:expr, $index:expr) => {
        $self.cm_data.add($index)
    };
}

#[allow(unused_macros)]
macro_rules! rmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.row_stride + $col
    };
}

#[allow(unused_macros)]
macro_rules! cmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.col_stride + $row
    };
}

#[allow(unused_macros)]
macro_rules! rmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.row_stride + $row
    };
}

#[allow(unused_macros)]
macro_rules! cmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        //Col Major Dataset with Row Major Indexing
        $row * $self.col_stride + $col
    };
}

#[allow(unused_macros)]
macro_rules! rmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.rm_data.add(rmd_index!($self, $row, $col)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index!($self, $row, $col)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.rm_data.add($index) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.rm_data.add($index)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.cm_data.add($index)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.rm_data.add(rmd_index!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.rm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.rm_data.add($index)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index_t!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col)))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iget {
    ($self:expr, $index:expr) => {
        *($self.rm_data.add($index))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *$self.rm_data.add(rmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iget_t {
    ($self:expr, $index:expr) => {
        *$self.rm_data.add($index)
    };
}

#[allow(unused_macros)]
macro_rules! cmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col)))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iget {
    ($self:expr, $index:expr) => {
        *($self.cm_data.add($index))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *$self.cm_data.add(cmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iget_t {
    ($self:expr, $index:expr) => {
        *$self.cm_data.add($index)
    };
}

impl<T> RowMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) fn new(rows: usize, cols: usize) -> RowMajorDataset<T> {
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
            simd_enabled: false,
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
                return Self::new(rows, cols);
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
                simd_enabled: true,
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
}

impl<T> ColMajorDataset<T>
where
    T: MatrixElement,
{
    pub(super) fn new(rows: usize, cols: usize) -> ColMajorDataset<T> {
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
            simd_enabled: false,
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
                return Self::new(rows, cols);
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
                simd_enabled: true,
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

//TODO: Remove or reimplement this hacky trait
trait TransposeDebug {
    fn to_debug_transpose(&self, precision: usize) -> String;
}

impl<T> TransposeDebug for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn to_debug_transpose(&self, precision: usize) -> String {
        let mut str = String::new();
        str.push_str(&format!("[RMDT:{}x{}]:", self.rows, self.row_stride));
        //        let precision = f.precision().unwrap_or(1);
        for col in 0..self.row_stride {
            for row in 0..self.rows {
                str.push_str(&format!("{:.*?}", precision, unsafe {
                    rmd_get!(self, row, col)
                }));
                if row < self.rows - 1 {
                    str.push_str(&format!(","));
                }
            }
            str.push_str(&format!(";"));
        }

        return str;
    }
}

impl<T> TransposeDebug for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn to_debug_transpose(&self, precision: usize) -> String {
        let mut str = String::new();
        str.push_str(&format!("[CMDT:{}x{}]:", self.cols, self.col_stride));
        //        let precision = f.precision().unwrap_or(1);
        for row in 0..self.col_stride {
            for col in 0..self.cols {
                str.push_str(&format!("{:.*?}", precision, unsafe {
                    cmd_get!(self, row, col)
                }));
                if col < self.cols - 1 {
                    str.push_str(&format!(","));
                }
            }
            str.push_str(&format!(";"));
        }

        return str;
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::dataset::TransposeDebug;

    use super::RowMajorDataset;

    #[test]
    fn test_rm_index() {
        let rows = 2;
        let cols = 3;
        let rm_ds: RowMajorDataset<u64> = RowMajorDataset::new(rows, cols);
        let mut val = 0;
        for row in 0..rows {
            for col in 0..cols {
                unsafe { rmd_assign!(rm_ds, row, col, val) }
                val += 1;
            }
        }

        assert_eq!(format!("{:?}", rm_ds), "[RMD:2x3]:0,1,2;3,4,5;");
        assert_eq!(
            format!("{}", rm_ds.to_debug_transpose(1)),
            "[RMDT:2x3]:0,3;1,4;2,5;"
        );
    }
}
