pub(in crate::matrix::cm) mod add;
pub(in crate::matrix::cm) mod addassign;
pub(in crate::matrix::cm) mod addinto;
pub(in crate::matrix::cm) mod eq;
pub(in crate::matrix::cm) mod fill;
pub(in crate::matrix::cm) mod get;
pub(in crate::matrix::cm) mod macros;
pub(in crate::matrix::cm) mod mul;
pub(in crate::matrix::cm) mod mulassign;
pub(in crate::matrix::cm) mod mulinto;
pub(in crate::matrix::cm) mod set;
pub(in crate::matrix::cm) mod sub;
pub(in crate::matrix::cm) mod subassign;
pub(in crate::matrix::cm) mod subinto;

use crate::matrix::alloc_mem;
use crate::matrix::cm::macros::*;
use crate::matrix::macros::*;
use crate::matrix::simd::simd_align;
use crate::matrix::simd::simd_detect;
use crate::matrix::IterType;
use crate::matrix::MatrixElement;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

use std::alloc::dealloc;
extern crate alloc;
use alloc::alloc::Layout;

pub struct MatrixColMajor<T>
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

impl<T> MatrixColMajor<T>
where
    T: MatrixElement,
{
    pub(in crate::matrix) fn new(
        rows: usize,
        cols: usize,
        simd_optimized: bool,
    ) -> MatrixColMajor<T> {
        let mut simd_enabled = true;
        if !T::simd_supported() {
            simd_enabled = false;
        }

        if simd_optimized {
            return MatrixColMajor::simd_optimized(rows, cols, simd_enabled);
        } else {
            return MatrixColMajor::standard(rows, cols, simd_enabled);
        }
    }

    pub(in crate::matrix) fn from(m: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        return MatrixColMajor::new(m.rows, m.cols, m.simd_optimized);
    }

    pub(in crate::matrix) fn standard(
        rows: usize,
        cols: usize,
        simd_enabled: bool,
    ) -> MatrixColMajor<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let ds = MatrixColMajor {
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
    ) -> MatrixColMajor<T> {
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

            let ds = MatrixColMajor {
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

    impl_simd_fn!(self);

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

impl<T> MatrixColMajor<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn iter_rows(&self) -> MatrixColMajorIterator<T> {
        return MatrixColMajorIterator::new(self, IterType::IterRows);
    }

    pub fn iter_cols(&self) -> MatrixColMajorIterator<T> {
        return MatrixColMajorIterator::new(self, IterType::IterCols);
    }
}

impl<T> Drop for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.cm_len).unwrap();
        unsafe { dealloc(self.cm_data as *mut u8, layout) }
    }
}

impl<T> Debug for MatrixColMajor<T>
where
    T: MatrixElement,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let limit: usize;
        if self.is_transpose {
            limit = self.rows;
            if self.simd_optimized {
                write!(
                    f,
                    "[CM/t:<{}>/{}:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.col_stride,
                    self.rows,
                    self.cols
                )?;
            } else {
                write!(
                    f,
                    "[CM/t:<{}>:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.rows,
                    self.cols,
                )?;
            }
        } else {
            limit = self.cols;
            if self.simd_optimized {
                write!(
                    f,
                    "[CM:<{}>/{}:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.col_stride,
                    self.rows,
                    self.cols
                )?;
            } else {
                write!(
                    f,
                    "[CM:<{}>:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.rows,
                    self.cols,
                )?;
            }
        }

        let precision = f.precision().unwrap_or(1);
        for col in 0..limit {
            for row in 0..self.col_stride {
                write!(f, "{:.*?}", precision, unsafe { cm_get!(self, row, col) })?;
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

impl_iter!(MatrixColMajorIterator, MatrixColMajor);

#[cfg(test)]
mod tests {
    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::MatrixColMajor;
    use crate::matrix::traits::*;

    #[test]
    fn test_debug() {
        let mut m = matrix_cm!([u8, 2, 3, false], 1,4;2,5;3,6);
        assert_eq!(format!("{:?}", &m), "[CM:<u8>:2x3]:1,4;2,5;3,6");
        m.transpose();
        assert_eq!(format!("{:?}", &m), "[CM/t:<u8>:3x2]:1,4;2,5;3,6");
        let mut m = matrix_cm!([u8, 2, 3, true], 1,4;2,5;3,6);
        assert_eq!(format!("{:?}", &m), "[CM:<u8>/16:2x3]:1,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0;2,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0;3,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0");
        m.transpose();
        assert_eq!(format!("{:?}", &m), "[CM/t:<u8>/16:3x2]:1,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0;2,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0;3,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0");
    }

    #[test]
    fn test_iter_rows() {
        let mut m = matrix_cm!([u8, 2, 3, false], 1,4;2,5;3,6);
        let mut iter = m.iter_rows();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), None);

        m.transpose();
        let mut iter = m.iter_rows();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_cols() {
        let mut m = matrix_cm!([u8, 2,3, false], 1,4;2,5;3,6);
        let mut iter = m.iter_cols();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), None);

        m.transpose();
        let mut iter = m.iter_cols();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), None);
    }
}
