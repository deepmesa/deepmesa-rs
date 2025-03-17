pub(in crate::matrix::rm) mod add;
pub(in crate::matrix::rm) mod addassign;
pub(in crate::matrix::rm) mod addinto;
pub(in crate::matrix::rm) mod eq;
pub(in crate::matrix::rm) mod fill;
pub(in crate::matrix::rm) mod get;
pub(in crate::matrix) mod macros;
pub(in crate::matrix::rm) mod mul;
pub(in crate::matrix::rm) mod mulassign;
pub(in crate::matrix::rm) mod mulinto;
pub(in crate::matrix::rm) mod set;
pub(in crate::matrix::rm) mod sub;
pub(in crate::matrix::rm) mod subassign;
pub(in crate::matrix::rm) mod subinto;

use crate::matrix::alloc_mem;
use crate::matrix::macros::impl_iter;
use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
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

pub(in crate::matrix) struct MatrixRowMajor<T>
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
    pub(in crate::matrix) simd_enabled: bool,
}

impl<T> MatrixRowMajor<T>
where
    T: MatrixElement,
{
    pub fn new(rows: usize, cols: usize, simd_optimized: bool) -> MatrixRowMajor<T> {
        let mut simd_enabled = true;
        if !T::simd_supported() {
            simd_enabled = false;
        }

        if simd_optimized {
            return MatrixRowMajor::simd_optimized(rows, cols, simd_enabled);
        } else {
            return MatrixRowMajor::standard(rows, cols, simd_enabled);
        }
    }

    pub(in crate::matrix::rm) fn from(m: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        return MatrixRowMajor::new(m.rows, m.cols, m.simd_optimized);
    }

    pub(in crate::matrix::rm) fn standard(
        rows: usize,
        cols: usize,
        simd_enabled: bool,
    ) -> MatrixRowMajor<T> {
        let len = rows * cols;
        let data: *mut T;
        unsafe {
            data = alloc_mem::<T>(len);
        }

        let m = MatrixRowMajor {
            rm_data: data,
            rows,
            cols,
            row_stride: cols,
            rm_len: len,
            row_pad: 0,
            simd_optimized: false,
            is_transpose: false,
            simd_enabled,
        };

        debug_assert!(m.row_stride > 0);
        debug_assert!(!m.rm_data.is_null());
        debug_assert!(m.row_stride == cols);
        debug_assert!(m.row_stride == cols + m.row_pad);
        debug_assert!(rows * m.row_stride == (cols + m.row_pad) * rows);
        debug_assert!(m.rm_len == (cols + m.row_pad) * rows);
        debug_assert!(m.rm_len == rows * m.row_stride);

        return m;
    }

    pub(in crate::matrix::rm) fn simd_optimized(
        rows: usize,
        cols: usize,
        simd_enabled: bool,
    ) -> MatrixRowMajor<T> {
        unsafe {
            let simd_vec_size = simd_detect();
            if simd_vec_size == 0 {
                return Self::standard(rows, cols, simd_enabled);
            }

            let data: *mut T;

            let row_stride = simd_align::<T>(cols, simd_vec_size);
            let rm_len = rows * row_stride;
            let row_pad = row_stride - cols;
            data = alloc_mem::<T>(rm_len);

            let m = MatrixRowMajor {
                rm_data: data,
                rows,
                cols,
                row_stride,
                rm_len,
                row_pad,
                simd_optimized: true,
                is_transpose: false,
                simd_enabled,
            };
            debug_assert!(m.row_stride > 0);
            debug_assert!(!m.rm_data.is_null());
            debug_assert!(m.row_stride == cols + m.row_pad);
            debug_assert!(rows * m.row_stride == (cols + m.row_pad) * rows);
            debug_assert!(m.rm_len == (cols + m.row_pad) * rows);
            debug_assert!(m.rm_len == rows * m.row_stride);
            return m;
        }
    }

    pub fn set_simd_enabled(&mut self, simd_enabled: bool) {
        self.simd_enabled = simd_enabled;
    }

    pub fn transpose(&mut self) {
        fn_transpose!(self);
    }

    pub fn is_simd_optimized(&self) -> bool {
        return self.simd_optimized;
    }

    impl_simd_fn!(self);
}

impl<T> MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn iter_rows(&self) -> MatrixRowMajorIterator<T> {
        return MatrixRowMajorIterator::new(self, IterType::IterRows);
    }

    pub fn iter_cols(&self) -> MatrixRowMajorIterator<T> {
        return MatrixRowMajorIterator::new(self, IterType::IterCols);
    }
}

impl<T> Drop for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.rm_len).unwrap();
        unsafe { dealloc(self.rm_data as *mut u8, layout) }
    }
}

impl<T> Debug for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let limit: usize;
        if self.is_transpose {
            limit = self.cols;
            if self.simd_optimized {
                write!(
                    f,
                    "[RM/t:<{}>/{}:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.row_stride,
                    self.rows,
                    self.cols
                )?;
            } else {
                write!(
                    f,
                    "[RM/t:<{}>:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.rows,
                    self.cols
                )?;
            }
        } else {
            limit = self.rows;
            if self.simd_optimized {
                write!(
                    f,
                    "[RM:<{}>/{}:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.row_stride,
                    self.rows,
                    self.cols
                )?;
            } else {
                write!(
                    f,
                    "[RM:<{}>:{}x{}]:",
                    std::any::type_name::<T>(),
                    self.rows,
                    self.cols,
                )?;
            }
        }
        let precision = f.precision().unwrap_or(1);
        for row in 0..limit {
            for col in 0..self.row_stride {
                write!(f, "{:.*?}", precision, unsafe { rm_get!(self, row, col) })?;
                if col < self.row_stride - 1 {
                    write!(f, ",")?;
                }
            }
            if row < limit - 1 {
                write!(f, ";")?;
            }
        }

        Ok(())
    }
}

impl_iter!(MatrixRowMajorIterator, MatrixRowMajor);

#[cfg(test)]
mod tests {
    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::MatrixRowMajor;
    use crate::matrix::traits::*;

    #[test]
    fn test_debug() {
        let mut m = matrix_rm!([u8, 2, 3, false], 1,2,3;4,5,6);
        assert_eq!(format!("{:?}", &m), "[RM:<u8>:2x3]:1,2,3;4,5,6");
        m.transpose();
        assert_eq!(format!("{:?}", &m), "[RM/t:<u8>:3x2]:1,2,3;4,5,6");
        let mut m = matrix_rm!([u8, 2, 3, true], 1,2,3;4,5,6);
        assert_eq!(
            format!("{:?}", &m),
            "[RM:<u8>/16:2x3]:1,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0;4,5,6,0,0,0,0,0,0,0,0,0,0,0,0,0"
        );
        m.transpose();
        assert_eq!(
            format!("{:?}", &m),
            "[RM/t:<u8>/16:3x2]:1,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0;4,5,6,0,0,0,0,0,0,0,0,0,0,0,0,0"
        );
    }

    #[test]
    fn test_iter_rows() {
        let mut m = matrix_rm!([u8, 2, 3, false], 1,2,3;4,5,6);
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
        let mut m = matrix_rm!([u8, 2, 3, false], 1,2,3;4,5,6);
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
