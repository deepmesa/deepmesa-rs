use crate::matrix::macros::bounds_check_col;
use crate::matrix::macros::bounds_check_row;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use std::ops::Index;
use std::ops::IndexMut;

impl<T> MatrixRowMajor<T>
where
    T: MatrixElement,
{
    pub fn get(&self, row: usize, col: usize) -> T {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                return rm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return rm_get!(self, row, col);
            }
        }
    }

    pub fn get_mut(&self, row: usize, col: usize) -> &mut T {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                return &mut rm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return &mut rm_get!(self, row, col);
            }
        }
    }
}

impl<T> Index<(usize, usize)> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    type Output = T;
    fn index(&self, (row, col): (usize, usize)) -> &T {
        if self.is_transpose {
            unsafe {
                return &rm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return &rm_get!(self, row, col);
            }
        }
    }
}

impl<T> IndexMut<(usize, usize)> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn index_mut(&mut self, (row, col): (usize, usize)) -> &mut T {
        if self.is_transpose {
            unsafe {
                return &mut rm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return &mut rm_get!(self, row, col);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;

    #[test]
    fn test_index() {
        let mut m = matrix_rm!([u8, 2, 3, false], 3,4,5;6,7,8);
        assert_eq!(m[(0, 0)], 3u8);
        assert_eq!(m[(0, 1)], 4u8);
        assert_eq!(m[(0, 2)], 5u8);
        assert_eq!(m[(1, 0)], 6u8);
        assert_eq!(m[(1, 1)], 7u8);
        assert_eq!(m[(1, 2)], 8u8);

        m.transpose();
        assert_eq!(m[(0, 0)], 3u8);
        assert_eq!(m[(0, 1)], 6u8);
    }

    #[test]
    fn test_index_mut() {
        let mut m = matrix_rm!([u8, 2, 3, false], 3,4,5;6,7,8);
        m[(0, 0)] += 1;
        assert_eq!(m[(0, 0)], 4u8);
        m[(0, 1)] += 1;
        assert_eq!(m[(0, 1)], 5u8);
        m[(0, 2)] += 1;
        assert_eq!(m[(0, 2)], 6u8);
        m[(1, 0)] += 1;
        assert_eq!(m[(1, 0)], 7u8);
        m[(1, 1)] += 1;
        assert_eq!(m[(1, 1)], 8u8);
        m[(1, 2)] += 1;
        assert_eq!(m[(1, 2)], 9u8);
    }

    #[test]
    fn test_get() {
        let mut rm = matrix_rm!([u8, 2, 3, false], 3,4,5;6,7,8);
        assert_eq!(3, rm.get(0, 0));
        assert_eq!(4, rm.get(0, 1));
        assert_eq!(5, rm.get(0, 2));
        assert_eq!(6, rm.get(1, 0));
        assert_eq!(7, rm.get(1, 1));
        assert_eq!(8, rm.get(1, 2));

        rm.transpose();
        assert_eq!(3, rm.get(0, 0));
        assert_eq!(6, rm.get(0, 1));
        assert_eq!(4, rm.get(1, 0));
        assert_eq!(7, rm.get(1, 1));
        assert_eq!(5, rm.get(2, 0));
        assert_eq!(8, rm.get(2, 1));
    }
}
