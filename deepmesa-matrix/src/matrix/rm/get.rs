use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for MatrixRowMajor<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < self.rows);
        debug_assert!(col < self.cols);
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
}

#[cfg(test)]
mod tests {
    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;
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
