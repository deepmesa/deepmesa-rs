use crate::matrix::macros::bounds_check_col;
use crate::matrix::macros::bounds_check_row;

use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::traits::MatrixElement;

use std::ops::Index;
use std::ops::IndexMut;

impl<T> MatrixColMajor<T>
where
    T: MatrixElement,
{
    pub fn get(&self, row: usize, col: usize) -> T {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                return cm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return cm_get!(self, row, col);
            }
        }
    }

    pub fn get_mut(&self, row: usize, col: usize) -> &mut T {
        bounds_check_row!(row, self);
        bounds_check_col!(col, self);
        if self.is_transpose {
            unsafe {
                return &mut cm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return &mut cm_get!(self, row, col);
            }
        }
    }
}

impl<T> Index<(usize, usize)> for MatrixColMajor<T>
where
    T: MatrixElement,
{
    type Output = T;
    fn index(&self, (row, col): (usize, usize)) -> &T {
        if self.is_transpose {
            unsafe {
                return &cm_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return &cm_get!(self, row, col);
            }
        }
    }
}

// impl<T> IndexMut<usize> for MatrixColMajor<T>
// where
//     T: MatrixElement,
// {
//     fn index_mut(&mut self, index: usize) -> &mut [T] {
//         let mut idx = 0;
//         if self.is_transpose {
//             idx = cm_index_t!(self, 0, index);
//         } else {
//             idx = cm_index!(self, 0, index);
//         }
//         unsafe {
//             return std::slice::from_raw_parts_mut(self.cm_data.add(idx), self.rows);
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;

    #[test]
    fn test_index() {
        let m = matrix_cm!([u8, 2, 3, false], 3,6;4,7;5,8);
        assert_eq!(m[(0, 0)], 3u8);
        //        assert_eq!(m[0][1], 4u8);
        // assert_eq!(m[0][2], 5u8);
        // assert_eq!(m[1][0], 6u8);
        // assert_eq!(m[1][1], 7u8);
        // assert_eq!(m[1][2], 8u8);
    }

    // #[test]
    // fn test_index_mut() {
    //     let mut m = matrix_rm!([u8, 2, 3, false], 3,4,5;6,7,8);
    //     m[0][0] += 1;
    //     assert_eq!(m[0][0], 4u8);
    //     m[0][1] += 1;
    //     assert_eq!(m[0][1], 5u8);
    //     m[0][2] += 1;
    //     assert_eq!(m[0][2], 6u8);
    //     m[1][0] += 1;
    //     assert_eq!(m[1][0], 7u8);
    //     m[1][1] += 1;
    //     assert_eq!(m[1][1], 8u8);
    //     m[1][2] += 1;
    //     assert_eq!(m[1][2], 9u8);
    // }

    #[test]
    fn test_get() {
        let mut m = matrix_cm!([u8, 2, 3, false], 3,6;4,7;5,8);
        assert_eq!(3, m.get(0, 0));
        assert_eq!(4, m.get(0, 1));
        assert_eq!(5, m.get(0, 2));
        assert_eq!(6, m.get(1, 0));
        assert_eq!(7, m.get(1, 1));
        assert_eq!(8, m.get(1, 2));

        m.transpose();
        assert_eq!(3, m.get(0, 0));
        assert_eq!(6, m.get(0, 1));
        assert_eq!(4, m.get(1, 0));
        assert_eq!(7, m.get(1, 1));
        assert_eq!(5, m.get(2, 0));
        assert_eq!(8, m.get(2, 1));
    }
}
