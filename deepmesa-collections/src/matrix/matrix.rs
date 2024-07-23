use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;

use crate::matrix::iter::{IterType, MatrixIterator};
use crate::matrix::traits::MatrixElement;

pub struct Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub(crate) rows: usize,
    pub(crate) cols: usize,
    pub(crate) data: Vec<T>,
    pub(crate) is_transpose: bool,
    pub is_square: bool,
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(rows: usize, cols: usize) -> Matrix<T> {
        Matrix {
            rows,
            cols,
            data: Vec::with_capacity(rows * cols),
            is_transpose: false,
            is_square: rows == cols,
        }
    }

    pub fn identity(size: usize) -> Matrix<T> {
        let mut data: Vec<T> = Vec::with_capacity(size * size);

        //iterate over all the rows
        for row in 0..size {
            for col in 0..size {
                if row == col {
                    data.push(T::one());
                } else {
                    data.push(T::zero());
                }
            }
        }

        Matrix {
            rows: size,
            cols: size,
            data,
            is_transpose: false,
            is_square: true,
        }
    }

    pub fn is_square(&self) -> bool {
        self.is_square
    }

    pub fn rows(&self) -> usize {
        if self.is_transpose {
            return self.cols;
        }
        return self.rows;
    }

    pub fn cols(&self) -> usize {
        if self.is_transpose {
            return self.rows;
        }
        return self.cols;
    }

    pub fn col_iter(&self) -> MatrixIterator<T> {
        if self.is_transpose {
            return MatrixIterator::new(&self, IterType::IterRows);
        }
        MatrixIterator::new(&self, IterType::IterCols)
    }

    pub fn row_iter(&self) -> MatrixIterator<T> {
        if self.is_transpose {
            return MatrixIterator::new(&self, IterType::IterCols);
        }
        MatrixIterator::new(&self, IterType::IterRows)
    }
}

impl<T> Debug for Matrix<T>
where
    T: MatrixElement<Output = T>, // + Add<Output = T>
                                  // + Sub<Output = T>
                                  // + Mul<Output = T>
                                  // + Div<Output = T>
                                  // + MulAssign
                                  // + DivAssign
                                  // + AddAssign
                                  // + SubAssign
                                  // + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[{}x{}]:", self.rows(), self.cols())?;
        let mut ct = 0;
        let precision = f.precision().unwrap_or(1);
        for item in self.row_iter() {
            write!(f, "{:.*?}", precision, item)?;
            ct += 1;
            if ct == self.cols() {
                write!(f, ";")?;
                ct = 0;
            } else {
                write!(f, ",")?;
            }
        }

        Ok(())
    }
}

impl<T> Display for Matrix<T>
where
    T: MatrixElement<Output = T>, // + Add<Output = T>
                                  // + Sub<Output = T>
                                  // + Mul<Output = T>
                                  // + Div<Output = T>
                                  // + MulAssign
                                  // + DivAssign
                                  // + AddAssign
                                  // + SubAssign
                                  // + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}x{}:", self.rows(), self.cols())?;
        // let mut ct = 0;
        // for item in self.row_iter() {
        //     write!(f, "{:.1?}", item)?;
        //     ct += 1;
        //     if ct == self.cols() {
        //         write!(f, ";")?;
        //         ct = 0;
        //     } else {
        //         write!(f, ",")?;
        //     }
        // }
        let precision = f.precision().unwrap_or(1);
        write!(f, "{:.*?}", precision, 1.2345678)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Matrix;
    macro_rules! assert_matrix {
        ($m:ident, $rows:literal, $cols:literal, $capacity:literal, $len:literal, $transpose:literal, $square:literal) => {
            assert_eq!($m.rows, $rows);
            assert_eq!($m.cols, $cols);
            assert_eq!($m.data.capacity(), $capacity);
            assert_eq!($m.data.len(), $len);
            assert_eq!($m.is_transpose, $transpose);
            assert_eq!($m.is_square, $square);
        };
    }

    macro_rules! test_new_type {
        ($fn_name:ident, $t:ty, $rows:literal, $cols:literal, $capacity:literal) => {
            #[test]
            fn $fn_name() {
                let m: Matrix<$t> = Matrix::new($rows, $cols);
                assert_matrix!(m, $rows, $cols, $capacity, 0, false, false);
            }
        };
    }

    test_new_type!(test_new_f32, f32, 3, 2, 6);
    test_new_type!(test_new_f64, f64, 3, 2, 6);
    test_new_type!(test_new_u8, u8, 3, 2, 6);
    test_new_type!(test_new_u16, u16, 3, 2, 6);
    test_new_type!(test_new_u32, u32, 3, 2, 6);
    test_new_type!(test_new_u64, u64, 3, 2, 6);
    test_new_type!(test_new_u128, u128, 3, 2, 6);
    test_new_type!(test_new_i8, i8, 3, 2, 6);
    test_new_type!(test_new_i16, i16, 3, 2, 6);
    test_new_type!(test_new_i32, i32, 3, 2, 6);
    test_new_type!(test_new_i64, i64, 3, 2, 6);
    test_new_type!(test_new_i128, i128, 3, 2, 6);

    macro_rules! test_identity_matrix {
        ($fn_name:ident, $t:ty, $size:literal, $capacity:literal, $precision:literal, $t_str:literal) => {
            #[test]
            fn $fn_name() {
                let m: Matrix<$t> = Matrix::identity($size);
                assert_matrix!(m, $size, $size, $capacity, $capacity, false, true);
                let precision = $precision;
                assert_eq!(format!("{:.*?}", precision, m), $t_str);
            }
        };
    }
    test_identity_matrix!(
        test_identity_matrix_u8,
        u8,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_u16,
        u16,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_u32,
        u32,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_u64,
        u64,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_u128,
        u128,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_i8,
        i8,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_i16,
        i16,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_i32,
        i32,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_i64,
        i64,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_i128,
        i128,
        3,
        9,
        0,
        "[3x3]:1,0,0;0,1,0;0,0,1;"
    );

    test_identity_matrix!(
        test_identity_matrix_f32,
        f32,
        3,
        9,
        1,
        "[3x3]:1.0,0.0,0.0;0.0,1.0,0.0;0.0,0.0,1.0;"
    );

    test_identity_matrix!(
        test_identity_matrix_f64,
        f64,
        3,
        9,
        1,
        "[3x3]:1.0,0.0,0.0;0.0,1.0,0.0;0.0,0.0,1.0;"
    );
}
