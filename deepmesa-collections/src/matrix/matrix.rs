use crate::matrix::traits::MatrixElement;

pub struct Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    rows: usize,
    cols: usize,
    data: Vec<T>,
    is_transpose: bool,
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

    #[test]
    fn test_identity_u8() {
        let m: Matrix<u8> = Matrix::identity(3);
        assert_matrix!(m, 3, 3, 9, 9, false, true);
        //TODO: impl the Debug and Display traits and then use to_string to assert the values of the matrix using macros
    }
}
