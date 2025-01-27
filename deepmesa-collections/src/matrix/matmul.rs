use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;
use crate::matrix::traits::MatrixElement;

pub struct MatrixMultiply<'a, T>
where
    T: MatrixElement<Output = T>,
{
    m1: &'a Matrix<T>,
    m2: &'a Matrix<T>,
}

impl<'a, T> MatrixMultiply<'a, T>
where
    T: MatrixElement<Output = T> + std::ops::Mul<Output = T> + std::ops::AddAssign,
{
    pub fn new(m1: &'a Matrix<T>, m2: &'a Matrix<T>) -> MatrixMultiply<'a, T> {
        if m1.cols() != m2.rows() {
            //TODO: Add a better message with the dimensions
            panic!("Cannot multiply matrices m1 & m2. Dimensions are incorrect");
        }
        return MatrixMultiply { m1, m2 };
    }

    pub fn mul(&self, m_type: MatrixType, simd_optimized: bool) -> Matrix<T> {
        let mut result = Matrix::new(self.m1.rows(), self.m2.cols(), m_type, simd_optimized);

        for row in 0..self.m1.rows() {
            for col in 0..self.m2.cols() {
                let val = self.compute(row, col);
                result.set(row, col, val);
            }
        }
        return result;
    }

    fn compute(&self, row_m1: usize, col_m2: usize) -> T {
        let mut val: T = T::zero();
        for idx in 0..self.m1.cols() {
            //Get the ptr for the dataset for self
            //get the ptr for the dataset for other
            //Do the subtraction
            //Operations
            // Matrix: Add, Sub, Mul, Div,
            // Matrix: AddAssign, SubAssign, MulAssign, DivAssign,

            // Scalar: Add, Sub, Mul, Div
            // Scalar: AddAssign, SubAssign, MulAssign, DivAssign

            // Set, Get, Fill
            val += self.m1.get_unchecked(row_m1, idx) * self.m2.get_unchecked(idx, col_m2);
        }

        return val;
    }
}
