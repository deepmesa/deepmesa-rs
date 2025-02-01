use crate::matrix::matrix::Matrix;
use crate::matrix::traits::AddInto;
use crate::matrix::traits::MatrixElement;

impl<T> std::ops::Add<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(self, rhs: T) -> Matrix<T> {
        let mut result = Matrix::new(self.rows, self.cols, self.m_type, self.is_simd_optimized());
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> std::ops::Add<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(self, rhs: &Matrix<T>) -> Matrix<T> {
        let mut result = Matrix::new(self.rows, self.cols, self.m_type, self.is_simd_optimized());
        self.add_into(rhs, &mut result);
        return result;
    }
}
