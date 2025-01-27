use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;
use crate::matrix::traits::MatrixElement;

impl<T> std::ops::AddAssign<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: T) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.add_assign(rhs);
            }
            MatrixType::RowMajor => {
                self.rmd.add_assign(rhs);
            }
            MatrixType::DualIndex => {
                self.did.add_assign(rhs);
            }
        }
    }
}

impl<T> std::ops::AddAssign<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &Matrix<T>) {
        shape_check!(self, rhs);
        match self.m_type {
            MatrixType::ColMajor => match rhs.m_type {
                MatrixType::RowMajor => self.cmd.add_assign(&rhs.rmd),
                _ => self.cmd.add_assign(&rhs.cmd),
            },
            MatrixType::RowMajor => match rhs.m_type {
                MatrixType::ColMajor => self.rmd.add_assign(&rhs.cmd),
                _ => self.rmd.add_assign(&rhs.rmd),
            },
            MatrixType::DualIndex => match rhs.m_type {
                MatrixType::ColMajor => self.did.add_assign(&rhs.cmd),
                _ => self.did.add_assign(&rhs.rmd),
            },
        }
    }
}
