use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;

impl<T> std::ops::AddAssign<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: T) {
        dispatch_mut!(self, ds, ds.add_assign(rhs));
    }
}

impl<T> std::ops::AddAssign<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &Matrix<T>) {
        shape_check!(self, rhs);
        dispatch_mut!(self, ds, dispatch!(rhs, rhs, ds.add_assign(rhs)));
    }
}

#[cfg(test)]
mod tests {}
