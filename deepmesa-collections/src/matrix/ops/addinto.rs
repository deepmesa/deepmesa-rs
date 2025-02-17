use crate::matrix::did::data::SyncDirection;
use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::traits::{AddInto, MatrixElement};
use crate::matrix::Dataset;

impl<T> AddInto<T, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut Matrix<T>) {
        dispatch!(
            self,
            ds,
            dispatch_mut!(result, result, ds.add_into(rhs, result))
        );
    }
}

impl<T> AddInto<&Matrix<T>, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &Matrix<T>, result: &mut Matrix<T>) {
        shape_check!(self, rhs);
        shape_check!(self, result);

        dispatch!(
            self,
            ds,
            dispatch_mut!(
                result,
                result,
                dispatch!(rhs, rhs, ds.add_into(rhs, result))
            )
        );
    }
}
