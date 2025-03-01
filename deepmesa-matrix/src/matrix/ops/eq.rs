use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn eq(&self, other: &Matrix<T>) -> bool {
        dispatch!(self, ds, dispatch!(other, other, return ds.eq(other)));
        //TODO: Should eq check the layout of the Matrix?Maybe not
    }
}
