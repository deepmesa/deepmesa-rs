use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::traits::{AddInto, MatrixElement};

macro_rules! dispatch {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &$self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

macro_rules! dispatch_mut {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &mut $self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

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
        // match self.data {
        //     MatrixData::ColMajor(ds) => match &mut result.data {
        //         MatrixData::ColMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::RowMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::DualIndex(result) => ds.add_into(rhs, result),
        //     },
        //     MatrixData::RowMajor(ds) => match &mut result.data {
        //         MatrixData::ColMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::RowMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::DualIndex(result) => ds.add_into(rhs, result),
        //     },
        //     MatrixData::DualIndex(ds) => match &mut result.data {
        //         MatrixData::ColMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::RowMajor(result) => ds.add_into(rhs, result),
        //         MatrixData::DualIndex(result) => ds.add_into(rhs, result),
        //     },
        // }
    }
}

impl<T> AddInto<&Matrix<T>, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &Matrix<T>, result: &mut Matrix<T>) {
        dispatch!(
            self,
            ds,
            dispatch_mut!(
                result,
                result,
                dispatch!(rhs, rhs, ds.add_into(rhs, result))
            )
        );
        // match &self.data {
        //     //Self: ColMajor
        //     MatrixData::ColMajor(ds) => match &mut result.data {
        //         //Result: ColMajor
        //         MatrixData::ColMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result: RowMajor
        //         MatrixData::RowMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result: DualIndex
        //         MatrixData::DualIndex(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //     },
        //     //Self: RowMajor
        //     MatrixData::RowMajor(ds) => match &mut result.data {
        //         //Result ColMajor
        //         MatrixData::ColMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result RowMajor
        //         MatrixData::RowMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result DualIndex
        //         MatrixData::DualIndex(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //     },
        //     //Self: DualIndex
        //     MatrixData::DualIndex(ds) => match &mut result.data {
        //         //Result ColMajor
        //         MatrixData::ColMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result RowMajor
        //         MatrixData::RowMajor(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //         //Result DualIndex
        //         MatrixData::DualIndex(result) => match &rhs.data {
        //             MatrixData::ColMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::RowMajor(rhs) => ds.add_into(rhs, result),
        //             MatrixData::DualIndex(rhs) => ds.add_into(rhs, result),
        //         },
        //     },
        // }
    }
}
