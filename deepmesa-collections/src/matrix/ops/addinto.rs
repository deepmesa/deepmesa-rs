use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdPtrAddInto;
use crate::matrix::traits::{AddInto, MatrixElement, SimdAddInto};
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

impl<T> SimdAddInto<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn simd_add_into(&self, result: &mut Matrix<T>, val: T) {
        dispatch!(self, ds, {
            let ptr = ds.data_ptr();
            let len = ds.len();
            match &mut result.data {
                MatrixData::ColMajor(result) => {
                    let dst = result.data_ptr();
                    unsafe {
                        SimdKernel::ptr_add_into(ptr, dst, len, val);
                    }
                }
                MatrixData::RowMajor(result) => {
                    let dst = result.data_ptr();
                    unsafe {
                        SimdKernel::ptr_add_into(ptr, dst, len, val);
                    }
                }
                MatrixData::DualIndex(result) => {
                    let dst = result.data_ptr();
                    unsafe {
                        SimdKernel::ptr_add_into(ptr, dst, len, val);
                    }
                    //TODO: Sync
                }
            }
        });
    }
}
