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

        // match &mut self.data {
        //     MatrixData::ColMajor(ds) => ds.add_assign(rhs),
        //     MatrixData::RowMajor(ds) => ds.add_assign(rhs),
        //     MatrixData::DualIndex(ds) => ds.add_assign(rhs),
        // }
    }
}

// impl<T> SimdAddAssign<T> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn simd_add_assign(&mut self, val: T) {
//         match &mut self.data {
//             MatrixData::ColMajor(ds) => {
//                 let ptr = ds.data_ptr();
//                 let len = ds.len();
//                 unsafe {
//                     SimdKernel::ptr_add_assign(ptr, len, val);
//                 }
//             }
//             MatrixData::RowMajor(ds) => {
//                 let ptr = ds.data_ptr();
//                 let len = ds.len();
//                 unsafe {
//                     SimdKernel::ptr_add_assign(ptr, len, val);
//                 }
//             }
//             MatrixData::DualIndex(ds) => {
//                 let ptr = ds.data_ptr();
//                 let len = ds.len();
//                 unsafe {
//                     SimdKernel::ptr_add_assign(ptr, len, val);
//                 }
//                 //TODO: Sync
//             }
//         }

//         // match &self.data {
//         //     MatrixData::ColMajor(ds) => {
//         //         let ptr = ds.data_ptr();
//         //         let len = ds.len();
//         //         unsafe {
//         //             SimdKernel::ptr_add_assign(ptr, len, val);
//         //         }
//         //         println!("IN SIMD_ADD_ASSIGN: {:?}", self);
//         //     }
//         //     MatrixData::RowMajor(ds) => {
//         //         let ptr = ds.data_ptr();
//         //         let len = ds.len();
//         //         unsafe {
//         //             SimdKernel::ptr_add_assign(ptr, len, val);
//         //         }
//         //         println!("IN SIMD_ADD_ASSIGN: {:?}", self);
//         //     }
//         //     MatrixData::DualIndex(ds) => {
//         //         let ptr = ds.data_ptr();
//         //         let len = ds.len();
//         //         unsafe {
//         //             SimdKernel::ptr_add_assign(ptr, len, val);
//         //         }
//         //         println!("IN SIMD_ADD_ASSIGN: {:?}", self);
//         //     }
//         // }
//         // match self.m_type {
//         //     MatrixType::ColMajor(ds) => {
//         //         //                ds.simd_add_assign(rhs);
//         //     }
//         //     MatrixType::RowMajor => {
//         //         println!("Running simd_add_assign!");
//         //         self.rmd.simd_add_assign(val);
//         //     }
//         //     MatrixType::DualIndex => {
//         //         //                self.did.simd_add_assign(rhs);
//         //     }
//         //        }
//     }
// }

impl<T> std::ops::AddAssign<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &Matrix<T>) {
        shape_check!(self, rhs);
        dispatch_mut!(self, ds, dispatch!(rhs, rhs, ds.add_assign(rhs)));

        // match &mut self.data {
        //     MatrixData::ColMajor(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        //     MatrixData::RowMajor(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        //     MatrixData::DualIndex(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        // }
    }
}
