use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::MulInto;
use std::ops::Mul;
use std::ops::MulAssign;

impl<T> Mul<T> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(mut self, rhs: T) -> RowMajorDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(mut self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(mut self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(mut self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<T> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(self, rhs: T) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&RowMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&ColMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&DualIndexDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn mul(self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

// #[cfg(test)]
// mod tests {

//     use crate::matrix::cmd::data::*;
//     use crate::matrix::cmd::macros::col_major_dataset;
//     use crate::matrix::did::data::*;
//     use crate::matrix::did::macros::dual_index_dataset;
//     use crate::matrix::matrix::matrix;
//     use crate::matrix::matrix::*;
//     use crate::matrix::rmd::data::*;
//     use crate::matrix::rmd::macros::row_major_dataset;
//     use crate::matrix::traits::*;
//     use std::any::Any;
//     use std::ops::Mul;

//     macro_rules! lhs {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 2,3,4;5,6,7)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3,2, $simd], 2,5;3,6;4,7);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//     }

//     macro_rules! rhs {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t,2,3, $simd], 6,7,8;9,10,11)
//         };
//         (cmd, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t,2,3,false], 6,7,8;9,10,11)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t,2,3, false], 6,7,8;9,10,11)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
//                 did.transpose();
//                 did
//             }
//         };
//     }

//     macro_rules! result {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 12,21,32;45,60,77)
//         };
//         (val, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 6,9,12;15,18,21)
//         };
//     }

//     macro_rules! test_mul {
//         ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
//             let lhs = lhs!($lhs, $simd, $t);
//             let rhs = rhs!($rhs, $simd, $t);
//             let out = lhs.mul(&rhs);
//             assert_eq!(out, result!(rmd, $simd, $t));
//         };
//     }

//     macro_rules! test_mul_val {
//         ($t:ty, $simd:ident, $lhs:ident) => {
//             let lhs = lhs!($lhs, $simd, $t);
//             let rhs = 3 as $t;
//             let out = lhs.mul(rhs);
//             assert_eq!(out, result!(val, $simd, $t));
//         };
//     }

//     macro_rules! fn_test_mul_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_val!(u8, false, $lhs);
//                 test_mul_val!(u16, false, $lhs);
//                 test_mul_val!(u32, false, $lhs);
//                 test_mul_val!(u64, false, $lhs);
//                 test_mul_val!(u128, false, $lhs);
//                 test_mul_val!(i8, false, $lhs);
//                 test_mul_val!(i16, false, $lhs);
//                 test_mul_val!(i32, false, $lhs);
//                 test_mul_val!(i64, false, $lhs);
//                 test_mul_val!(i128, false, $lhs);
//                 test_mul_val!(f32, false, $lhs);
//                 test_mul_val!(f64, false, $lhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_val_simd {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_val!(u8, true, $lhs);
//                 test_mul_val!(u16, true, $lhs);
//                 test_mul_val!(u32, true, $lhs);
//                 test_mul_val!(i8, true, $lhs);
//                 test_mul_val!(i16, true, $lhs);
//                 test_mul_val!(i32, true, $lhs);
//                 test_mul_val!(f32, true, $lhs);
//                 test_mul_val!(f64, true, $lhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul!(u8, false, $lhs, $rhs);
//                 test_mul!(u16, false, $lhs, $rhs);
//                 test_mul!(u32, false, $lhs, $rhs);
//                 test_mul!(u64, false, $lhs, $rhs);
//                 test_mul!(u128, false, $lhs, $rhs);
//                 test_mul!(i8, false, $lhs, $rhs);
//                 test_mul!(i16, false, $lhs, $rhs);
//                 test_mul!(i32, false, $lhs, $rhs);
//                 test_mul!(i64, false, $lhs, $rhs);
//                 test_mul!(i128, false, $lhs, $rhs);
//                 test_mul!(f32, false, $lhs, $rhs);
//                 test_mul!(f64, false, $lhs, $rhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_simd {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul!(u8, true, $lhs, $rhs);
//                 test_mul!(u16, true, $lhs, $rhs);
//                 test_mul!(u32, true, $lhs, $rhs);
//                 test_mul!(i8, true, $lhs, $rhs);
//                 test_mul!(i16, true, $lhs, $rhs);
//                 test_mul!(i32, true, $lhs, $rhs);
//                 test_mul!(f32, true, $lhs, $rhs);
//                 test_mul!(f64, true, $lhs, $rhs);
//             }
//         };
//     }

//     fn_test_mul_val!(test_mul_val_rmd, rmd);
//     fn_test_mul_val!(test_mul_val_rmd_t, rmd_t);

//     fn_test_mul_val_simd!(test_mul_simd_val_rmd, rmd);
//     fn_test_mul_val_simd!(test_mul_simd_val_rmd_t, rmd_t);

//     fn_test_mul!(test_mul_rmd_rmd, rmd, rmd);
//     fn_test_mul!(test_mul_rmd_cmd, rmd, cmd);
//     fn_test_mul!(test_mul_rmd_did, rmd, did);

//     fn_test_mul!(test_mul_rmd_rmd_t, rmd, rmd_t);
//     fn_test_mul!(test_mul_rmd_cmd_t, rmd, cmd_t);
//     fn_test_mul!(test_mul_rmd_did_t, rmd, did_t);

//     fn_test_mul!(test_mul_rmd_t_rmd, rmd_t, rmd);
//     fn_test_mul!(test_mul_rmd_t_cmd, rmd_t, cmd);
//     fn_test_mul!(test_mul_rmd_t_did, rmd_t, did);

//     fn_test_mul!(test_mul_rmd_t_rmd_t, rmd_t, rmd_t);
//     fn_test_mul!(test_mul_rmd_t_cmd_t, rmd_t, cmd_t);
//     fn_test_mul!(test_mul_rmd_t_did_t, rmd_t, did_t);

//     //
//     fn_test_mul_simd!(test_mul_simd_rmd_rmd, rmd, rmd);
//     fn_test_mul_simd!(test_mul_simd_rmd_cmd, rmd, cmd);
//     fn_test_mul_simd!(test_mul_simd_rmd_did, rmd, did);

//     fn_test_mul_simd!(test_mul_simd_rmd_rmd_t, rmd, rmd_t);
//     fn_test_mul_simd!(test_mul_simd_rmd_cmd_t, rmd, cmd_t);
//     fn_test_mul_simd!(test_mul_simd_rmd_did_t, rmd, did_t);

//     fn_test_mul_simd!(test_mul_simd_rmd_t_rmd, rmd_t, rmd);
//     fn_test_mul_simd!(test_mul_simd_rmd_t_cmd, rmd_t, cmd);
//     fn_test_mul_simd!(test_mul_simd_rmd_t_did, rmd_t, did);

//     fn_test_mul_simd!(test_mul_simd_rmd_t_rmd_t, rmd_t, rmd_t);
//     fn_test_mul_simd!(test_mul_simd_rmd_t_cmd_t, rmd_t, cmd_t);
//     fn_test_mul_simd!(test_mul_simd_rmd_t_did_t, rmd_t, did_t);
// }
