use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::AddInto;
use crate::matrix::traits::MatrixElement;
use std::ops::Add;
use std::ops::AddAssign;

impl<T> Add<T> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(mut self, rhs: T) -> RowMajorDataset<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<&RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(mut self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<&ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(mut self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<&DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(mut self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<T> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(self, rhs: T) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> Add<&RowMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> Add<&ColMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> Add<&DualIndexDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn add(self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.add_into(rhs, &mut result);
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
//     use std::ops::Add;

//     macro_rules! lhs {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 1,2,3;4,5,6)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3,2, $simd], 1,4;2,5;3,6);
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
//             row_major_dataset!([$t, 2, 3, $simd], 7,9,11;13,15,17)
//         };
//         (val, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 4,5,6;7,8,9)
//         };
//     }

//     macro_rules! test_add {
//         ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
//             let lhs = lhs!($lhs, $simd, $t);
//             let rhs = rhs!($rhs, $simd, $t);
//             let out = lhs.add(&rhs);
//             assert_eq!(out, result!(rmd, $simd, $t));
//         };
//     }

//     macro_rules! test_add_val {
//         ($t:ty, $simd:ident, $lhs:ident) => {
//             let lhs = lhs!($lhs, $simd, $t);
//             let rhs = 3 as $t;
//             let out = lhs.add(rhs);
//             assert_eq!(out, result!(val, $simd, $t));
//         };
//     }

//     macro_rules! fn_test_add_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_val!(u8, false, $lhs);
//                 test_add_val!(u16, false, $lhs);
//                 test_add_val!(u32, false, $lhs);
//                 test_add_val!(u64, false, $lhs);
//                 test_add_val!(u128, false, $lhs);
//                 test_add_val!(i8, false, $lhs);
//                 test_add_val!(i16, false, $lhs);
//                 test_add_val!(i32, false, $lhs);
//                 test_add_val!(i64, false, $lhs);
//                 test_add_val!(i128, false, $lhs);
//                 test_add_val!(f32, false, $lhs);
//                 test_add_val!(f64, false, $lhs);
//             }
//         };
//     }

//     macro_rules! fn_test_add_val_simd {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_val!(u8, true, $lhs);
//                 test_add_val!(u16, true, $lhs);
//                 test_add_val!(u32, true, $lhs);
//                 test_add_val!(i8, true, $lhs);
//                 test_add_val!(i16, true, $lhs);
//                 test_add_val!(i32, true, $lhs);
//                 test_add_val!(f32, true, $lhs);
//                 test_add_val!(f64, true, $lhs);
//             }
//         };
//     }

//     macro_rules! fn_test_add {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add!(u8, false, $lhs, $rhs);
//                 test_add!(u16, false, $lhs, $rhs);
//                 test_add!(u32, false, $lhs, $rhs);
//                 test_add!(u64, false, $lhs, $rhs);
//                 test_add!(u128, false, $lhs, $rhs);
//                 test_add!(i8, false, $lhs, $rhs);
//                 test_add!(i16, false, $lhs, $rhs);
//                 test_add!(i32, false, $lhs, $rhs);
//                 test_add!(i64, false, $lhs, $rhs);
//                 test_add!(i128, false, $lhs, $rhs);
//                 test_add!(f32, false, $lhs, $rhs);
//                 test_add!(f64, false, $lhs, $rhs);
//             }
//         };
//     }

//     macro_rules! fn_test_add_simd {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add!(u8, true, $lhs, $rhs);
//                 test_add!(u16, true, $lhs, $rhs);
//                 test_add!(u32, true, $lhs, $rhs);
//                 test_add!(i8, true, $lhs, $rhs);
//                 test_add!(i16, true, $lhs, $rhs);
//                 test_add!(i32, true, $lhs, $rhs);
//                 test_add!(f32, true, $lhs, $rhs);
//                 test_add!(f64, true, $lhs, $rhs);
//             }
//         };
//     }

//     fn_test_add_val!(test_add_val_rmd, rmd);
//     fn_test_add_val!(test_add_val_rmd_t, rmd_t);

//     fn_test_add_val_simd!(test_add_simd_val_rmd, rmd);
//     fn_test_add_val_simd!(test_add_simd_val_rmd_t, rmd_t);

//     fn_test_add!(test_add_rmd_rmd, rmd, rmd);
//     fn_test_add!(test_add_rmd_cmd, rmd, cmd);
//     fn_test_add!(test_add_rmd_did, rmd, did);

//     fn_test_add!(test_add_rmd_rmd_t, rmd, rmd_t);
//     fn_test_add!(test_add_rmd_cmd_t, rmd, cmd_t);
//     fn_test_add!(test_add_rmd_did_t, rmd, did_t);

//     fn_test_add!(test_add_rmd_t_rmd, rmd_t, rmd);
//     fn_test_add!(test_add_rmd_t_cmd, rmd_t, cmd);
//     fn_test_add!(test_add_rmd_t_did, rmd_t, did);

//     fn_test_add!(test_add_rmd_t_rmd_t, rmd_t, rmd_t);
//     fn_test_add!(test_add_rmd_t_cmd_t, rmd_t, cmd_t);
//     fn_test_add!(test_add_rmd_t_did_t, rmd_t, did_t);

//     //
//     fn_test_add_simd!(test_add_simd_rmd_rmd, rmd, rmd);
//     fn_test_add_simd!(test_add_simd_rmd_cmd, rmd, cmd);
//     fn_test_add_simd!(test_add_simd_rmd_did, rmd, did);

//     fn_test_add_simd!(test_add_simd_rmd_rmd_t, rmd, rmd_t);
//     fn_test_add_simd!(test_add_simd_rmd_cmd_t, rmd, cmd_t);
//     fn_test_add_simd!(test_add_simd_rmd_did_t, rmd, did_t);

//     fn_test_add_simd!(test_add_simd_rmd_t_rmd, rmd_t, rmd);
//     fn_test_add_simd!(test_add_simd_rmd_t_cmd, rmd_t, cmd);
//     fn_test_add_simd!(test_add_simd_rmd_t_did, rmd_t, did);

//     fn_test_add_simd!(test_add_simd_rmd_t_rmd_t, rmd_t, rmd_t);
//     fn_test_add_simd!(test_add_simd_rmd_t_cmd_t, rmd_t, cmd_t);
//     fn_test_add_simd!(test_add_simd_rmd_t_did_t, rmd_t, did_t);
// }
