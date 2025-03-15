use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::{AddInto, MatrixElement};

use crate::matrix::did::data::SyncDirection;
use crate::matrix::simd::kernel::SimdKernel;

impl<T> AddInto<T, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<T, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<T, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

// #[cfg(test)]
// mod tests {
//     use crate::matrix::cmd::data::*;
//     use crate::matrix::cmd::macros::col_major_dataset;
//     use crate::matrix::did::data::*;
//     use crate::matrix::did::macros::dual_index_dataset;
//     use crate::matrix::rmd::data::*;
//     use crate::matrix::rmd::macros::row_major_dataset;
//     use crate::matrix::traits::*;

//     macro_rules! lhs {
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 5,6,7;8,9,10)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3,2, $simd], 5,8;6,9;7,10);
//                 did.transpose();
//                 did
//             }
//         };
//     }

//     macro_rules! rhs {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t,2,3, $simd], 12,13,14;15,16,17)
//         };
//         (cmd, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t,2,3,false], 12,13,14;15,16,17)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t,2,3, false], 12,13,14;15,16,17)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
//                 did.transpose();
//                 did
//             }
//         };
//     }

//     macro_rules! out {
//         (rmd, $simd:ident, $t:ty) => {
//             RowMajorDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {{
//             let mut rmd = RowMajorDataset::<$t>::new(3, 2, $simd, $simd);
//             rmd.transpose();
//             rmd
//         }};
//         (cmd, $simd:ident, $t:ty) => {
//             ColMajorDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (cmd_t, $simd:ident, $t:ty) => {{
//             let mut cmd = ColMajorDataset::<$t>::new(3, 2, $simd, $simd);
//             cmd.transpose();
//             cmd
//         }};
//         (did, $simd:ident, $t:ty) => {
//             DualIndexDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (did_t, $simd:ident, $t:ty) => {{
//             let mut did = DualIndexDataset::<$t>::new(3, 2, $simd, $simd);
//             did.transpose();
//             did
//         }};
//     }

//     macro_rules! result {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 17,19,21;23,25,27)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 17,23;19,25;21,27);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 17,19,21;23,25,27)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3, 2, $simd], 17,23;19,25;21,27);
//                 did.transpose();
//                 did
//             }
//         };
//         (cmd, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t, 2, 3, $simd], 17,19,21;23,25,27)
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 17,23;19,25;21,27);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//         (val, rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 12,13,14;15,16,17)
//         };
//         (val, rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 12,15;13,16;14,17);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (val, did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 12,13,14;15,16,17)
//         };
//         (val, did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3, 2, $simd], 12,15;13,16;14,17);
//                 did.transpose();
//                 did
//             }
//         };
//         (val, cmd, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t, 2, 3, $simd], 12,13,14;15,16,17)
//         };
//         (val, cmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 12,15;13,16;14,17);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//     }

//     macro_rules! test_add_into_val {
//         ($t:ty, $simd:ident, $lhs:ident, $out:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = 7 as $t;
//             let mut out = out!($out, $simd, $t);
//             lhs.add_into(rhs, &mut out);
//             assert_eq!(out, result!(val, $out, $simd, $t));
//         };
//     }

//     macro_rules! test_add_into {
//         ($t:ty, $simd:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = rhs!($rhs, $simd, $t);
//             let mut out = out!($out, $simd, $t);
//             lhs.add_into(&rhs, &mut out);
//             assert_eq!(out, result!($out, $simd, $t));
//         };
//     }

//     macro_rules! fn_test_add_into_val {
//         ($fn_name:ident, $lhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_into_val!(u8, false, $lhs, $out);
//                 test_add_into_val!(u16, false, $lhs, $out);
//                 test_add_into_val!(u32, false, $lhs, $out);
//                 test_add_into_val!(u64, false, $lhs, $out);
//                 test_add_into_val!(u128, false, $lhs, $out);
//                 test_add_into_val!(i8, false, $lhs, $out);
//                 test_add_into_val!(i16, false, $lhs, $out);
//                 test_add_into_val!(i32, false, $lhs, $out);
//                 test_add_into_val!(i64, false, $lhs, $out);
//                 test_add_into_val!(i128, false, $lhs, $out);
//                 test_add_into_val!(f32, false, $lhs, $out);
//                 test_add_into_val!(f64, false, $lhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_add_into_val_simd {
//         ($fn_name:ident, $lhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_into_val!(u8, true, $lhs, $out);
//                 test_add_into_val!(u16, true, $lhs, $out);
//                 test_add_into_val!(u32, true, $lhs, $out);
//                 test_add_into_val!(i8, true, $lhs, $out);
//                 test_add_into_val!(i16, true, $lhs, $out);
//                 test_add_into_val!(i32, true, $lhs, $out);
//                 test_add_into_val!(f32, true, $lhs, $out);
//                 test_add_into_val!(f64, true, $lhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_add_into {
//         ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_into!(u8, false, $lhs, $rhs, $out);
//                 test_add_into!(u16, false, $lhs, $rhs, $out);
//                 test_add_into!(u32, false, $lhs, $rhs, $out);
//                 test_add_into!(u64, false, $lhs, $rhs, $out);
//                 test_add_into!(u128, false, $lhs, $rhs, $out);
//                 test_add_into!(i8, false, $lhs, $rhs, $out);
//                 test_add_into!(i16, false, $lhs, $rhs, $out);
//                 test_add_into!(i32, false, $lhs, $rhs, $out);
//                 test_add_into!(i64, false, $lhs, $rhs, $out);
//                 test_add_into!(i128, false, $lhs, $rhs, $out);
//                 test_add_into!(f32, false, $lhs, $rhs, $out);
//                 test_add_into!(f64, false, $lhs, $rhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_add_into_simd {
//         ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_into!(u8, true, $lhs, $rhs, $out);
//                 test_add_into!(u16, true, $lhs, $rhs, $out);
//                 test_add_into!(u32, true, $lhs, $rhs, $out);
//                 test_add_into!(i8, true, $lhs, $rhs, $out);
//                 test_add_into!(i16, true, $lhs, $rhs, $out);
//                 test_add_into!(i32, true, $lhs, $rhs, $out);
//                 test_add_into!(f32, true, $lhs, $rhs, $out);
//                 test_add_into!(f64, true, $lhs, $rhs, $out);
//             }
//         };
//     }

//     fn_test_add_into_val!(test_add_into_val_did_rmd, did, rmd);
//     fn_test_add_into_val!(test_add_into_val_did_cmd, did, cmd);
//     fn_test_add_into_val!(test_add_into_val_did_did, did, did);

//     fn_test_add_into_val!(test_add_into_val_did_t_rmd, did_t, rmd);
//     fn_test_add_into_val!(test_add_into_val_did_t_cmd, did_t, cmd);
//     fn_test_add_into_val!(test_add_into_val_did_t_did, did_t, did);

//     fn_test_add_into_val!(test_add_into_val_did_rmd_t, did, rmd_t);
//     fn_test_add_into_val!(test_add_into_val_did_cmd_t, did, cmd_t);
//     fn_test_add_into_val!(test_add_into_val_did_did_t, did, did_t);

//     fn_test_add_into_val!(test_add_into_val_did_t_rmd_t, did_t, rmd_t);
//     fn_test_add_into_val!(test_add_into_val_did_t_cmd_t, did_t, cmd_t);
//     fn_test_add_into_val!(test_add_into_val_did_t_did_t, did_t, did_t);

//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_rmd, did, rmd);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_cmd, did, cmd);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_did, did, did);

//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_rmd, did_t, rmd);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_cmd, did_t, cmd);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_did, did_t, did);

//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_rmd_t, did, rmd_t);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_cmd_t, did, cmd_t);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_did_t, did, did_t);

//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_rmd_t, did_t, rmd_t);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_cmd_t, did_t, cmd_t);
//     fn_test_add_into_val_simd!(test_add_into_val_simd_did_t_did_t, did_t, did_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_rmd_rmd, did, rmd, rmd);
//     fn_test_add_into!(test_add_into_did_rmd_rmd_t, did, rmd, rmd_t);

//     fn_test_add_into!(test_add_into_did_rmd_t_rmd, did, rmd_t, rmd);
//     fn_test_add_into!(test_add_into_did_rmd_t_rmd_t, did, rmd_t, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_rmd, did_t, rmd, rmd);
//     fn_test_add_into!(test_add_into_did_t_rmd_rmd_t, did_t, rmd, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_t_rmd, did_t, rmd_t, rmd);
//     fn_test_add_into!(test_add_into_did_t_rmd_t_rmd_t, did_t, rmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_rmd_cmd, did, rmd, cmd);
//     fn_test_add_into!(test_add_into_did_rmd_cmd_t, did, rmd, cmd_t);

//     fn_test_add_into!(test_add_into_did_rmd_t_cmd, did, rmd_t, cmd);
//     fn_test_add_into!(test_add_into_did_rmd_t_cmd_t, did, rmd_t, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_cmd, did_t, rmd, cmd);
//     fn_test_add_into!(test_add_into_did_t_rmd_cmd_t, did_t, rmd, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_t_cmd, did_t, rmd_t, cmd);
//     fn_test_add_into!(test_add_into_did_t_rmd_t_cmd_t, did_t, rmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_rmd_did, did, rmd, did);
//     fn_test_add_into!(test_add_into_did_rmd_did_t, did, rmd, did_t);

//     fn_test_add_into!(test_add_into_did_rmd_t_did, did, rmd_t, did);
//     fn_test_add_into!(test_add_into_did_rmd_t_did_t, did, rmd_t, did_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_did, did_t, rmd, did);
//     fn_test_add_into!(test_add_into_did_t_rmd_did_t, did_t, rmd, did_t);

//     fn_test_add_into!(test_add_into_did_t_rmd_t_did, did_t, rmd_t, did);
//     fn_test_add_into!(test_add_into_did_t_rmd_t_did_t, did_t, rmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_cmd_rmd, did, cmd, rmd);
//     fn_test_add_into!(test_add_into_did_cmd_rmd_t, did, cmd, rmd_t);

//     fn_test_add_into!(test_add_into_did_cmd_t_rmd, did, cmd_t, rmd);
//     fn_test_add_into!(test_add_into_did_cmd_t_rmd_t, did, cmd_t, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_rmd, did_t, cmd, rmd);
//     fn_test_add_into!(test_add_into_did_t_cmd_rmd_t, did_t, cmd, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_t_rmd, did_t, cmd_t, rmd);
//     fn_test_add_into!(test_add_into_did_t_cmd_t_rmd_t, did_t, cmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_cmd_cmd, did, cmd, cmd);
//     fn_test_add_into!(test_add_into_did_cmd_cmd_t, did, cmd, cmd_t);

//     fn_test_add_into!(test_add_into_did_cmd_t_cmd, did, cmd_t, cmd);
//     fn_test_add_into!(test_add_into_did_cmd_t_cmd_t, did, cmd_t, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_cmd, did_t, cmd, cmd);
//     fn_test_add_into!(test_add_into_did_t_cmd_cmd_t, did_t, cmd, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_t_cmd, did_t, cmd_t, cmd);
//     fn_test_add_into!(test_add_into_did_t_cmd_t_cmd_t, did_t, cmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_cmd_did, did, cmd, did);
//     fn_test_add_into!(test_add_into_did_cmd_did_t, did, cmd, did_t);

//     fn_test_add_into!(test_add_into_did_cmd_t_did, did, cmd_t, did);
//     fn_test_add_into!(test_add_into_did_cmd_t_did_t, did, cmd_t, did_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_did, did_t, cmd, did);
//     fn_test_add_into!(test_add_into_did_t_cmd_did_t, did_t, cmd, did_t);

//     fn_test_add_into!(test_add_into_did_t_cmd_t_did, did_t, cmd_t, did);
//     fn_test_add_into!(test_add_into_did_t_cmd_t_did_t, did_t, cmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_did_rmd, did, did, rmd);
//     fn_test_add_into!(test_add_into_did_did_rmd_t, did, did, rmd_t);

//     fn_test_add_into!(test_add_into_did_did_t_rmd, did, did_t, rmd);
//     fn_test_add_into!(test_add_into_did_did_t_rmd_t, did, did_t, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_did_rmd, did_t, did, rmd);
//     fn_test_add_into!(test_add_into_did_t_did_rmd_t, did_t, did, rmd_t);

//     fn_test_add_into!(test_add_into_did_t_did_t_rmd, did_t, did_t, rmd);
//     fn_test_add_into!(test_add_into_did_t_did_t_rmd_t, did_t, did_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_did_cmd, did, did, cmd);
//     fn_test_add_into!(test_add_into_did_did_cmd_t, did, did, cmd_t);

//     fn_test_add_into!(test_add_into_did_did_t_cmd, did, did_t, cmd);
//     fn_test_add_into!(test_add_into_did_did_t_cmd_t, did, did_t, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_did_cmd, did_t, did, cmd);
//     fn_test_add_into!(test_add_into_did_t_did_cmd_t, did_t, did, cmd_t);

//     fn_test_add_into!(test_add_into_did_t_did_t_cmd, did_t, did_t, cmd);
//     fn_test_add_into!(test_add_into_did_t_did_t_cmd_t, did_t, did_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into!(test_add_into_did_did_did, did, did, did);
//     fn_test_add_into!(test_add_into_did_did_did_t, did, did, did_t);

//     fn_test_add_into!(test_add_into_did_did_t_did, did, did_t, did);
//     fn_test_add_into!(test_add_into_did_did_t_did_t, did, did_t, did_t);

//     fn_test_add_into!(test_add_into_did_t_did_did, did_t, did, did);
//     fn_test_add_into!(test_add_into_did_t_did_did_t, did_t, did, did_t);

//     fn_test_add_into!(test_add_into_did_t_did_t_did, did_t, did_t, did);
//     fn_test_add_into!(test_add_into_did_t_did_t_did_t, did_t, did_t, did_t);

//     //////////////////////////////////////////////////////////////////////////////
//     // SIMD Tests
//     //////////////////////////////////////////////////////////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_rmd, did, rmd, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_rmd_t, did, rmd, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_rmd, did, rmd_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_rmd_t, did, rmd_t, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_rmd, did_t, rmd, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_rmd_t, did_t, rmd, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_rmd, did_t, rmd_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_rmd_t, did_t, rmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_cmd, did, rmd, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_cmd_t, did, rmd, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_cmd, did, rmd_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_cmd_t, did, rmd_t, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_cmd, did_t, rmd, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_cmd_t, did_t, rmd, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_cmd, did_t, rmd_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_cmd_t, did_t, rmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&RowMajordataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_did, did, rmd, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_did_t, did, rmd, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_did, did, rmd_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_rmd_t_did_t, did, rmd_t, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_did, did_t, rmd, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_did_t, did_t, rmd, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_did, did_t, rmd_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_rmd_t_did_t, did_t, rmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_rmd, did, cmd, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_rmd_t, did, cmd, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_rmd, did, cmd_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_rmd_t, did, cmd_t, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_rmd, did_t, cmd, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_rmd_t, did_t, cmd, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_rmd, did_t, cmd_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_rmd_t, did_t, cmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_cmd, did, cmd, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_cmd_t, did, cmd, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_cmd, did, cmd_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_cmd_t, did, cmd_t, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_cmd, did_t, cmd, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_cmd_t, did_t, cmd, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_cmd, did_t, cmd_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_cmd_t, did_t, cmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&ColMajordataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_did, did, cmd, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_did_t, did, cmd, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_did, did, cmd_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_cmd_t_did_t, did, cmd_t, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_did, did_t, cmd, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_did_t, did_t, cmd, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_did, did_t, cmd_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_cmd_t_did_t, did_t, cmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, RowMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_did_rmd, did, did, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_rmd_t, did, did, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_rmd, did, did_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_rmd_t, did, did_t, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_rmd, did_t, did, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_rmd_t, did_t, did, rmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_rmd, did_t, did_t, rmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_rmd_t, did_t, did_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, ColMajorDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_did_cmd, did, did, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_cmd_t, did, did, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_cmd, did, did_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_cmd_t, did, did_t, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_cmd, did_t, did, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_cmd_t, did_t, did, cmd_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_cmd, did_t, did_t, cmd);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_cmd_t, did_t, did_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test AddInto<&DualIndexDataset<T>, DualndexDataset<T>> for DualIndexdataset<T>
//     fn_test_add_into_simd!(test_add_into_simd_did_did_did, did, did, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_did_t, did, did, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_did, did, did_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_did_t_did_t, did, did_t, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_did, did_t, did, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_did_t, did_t, did, did_t);

//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_did, did_t, did_t, did);
//     fn_test_add_into_simd!(test_add_into_simd_did_t_did_t_did_t, did_t, did_t, did_t);
// }
