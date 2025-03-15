use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::did::data::SyncDirection;
use crate::matrix::did::macros::simd_mul_assign;
use crate::matrix::macros::*;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdMulAssign;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use std::ops::MulAssign;

impl<T> MulAssign<T> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, val: T) {
        if self.use_simd() {
            let ptr = self.rmd.rm_data;
            let len = self.len();
            unsafe {
                SimdKernel::simd_mul_assign(ptr, val, len);
            }
            self.sync(SyncDirection::RmdToCmd);
            return;
        }

        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rmd_mul_assign_t!(self.rmd, row, col, val);
                cmd_mul_assign_t!(self.cmd, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rmd_mul_assign!(self.rmd, row, col, val);
                cmd_mul_assign!(self.cmd, row, col, val);
            });
        }
    }
}

impl<T> MulAssign<&RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(
                    rmd_t,
                    rmd_t,
                    self.rmd,
                    rhs,
                    self.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = rmd_get_t!(rhs, row, col);
                    rmd_mul_assign_t!(self.rmd, row, col, val);
                    cmd_mul_assign_t!(self.cmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_assign!(
                    cmd_t,
                    rmd,
                    self.cmd,
                    rhs,
                    self.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = rmd_get!(rhs, row, col);
                    rmd_mul_assign_t!(self.rmd, row, col, val);
                    cmd_mul_assign_t!(self.cmd, row, col, val);
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_mul_assign!(
                    cmd,
                    rmd_t,
                    self.cmd,
                    rhs,
                    self.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = rmd_get_t!(rhs, row, col);
                    rmd_mul_assign!(self.rmd, row, col, val);
                    cmd_mul_assign!(self.cmd, row, col, val);
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(
                    rmd,
                    rmd,
                    self.rmd,
                    rhs,
                    self.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = rmd_get!(rhs, row, col);
                    rmd_mul_assign!(self.rmd, row, col, val);
                    cmd_mul_assign!(self.cmd, row, col, val);
                });
            }
        }
    }
}

impl<T> MulAssign<&ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_mul_assign!(
                    cmd_t,
                    cmd_t,
                    self.cmd,
                    rhs,
                    self.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = cmd_get_t!(rhs, row, col);
                    rmd_mul_assign_t!(self.rmd, row, col, val);
                    cmd_mul_assign_t!(self.cmd, row, col, val);
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(
                    rmd_t,
                    cmd,
                    self.rmd,
                    rhs,
                    self.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = cmd_get!(rhs, row, col);
                    rmd_mul_assign_t!(self.rmd, row, col, val);
                    cmd_mul_assign_t!(self.cmd, row, col, val);
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(
                    rmd,
                    cmd_t,
                    self.rmd,
                    rhs,
                    self.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = cmd_get_t!(rhs, row, col);
                    rmd_mul_assign!(self.rmd, row, col, val);
                    cmd_mul_assign!(self.cmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_assign!(
                    cmd,
                    cmd,
                    self.cmd,
                    rhs,
                    self.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self.rmd, row, col, unsafe {
                    let val = cmd_get!(rhs, row, col);
                    rmd_mul_assign!(self.rmd, row, col, val);
                    cmd_mul_assign!(self.cmd, row, col, val);
                });
            }
        }
    }
}

impl<T> MulAssign<&DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.mul_assign(&rhs.rmd);
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
//     use std::ops::MulAssign;

//     macro_rules! lhs {
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 2,3,4;5,6,7)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3,2, $simd], 2,5;3,6;4,7);
//                 did.transpose();
//                 did
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

//     macro_rules! test_mul_assign {
//         ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = rhs!($rhs, $simd, $t);
//             lhs.mul_assign(&rhs);
//             assert_eq!(lhs, result!(rmd, $simd, $t));
//         };
//     }

//     macro_rules! test_mul_assign_val {
//         ($t:ty, $simd: ident, $lhs:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = 3 as $t;
//             lhs.mul_assign(rhs);
//             assert_eq!(lhs, result!(val, $simd, $t));
//         };
//     }

//     macro_rules! fn_test_mul_assign_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_assign_val!(u8, false, $lhs);
//                 test_mul_assign_val!(u16, false, $lhs);
//                 test_mul_assign_val!(u32, false, $lhs);
//                 test_mul_assign_val!(u64, false, $lhs);
//                 test_mul_assign_val!(u128, false, $lhs);
//                 test_mul_assign_val!(i8, false, $lhs);
//                 test_mul_assign_val!(i16, false, $lhs);
//                 test_mul_assign_val!(i32, false, $lhs);
//                 test_mul_assign_val!(i64, false, $lhs);
//                 test_mul_assign_val!(i128, false, $lhs);
//                 test_mul_assign_val!(f32, false, $lhs);
//                 test_mul_assign_val!(f64, false, $lhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_assign {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_assign!(u8, false, $lhs, $rhs);
//                 test_mul_assign!(u16, false, $lhs, $rhs);
//                 test_mul_assign!(u32, false, $lhs, $rhs);
//                 test_mul_assign!(u64, false, $lhs, $rhs);
//                 test_mul_assign!(u128, false, $lhs, $rhs);
//                 test_mul_assign!(i8, false, $lhs, $rhs);
//                 test_mul_assign!(i16, false, $lhs, $rhs);
//                 test_mul_assign!(i32, false, $lhs, $rhs);
//                 test_mul_assign!(i64, false, $lhs, $rhs);
//                 test_mul_assign!(i128, false, $lhs, $rhs);
//                 test_mul_assign!(f32, false, $lhs, $rhs);
//                 test_mul_assign!(f64, false, $lhs, $rhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_assign_simd {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_assign!(u8, true, $lhs, $rhs);
//                 test_mul_assign!(u16, true, $lhs, $rhs);
//                 test_mul_assign!(u32, true, $lhs, $rhs);
//                 test_mul_assign!(i8, true, $lhs, $rhs);
//                 test_mul_assign!(i16, true, $lhs, $rhs);
//                 test_mul_assign!(i32, true, $lhs, $rhs);
//                 test_mul_assign!(f32, true, $lhs, $rhs);
//                 test_mul_assign!(f64, true, $lhs, $rhs);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_assign_simd_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_assign_val!(u8, true, $lhs);
//                 test_mul_assign_val!(u16, true, $lhs);
//                 test_mul_assign_val!(u32, true, $lhs);
//                 test_mul_assign_val!(i8, true, $lhs);
//                 test_mul_assign_val!(i16, true, $lhs);
//                 test_mul_assign_val!(i32, true, $lhs);
//                 test_mul_assign_val!(f32, true, $lhs);
//                 test_mul_assign_val!(f64, true, $lhs);
//             }
//         };
//     }

//     fn_test_mul_assign_val!(test_mul_assign_did_val, did);
//     fn_test_mul_assign_val!(test_mul_assign_did_t_val, did_t);

//     fn_test_mul_assign!(test_mul_assign_did_rmd, did, rmd);
//     fn_test_mul_assign!(test_mul_assign_did_cmd, did, cmd);
//     fn_test_mul_assign!(test_mul_assign_did_did, did, did);
//     fn_test_mul_assign!(test_mul_assign_did_rmd_t, did, rmd_t);
//     fn_test_mul_assign!(test_mul_assign_did_cmd_t, did, cmd_t);
//     fn_test_mul_assign!(test_mul_assign_did_did_t, did, did_t);

//     fn_test_mul_assign!(test_mul_assign_did_t_rmd, did_t, rmd);
//     fn_test_mul_assign!(test_mul_assign_did_t_cmd, did_t, cmd);
//     fn_test_mul_assign!(test_mul_assign_did_t_did, did_t, did);
//     fn_test_mul_assign!(test_mul_assign_did_t_rmd_t, did_t, rmd_t);
//     fn_test_mul_assign!(test_mul_assign_did_t_cmd_t, did_t, cmd_t);
//     fn_test_mul_assign!(test_mul_assign_did_t_did_t, did_t, did_t);

//     fn_test_mul_assign_simd_val!(test_mul_assign_simd_did_val, did);
//     fn_test_mul_assign_simd_val!(test_mul_assign_simd_did_t_val, did_t);

//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_rmd, did, rmd);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_cmd, did, cmd);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_did, did, did);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_rmd_t, did, rmd_t);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_cmd_t, did, cmd_t);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_did_t, did, did_t);

//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_rmd, did_t, rmd);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_cmd, did_t, cmd);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_did, did_t, did);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_rmd_t, did_t, rmd_t);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_cmd_t, did_t, cmd_t);
//     fn_test_mul_assign_simd!(test_mul_assign_simd_did_t_did_t, did_t, did_t);
// }
