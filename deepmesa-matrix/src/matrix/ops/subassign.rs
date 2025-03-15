use crate::matrix::macros::*;
use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::traits::MatrixElement;

impl<T> std::ops::SubAssign<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: T) {
        dispatch_mut!(self, ds, ds.sub_assign(rhs));
    }
}

impl<T> std::ops::SubAssign<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: &Matrix<T>) {
        shape_check!(self, rhs);
        dispatch_mut!(self, ds, dispatch!(rhs, rhs, ds.sub_assign(rhs)));
    }
}

// #[cfg(test)]
// mod tests {
//     use crate::matrix::matrix::matrix;
//     use crate::matrix::matrix::matrix_simd;
//     use crate::matrix::matrix::Matrix;
//     use crate::matrix::matrix::MatrixData;
//     use crate::matrix::matrix::MatrixType;
//     use crate::matrix::traits::*;
//     use std::ops::SubAssign;

//     macro_rules! m_lhs {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 10,20,30;40,50,60);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 10,20,30;40,50,60);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }
//     macro_rules! m_lhs_t {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 3,2], 10,40;20,50;30,60);
//                 m.set_simd_enabled(false);
//                 m.transpose();
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 3,2], 10,40;20,50;30,60);
//                 m.set_simd_enabled(false);
//                 m.transpose();
//                 m
//             }
//         };
//     }

//     macro_rules! lhs {
//         (rm, $t:ty) => {
//             m_lhs!(rm, $t)
//         };
//         (rm, simd, $t:ty) => {
//             m_lhs!(simd, rm, $t)
//         };
//         (rm_t, $t:ty) => {
//             m_lhs_t!(rm, $t)
//         };
//         (rm_t, simd, $t:ty) => {
//             m_lhs_t!(simd, rm, $t)
//         };
//         (cm, $t:ty) => {
//             m_lhs!(cm, $t)
//         };
//         (cm, simd, $t:ty) => {
//             m_lhs!(simd, cm, $t)
//         };
//         (cm_t, $t:ty) => {
//             m_lhs_t!(cm, $t)
//         };
//         (cm_t, simd, $t:ty) => {
//             m_lhs_t!(simd, cm, $t)
//         };
//         (di, $t:ty) => {
//             m_lhs!(di, $t)
//         };
//         (di, simd, $t:ty) => {
//             m_lhs!(simd, di, $t)
//         };
//         (di_t, $t:ty) => {
//             m_lhs_t!(di, $t)
//         };
//         (di_t, simd, $t:ty) => {
//             m_lhs_t!(simd, di, $t)
//         };
//     }

//     macro_rules! m_rhs {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 3,4,5;6,7,8);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 3,4,5;6,7,8);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }

//     macro_rules! m_rhs_t {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 3,2], 3,6;4,7;5,8);
//                 m.set_simd_enabled(false);
//                 m.transpose();
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 3,2], 3,6;4,7;5,8);
//                 m.set_simd_enabled(true);
//                 m.transpose();
//                 m
//             }
//         };
//     }

//     macro_rules! rhs {
//         (rm, $t:ty) => {
//             m_rhs!(rm, $t)
//         };
//         (rm_t, $t:ty) => {
//             m_rhs_t!(rm, $t)
//         };
//         (cm, $t:ty) => {
//             m_rhs!(cm, $t)
//         };
//         (cm_t, $t:ty) => {
//             m_rhs_t!(cm, $t)
//         };
//         (di, $t:ty) => {
//             m_rhs!(di, $t)
//         };
//         (di_t, $t:ty) => {
//             m_rhs_t!(di, $t)
//         };
//         //
//         (rm, simd, $t:ty) => {
//             m_rhs!(simd, rm, $t)
//         };
//         (rm_t, simd, $t:ty) => {
//             m_rhs_t!(simd, rm, $t)
//         };
//         (cm, simd,$t:ty) => {
//             m_rhs!(simd, cm, $t)
//         };
//         (cm_t, simd, $t:ty) => {
//             m_rhs_t!(simd, cm, $t)
//         };
//         (di, simd, $t:ty) => {
//             m_rhs!(simd, di, $t)
//         };
//         (di_t, simd, $t:ty) => {
//             m_rhs_t!(simd, di, $t)
//         };
//     }

//     macro_rules! m_res {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 7,16,25;34,43,52);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 7,16,25;34,43,52);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }

//     macro_rules! m_res_val {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 5,15,25;35,45,55);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 5,15,25;35,45,55);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }

//     macro_rules! result {
//         (rm, $t:ty) => {
//             m_res!(rm, $t)
//         };
//         (rm_t, $t:ty) => {
//             m_res!(rm, $t)
//         };
//         (cm, $t:ty) => {
//             m_res!(cm, $t)
//         };
//         (cm_t, $t:ty) => {
//             m_res!(cm, $t)
//         };
//         (di, $t:ty) => {
//             m_res!(di, $t)
//         };
//         (di_t, $t:ty) => {
//             m_res!(di, $t)
//         };
//         (val, rm, $t:ty) => {
//             m_res_val!(rm, $t)
//         };
//         (val, rm_t, $t:ty) => {
//             m_res_val!(rm, $t)
//         };
//         (val, cm, $t:ty) => {
//             m_res_val!(cm, $t)
//         };
//         (val, cm_t, $t:ty) => {
//             m_res_val!(cm, $t)
//         };
//         (val, di, $t:ty) => {
//             m_res_val!(di, $t)
//         };
//         (val, di_t, $t:ty) => {
//             m_res_val!(di, $t)
//         };
//         //
//         (rm, simd, $t:ty) => {
//             m_res!(simd, rm, $t)
//         };
//         (rm_t, simd, $t:ty) => {
//             m_res!(simd, rm, $t)
//         };
//         (cm, simd, $t:ty) => {
//             m_res!(simd, cm, $t)
//         };
//         (cm_t, simd, $t:ty) => {
//             m_res!(simd, cm, $t)
//         };
//         (di, simd, $t:ty) => {
//             m_res!(simd, di, $t)
//         };
//         (di_t, simd, $t:ty) => {
//             m_res!(simd, di, $t)
//         };
//         (val, simd, rm, $t:ty) => {
//             m_res_val!(simd, rm, $t)
//         };
//         (val, simd, rm_t, $t:ty) => {
//             m_res_val!(simd, rm, $t)
//         };
//         (val, simd, cm, $t:ty) => {
//             m_res_val!(simd, cm, $t)
//         };
//         (val, simd, cm_t, $t:ty) => {
//             m_res_val!(simd, cm, $t)
//         };
//         (val, simd, di, $t:ty) => {
//             m_res_val!(simd, di, $t)
//         };
//         (val, simd, di_t, $t:ty) => {
//             m_res_val!(simd, di, $t)
//         };
//     }

//     macro_rules! test_sub_assign_val {
//         ($lhs: ident, $t:ty) => {
//             let mut lhs = lhs!($lhs, $t);
//             let rhs = 5 as $t;
//             lhs.sub_assign(rhs);
//             assert_eq!(lhs, result!(val, $lhs, $t));

//             let mut lhs = lhs!($lhs, simd, $t);
//             let rhs = 5 as $t;
//             lhs.sub_assign(rhs);
//             assert_eq!(lhs, result!(val, simd, $lhs, $t));
//         };
//     }

//     macro_rules! fn_test_sub_assign_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_sub_assign_val!($lhs, u8);
//                 test_sub_assign_val!($lhs, u16);
//                 test_sub_assign_val!($lhs, u32);
//                 test_sub_assign_val!($lhs, u64);
//                 test_sub_assign_val!($lhs, u128);
//                 test_sub_assign_val!($lhs, i8);
//                 test_sub_assign_val!($lhs, i16);
//                 test_sub_assign_val!($lhs, i32);
//                 test_sub_assign_val!($lhs, i64);
//                 test_sub_assign_val!($lhs, i128);
//                 test_sub_assign_val!($lhs, f32);
//                 test_sub_assign_val!($lhs, f64);
//             }
//         };
//     }

//     macro_rules! test_sub_assign {
//         ($lhs: ident, $rhs:ident, $t:ty) => {
//             let mut lhs = lhs!($lhs, $t);
//             let rhs = rhs!($rhs, $t);
//             lhs.sub_assign(&rhs);
//             assert_eq!(lhs, result!($lhs, $t));

//             let mut lhs = lhs!($lhs, simd, $t);
//             let rhs = rhs!($rhs, simd, $t);
//             lhs.sub_assign(&rhs);
//             assert_eq!(lhs, result!($lhs, simd, $t));
//         };
//     }

//     macro_rules! fn_test_sub_assign {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_sub_assign!($lhs, $rhs, u8);
//                 //     test_sub_assign!($lhs, $rhs, u16);
//                 //     test_sub_assign!($lhs, $rhs, u32);
//                 //     test_sub_assign!($lhs, $rhs, u64);
//                 //     test_sub_assign!($lhs, $rhs, u128);
//                 //     test_sub_assign!($lhs, $rhs, i8);
//                 //     test_sub_assign!($lhs, $rhs, i16);
//                 //     test_sub_assign!($lhs, $rhs, i32);
//                 //     test_sub_assign!($lhs, $rhs, i64);
//                 //     test_sub_assign!($lhs, $rhs, i128);
//                 //     test_sub_assign!($lhs, $rhs, f32);
//                 //     test_sub_assign!($lhs, $rhs, f64);
//             }
//         };
//     }

//     fn_test_sub_assign_val!(test_sub_assign_val_rm, rm);
//     fn_test_sub_assign_val!(test_sub_assign_val_cm, cm);
//     fn_test_sub_assign_val!(test_sub_assign_val_di, di);

//     fn_test_sub_assign_val!(test_sub_assign_val_rm_t, rm_t);
//     fn_test_sub_assign_val!(test_sub_assign_val_cm_t, cm_t);
//     fn_test_sub_assign_val!(test_sub_assign_val_di_t, di_t);

//     ///
//     fn_test_sub_assign!(test_sub_assign_rm_rm, rm, rm);
//     fn_test_sub_assign!(test_sub_assign_rm_cm, rm, cm);
//     fn_test_sub_assign!(test_sub_assign_rm_di, rm, di);

//     fn_test_sub_assign!(test_sub_assign_rm_rm_t, rm, rm_t);
//     fn_test_sub_assign!(test_sub_assign_rm_cm_t, rm, cm_t);
//     fn_test_sub_assign!(test_sub_assign_rm_di_t, rm, di_t);

//     fn_test_sub_assign!(test_sub_assign_rm_t_rm, rm_t, rm);
//     fn_test_sub_assign!(test_sub_assign_rm_t_cm, rm_t, cm);
//     fn_test_sub_assign!(test_sub_assign_rm_t_di, rm_t, di);

//     fn_test_sub_assign!(test_sub_assign_rm_t_rm_t, rm_t, rm_t);
//     fn_test_sub_assign!(test_sub_assign_rm_t_cm_t, rm_t, cm_t);
//     fn_test_sub_assign!(test_sub_assign_rm_t_di_t, rm_t, di_t);

//     // ///////////
//     fn_test_sub_assign!(test_sub_assign_cm_rm, cm, rm);
//     fn_test_sub_assign!(test_sub_assign_cm_cm, cm, cm);
//     fn_test_sub_assign!(test_sub_assign_cm_di, cm, di);

//     fn_test_sub_assign!(test_sub_assign_cm_rm_t, cm, rm_t);
//     fn_test_sub_assign!(test_sub_assign_cm_cm_t, cm, cm_t);
//     fn_test_sub_assign!(test_sub_assign_cm_di_t, cm, di_t);

//     fn_test_sub_assign!(test_sub_assign_cm_t_rm, cm_t, rm);
//     fn_test_sub_assign!(test_sub_assign_cm_t_cm, cm_t, cm);
//     fn_test_sub_assign!(test_sub_assign_cm_t_di, cm_t, di);

//     fn_test_sub_assign!(test_sub_assign_cm_t_rm_t, cm_t, rm_t);
//     fn_test_sub_assign!(test_sub_assign_cm_t_cm_t, cm_t, cm_t);
//     fn_test_sub_assign!(test_sub_assign_cm_t_di_t, cm_t, di_t);

//     // ///////////
//     fn_test_sub_assign!(test_sub_assign_di_rm, di, rm);
//     fn_test_sub_assign!(test_sub_assign_di_cm, di, cm);
//     fn_test_sub_assign!(test_sub_assign_di_di, di, di);

//     fn_test_sub_assign!(test_sub_assign_di_rm_t, di, rm_t);
//     fn_test_sub_assign!(test_sub_assign_di_cm_t, di, cm_t);
//     fn_test_sub_assign!(test_sub_assign_di_di_t, di, di_t);

//     fn_test_sub_assign!(test_sub_assign_di_t_rm, di_t, rm);
//     fn_test_sub_assign!(test_sub_assign_di_t_cm, di_t, cm);
//     fn_test_sub_assign!(test_sub_assign_di_t_di, di_t, di);

//     fn_test_sub_assign!(test_sub_assign_di_t_rm_t, di_t, rm_t);
//     fn_test_sub_assign!(test_sub_assign_di_t_cm_t, di_t, cm_t);
//     fn_test_sub_assign!(test_sub_assign_di_t_di_t, di_t, di_t);
// }
