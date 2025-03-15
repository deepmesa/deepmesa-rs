use crate::matrix::macros::*;
use crate::matrix::matrix::Matrix;
use crate::matrix::traits::AddInto;
use crate::matrix::traits::MatrixElement;
use std::ops::AddAssign;

impl<T> std::ops::Add<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(mut self, rhs: T) -> Matrix<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> std::ops::Add<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(mut self, rhs: &Matrix<T>) -> Matrix<T> {
        shape_check!(self, rhs);
        self.add_assign(rhs);
        return self;
    }
}

impl<T> std::ops::Add<T> for &Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(self, rhs: T) -> Matrix<T> {
        let mut result = Matrix::new(self.rows, self.cols, self.m_type, self.is_simd_optimized());
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> std::ops::Add<&Matrix<T>> for &Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = Matrix<T>;
    fn add(self, rhs: &Matrix<T>) -> Matrix<T> {
        shape_check!(self, rhs);
        let mut result = Matrix::new(self.rows, self.cols, self.m_type, self.is_simd_optimized());
        self.add_into(rhs, &mut result);
        return result;
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
//     use std::ops::Add;

//     macro_rules! m_lhs {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 1,2,3;4,5,6);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 1,2,3;4,5,6);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }
//     macro_rules! m_lhs_t {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 3,2], 1,4;2,5;3,6);
//                 m.set_simd_enabled(false);
//                 m.transpose();
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 3,2], 1,4;2,5;3,6);
//                 m.set_simd_enabled(true);
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
//                 let mut m = matrix!($layout, [$t, 2, 3], 11,12,13;14,15,16);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 11,12,13;14,15,16);
//                 m.set_simd_enabled(true);
//                 m
//             }
//         };
//     }

//     macro_rules! m_rhs_t {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 3,2], 11,14;12,15;13,16);
//                 m.set_simd_enabled(false);
//                 m.transpose();
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 3,2], 11,14;12,15;13,16);
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
//                 let mut m = matrix!($layout, [$t, 2, 3], 12,14,16;18,20,22);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 12,14,16;18,20,22);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//     }

//     macro_rules! m_res_val {
//         ($layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix!($layout, [$t, 2, 3], 5,6,7;8,9,10);
//                 m.set_simd_enabled(false);
//                 m
//             }
//         };
//         (simd, $layout:ident, $t:ty) => {
//             {
//                 let mut m = matrix_simd!($layout, [$t, 2, 3], 5,6,7;8,9,10);
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

//     macro_rules! test_add {
//         ($lhs: ident, $rhs:ident, $t:ty) => {
//             let lhs = lhs!($lhs, $t);
//             let rhs = rhs!($rhs, $t);
//             let out = lhs.add(&rhs);
//             assert_eq!(out, result!($lhs, $t));

//             let lhs = lhs!($lhs, simd, $t);
//             let rhs = rhs!($rhs, simd, $t);
//             let out = lhs.add(&rhs);
//             assert_eq!(out, result!($lhs, simd, $t));
//         };
//     }

//     macro_rules! test_add_val {
//         ($lhs: ident, $t:ty) => {
//             let lhs = lhs!($lhs, $t);
//             let rhs = 4 as $t;
//             let out = lhs.add(rhs);
//             assert_eq!(out, result!(val, $lhs, $t));

//             let lhs = lhs!($lhs, simd, $t);
//             let rhs = 4 as $t;
//             let out = lhs.add(rhs);
//             assert_eq!(out, result!(val, simd, $lhs, $t));
//         };
//     }

//     macro_rules! fn_test_add {
//         ($fn_name:ident, $lhs:ident, $rhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add!($lhs, $rhs, u8);
//                 test_add!($lhs, $rhs, u16);
//                 test_add!($lhs, $rhs, u32);
//                 test_add!($lhs, $rhs, u64);
//                 test_add!($lhs, $rhs, u128);
//                 test_add!($lhs, $rhs, i8);
//                 test_add!($lhs, $rhs, i16);
//                 test_add!($lhs, $rhs, i32);
//                 test_add!($lhs, $rhs, i64);
//                 test_add!($lhs, $rhs, i128);
//                 test_add!($lhs, $rhs, f32);
//                 test_add!($lhs, $rhs, f64);
//             }
//         };
//     }

//     macro_rules! fn_test_add_val {
//         ($fn_name:ident, $lhs:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_add_val!($lhs, u8);
//                 test_add_val!($lhs, u16);
//                 test_add_val!($lhs, u32);
//                 test_add_val!($lhs, u64);
//                 test_add_val!($lhs, u128);
//                 test_add_val!($lhs, i8);
//                 test_add_val!($lhs, i16);
//                 test_add_val!($lhs, i32);
//                 test_add_val!($lhs, i64);
//                 test_add_val!($lhs, i128);
//                 test_add_val!($lhs, f32);
//                 test_add_val!($lhs, f64);
//             }
//         };
//     }

//     fn_test_add_val!(test_add_val_rm, rm);
//     fn_test_add_val!(test_add_val_cm, cm);
//     fn_test_add_val!(test_add_val_di, di);

//     fn_test_add_val!(test_add_val_rm_t, rm_t);
//     fn_test_add_val!(test_add_val_cm_t, cm_t);
//     fn_test_add_val!(test_add_val_di_t, di_t);

//     fn_test_add!(test_add_rm_rm, rm, rm);
//     fn_test_add!(test_add_rm_cm, rm, cm);
//     fn_test_add!(test_add_rm_di, rm, di);

//     fn_test_add!(test_add_rm_rm_t, rm, rm_t);
//     fn_test_add!(test_add_rm_cm_t, rm, cm_t);
//     fn_test_add!(test_add_rm_di_t, rm, di_t);

//     fn_test_add!(test_add_rm_t_rm, rm_t, rm);
//     fn_test_add!(test_add_rm_t_cm, rm_t, cm);
//     fn_test_add!(test_add_rm_t_di, rm_t, di);

//     fn_test_add!(test_add_rm_t_rm_t, rm_t, rm_t);
//     fn_test_add!(test_add_rm_t_cm_t, rm_t, cm_t);
//     fn_test_add!(test_add_rm_t_di_t, rm_t, di_t);

//     //
//     fn_test_add!(test_add_cm_rm, cm, rm);
//     fn_test_add!(test_add_cm_cm, cm, cm);
//     fn_test_add!(test_add_cm_di, cm, di);

//     fn_test_add!(test_add_cm_rm_t, cm, rm_t);
//     fn_test_add!(test_add_cm_cm_t, cm, cm_t);
//     fn_test_add!(test_add_cm_di_t, cm, di_t);

//     fn_test_add!(test_add_cm_t_rm, cm_t, rm);
//     fn_test_add!(test_add_cm_t_cm, cm_t, cm);
//     fn_test_add!(test_add_cm_t_di, cm_t, di);

//     fn_test_add!(test_add_cm_t_rm_t, cm_t, rm_t);
//     fn_test_add!(test_add_cm_t_cm_t, cm_t, cm_t);
//     fn_test_add!(test_add_cm_t_di_t, cm_t, di_t);

//     //
//     fn_test_add!(test_add_di_rm, di, rm);
//     fn_test_add!(test_add_di_cm, di, cm);
//     fn_test_add!(test_add_di_di, di, di);

//     fn_test_add!(test_add_di_rm_t, di, rm_t);
//     fn_test_add!(test_add_di_cm_t, di, cm_t);
//     fn_test_add!(test_add_di_di_t, di, di_t);

//     fn_test_add!(test_add_di_t_rm, di_t, rm);
//     fn_test_add!(test_add_di_t_cm, di_t, cm);
//     fn_test_add!(test_add_di_t_di, di_t, di);

//     fn_test_add!(test_add_di_t_rm_t, di_t, rm_t);
//     fn_test_add!(test_add_di_t_cm_t, di_t, cm_t);
//     fn_test_add!(test_add_di_t_di_t, di_t, di_t);
// }
