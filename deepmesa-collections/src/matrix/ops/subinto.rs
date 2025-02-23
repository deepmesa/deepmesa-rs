use crate::matrix::did::data::SyncDirection;
use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::ops::macros::dispatch;
use crate::matrix::ops::macros::dispatch_mut;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::traits::{MatrixElement, SubInto};

impl<T> SubInto<T, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut Matrix<T>) {
        dispatch!(
            self,
            ds,
            dispatch_mut!(result, result, ds.sub_into(rhs, result))
        );
    }
}

impl<T> SubInto<&Matrix<T>, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &Matrix<T>, result: &mut Matrix<T>) {
        shape_check!(self, rhs);
        shape_check!(self, result);

        dispatch!(
            self,
            ds,
            dispatch_mut!(
                result,
                result,
                dispatch!(rhs, rhs, ds.sub_into(rhs, result))
            )
        );
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::matrix::matrix;
    use crate::matrix::matrix::matrix_simd;
    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixData;
    use crate::matrix::matrix::MatrixType;
    use crate::matrix::traits::*;
    use std::ops::SubAssign;

    macro_rules! m_lhs {
        ($layout:ident, $t:ty) => {
            {
                let mut m = matrix!($layout, [$t, 2, 3], 10,20,30;40,50,60);
                m.set_simd_enabled(false);
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 2, 3], 10,20,30;40,50,60);
                m.set_simd_enabled(true);
                m
            }
        };
    }
    macro_rules! m_lhs_t {
        ($layout:ident, $t:ty) => {
            {
                let mut m = matrix!($layout, [$t, 3,2], 10,40;20,50;30,60);
                m.set_simd_enabled(false);
                m.transpose();
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 3,2], 10,40;20,50;30,60);
                m.set_simd_enabled(true);
                m.transpose();
                m
            }
        };
    }

    macro_rules! lhs {
        (rm, $t:ty) => {
            m_lhs!(rm, $t)
        };
        (rm, simd, $t:ty) => {
            m_lhs!(simd, rm, $t)
        };
        (rm_t, $t:ty) => {
            m_lhs_t!(rm, $t)
        };
        (rm_t, simd, $t:ty) => {
            m_lhs_t!(simd, rm, $t)
        };
        (cm, $t:ty) => {
            m_lhs!(cm, $t)
        };
        (cm, simd, $t:ty) => {
            m_lhs!(simd, cm, $t)
        };
        (cm_t, $t:ty) => {
            m_lhs_t!(cm, $t)
        };
        (cm_t, simd, $t:ty) => {
            m_lhs_t!(simd, cm, $t)
        };
        (di, $t:ty) => {
            m_lhs!(di, $t)
        };
        (di, simd, $t:ty) => {
            m_lhs!(simd, di, $t)
        };
        (di_t, $t:ty) => {
            m_lhs_t!(di, $t)
        };
        (di_t, simd, $t:ty) => {
            m_lhs_t!(simd, di, $t)
        };
    }

    macro_rules! m_rhs {
        ($layout:ident, $t:ty) => {
            {
                let mut m = matrix!($layout, [$t, 2, 3], 2,4,6;8,10,12);
                m.set_simd_enabled(false);
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 2, 3], 2,4,6;8,10,12);
                m.set_simd_enabled(true);
                m
            }
        };
    }

    macro_rules! m_rhs_t {
        ($layout:ident, $t:ty) => {
            {
                let mut m = matrix!($layout, [$t, 3,2], 2,8;4,10;6,12);
                m.set_simd_enabled(false);
                m.transpose();
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 3,2], 2,8;4,10;6,12);
                m.set_simd_enabled(true);
                m.transpose();
                m
            }
        };
    }

    macro_rules! rhs {
        (rm, $t:ty) => {
            m_rhs!(rm, $t)
        };
        (rm_t, $t:ty) => {
            m_rhs_t!(rm, $t)
        };
        (cm, $t:ty) => {
            m_rhs!(cm, $t)
        };
        (cm_t, $t:ty) => {
            m_rhs_t!(cm, $t)
        };
        (di, $t:ty) => {
            m_rhs!(di, $t)
        };
        (di_t, $t:ty) => {
            m_rhs_t!(di, $t)
        };
        //
        (rm, simd, $t:ty) => {
            m_rhs!(simd, rm, $t)
        };
        (rm_t, simd, $t:ty) => {
            m_rhs_t!(simd, rm, $t)
        };
        (cm, simd,$t:ty) => {
            m_rhs!(simd, cm, $t)
        };
        (cm_t, simd, $t:ty) => {
            m_rhs_t!(simd, cm, $t)
        };
        (di, simd, $t:ty) => {
            m_rhs!(simd, di, $t)
        };
        (di_t, simd, $t:ty) => {
            m_rhs_t!(simd, di, $t)
        };
    }

    macro_rules! m_res {
        ($layout:ident, $t:ty) => {
            {
                let mut m = matrix!($layout, [$t, 2, 3], 8,16,24;32,40,48);
                m.set_simd_enabled(false);
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 2, 3], 8,16,24;32,40,48);
                m.set_simd_enabled(true);
                m
            }
        };
    }

    macro_rules! m_res_val {
        ($layout:ident, $t:ty) => {
            {
                let mut m  =  matrix!($layout, [$t, 2, 3], 6,16,26;36,46,56);
                m.set_simd_enabled(false);
                m
            }
        };
        (simd, $layout:ident, $t:ty) => {
            {
                let mut m = matrix_simd!($layout, [$t, 2, 3], 6,16,26;36,46,56);
                m.set_simd_enabled(true);
                m
            }
        };
    }

    macro_rules! out {
        (rm, $simd:ident, $t:ty) => {
            Matrix::<$t>::new(2, 3, MatrixType::RowMajor, $simd)
        };
        (rm_t, $simd:ident, $t:ty) => {{
            let mut m = Matrix::<$t>::new(3, 2, MatrixType::RowMajor, $simd);
            m.transpose();
            m
        }};
        (cm, $simd:ident, $t:ty) => {
            Matrix::<$t>::new(2, 3, MatrixType::ColMajor, $simd)
        };
        (cm_t, $simd:ident, $t:ty) => {{
            let mut m = Matrix::<$t>::new(3, 2, MatrixType::ColMajor, $simd);
            m.transpose();
            m
        }};
        (di, $simd:ident, $t:ty) => {
            Matrix::<$t>::new(2, 3, MatrixType::DualIndex, $simd)
        };
        (di_t, $simd:ident, $t:ty) => {{
            let mut m = Matrix::<$t>::new(3, 2, MatrixType::DualIndex, $simd);
            m.transpose();
            m
        }};
    }

    macro_rules! result {
        (rm, $t:ty) => {
            m_res!(rm, $t)
        };
        (rm_t, $t:ty) => {
            m_res!(rm, $t)
        };
        (cm, $t:ty) => {
            m_res!(cm, $t)
        };
        (cm_t, $t:ty) => {
            m_res!(cm, $t)
        };
        (di, $t:ty) => {
            m_res!(di, $t)
        };
        (di_t, $t:ty) => {
            m_res!(di, $t)
        };
        (val, rm, $t:ty) => {
            m_res_val!(rm, $t)
        };
        (val, rm_t, $t:ty) => {
            m_res_val!(rm, $t)
        };
        (val, cm, $t:ty) => {
            m_res_val!(cm, $t)
        };
        (val, cm_t, $t:ty) => {
            m_res_val!(cm, $t)
        };
        (val, di, $t:ty) => {
            m_res_val!(di, $t)
        };
        (val, di_t, $t:ty) => {
            m_res_val!(di, $t)
        };
        //
        (rm, simd, $t:ty) => {
            m_res!(simd, rm, $t)
        };
        (rm_t, simd, $t:ty) => {
            m_res!(simd, rm, $t)
        };
        (cm, simd, $t:ty) => {
            m_res!(simd, cm, $t)
        };
        (cm_t, simd, $t:ty) => {
            m_res!(simd, cm, $t)
        };
        (di, simd, $t:ty) => {
            m_res!(simd, di, $t)
        };
        (di_t, simd, $t:ty) => {
            m_res!(simd, di, $t)
        };
        (val, simd, rm, $t:ty) => {
            m_res_val!(simd, rm, $t)
        };
        (val, simd, rm_t, $t:ty) => {
            m_res_val!(simd, rm, $t)
        };
        (val, simd, cm, $t:ty) => {
            m_res_val!(simd, cm, $t)
        };
        (val, simd, cm_t, $t:ty) => {
            m_res_val!(simd, cm, $t)
        };
        (val, simd, di, $t:ty) => {
            m_res_val!(simd, di, $t)
        };
        (val, simd, di_t, $t:ty) => {
            m_res_val!(simd, di, $t)
        };
    }

    macro_rules! test_sub_into_val {
        ($lhs: ident, $out:ident, $t:ty) => {
            let lhs = lhs!($lhs, $t);
            let rhs = 4 as $t;
            let mut out = out!($out, false, $t);
            lhs.sub_into(rhs, &mut out);
            assert_eq!(out, result!(val, $lhs, $t));

            let lhs = lhs!($lhs, simd, $t);
            let rhs = 4 as $t;
            let mut out = out!($out, true, $t);
            lhs.sub_into(rhs, &mut out);
            assert_eq!(out, result!(val, simd, $lhs, $t));
        };
    }

    macro_rules! fn_test_sub_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!($lhs, $out, u8);
                test_sub_into_val!($lhs, $out, u16);
                test_sub_into_val!($lhs, $out, u32);
                test_sub_into_val!($lhs, $out, u64);
                test_sub_into_val!($lhs, $out, u128);
                test_sub_into_val!($lhs, $out, i8);
                test_sub_into_val!($lhs, $out, i16);
                test_sub_into_val!($lhs, $out, i32);
                test_sub_into_val!($lhs, $out, i64);
                test_sub_into_val!($lhs, $out, i128);
                test_sub_into_val!($lhs, $out, f32);
                test_sub_into_val!($lhs, $out, f64);
            }
        };
    }

    macro_rules! test_sub_into {
        ($lhs: ident, $rhs:ident, $out:ident, $t:ty) => {
            let lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            let mut out = out!($out, false, $t);
            lhs.sub_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $t));

            let lhs = lhs!($lhs, simd, $t);
            let rhs = rhs!($rhs, simd, $t);
            let mut out = out!($out, true, $t);
            lhs.sub_into(&rhs, &mut out);
            assert_eq!(out, result!($out, simd, $t));
        };
    }

    macro_rules! fn_test_sub_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!($lhs, $rhs, $out, u8);
                test_sub_into!($lhs, $rhs, $out, u16);
                test_sub_into!($lhs, $rhs, $out, u32);
                test_sub_into!($lhs, $rhs, $out, u64);
                test_sub_into!($lhs, $rhs, $out, u128);
                test_sub_into!($lhs, $rhs, $out, i8);
                test_sub_into!($lhs, $rhs, $out, i16);
                test_sub_into!($lhs, $rhs, $out, i32);
                test_sub_into!($lhs, $rhs, $out, i64);
                test_sub_into!($lhs, $rhs, $out, i128);
                test_sub_into!($lhs, $rhs, $out, f32);
                test_sub_into!($lhs, $rhs, $out, f64);
            }
        };
    }

    fn_test_sub_into_val!(test_sub_into_val_rm_rm, rm, rm);
    fn_test_sub_into_val!(test_sub_into_val_rm_cm, rm, cm);
    fn_test_sub_into_val!(test_sub_into_val_rm_di, rm, di);

    fn_test_sub_into_val!(test_sub_into_val_rm_rm_t, rm, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_rm_cm_t, rm, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_rm_di_t, rm, di_t);

    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm, rm_t, rm);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_cm, rm_t, cm);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_di, rm_t, di);

    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm_t, rm_t, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_cm_t, rm_t, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_di_t, rm_t, di_t);

    /////
    fn_test_sub_into_val!(test_sub_into_val_cm_rm, cm, rm);
    fn_test_sub_into_val!(test_sub_into_val_cm_cm, cm, cm);
    fn_test_sub_into_val!(test_sub_into_val_cm_di, cm, di);

    fn_test_sub_into_val!(test_sub_into_val_cm_rm_t, cm, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_cm_cm_t, cm, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_cm_di_t, cm, di_t);

    fn_test_sub_into_val!(test_sub_into_val_cm_t_rm, cm_t, rm);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_cm, cm_t, cm);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_di, cm_t, di);

    fn_test_sub_into_val!(test_sub_into_val_cm_t_rm_t, cm_t, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_cm_t, cm_t, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_di_t, cm_t, di_t);

    /////
    fn_test_sub_into_val!(test_sub_into_val_di_rm, di, rm);
    fn_test_sub_into_val!(test_sub_into_val_di_cm, di, cm);
    fn_test_sub_into_val!(test_sub_into_val_di_di, di, di);

    fn_test_sub_into_val!(test_sub_into_val_di_rm_t, di, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_di_cm_t, di, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_di_di_t, di, di_t);

    fn_test_sub_into_val!(test_sub_into_val_di_t_rm, di_t, rm);
    fn_test_sub_into_val!(test_sub_into_val_di_t_cm, di_t, cm);
    fn_test_sub_into_val!(test_sub_into_val_di_t_di, di_t, di);

    fn_test_sub_into_val!(test_sub_into_val_di_t_rm_t, di_t, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_di_t_cm_t, di_t, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_di_t_di_t, di_t, di_t);

    ///////
    fn_test_sub_into!(test_sub_into_rm_rm_rm, rm, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_cm, rm, rm, cm);
    fn_test_sub_into!(test_sub_into_rm_rm_di, rm, rm, di);

    fn_test_sub_into!(test_sub_into_rm_rm_rm_t, rm, rm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_cm_t, rm, rm, cm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_di_t, rm, rm, di_t);

    fn_test_sub_into!(test_sub_into_rm_cm_rm, rm, cm, rm);
    fn_test_sub_into!(test_sub_into_rm_cm_cm, rm, cm, cm);
    fn_test_sub_into!(test_sub_into_rm_cm_di, rm, cm, di);

    fn_test_sub_into!(test_sub_into_rm_cm_rm_t, rm, cm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_cm_cm_t, rm, cm, cm_t);
    fn_test_sub_into!(test_sub_into_rm_cm_di_t, rm, cm, di_t);

    fn_test_sub_into!(test_sub_into_rm_di_rm, rm, di, rm);
    fn_test_sub_into!(test_sub_into_rm_di_cm, rm, di, cm);
    fn_test_sub_into!(test_sub_into_rm_di_di, rm, di, di);

    fn_test_sub_into!(test_sub_into_rm_di_rm_t, rm, di, rm_t);
    fn_test_sub_into!(test_sub_into_rm_di_cm_t, rm, di, cm_t);
    fn_test_sub_into!(test_sub_into_rm_di_di_t, rm, di, di_t);

    fn_test_sub_into!(test_sub_into_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_t_cm, rm, rm_t, cm);
    fn_test_sub_into!(test_sub_into_rm_rm_t_di, rm, rm_t, di);

    fn_test_sub_into!(test_sub_into_rm_rm_t_rm_t, rm, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_t_cm_t, rm, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_t_di_t, rm, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_rm_cm_t_rm, rm, cm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_cm_t_cm, rm, cm_t, cm);
    fn_test_sub_into!(test_sub_into_rm_cm_t_di, rm, cm_t, di);

    fn_test_sub_into!(test_sub_into_rm_cm_t_rm_t, rm, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_cm_t_cm_t, rm, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_cm_t_di_t, rm, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_rm_di_t_rm, rm, di_t, rm);
    fn_test_sub_into!(test_sub_into_rm_di_t_cm, rm, di_t, cm);
    fn_test_sub_into!(test_sub_into_rm_di_t_di, rm, di_t, di);

    fn_test_sub_into!(test_sub_into_rm_di_t_rm_t, rm, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_di_t_cm_t, rm, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_di_t_di_t, rm, di_t, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_cm, rm_t, rm, cm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_di, rm_t, rm, di);

    fn_test_sub_into!(test_sub_into_rm_t_rm_rm_t, rm_t, rm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_cm_t, rm_t, rm, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_di_t, rm_t, rm, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_cm_rm, rm_t, cm, rm);
    fn_test_sub_into!(test_sub_into_rm_t_cm_cm, rm_t, cm, cm);
    fn_test_sub_into!(test_sub_into_rm_t_cm_di, rm_t, cm, di);

    fn_test_sub_into!(test_sub_into_rm_t_cm_rm_t, rm_t, cm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_cm_cm_t, rm_t, cm, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_cm_di_t, rm_t, cm, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_di_rm, rm_t, di, rm);
    fn_test_sub_into!(test_sub_into_rm_t_di_cm, rm_t, di, cm);
    fn_test_sub_into!(test_sub_into_rm_t_di_di, rm_t, di, di);

    fn_test_sub_into!(test_sub_into_rm_t_di_rm_t, rm_t, di, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_di_cm_t, rm_t, di, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_di_di_t, rm_t, di, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_cm, rm_t, rm_t, cm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_di, rm_t, rm_t, di);

    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_cm_t, rm_t, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_di_t, rm_t, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_cm_t_rm, rm_t, cm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_t_cm_t_cm, rm_t, cm_t, cm);
    fn_test_sub_into!(test_sub_into_rm_t_cm_t_di, rm_t, cm_t, di);

    fn_test_sub_into!(test_sub_into_rm_t_cm_t_rm_t, rm_t, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_cm_t_cm_t, rm_t, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_cm_t_di_t, rm_t, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_rm_t_di_t_rm, rm_t, di_t, rm);
    fn_test_sub_into!(test_sub_into_rm_t_di_t_cm, rm_t, di_t, cm);
    fn_test_sub_into!(test_sub_into_rm_t_di_t_di, rm_t, di_t, di);

    fn_test_sub_into!(test_sub_into_rm_t_di_t_rm_t, rm_t, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_di_t_cm_t, rm_t, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_rm_t_di_t_di_t, rm_t, di_t, di_t);

    /////////
    fn_test_sub_into!(test_sub_into_cm_rm_rm, cm, rm, rm);
    fn_test_sub_into!(test_sub_into_cm_rm_cm, cm, rm, cm);
    fn_test_sub_into!(test_sub_into_cm_rm_di, cm, rm, di);

    fn_test_sub_into!(test_sub_into_cm_rm_rm_t, cm, rm, rm_t);
    fn_test_sub_into!(test_sub_into_cm_rm_cm_t, cm, rm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_rm_di_t, cm, rm, di_t);

    fn_test_sub_into!(test_sub_into_cm_cm_rm, cm, cm, rm);
    fn_test_sub_into!(test_sub_into_cm_cm_cm, cm, cm, cm);
    fn_test_sub_into!(test_sub_into_cm_cm_di, cm, cm, di);

    fn_test_sub_into!(test_sub_into_cm_cm_rm_t, cm, cm, rm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_cm_t, cm, cm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_di_t, cm, cm, di_t);

    fn_test_sub_into!(test_sub_into_cm_di_rm, cm, di, rm);
    fn_test_sub_into!(test_sub_into_cm_di_cm, cm, di, cm);
    fn_test_sub_into!(test_sub_into_cm_di_di, cm, di, di);

    fn_test_sub_into!(test_sub_into_cm_di_rm_t, cm, di, rm_t);
    fn_test_sub_into!(test_sub_into_cm_di_cm_t, cm, di, cm_t);
    fn_test_sub_into!(test_sub_into_cm_di_di_t, cm, di, di_t);

    fn_test_sub_into!(test_sub_into_cm_rm_t_rm, cm, rm_t, rm);
    fn_test_sub_into!(test_sub_into_cm_rm_t_cm, cm, rm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_rm_t_di, cm, rm_t, di);

    fn_test_sub_into!(test_sub_into_cm_rm_t_rm_t, cm, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_rm_t_cm_t, cm, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_rm_t_di_t, cm, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_cm_cm_t_rm, cm, cm_t, rm);
    fn_test_sub_into!(test_sub_into_cm_cm_t_cm, cm, cm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_cm_t_di, cm, cm_t, di);

    fn_test_sub_into!(test_sub_into_cm_cm_t_rm_t, cm, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_t_cm_t, cm, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_t_di_t, cm, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_cm_di_t_rm, cm, di_t, rm);
    fn_test_sub_into!(test_sub_into_cm_di_t_cm, cm, di_t, cm);
    fn_test_sub_into!(test_sub_into_cm_di_t_di, cm, di_t, di);

    fn_test_sub_into!(test_sub_into_cm_di_t_rm_t, cm, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_di_t_cm_t, cm, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_di_t_di_t, cm, di_t, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_rm_rm, cm_t, rm, rm);
    fn_test_sub_into!(test_sub_into_cm_t_rm_cm, cm_t, rm, cm);
    fn_test_sub_into!(test_sub_into_cm_t_rm_di, cm_t, rm, di);

    fn_test_sub_into!(test_sub_into_cm_t_rm_rm_t, cm_t, rm, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_rm_cm_t, cm_t, rm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_rm_di_t, cm_t, rm, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_cm_rm, cm_t, cm, rm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_cm, cm_t, cm, cm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_di, cm_t, cm, di);

    fn_test_sub_into!(test_sub_into_cm_t_cm_rm_t, cm_t, cm, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_cm_t, cm_t, cm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_di_t, cm_t, cm, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_di_rm, cm_t, di, rm);
    fn_test_sub_into!(test_sub_into_cm_t_di_cm, cm_t, di, cm);
    fn_test_sub_into!(test_sub_into_cm_t_di_di, cm_t, di, di);

    fn_test_sub_into!(test_sub_into_cm_t_di_rm_t, cm_t, di, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_di_cm_t, cm_t, di, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_di_di_t, cm_t, di, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_rm_t_rm, cm_t, rm_t, rm);
    fn_test_sub_into!(test_sub_into_cm_t_rm_t_cm, cm_t, rm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_t_rm_t_di, cm_t, rm_t, di);

    fn_test_sub_into!(test_sub_into_cm_t_rm_t_rm_t, cm_t, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_rm_t_cm_t, cm_t, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_rm_t_di_t, cm_t, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_cm_t_rm, cm_t, cm_t, rm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_cm, cm_t, cm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_di, cm_t, cm_t, di);

    fn_test_sub_into!(test_sub_into_cm_t_cm_t_rm_t, cm_t, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_cm_t, cm_t, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_di_t, cm_t, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_cm_t_di_t_rm, cm_t, di_t, rm);
    fn_test_sub_into!(test_sub_into_cm_t_di_t_cm, cm_t, di_t, cm);
    fn_test_sub_into!(test_sub_into_cm_t_di_t_di, cm_t, di_t, di);

    fn_test_sub_into!(test_sub_into_cm_t_di_t_rm_t, cm_t, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_cm_t_di_t_cm_t, cm_t, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_di_t_di_t, cm_t, di_t, di_t);

    /////////
    fn_test_sub_into!(test_sub_into_di_rm_rm, di, rm, rm);
    fn_test_sub_into!(test_sub_into_di_rm_cm, di, rm, cm);
    fn_test_sub_into!(test_sub_into_di_rm_di, di, rm, di);

    fn_test_sub_into!(test_sub_into_di_rm_rm_t, di, rm, rm_t);
    fn_test_sub_into!(test_sub_into_di_rm_cm_t, di, rm, cm_t);
    fn_test_sub_into!(test_sub_into_di_rm_di_t, di, rm, di_t);

    fn_test_sub_into!(test_sub_into_di_cm_rm, di, cm, rm);
    fn_test_sub_into!(test_sub_into_di_cm_cm, di, cm, cm);
    fn_test_sub_into!(test_sub_into_di_cm_di, di, cm, di);

    fn_test_sub_into!(test_sub_into_di_cm_rm_t, di, cm, rm_t);
    fn_test_sub_into!(test_sub_into_di_cm_cm_t, di, cm, cm_t);
    fn_test_sub_into!(test_sub_into_di_cm_di_t, di, cm, di_t);

    fn_test_sub_into!(test_sub_into_di_di_rm, di, di, rm);
    fn_test_sub_into!(test_sub_into_di_di_cm, di, di, cm);
    fn_test_sub_into!(test_sub_into_di_di_di, di, di, di);

    fn_test_sub_into!(test_sub_into_di_di_rm_t, di, di, rm_t);
    fn_test_sub_into!(test_sub_into_di_di_cm_t, di, di, cm_t);
    fn_test_sub_into!(test_sub_into_di_di_di_t, di, di, di_t);

    fn_test_sub_into!(test_sub_into_di_rm_t_rm, di, rm_t, rm);
    fn_test_sub_into!(test_sub_into_di_rm_t_cm, di, rm_t, cm);
    fn_test_sub_into!(test_sub_into_di_rm_t_di, di, rm_t, di);

    fn_test_sub_into!(test_sub_into_di_rm_t_rm_t, di, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_rm_t_cm_t, di, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_rm_t_di_t, di, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_di_cm_t_rm, di, cm_t, rm);
    fn_test_sub_into!(test_sub_into_di_cm_t_cm, di, cm_t, cm);
    fn_test_sub_into!(test_sub_into_di_cm_t_di, di, cm_t, di);

    fn_test_sub_into!(test_sub_into_di_cm_t_rm_t, di, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_cm_t_cm_t, di, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_cm_t_di_t, di, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_di_di_t_rm, di, di_t, rm);
    fn_test_sub_into!(test_sub_into_di_di_t_cm, di, di_t, cm);
    fn_test_sub_into!(test_sub_into_di_di_t_di, di, di_t, di);

    fn_test_sub_into!(test_sub_into_di_di_t_rm_t, di, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_di_t_cm_t, di, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_di_t_di_t, di, di_t, di_t);

    fn_test_sub_into!(test_sub_into_di_t_rm_rm, di_t, rm, rm);
    fn_test_sub_into!(test_sub_into_di_t_rm_cm, di_t, rm, cm);
    fn_test_sub_into!(test_sub_into_di_t_rm_di, di_t, rm, di);

    fn_test_sub_into!(test_sub_into_di_t_rm_rm_t, di_t, rm, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_rm_cm_t, di_t, rm, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_rm_di_t, di_t, rm, di_t);

    fn_test_sub_into!(test_sub_into_di_t_cm_rm, di_t, cm, rm);
    fn_test_sub_into!(test_sub_into_di_t_cm_cm, di_t, cm, cm);
    fn_test_sub_into!(test_sub_into_di_t_cm_di, di_t, cm, di);

    fn_test_sub_into!(test_sub_into_di_t_cm_rm_t, di_t, cm, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_cm_cm_t, di_t, cm, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_cm_di_t, di_t, cm, di_t);

    fn_test_sub_into!(test_sub_into_di_t_di_rm, di_t, di, rm);
    fn_test_sub_into!(test_sub_into_di_t_di_cm, di_t, di, cm);
    fn_test_sub_into!(test_sub_into_di_t_di_di, di_t, di, di);

    fn_test_sub_into!(test_sub_into_di_t_di_rm_t, di_t, di, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_di_cm_t, di_t, di, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_di_di_t, di_t, di, di_t);

    fn_test_sub_into!(test_sub_into_di_t_rm_t_rm, di_t, rm_t, rm);
    fn_test_sub_into!(test_sub_into_di_t_rm_t_cm, di_t, rm_t, cm);
    fn_test_sub_into!(test_sub_into_di_t_rm_t_di, di_t, rm_t, di);

    fn_test_sub_into!(test_sub_into_di_t_rm_t_rm_t, di_t, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_rm_t_cm_t, di_t, rm_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_rm_t_di_t, di_t, rm_t, di_t);

    fn_test_sub_into!(test_sub_into_di_t_cm_t_rm, di_t, cm_t, rm);
    fn_test_sub_into!(test_sub_into_di_t_cm_t_cm, di_t, cm_t, cm);
    fn_test_sub_into!(test_sub_into_di_t_cm_t_di, di_t, cm_t, di);

    fn_test_sub_into!(test_sub_into_di_t_cm_t_rm_t, di_t, cm_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_cm_t_cm_t, di_t, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_cm_t_di_t, di_t, cm_t, di_t);

    fn_test_sub_into!(test_sub_into_di_t_di_t_rm, di_t, di_t, rm);
    fn_test_sub_into!(test_sub_into_di_t_di_t_cm, di_t, di_t, cm);
    fn_test_sub_into!(test_sub_into_di_t_di_t_di, di_t, di_t, di);

    fn_test_sub_into!(test_sub_into_di_t_di_t_rm_t, di_t, di_t, rm_t);
    fn_test_sub_into!(test_sub_into_di_t_di_t_cm_t, di_t, di_t, cm_t);
    fn_test_sub_into!(test_sub_into_di_t_di_t_di_t, di_t, di_t, di_t);
}
