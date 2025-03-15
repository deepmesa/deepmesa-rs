use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::shape_check;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::MulInto;
use std::ops::Mul;
use std::ops::MulAssign;

impl<T> Mul<T> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn mul(mut self, rhs: T) -> MatrixColMajor<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn mul(mut self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<T> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn mul(self, rhs: T) -> MatrixColMajor<T> {
        let mut result = MatrixColMajor::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&MatrixColMajor<T>> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn mul(self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        let mut result = MatrixColMajor::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::Mul;

    macro_rules! lhs {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 2,5;3,6;4,7);
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3,2, $simd], 2,3,4;5,6,7);
                cm.transpose();
                cm
            }
        };
    }

    macro_rules! rhs {
        (cm, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t,3,2, $simd], 6,7,8;9,10,11);
                cm.transpose();
                cm
            }
        };
        (cm_t, $simd:ident, $t:ty) => {
            matrix_cm!([$t,2,3, false], 6,9;7,10;8,11);
        };
    }

    macro_rules! result {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 12,45;21,60;32,77);
        };
        (val, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 6,15;9,18;12,21);
        };
    }

    macro_rules! test_mul {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.mul(&rhs);
            assert_eq!(out, result!(cm, $simd, $t));
        };
    }

    macro_rules! test_mul_val {
        ($t:ty, $simd:ident, $lhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            let out = lhs.mul(rhs);
            assert_eq!(out, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_mul_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_val!(u8, false, $lhs);
                test_mul_val!(u16, false, $lhs);
                test_mul_val!(u32, false, $lhs);
                test_mul_val!(u64, false, $lhs);
                test_mul_val!(u128, false, $lhs);
                test_mul_val!(i8, false, $lhs);
                test_mul_val!(i16, false, $lhs);
                test_mul_val!(i32, false, $lhs);
                test_mul_val!(i64, false, $lhs);
                test_mul_val!(i128, false, $lhs);
                test_mul_val!(f32, false, $lhs);
                test_mul_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul_val_simd {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_val!(u8, true, $lhs);
                test_mul_val!(u16, true, $lhs);
                test_mul_val!(u32, true, $lhs);
                test_mul_val!(i8, true, $lhs);
                test_mul_val!(i16, true, $lhs);
                test_mul_val!(i32, true, $lhs);
                test_mul_val!(f32, true, $lhs);
                test_mul_val!(f64, true, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul!(u8, false, $lhs, $rhs);
                test_mul!(u16, false, $lhs, $rhs);
                test_mul!(u32, false, $lhs, $rhs);
                test_mul!(u64, false, $lhs, $rhs);
                test_mul!(u128, false, $lhs, $rhs);
                test_mul!(i8, false, $lhs, $rhs);
                test_mul!(i16, false, $lhs, $rhs);
                test_mul!(i32, false, $lhs, $rhs);
                test_mul!(i64, false, $lhs, $rhs);
                test_mul!(i128, false, $lhs, $rhs);
                test_mul!(f32, false, $lhs, $rhs);
                test_mul!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_mul_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul!(u8, true, $lhs, $rhs);
                test_mul!(u16, true, $lhs, $rhs);
                test_mul!(u32, true, $lhs, $rhs);
                test_mul!(i8, true, $lhs, $rhs);
                test_mul!(i16, true, $lhs, $rhs);
                test_mul!(i32, true, $lhs, $rhs);
                test_mul!(f32, true, $lhs, $rhs);
                test_mul!(f64, true, $lhs, $rhs);
            }
        };
    }

    fn_test_mul!(test_mul_cm_cm, cm, cm);
    fn_test_mul!(test_mul_cm_cm_t, cm, cm_t);
    fn_test_mul!(test_mul_cm_t_cm, cm_t, cm);
    fn_test_mul!(test_mul_cm_t_cm_t, cm_t, cm_t);
    fn_test_mul_simd!(test_mul_simd_cm_cm, cm, cm);
    fn_test_mul_simd!(test_mul_simd_cm_cm_t, cm, cm_t);
    fn_test_mul_simd!(test_mul_simd_cm_t_cm, cm_t, cm);
    fn_test_mul_simd!(test_mul_simd_cm_t_cm_t, cm_t, cm_t);
}
