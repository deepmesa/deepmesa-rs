use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::shape_check;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::SubInto;
use std::ops::Sub;
use std::ops::SubAssign;

impl<T> Sub<T> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn sub(mut self, rhs: T) -> MatrixColMajor<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<&MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn sub(mut self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<T> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn sub(self, rhs: T) -> MatrixColMajor<T> {
        let mut result = MatrixColMajor::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

impl<T> Sub<&MatrixColMajor<T>> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn sub(self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        let mut result = MatrixColMajor::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::Sub;

    macro_rules! lhs {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 10,40;20,50;30,60)
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3,2, $simd], 10,20,30;40,50,60);
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
            matrix_cm!([$t,2,3, false], 6,9;7,10;8,11)
        };
    }

    macro_rules! result {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 4,31;13,40;22,49)
        };
        (val, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 7,37;17,47;27,57)
        };
    }

    macro_rules! test_sub {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.sub(&rhs);
            assert_eq!(out, result!(cm, $simd, $t));
        };
    }

    macro_rules! test_sub_val {
        ($t:ty, $simd:ident, $lhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            let out = lhs.sub(rhs);
            assert_eq!(out, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_sub_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_val!(u8, false, $lhs);
                test_sub_val!(u16, false, $lhs);
                test_sub_val!(u32, false, $lhs);
                test_sub_val!(u64, false, $lhs);
                test_sub_val!(u128, false, $lhs);
                test_sub_val!(i8, false, $lhs);
                test_sub_val!(i16, false, $lhs);
                test_sub_val!(i32, false, $lhs);
                test_sub_val!(i64, false, $lhs);
                test_sub_val!(i128, false, $lhs);
                test_sub_val!(f32, false, $lhs);
                test_sub_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub_val_simd {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_val!(u8, true, $lhs);
                test_sub_val!(u16, true, $lhs);
                test_sub_val!(u32, true, $lhs);
                test_sub_val!(i8, true, $lhs);
                test_sub_val!(i16, true, $lhs);
                test_sub_val!(i32, true, $lhs);
                test_sub_val!(f32, true, $lhs);
                test_sub_val!(f64, true, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub!(u8, false, $lhs, $rhs);
                test_sub!(u16, false, $lhs, $rhs);
                test_sub!(u32, false, $lhs, $rhs);
                test_sub!(u64, false, $lhs, $rhs);
                test_sub!(u128, false, $lhs, $rhs);
                test_sub!(i8, false, $lhs, $rhs);
                test_sub!(i16, false, $lhs, $rhs);
                test_sub!(i32, false, $lhs, $rhs);
                test_sub!(i64, false, $lhs, $rhs);
                test_sub!(i128, false, $lhs, $rhs);
                test_sub!(f32, false, $lhs, $rhs);
                test_sub!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_sub_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub!(u8, true, $lhs, $rhs);
                test_sub!(u16, true, $lhs, $rhs);
                test_sub!(u32, true, $lhs, $rhs);
                test_sub!(i8, true, $lhs, $rhs);
                test_sub!(i16, true, $lhs, $rhs);
                test_sub!(i32, true, $lhs, $rhs);
                test_sub!(f32, true, $lhs, $rhs);
                test_sub!(f64, true, $lhs, $rhs);
            }
        };
    }

    fn_test_sub!(test_sub_cm_cm, cm, cm);
    fn_test_sub!(test_sub_cm_cm_t, cm, cm_t);
    fn_test_sub!(test_sub_cm_t_cm, cm_t, cm);
    fn_test_sub!(test_sub_cm_t_cm_t, cm_t, cm_t);
    fn_test_sub_simd!(test_sub_simd_cm_cm, cm, cm);
    fn_test_sub_simd!(test_sub_simd_cm_cm_t, cm, cm_t);
    fn_test_sub_simd!(test_sub_simd_cm_t_cm, cm_t, cm);
    fn_test_sub_simd!(test_sub_simd_cm_t_cm_t, cm_t, cm_t);
}
