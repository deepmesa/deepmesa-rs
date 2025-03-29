use crate::matrix::macros::shape_check;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::SubInto;
use std::ops::Sub;
use std::ops::SubAssign;

impl<T> Sub<T> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn sub(mut self, rhs: T) -> MatrixRowMajor<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<&MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn sub(mut self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        shape_check!(self, rhs);
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<T> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn sub(self, rhs: T) -> MatrixRowMajor<T> {
        let mut result = MatrixRowMajor::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

impl<T> Sub<&MatrixRowMajor<T>> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn sub(self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        shape_check!(self, rhs);
        let mut result = MatrixRowMajor::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;
    use std::ops::Sub;

    macro_rules! lhs {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 10,20,30;40,50,60)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2, $simd], 10,40;20,50;30,60);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! rhs {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t,2,3, $simd], 6,7,8;9,10,11)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t,3,2, $simd], 6,9;7,10;8,11);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! result {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 4,13,22;31,40,49)
        };
        (val, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 7,17,27;37,47,57)
        };
    }

    macro_rules! test_sub {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.sub(&rhs);
            assert_eq!(out, result!(rm, $simd, $t));
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

    fn_test_sub_val!(test_sub_val_rm, rm);
    fn_test_sub_val!(test_sub_val_rm_t, rm_t);
    fn_test_sub_val_simd!(test_sub_simd_val_rm, rm);
    fn_test_sub_val_simd!(test_sub_simd_val_rm_t, rm_t);
    fn_test_sub!(test_sub_rm_rm, rm, rm);
    fn_test_sub!(test_sub_rm_rm_t, rm, rm_t);
    fn_test_sub!(test_sub_rm_t_rm, rm_t, rm);
    fn_test_sub!(test_sub_rm_t_rm_t, rm_t, rm_t);
    fn_test_sub_simd!(test_sub_simd_rm_rm, rm, rm);
    fn_test_sub_simd!(test_sub_simd_rm_rm_t, rm, rm_t);
    fn_test_sub_simd!(test_sub_simd_rm_t_rm, rm_t, rm);
    fn_test_sub_simd!(test_sub_simd_rm_t_rm_t, rm_t, rm_t);
}
