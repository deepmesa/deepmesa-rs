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
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 10,20,30;40,50,60)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2], 10,40;20,50;30,60);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! rhs {
        (rm, $t:ty) => {
            matrix_rm!([$t,2,3], 6,7,8;9,10,11)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t,3,2], 6,9;7,10;8,11);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! result {
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 4,13,22;31,40,49)
        };
        (val, $t:ty) => {
            matrix_rm!([$t, 2, 3], 7,17,27;37,47,57)
        };
    }

    macro_rules! test_sub {
        ($t:ty, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            let out = lhs.sub(&rhs);
            assert_eq!(out, result!(rm, $t));
        };
    }

    macro_rules! test_sub_val {
        ($t:ty, $lhs:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = 3 as $t;
            let out = lhs.sub(rhs);
            assert_eq!(out, result!(val, $t));
        };
    }

    macro_rules! fn_test_sub_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_val!(u8, $lhs);
                test_sub_val!(u16, $lhs);
                test_sub_val!(u32, $lhs);
                test_sub_val!(u64, $lhs);
                test_sub_val!(u128, $lhs);
                test_sub_val!(i8, $lhs);
                test_sub_val!(i16, $lhs);
                test_sub_val!(i32, $lhs);
                test_sub_val!(i64, $lhs);
                test_sub_val!(i128, $lhs);
                test_sub_val!(f32, $lhs);
                test_sub_val!(f64, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub!(u8, $lhs, $rhs);
                test_sub!(u16, $lhs, $rhs);
                test_sub!(u32, $lhs, $rhs);
                test_sub!(u64, $lhs, $rhs);
                test_sub!(u128, $lhs, $rhs);
                test_sub!(i8, $lhs, $rhs);
                test_sub!(i16, $lhs, $rhs);
                test_sub!(i32, $lhs, $rhs);
                test_sub!(i64, $lhs, $rhs);
                test_sub!(i128, $lhs, $rhs);
                test_sub!(f32, $lhs, $rhs);
                test_sub!(f64, $lhs, $rhs);
            }
        };
    }

    fn_test_sub_val!(test_sub_val_rm, rm);
    fn_test_sub_val!(test_sub_val_rm_t, rm_t);
    fn_test_sub!(test_sub_rm_rm, rm, rm);
    fn_test_sub!(test_sub_rm_rm_t, rm, rm_t);
    fn_test_sub!(test_sub_rm_t_rm, rm_t, rm);
    fn_test_sub!(test_sub_rm_t_rm_t, rm_t, rm_t);
}
