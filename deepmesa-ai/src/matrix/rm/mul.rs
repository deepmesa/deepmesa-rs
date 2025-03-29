use crate::matrix::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::MulInto;
use std::ops::Mul;
use std::ops::MulAssign;

impl<T> Mul<T> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn mul(mut self, rhs: T) -> MatrixRowMajor<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn mul(mut self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        shape_check!(self, rhs);
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<T> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn mul(self, rhs: T) -> MatrixRowMajor<T> {
        let mut result = MatrixRowMajor::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&MatrixRowMajor<T>> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn mul(self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        shape_check!(self, rhs);
        let mut result = MatrixRowMajor::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;
    use std::ops::Mul;

    macro_rules! lhs {
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 2,3,4;5,6,7)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2], 2,5;3,6;4,7);
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
            matrix_rm!([$t, 2, 3], 12,21,32;45,60,77)
        };
        (val, $t:ty) => {
            matrix_rm!([$t, 2, 3], 6,9,12;15,18,21)
        };
    }

    macro_rules! test_mul {
        ($t:ty, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            let out = lhs.mul(&rhs);
            assert_eq!(out, result!(rm, $t));
        };
    }

    macro_rules! test_mul_val {
        ($t:ty, $lhs:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = 3 as $t;
            let out = lhs.mul(rhs);
            assert_eq!(out, result!(val, $t));
        };
    }

    macro_rules! fn_test_mul_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_val!(u8, $lhs);
                test_mul_val!(u16, $lhs);
                test_mul_val!(u32, $lhs);
                test_mul_val!(u64, $lhs);
                test_mul_val!(u128, $lhs);
                test_mul_val!(i8, $lhs);
                test_mul_val!(i16, $lhs);
                test_mul_val!(i32, $lhs);
                test_mul_val!(i64, $lhs);
                test_mul_val!(i128, $lhs);
                test_mul_val!(f32, $lhs);
                test_mul_val!(f64, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul!(u8, $lhs, $rhs);
                test_mul!(u16, $lhs, $rhs);
                test_mul!(u32, $lhs, $rhs);
                test_mul!(u64, $lhs, $rhs);
                test_mul!(u128, $lhs, $rhs);
                test_mul!(i8, $lhs, $rhs);
                test_mul!(i16, $lhs, $rhs);
                test_mul!(i32, $lhs, $rhs);
                test_mul!(i64, $lhs, $rhs);
                test_mul!(i128, $lhs, $rhs);
                test_mul!(f32, $lhs, $rhs);
                test_mul!(f64, $lhs, $rhs);
            }
        };
    }

    fn_test_mul_val!(test_mul_val_rm, rm);
    fn_test_mul_val!(test_mul_val_rm_t, rm_t);
    fn_test_mul!(test_mul_rm_rm, rm, rm);
    fn_test_mul!(test_mul_rm_rm_t, rm, rm_t);
    fn_test_mul!(test_mul_rm_t_rm, rm_t, rm);
    fn_test_mul!(test_mul_rm_t_rm_t, rm_t, rm_t);
}
