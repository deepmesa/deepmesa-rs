use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::AddInto;
use crate::matrix::MatrixElement;
use std::ops::Add;
use std::ops::AddAssign;

impl<T> Add<T> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn add(mut self, rhs: T) -> MatrixRowMajor<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<&MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn add(mut self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<T> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn add(self, rhs: T) -> MatrixRowMajor<T> {
        let mut result = MatrixRowMajor::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> Add<&MatrixRowMajor<T>> for &MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixRowMajor<T>;
    fn add(self, rhs: &MatrixRowMajor<T>) -> MatrixRowMajor<T> {
        let mut result = MatrixRowMajor::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::Add;

    macro_rules! lhs {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 1,2,3;4,5,6)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2, $simd], 1,4;2,5;3,6);
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
            matrix_rm!([$t, 2, 3, $simd], 7,9,11;13,15,17)
        };
        (val, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 4,5,6;7,8,9)
        };
    }

    macro_rules! test_add {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.add(&rhs);
            assert_eq!(out, result!(rm, $simd, $t));
        };
    }

    macro_rules! test_add_val {
        ($t:ty, $simd:ident, $lhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            let out = lhs.add(rhs);
            assert_eq!(out, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_add_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_val!(u8, false, $lhs);
                test_add_val!(u16, false, $lhs);
                test_add_val!(u32, false, $lhs);
                test_add_val!(u64, false, $lhs);
                test_add_val!(u128, false, $lhs);
                test_add_val!(i8, false, $lhs);
                test_add_val!(i16, false, $lhs);
                test_add_val!(i32, false, $lhs);
                test_add_val!(i64, false, $lhs);
                test_add_val!(i128, false, $lhs);
                test_add_val!(f32, false, $lhs);
                test_add_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_add_val_simd {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_val!(u8, true, $lhs);
                test_add_val!(u16, true, $lhs);
                test_add_val!(u32, true, $lhs);
                test_add_val!(i8, true, $lhs);
                test_add_val!(i16, true, $lhs);
                test_add_val!(i32, true, $lhs);
                test_add_val!(f32, true, $lhs);
                test_add_val!(f64, true, $lhs);
            }
        };
    }

    macro_rules! fn_test_add {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add!(u8, false, $lhs, $rhs);
                test_add!(u16, false, $lhs, $rhs);
                test_add!(u32, false, $lhs, $rhs);
                test_add!(u64, false, $lhs, $rhs);
                test_add!(u128, false, $lhs, $rhs);
                test_add!(i8, false, $lhs, $rhs);
                test_add!(i16, false, $lhs, $rhs);
                test_add!(i32, false, $lhs, $rhs);
                test_add!(i64, false, $lhs, $rhs);
                test_add!(i128, false, $lhs, $rhs);
                test_add!(f32, false, $lhs, $rhs);
                test_add!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_add_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add!(u8, true, $lhs, $rhs);
                test_add!(u16, true, $lhs, $rhs);
                test_add!(u32, true, $lhs, $rhs);
                test_add!(i8, true, $lhs, $rhs);
                test_add!(i16, true, $lhs, $rhs);
                test_add!(i32, true, $lhs, $rhs);
                test_add!(f32, true, $lhs, $rhs);
                test_add!(f64, true, $lhs, $rhs);
            }
        };
    }

    fn_test_add_val!(test_add_val_rm, rm);
    fn_test_add_val!(test_add_val_rm_t, rm_t);
    fn_test_add_val_simd!(test_add_simd_val_rm, rm);
    fn_test_add_val_simd!(test_add_simd_val_rm_t, rm_t);
    fn_test_add!(test_add_rm_rm, rm, rm);
    fn_test_add!(test_add_rm_rm_t, rm, rm_t);
    fn_test_add!(test_add_rm_t_rm, rm_t, rm);
    fn_test_add!(test_add_rm_t_rm_t, rm_t, rm_t);
    fn_test_add_simd!(test_add_simd_rm_rm, rm, rm);
    fn_test_add_simd!(test_add_simd_rm_rm_t, rm, rm_t);
    fn_test_add_simd!(test_add_simd_rm_t_rm, rm_t, rm);
    fn_test_add_simd!(test_add_simd_rm_t_rm_t, rm_t, rm_t);
}
