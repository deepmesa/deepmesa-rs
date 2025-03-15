use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::shape_check;
use crate::matrix::traits::AddInto;
use crate::matrix::traits::MatrixElement;
use std::ops::Add;
use std::ops::AddAssign;

impl<T> Add<T> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn add(mut self, rhs: T) -> MatrixColMajor<T> {
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<&MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn add(mut self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        self.add_assign(rhs);
        return self;
    }
}

impl<T> Add<T> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn add(self, rhs: T) -> MatrixColMajor<T> {
        let mut result = MatrixColMajor::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

impl<T> Add<&MatrixColMajor<T>> for &MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    type Output = MatrixColMajor<T>;
    fn add(self, rhs: &MatrixColMajor<T>) -> MatrixColMajor<T> {
        shape_check!(self, rhs);
        let mut result = MatrixColMajor::from(&self);
        self.add_into(rhs, &mut result);
        return result;
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::Add;

    macro_rules! lhs {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 1,4;2,5;3,6);
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3, 2, $simd], 1,2,3;4,5,6);
                cm.transpose();
                cm
            }
        };
    }

    macro_rules! rhs {
        (cm, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t,3,2,$simd], 6,7,8;9,10,11);
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
            matrix_cm!([$t, 2, 3, $simd], 7,13;9,15;11,17);
        };
        (val, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 4,7;5,8;6,9);
        };
    }

    macro_rules! test_add {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.add(&rhs);
            assert_eq!(out, result!(cm, $simd, $t));
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

    fn_test_add!(test_add_cm_cm, cm, cm);
    fn_test_add!(test_add_cm_cm_t, cm, cm_t);
    fn_test_add!(test_add_cm_t_cm, cm_t, cm);
    fn_test_add!(test_add_cm_t_cm_t, cm_t, cm_t);
    fn_test_add_simd!(test_add_simd_cm_cm, cm, cm);
    fn_test_add_simd!(test_add_simd_cm_cm_t, cm, cm_t);
    fn_test_add_simd!(test_add_simd_cm_t_cm, cm_t, cm);
    fn_test_add_simd!(test_add_simd_cm_t_cm_t, cm_t, cm_t);
}
