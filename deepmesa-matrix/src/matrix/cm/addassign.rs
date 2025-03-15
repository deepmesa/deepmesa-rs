use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdAddAssign;
use crate::matrix::traits::MatrixElement;
use std::ops::AddAssign;

impl<T> AddAssign<T> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, val: T) {
        if self.use_simd() {
            unsafe {
                SimdKernel::simd_add_assign(self.cm_data, val, self.cm_len);
            }
            return;
        }

        if self.is_transpose {
            iterate_col_major!(self, row, col, unsafe {
                cm_add_assign_t!(self, row, col, val);
            });
        } else {
            iterate_col_major!(self, row, col, unsafe {
                cm_add_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> AddAssign<&MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &MatrixColMajor<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::cm::macros::simd_add_assign!(cm_t, cm_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cm_add_assign_t!(self, row, col, cm_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cm::macros::simd_add_assign!(cm_t, cm, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cm_add_assign_t!(self, row, col, cm_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::cm::macros::simd_add_assign!(cm, cm_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cm_add_assign!(self, row, col, cm_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cm::macros::simd_add_assign!(cm, cm, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cm_add_assign!(self, row, col, cm_get!(rhs, row, col));
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::AddAssign;

    macro_rules! lhs {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 1,2,3;4,5,6)
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3,2, $simd], 1,4;2,5;3,6);
                cm.transpose();
                cm
            }
        };
    }

    macro_rules! rhs {
        (cm, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t,3,2, $simd], 6,9;7,10;8,11);
                cm.transpose();
                cm
            }
        };
        (cm_t, $simd:ident, $t:ty) => {
            matrix_cm!([$t,2,3, false], 6,7,8;9,10,11)
        };
    }

    macro_rules! result {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 7,9,11;13,15,17)
        };
        (val, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 4,5,6;7,8,9)
        };
    }

    macro_rules! test_add_assign {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            lhs.add_assign(&rhs);
            assert_eq!(lhs, result!(cm, $simd, $t));
        };
    }

    macro_rules! test_add_assign_val {
        ($t:ty, $simd: ident, $lhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            lhs.add_assign(rhs);
            assert_eq!(lhs, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_add_assign_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign_val!(u8, false, $lhs);
                test_add_assign_val!(u16, false, $lhs);
                test_add_assign_val!(u32, false, $lhs);
                test_add_assign_val!(u64, false, $lhs);
                test_add_assign_val!(u128, false, $lhs);
                test_add_assign_val!(i8, false, $lhs);
                test_add_assign_val!(i16, false, $lhs);
                test_add_assign_val!(i32, false, $lhs);
                test_add_assign_val!(i64, false, $lhs);
                test_add_assign_val!(i128, false, $lhs);
                test_add_assign_val!(f32, false, $lhs);
                test_add_assign_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_add_assign {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign!(u8, false, $lhs, $rhs);
                test_add_assign!(u16, false, $lhs, $rhs);
                test_add_assign!(u32, false, $lhs, $rhs);
                test_add_assign!(u64, false, $lhs, $rhs);
                test_add_assign!(u128, false, $lhs, $rhs);
                test_add_assign!(i8, false, $lhs, $rhs);
                test_add_assign!(i16, false, $lhs, $rhs);
                test_add_assign!(i32, false, $lhs, $rhs);
                test_add_assign!(i64, false, $lhs, $rhs);
                test_add_assign!(i128, false, $lhs, $rhs);
                test_add_assign!(f32, false, $lhs, $rhs);
                test_add_assign!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_add_assign_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign!(u8, true, $lhs, $rhs);
                test_add_assign!(u16, true, $lhs, $rhs);
                test_add_assign!(u32, true, $lhs, $rhs);
                test_add_assign!(i8, true, $lhs, $rhs);
                test_add_assign!(i16, true, $lhs, $rhs);
                test_add_assign!(i32, true, $lhs, $rhs);
                test_add_assign!(f32, true, $lhs, $rhs);
                test_add_assign!(f64, true, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_add_assign_simd_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign_val!(u8, true, $lhs);
                test_add_assign_val!(u16, true, $lhs);
                test_add_assign_val!(u32, true, $lhs);
                test_add_assign_val!(i8, true, $lhs);
                test_add_assign_val!(i16, true, $lhs);
                test_add_assign_val!(i32, true, $lhs);
                test_add_assign_val!(f32, true, $lhs);
                test_add_assign_val!(f64, true, $lhs);
            }
        };
    }

    fn_test_add_assign_val!(test_add_assign_cm_val, cm);
    fn_test_add_assign_val!(test_add_assign_cm_t_val, cm_t);

    fn_test_add_assign!(test_add_assign_cm_cm, cm, cm);
    fn_test_add_assign!(test_add_assign_cm_cm_t, cm, cm_t);

    fn_test_add_assign!(test_add_assign_cm_t_cm, cm_t, cm);
    fn_test_add_assign!(test_add_assign_cm_t_cm_t, cm_t, cm_t);

    fn_test_add_assign_simd_val!(test_add_assign_simd_cm_val, cm);
    fn_test_add_assign_simd_val!(test_add_assign_simd_cm_t_val, cm_t);

    fn_test_add_assign_simd!(test_add_assign_simd_cm_cm, cm, cm);
    fn_test_add_assign_simd!(test_add_assign_simd_cm_cm_t, cm, cm_t);

    fn_test_add_assign_simd!(test_add_assign_simd_cm_t_cm, cm_t, cm);
    fn_test_add_assign_simd!(test_add_assign_simd_cm_t_cm_t, cm_t, cm_t);
}
