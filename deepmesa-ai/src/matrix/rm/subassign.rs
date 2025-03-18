use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdSubAssign;
use crate::matrix::traits::MatrixElement;
use std::ops::SubAssign;

impl<T> SubAssign<T> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, val: T) {
        if self.use_simd() {
            unsafe {
                SimdKernel::simd_sub_assign(self.rm_data, val, self.rm_len);
            }
            return;
        }

        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rm_sub_assign_t!(self, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rm_sub_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> SubAssign<&MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: &MatrixRowMajor<T>) {
        shape_check!(self, rhs);
        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::rm::macros::simd_sub_assign!(rm_t, rm_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rm_sub_assign_t!(self, row, col, rm_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rm::macros::simd_sub_assign!(rm_t, rm, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rm_sub_assign_t!(self, row, col, rm_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::rm::macros::simd_sub_assign!(rm, rm_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rm_sub_assign!(self, row, col, rm_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rm::macros::simd_sub_assign!(rm, rm, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rm_sub_assign!(self, row, col, rm_get!(rhs, row, col));
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::SubAssign;

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

    macro_rules! test_sub_assign {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            lhs.sub_assign(&rhs);
            assert_eq!(lhs, result!(rm, $simd, $t));
        };
    }

    macro_rules! test_sub_assign_val {
        ($t:ty, $simd: ident, $lhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            lhs.sub_assign(rhs);
            assert_eq!(lhs, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_sub_assign_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_assign_val!(u8, false, $lhs);
                test_sub_assign_val!(u16, false, $lhs);
                test_sub_assign_val!(u32, false, $lhs);
                test_sub_assign_val!(u64, false, $lhs);
                test_sub_assign_val!(u128, false, $lhs);
                test_sub_assign_val!(i8, false, $lhs);
                test_sub_assign_val!(i16, false, $lhs);
                test_sub_assign_val!(i32, false, $lhs);
                test_sub_assign_val!(i64, false, $lhs);
                test_sub_assign_val!(i128, false, $lhs);
                test_sub_assign_val!(f32, false, $lhs);
                test_sub_assign_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub_assign {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_assign!(u8, false, $lhs, $rhs);
                test_sub_assign!(u16, false, $lhs, $rhs);
                test_sub_assign!(u32, false, $lhs, $rhs);
                test_sub_assign!(u64, false, $lhs, $rhs);
                test_sub_assign!(u128, false, $lhs, $rhs);
                test_sub_assign!(i8, false, $lhs, $rhs);
                test_sub_assign!(i16, false, $lhs, $rhs);
                test_sub_assign!(i32, false, $lhs, $rhs);
                test_sub_assign!(i64, false, $lhs, $rhs);
                test_sub_assign!(i128, false, $lhs, $rhs);
                test_sub_assign!(f32, false, $lhs, $rhs);
                test_sub_assign!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_sub_assign_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_assign!(u8, true, $lhs, $rhs);
                test_sub_assign!(u16, true, $lhs, $rhs);
                test_sub_assign!(u32, true, $lhs, $rhs);
                test_sub_assign!(i8, true, $lhs, $rhs);
                test_sub_assign!(i16, true, $lhs, $rhs);
                test_sub_assign!(i32, true, $lhs, $rhs);
                test_sub_assign!(f32, true, $lhs, $rhs);
                test_sub_assign!(f64, true, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_sub_assign_simd_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_assign_val!(u8, true, $lhs);
                test_sub_assign_val!(u16, true, $lhs);
                test_sub_assign_val!(u32, true, $lhs);
                test_sub_assign_val!(i8, true, $lhs);
                test_sub_assign_val!(i16, true, $lhs);
                test_sub_assign_val!(i32, true, $lhs);
                test_sub_assign_val!(f32, true, $lhs);
                test_sub_assign_val!(f64, true, $lhs);
            }
        };
    }

    fn_test_sub_assign_val!(test_sub_assign_rm_val, rm);
    fn_test_sub_assign_val!(test_sub_assign_rm_t_val, rm_t);
    fn_test_sub_assign!(test_sub_assign_rm_rm, rm, rm);
    fn_test_sub_assign!(test_sub_assign_rm_rm_t, rm, rm_t);
    fn_test_sub_assign!(test_sub_assign_rm_t_rm, rm_t, rm);
    fn_test_sub_assign!(test_sub_assign_rm_t_rm_t, rm_t, rm_t);
    fn_test_sub_assign_simd_val!(test_sub_assign_simd_rm_val, rm);
    fn_test_sub_assign_simd_val!(test_sub_assign_simd_rm_t_val, rm_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_rm_rm, rm, rm);
    fn_test_sub_assign_simd!(test_sub_assign_simd_rm_rm_t, rm, rm_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_rm_t_rm, rm_t, rm);
    fn_test_sub_assign_simd!(test_sub_assign_simd_rm_t_rm_t, rm_t, rm_t);
}
