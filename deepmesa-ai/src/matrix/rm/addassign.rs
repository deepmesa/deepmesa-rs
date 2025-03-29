use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::MatrixElement;
use std::ops::AddAssign;

impl<T> AddAssign<T> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, val: T) {
        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rm_add_assign_t!(self, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rm_add_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> AddAssign<&MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &MatrixRowMajor<T>) {
        shape_check!(self, rhs);
        if self.is_transpose {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_add_assign_t!(self, row, col, rm_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rm_add_assign_t!(self, row, col, rm_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_add_assign!(self, row, col, rm_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rm_add_assign!(self, row, col, rm_get!(rhs, row, col));
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
    use std::ops::AddAssign;

    macro_rules! lhs {
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 1,2,3;4,5,6)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2], 1,4;2,5;3,6);
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
            matrix_rm!([$t, 2, 3], 7,9,11;13,15,17)
        };
        (val, $t:ty) => {
            matrix_rm!([$t, 2, 3], 4,5,6;7,8,9)
        };
    }

    macro_rules! test_add_assign {
        ($t:ty, $lhs:ident, $rhs:ident) => {
            let mut lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            lhs.add_assign(&rhs);
            assert_eq!(lhs, result!(rm, $t));
        };
    }

    macro_rules! test_add_assign_val {
        ($t:ty, $lhs:ident) => {
            let mut lhs = lhs!($lhs, $t);
            let rhs = 3 as $t;
            lhs.add_assign(rhs);
            assert_eq!(lhs, result!(val, $t));
        };
    }

    macro_rules! fn_test_add_assign_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign_val!(u8, $lhs);
                test_add_assign_val!(u16, $lhs);
                test_add_assign_val!(u32, $lhs);
                test_add_assign_val!(u64, $lhs);
                test_add_assign_val!(u128, $lhs);
                test_add_assign_val!(i8, $lhs);
                test_add_assign_val!(i16, $lhs);
                test_add_assign_val!(i32, $lhs);
                test_add_assign_val!(i64, $lhs);
                test_add_assign_val!(i128, $lhs);
                test_add_assign_val!(f32, $lhs);
                test_add_assign_val!(f64, $lhs);
            }
        };
    }

    macro_rules! fn_test_add_assign {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_add_assign!(u8, $lhs, $rhs);
                test_add_assign!(u16, $lhs, $rhs);
                test_add_assign!(u32, $lhs, $rhs);
                test_add_assign!(u64, $lhs, $rhs);
                test_add_assign!(u128, $lhs, $rhs);
                test_add_assign!(i8, $lhs, $rhs);
                test_add_assign!(i16, $lhs, $rhs);
                test_add_assign!(i32, $lhs, $rhs);
                test_add_assign!(i64, $lhs, $rhs);
                test_add_assign!(i128, $lhs, $rhs);
                test_add_assign!(f32, $lhs, $rhs);
                test_add_assign!(f64, $lhs, $rhs);
            }
        };
    }

    fn_test_add_assign_val!(test_add_assign_rm_val, rm);
    fn_test_add_assign_val!(test_add_assign_rm_t_val, rm_t);

    fn_test_add_assign!(test_add_assign_rm_rm, rm, rm);
    fn_test_add_assign!(test_add_assign_rm_rm_t, rm, rm_t);

    fn_test_add_assign!(test_add_assign_rm_t_rm, rm_t, rm);
    fn_test_add_assign!(test_add_assign_rm_t_rm_t, rm_t, rm_t);
}
