use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;

use crate::matrix::simd::traits::SimdAddInto;
use crate::matrix::traits::{AddInto, MatrixElement};

use crate::matrix::simd::kernel::SimdKernel;

impl<T> AddInto<T, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut MatrixRowMajor<T>) {
        shape_check!(self, result);
        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::rm::macros::simd_add_into!(rm_t, val, rm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get_t!(self, row, col) + rhs);
                });
            } else {
                crate::matrix::rm::macros::simd_add_into!(rm_t, val, rm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get_t!(self, row, col) + rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::rm::macros::simd_add_into!(rm, val, rm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get!(self, row, col) + rhs);
                });
            } else {
                crate::matrix::rm::macros::simd_add_into!(rm, val, rm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get!(self, row, col) + rhs);
                });
            }
        }
    }
}

impl<T> AddInto<&MatrixRowMajor<T>, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &MatrixRowMajor<T>, result: &mut MatrixRowMajor<T>) {
        shape_check!(self, rhs);
        shape_check!(self, result);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_add_into!(rm_t, rm_t, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_add_into!(rm_t, rm_t, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_add_into!(rm_t, rm, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_add_into!(rm_t, rm, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_add_into!(rm, rm_t, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_add_into!(rm, rm_t, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_add_into!(rm, rm, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_add_into!(rm, rm, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;

    macro_rules! lhs {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 5,6,7;8,9,10)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2, $simd], 5,8;6,9;7,10);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! rhs {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t,2,3, $simd], 12,13,14;15,16,17)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t,3,2, $simd], 12,15;13,16;14,17);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! out {
        (rm, $simd:ident, $t:ty) => {
            MatrixRowMajor::<$t>::new(2, 3, $simd)
        };
        (rm_t, $simd:ident, $t:ty) => {{
            let mut rm = MatrixRowMajor::<$t>::new(3, 2, $simd);
            rm.transpose();
            rm
        }};
    }

    macro_rules! result {
        (rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 17,19,21;23,25,27)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2, $simd], 17,23;19,25;21,27);
                rm.transpose();
                rm
            }
        };
        (val, rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 12,13,14;15,16,17)
        };
        (val, rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2, $simd], 12,15;13,16;14,17);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! test_add_into_val {
        ($t:ty, $simd:ident, $lhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 7 as $t;
            let mut out = out!($out, $simd, $t);
            lhs.add_into(rhs, &mut out);
            assert_eq!(out, result!(val, $out, $simd, $t));
        };
    }

    macro_rules! test_add_into {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let mut out = out!($out, $simd, $t);
            lhs.add_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $simd, $t));
        };
    }

    macro_rules! fn_test_add_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into_val!(u8, false, $lhs, $out);
                test_add_into_val!(u16, false, $lhs, $out);
                test_add_into_val!(u32, false, $lhs, $out);
                test_add_into_val!(u64, false, $lhs, $out);
                test_add_into_val!(u128, false, $lhs, $out);
                test_add_into_val!(i8, false, $lhs, $out);
                test_add_into_val!(i16, false, $lhs, $out);
                test_add_into_val!(i32, false, $lhs, $out);
                test_add_into_val!(i64, false, $lhs, $out);
                test_add_into_val!(i128, false, $lhs, $out);
                test_add_into_val!(f32, false, $lhs, $out);
                test_add_into_val!(f64, false, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_add_into_val_simd {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into_val!(u8, true, $lhs, $out);
                test_add_into_val!(u16, true, $lhs, $out);
                test_add_into_val!(u32, true, $lhs, $out);
                test_add_into_val!(i8, true, $lhs, $out);
                test_add_into_val!(i16, true, $lhs, $out);
                test_add_into_val!(i32, true, $lhs, $out);
                test_add_into_val!(f32, true, $lhs, $out);
                test_add_into_val!(f64, true, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_add_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into!(u8, false, $lhs, $rhs, $out);
                test_add_into!(u16, false, $lhs, $rhs, $out);
                test_add_into!(u32, false, $lhs, $rhs, $out);
                test_add_into!(u64, false, $lhs, $rhs, $out);
                test_add_into!(u128, false, $lhs, $rhs, $out);
                test_add_into!(i8, false, $lhs, $rhs, $out);
                test_add_into!(i16, false, $lhs, $rhs, $out);
                test_add_into!(i32, false, $lhs, $rhs, $out);
                test_add_into!(i64, false, $lhs, $rhs, $out);
                test_add_into!(i128, false, $lhs, $rhs, $out);
                test_add_into!(f32, false, $lhs, $rhs, $out);
                test_add_into!(f64, false, $lhs, $rhs, $out);
            }
        };
    }

    macro_rules! fn_test_add_into_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into!(u8, true, $lhs, $rhs, $out);
                test_add_into!(u16, true, $lhs, $rhs, $out);
                test_add_into!(u32, true, $lhs, $rhs, $out);
                test_add_into!(i8, true, $lhs, $rhs, $out);
                test_add_into!(i16, true, $lhs, $rhs, $out);
                test_add_into!(i32, true, $lhs, $rhs, $out);
                test_add_into!(f32, true, $lhs, $rhs, $out);
                test_add_into!(f64, true, $lhs, $rhs, $out);
            }
        };
    }

    fn_test_add_into_val!(test_add_into_val_rm_rm, rm, rm);
    fn_test_add_into_val!(test_add_into_val_rm_t_rm, rm_t, rm);
    fn_test_add_into_val!(test_add_into_val_rm_rm_t, rm, rm_t);
    fn_test_add_into_val!(test_add_into_val_rm_t_rm_t, rm_t, rm_t);
    fn_test_add_into_val_simd!(test_add_into_val_simd_rm_rm, rm, rm);
    fn_test_add_into_val_simd!(test_add_into_val_simd_rm_t_rm, rm_t, rm);
    fn_test_add_into_val_simd!(test_add_into_val_simd_rm_rm_t, rm, rm_t);
    fn_test_add_into_val_simd!(test_add_into_val_simd_rm_t_rm_t, rm_t, rm_t);

    fn_test_add_into!(test_add_into_rm_rm_rm, rm, rm, rm);
    fn_test_add_into!(test_add_into_rm_rm_rm_t, rm, rm, rm_t);

    fn_test_add_into!(test_add_into_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_add_into!(test_add_into_rm_rm_t_rm_t, rm, rm_t, rm_t);

    fn_test_add_into!(test_add_into_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_add_into!(test_add_into_rm_t_rm_rm_t, rm_t, rm, rm_t);

    fn_test_add_into!(test_add_into_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_add_into!(test_add_into_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);

    //////////////////////////////////////////////////////////////////////////////
    // SIMD Tests
    //////////////////////////////////////////////////////////////////////////////
    fn_test_add_into_simd!(test_add_into_simd_rm_rm_rm, rm, rm, rm);
    fn_test_add_into_simd!(test_add_into_simd_rm_rm_rm_t, rm, rm, rm_t);

    fn_test_add_into_simd!(test_add_into_simd_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_add_into_simd!(test_add_into_simd_rm_rm_t_rm_t, rm, rm_t, rm_t);

    fn_test_add_into_simd!(test_add_into_simd_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_add_into_simd!(test_add_into_simd_rm_t_rm_rm_t, rm_t, rm, rm_t);

    fn_test_add_into_simd!(test_add_into_simd_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_add_into_simd!(test_add_into_simd_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);
}
