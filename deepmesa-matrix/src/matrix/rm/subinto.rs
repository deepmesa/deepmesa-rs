use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::simd::traits::SimdSubInto;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::{MatrixElement, SubInto};

use crate::matrix::simd::kernel::SimdKernel;

impl<T> SubInto<T, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut MatrixRowMajor<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::rm::macros::simd_sub_into!(rm_t, val, rm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get_t!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::rm::macros::simd_sub_into!(rm_t, val, rm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get_t!(self, row, col) - rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::rm::macros::simd_sub_into!(rm, val, rm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::rm::macros::simd_sub_into!(rm, val, rm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get!(self, row, col) - rhs);
                });
            }
        }
    }
}

impl<T> SubInto<&MatrixRowMajor<T>, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &MatrixRowMajor<T>, result: &mut MatrixRowMajor<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_sub_into!(rm_t, rm_t, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_sub_into!(rm_t, rm_t, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_sub_into!(rm_t, rm, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_sub_into!(rm_t, rm, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_sub_into!(rm, rm_t, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_sub_into!(rm, rm_t, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::rm::macros::simd_sub_into!(rm, rm, rm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::rm::macros::simd_sub_into!(rm, rm, rm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get!(rhs, row, col)
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
            matrix_rm!([$t, 2, 3, $simd], 50,60,70;80,90,100)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2, $simd], 50,80;60,90;70,100);
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
            matrix_rm!([$t, 2, 3, $simd], 38,47,56;65,74,83)
        };
        (rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2, $simd], 38,65;47,74;56,83);
                rm.transpose();
                rm
            }
        };
        (val, rm, $simd:ident, $t:ty) => {
            matrix_rm!([$t, 2, 3, $simd], 43,53,63;73,83,93)
        };
        (val, rm_t, $simd:ident, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2, $simd], 43,73;53,83;63,93);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! test_sub_into_val {
        ($t:ty, $simd:ident, $lhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 7 as $t;
            let mut out = out!($out, $simd, $t);
            lhs.sub_into(rhs, &mut out);
            assert_eq!(out, result!(val, $out, $simd, $t));
        };
    }

    macro_rules! test_sub_into {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let mut out = out!($out, $simd, $t);
            lhs.sub_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $simd, $t));
        };
    }

    macro_rules! fn_test_sub_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!(u8, false, $lhs, $out);
                test_sub_into_val!(u16, false, $lhs, $out);
                test_sub_into_val!(u32, false, $lhs, $out);
                test_sub_into_val!(u64, false, $lhs, $out);
                test_sub_into_val!(u128, false, $lhs, $out);
                test_sub_into_val!(i8, false, $lhs, $out);
                test_sub_into_val!(i16, false, $lhs, $out);
                test_sub_into_val!(i32, false, $lhs, $out);
                test_sub_into_val!(i64, false, $lhs, $out);
                test_sub_into_val!(i128, false, $lhs, $out);
                test_sub_into_val!(f32, false, $lhs, $out);
                test_sub_into_val!(f64, false, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into_val_simd {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!(u8, true, $lhs, $out);
                test_sub_into_val!(u16, true, $lhs, $out);
                test_sub_into_val!(u32, true, $lhs, $out);
                test_sub_into_val!(i8, true, $lhs, $out);
                test_sub_into_val!(i16, true, $lhs, $out);
                test_sub_into_val!(i32, true, $lhs, $out);
                test_sub_into_val!(f32, true, $lhs, $out);
                test_sub_into_val!(f64, true, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!(u8, false, $lhs, $rhs, $out);
                test_sub_into!(u16, false, $lhs, $rhs, $out);
                test_sub_into!(u32, false, $lhs, $rhs, $out);
                test_sub_into!(u64, false, $lhs, $rhs, $out);
                test_sub_into!(u128, false, $lhs, $rhs, $out);
                test_sub_into!(i8, false, $lhs, $rhs, $out);
                test_sub_into!(i16, false, $lhs, $rhs, $out);
                test_sub_into!(i32, false, $lhs, $rhs, $out);
                test_sub_into!(i64, false, $lhs, $rhs, $out);
                test_sub_into!(i128, false, $lhs, $rhs, $out);
                test_sub_into!(f32, false, $lhs, $rhs, $out);
                test_sub_into!(f64, false, $lhs, $rhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!(u8, true, $lhs, $rhs, $out);
                test_sub_into!(u16, true, $lhs, $rhs, $out);
                test_sub_into!(u32, true, $lhs, $rhs, $out);
                test_sub_into!(i8, true, $lhs, $rhs, $out);
                test_sub_into!(i16, true, $lhs, $rhs, $out);
                test_sub_into!(i32, true, $lhs, $rhs, $out);
                test_sub_into!(f32, true, $lhs, $rhs, $out);
                test_sub_into!(f64, true, $lhs, $rhs, $out);
            }
        };
    }

    fn_test_sub_into_val!(test_sub_into_val_rm_rm, rm, rm);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm, rm_t, rm);

    fn_test_sub_into_val!(test_sub_into_val_rm_rm_t, rm, rm_t);

    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm_t, rm_t, rm_t);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_rm_rm, rm, rm);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_rm_t_rm, rm_t, rm);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_rm_rm_t, rm, rm_t);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_rm_t_rm_t, rm_t, rm_t);

    fn_test_sub_into!(test_sub_into_rm_rm_rm, rm, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_rm_t, rm, rm, rm_t);

    fn_test_sub_into!(test_sub_into_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_t_rm_t, rm, rm_t, rm_t);

    fn_test_sub_into!(test_sub_into_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_rm_t, rm_t, rm, rm_t);

    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);

    //////////////////////////////////////////////////////////////////////////////
    // SIMD Tests
    //////////////////////////////////////////////////////////////////////////////
    fn_test_sub_into_simd!(test_sub_into_simd_rm_rm_rm, rm, rm, rm);
    fn_test_sub_into_simd!(test_sub_into_simd_rm_rm_rm_t, rm, rm, rm_t);

    fn_test_sub_into_simd!(test_sub_into_simd_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_sub_into_simd!(test_sub_into_simd_rm_rm_t_rm_t, rm, rm_t, rm_t);

    fn_test_sub_into_simd!(test_sub_into_simd_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_sub_into_simd!(test_sub_into_simd_rm_t_rm_rm_t, rm_t, rm, rm_t);

    fn_test_sub_into_simd!(test_sub_into_simd_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_sub_into_simd!(test_sub_into_simd_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);
}
