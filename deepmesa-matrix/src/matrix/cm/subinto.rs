use crate::matrix::cm::macros::*;
use crate::matrix::cm::MatrixColMajor;
use crate::matrix::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdSubInto;
use crate::matrix::traits::{MatrixElement, SubInto};

impl<T> SubInto<T, MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut MatrixColMajor<T>) {
        shape_check!(self, result);
        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cm::macros::simd_sub_into!(cm_t, val, cm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cm_assign_t!(result, row, col, cm_get_t!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cm::macros::simd_sub_into!(cm_t, val, cm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cm_assign!(result, row, col, cm_get_t!(self, row, col) - rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cm::macros::simd_sub_into!(cm, val, cm_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cm_assign_t!(result, row, col, cm_get!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cm::macros::simd_sub_into!(cm, val, cm, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cm_assign!(result, row, col, cm_get!(self, row, col) - rhs);
                });
            }
        }
    }
}

impl<T> SubInto<&MatrixColMajor<T>, MatrixColMajor<T>> for MatrixColMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &MatrixColMajor<T>, result: &mut MatrixColMajor<T>) {
        shape_check!(self, rhs);
        shape_check!(self, result);
        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cm::macros::simd_sub_into!(cm_t, cm_t, cm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign_t!(
                            result,
                            row,
                            col,
                            cm_get_t!(self, row, col) - cm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cm::macros::simd_sub_into!(cm_t, cm_t, cm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign!(
                            result,
                            row,
                            col,
                            cm_get_t!(self, row, col) - cm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cm::macros::simd_sub_into!(cm_t, cm, cm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign_t!(
                            result,
                            row,
                            col,
                            cm_get_t!(self, row, col) - cm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cm::macros::simd_sub_into!(cm_t, cm, cm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign!(
                            result,
                            row,
                            col,
                            cm_get_t!(self, row, col) - cm_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cm::macros::simd_sub_into!(cm, cm_t, cm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign_t!(
                            result,
                            row,
                            col,
                            cm_get!(self, row, col) - cm_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cm::macros::simd_sub_into!(cm, cm_t, cm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign!(
                            result,
                            row,
                            col,
                            cm_get!(self, row, col) - cm_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cm::macros::simd_sub_into!(cm, cm, cm_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign_t!(
                            result,
                            row,
                            col,
                            cm_get!(self, row, col) - cm_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cm::macros::simd_sub_into!(cm, cm, cm, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cm_assign!(
                            result,
                            row,
                            col,
                            cm_get!(self, row, col) - cm_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cm::macros::*;
    use crate::matrix::cm::*;
    use crate::matrix::traits::*;

    macro_rules! lhs {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 50,80;60,90;70,100)
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3,2, $simd], 50,60,70;80,90,100);
                cm.transpose();
                cm
            }
        };
    }

    macro_rules! rhs {
        (cm, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t,3,2, $simd], 12,13,14;15,16,17);
                cm.transpose();
                cm
            }
        };
        (cm_t, $simd:ident, $t:ty) => {
            matrix_cm!([$t,2,3, false], 12,15;13,16;14,17)
        };
    }

    macro_rules! out {
        (cm, $simd:ident, $t:ty) => {
            MatrixColMajor::<$t>::new(2, 3, $simd)
        };
        (cm_t, $simd:ident, $t:ty) => {{
            let mut cm = MatrixColMajor::<$t>::new(3, 2, $simd);
            cm.transpose();
            cm
        }};
    }

    macro_rules! result {
        (cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 38,65;47,74;56,83)
        };
        (cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3, 2, $simd], 38,47,56;65,74,83);
                cm.transpose();
                cm
            }
        };
        (val, cm, $simd:ident, $t:ty) => {
            matrix_cm!([$t, 2, 3, $simd], 43,73;53,83;63,93)
        };
        (val, cm_t, $simd:ident, $t:ty) => {
            {
                let mut cm = matrix_cm!([$t, 3, 2, $simd], 43,53,63;73,83,93);
                cm.transpose();
                cm
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

    fn_test_sub_into_val!(test_sub_into_val_cm_cm, cm, cm);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_cm, cm_t, cm);
    fn_test_sub_into_val!(test_sub_into_val_cm_cm_t, cm, cm_t);
    fn_test_sub_into_val!(test_sub_into_val_cm_t_cm_t, cm_t, cm_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cm_cm, cm, cm);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cm_t_cm, cm_t, cm);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cm_cm_t, cm, cm_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cm_t_cm_t, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_cm, cm, cm, cm);
    fn_test_sub_into!(test_sub_into_cm_cm_cm_t, cm, cm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_cm_t_cm, cm, cm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_cm_t_cm_t, cm, cm_t, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_cm, cm_t, cm, cm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_cm_t, cm_t, cm, cm_t);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_cm, cm_t, cm_t, cm);
    fn_test_sub_into!(test_sub_into_cm_t_cm_t_cm_t, cm_t, cm_t, cm_t);

    //////////////////////////////////////////////////////////////////////////////
    // SIMD Tests
    //////////////////////////////////////////////////////////////////////////////
    fn_test_sub_into_simd!(test_sub_into_simd_cm_cm_cm, cm, cm, cm);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_cm_cm_t, cm, cm, cm_t);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_cm_t_cm, cm, cm_t, cm);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_cm_t_cm_t, cm, cm_t, cm_t);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_t_cm_cm, cm_t, cm, cm);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_t_cm_cm_t, cm_t, cm, cm_t);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_t_cm_t_cm, cm_t, cm_t, cm);
    fn_test_sub_into_simd!(test_sub_into_simd_cm_t_cm_t_cm_t, cm_t, cm_t, cm_t);
}
