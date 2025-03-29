use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::{MatrixElement, SubInto};

impl<T> SubInto<T, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut MatrixRowMajor<T>) {
        shape_check!(self, result);
        if self.is_transpose {
            if result.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get_t!(self, row, col) - rhs);
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get_t!(self, row, col) - rhs);
                });
            }
        } else {
            if result.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get!(self, row, col) - rhs);
                });
            } else {
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
        shape_check!(self, rhs);
        shape_check!(self, result);
        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) - rm_get!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) - rm_get!(rhs, row, col)
                        );
                    });
                } else {
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
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 50,60,70;80,90,100)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2], 50,80;60,90;70,100);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! rhs {
        (rm, $t:ty) => {
            matrix_rm!([$t,2,3], 12,13,14;15,16,17)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t,3,2], 12,15;13,16;14,17);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! out {
        (rm, $t:ty) => {
            MatrixRowMajor::<$t>::new(2, 3)
        };
        (rm_t, $t:ty) => {{
            let mut rm = MatrixRowMajor::<$t>::new(3, 2);
            rm.transpose();
            rm
        }};
    }

    macro_rules! result {
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 38,47,56;65,74,83)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2], 38,65;47,74;56,83);
                rm.transpose();
                rm
            }
        };
        (val, rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 43,53,63;73,83,93)
        };
        (val, rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2], 43,73;53,83;63,93);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! test_sub_into_val {
        ($t:ty, $lhs:ident, $out:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = 7 as $t;
            let mut out = out!($out, $t);
            lhs.sub_into(rhs, &mut out);
            assert_eq!(out, result!(val, $out, $t));
        };
    }

    macro_rules! test_sub_into {
        ($t:ty, $lhs:ident, $rhs:ident, $out:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            let mut out = out!($out, $t);
            lhs.sub_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $t));
        };
    }

    macro_rules! fn_test_sub_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!(u8, $lhs, $out);
                test_sub_into_val!(u16, $lhs, $out);
                test_sub_into_val!(u32, $lhs, $out);
                test_sub_into_val!(u64, $lhs, $out);
                test_sub_into_val!(u128, $lhs, $out);
                test_sub_into_val!(i8, $lhs, $out);
                test_sub_into_val!(i16, $lhs, $out);
                test_sub_into_val!(i32, $lhs, $out);
                test_sub_into_val!(i64, $lhs, $out);
                test_sub_into_val!(i128, $lhs, $out);
                test_sub_into_val!(f32, $lhs, $out);
                test_sub_into_val!(f64, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!(u8, $lhs, $rhs, $out);
                test_sub_into!(u16, $lhs, $rhs, $out);
                test_sub_into!(u32, $lhs, $rhs, $out);
                test_sub_into!(u64, $lhs, $rhs, $out);
                test_sub_into!(u128, $lhs, $rhs, $out);
                test_sub_into!(i8, $lhs, $rhs, $out);
                test_sub_into!(i16, $lhs, $rhs, $out);
                test_sub_into!(i32, $lhs, $rhs, $out);
                test_sub_into!(i64, $lhs, $rhs, $out);
                test_sub_into!(i128, $lhs, $rhs, $out);
                test_sub_into!(f32, $lhs, $rhs, $out);
                test_sub_into!(f64, $lhs, $rhs, $out);
            }
        };
    }

    fn_test_sub_into_val!(test_sub_into_val_rm_rm, rm, rm);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm, rm_t, rm);
    fn_test_sub_into_val!(test_sub_into_val_rm_rm_t, rm, rm_t);
    fn_test_sub_into_val!(test_sub_into_val_rm_t_rm_t, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_rm, rm, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_rm_t, rm, rm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_rm_t_rm_t, rm, rm_t, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_rm_t, rm_t, rm, rm_t);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_sub_into!(test_sub_into_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);
}
