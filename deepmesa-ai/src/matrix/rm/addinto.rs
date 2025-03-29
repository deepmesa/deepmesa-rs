use crate::matrix::macros::*;
use crate::matrix::rm::macros::*;
use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::traits::{AddInto, MatrixElement};

impl<T> AddInto<T, MatrixRowMajor<T>> for MatrixRowMajor<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut MatrixRowMajor<T>) {
        shape_check!(self, result);
        if self.is_transpose {
            if result.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get_t!(self, row, col) + rhs);
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign!(result, row, col, rm_get_t!(self, row, col) + rhs);
                });
            }
        } else {
            if result.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rm_assign_t!(result, row, col, rm_get!(self, row, col) + rhs);
                });
            } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get_t!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get_t!(rhs, row, col)
                        );
                    });
                } else {
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
                    iterate_row_major!(self, row, col, unsafe {
                        rm_assign_t!(
                            result,
                            row,
                            col,
                            rm_get!(self, row, col) + rm_get!(rhs, row, col)
                        );
                    });
                } else {
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
        (rm, $t:ty) => {
            matrix_rm!([$t, 2, 3], 5,6,7;8,9,10)
        };
        (rm_t, $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3,2], 5,8;6,9;7,10);
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
        (rm,  $t:ty) => {
            MatrixRowMajor::<$t>::new(2, 3)
        };
        (rm_t,  $t:ty) => {{
            let mut rm = MatrixRowMajor::<$t>::new(3, 2);
            rm.transpose();
            rm
        }};
    }

    macro_rules! result {
        (rm,  $t:ty) => {
            matrix_rm!([$t, 2, 3], 17,19,21;23,25,27)
        };
        (rm_t,  $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2], 17,23;19,25;21,27);
                rm.transpose();
                rm
            }
        };
        (val, rm,  $t:ty) => {
            matrix_rm!([$t, 2, 3], 12,13,14;15,16,17)
        };
        (val, rm_t,  $t:ty) => {
            {
                let mut rm = matrix_rm!([$t, 3, 2], 12,15;13,16;14,17);
                rm.transpose();
                rm
            }
        };
    }

    macro_rules! test_add_into_val {
        ($t:ty, $lhs:ident, $out:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = 7 as $t;
            let mut out = out!($out, $t);
            lhs.add_into(rhs, &mut out);
            assert_eq!(out, result!(val, $out, $t));
        };
    }

    macro_rules! test_add_into {
        ($t:ty, $lhs:ident, $rhs:ident, $out:ident) => {
            let lhs = lhs!($lhs, $t);
            let rhs = rhs!($rhs, $t);
            let mut out = out!($out, $t);
            lhs.add_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $t));
        };
    }

    macro_rules! fn_test_add_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into_val!(u8, $lhs, $out);
                test_add_into_val!(u16, $lhs, $out);
                test_add_into_val!(u32, $lhs, $out);
                test_add_into_val!(u64, $lhs, $out);
                test_add_into_val!(u128, $lhs, $out);
                test_add_into_val!(i8, $lhs, $out);
                test_add_into_val!(i16, $lhs, $out);
                test_add_into_val!(i32, $lhs, $out);
                test_add_into_val!(i64, $lhs, $out);
                test_add_into_val!(i128, $lhs, $out);
                test_add_into_val!(f32, $lhs, $out);
                test_add_into_val!(f64, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_add_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_add_into!(u8, $lhs, $rhs, $out);
                test_add_into!(u16, $lhs, $rhs, $out);
                test_add_into!(u32, $lhs, $rhs, $out);
                test_add_into!(u64, $lhs, $rhs, $out);
                test_add_into!(u128, $lhs, $rhs, $out);
                test_add_into!(i8, $lhs, $rhs, $out);
                test_add_into!(i16, $lhs, $rhs, $out);
                test_add_into!(i32, $lhs, $rhs, $out);
                test_add_into!(i64, $lhs, $rhs, $out);
                test_add_into!(i128, $lhs, $rhs, $out);
                test_add_into!(f32, $lhs, $rhs, $out);
                test_add_into!(f64, $lhs, $rhs, $out);
            }
        };
    }

    fn_test_add_into_val!(test_add_into_val_rm_rm, rm, rm);
    fn_test_add_into_val!(test_add_into_val_rm_t_rm, rm_t, rm);
    fn_test_add_into_val!(test_add_into_val_rm_rm_t, rm, rm_t);
    fn_test_add_into_val!(test_add_into_val_rm_t_rm_t, rm_t, rm_t);

    fn_test_add_into!(test_add_into_rm_rm_rm, rm, rm, rm);
    fn_test_add_into!(test_add_into_rm_rm_rm_t, rm, rm, rm_t);

    fn_test_add_into!(test_add_into_rm_rm_t_rm, rm, rm_t, rm);
    fn_test_add_into!(test_add_into_rm_rm_t_rm_t, rm, rm_t, rm_t);

    fn_test_add_into!(test_add_into_rm_t_rm_rm, rm_t, rm, rm);
    fn_test_add_into!(test_add_into_rm_t_rm_rm_t, rm_t, rm, rm_t);

    fn_test_add_into!(test_add_into_rm_t_rm_t_rm, rm_t, rm_t, rm);
    fn_test_add_into!(test_add_into_rm_t_rm_t_rm_t, rm_t, rm_t, rm_t);
}
