use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::simd_mul_assign;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdMulAssign;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use std::ops::MulAssign;

impl<T> MulAssign<T> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, val: T) {
        if self.use_simd() {
            unsafe {
                SimdKernel::simd_mul_assign(self.rm_data, val, self.rm_len);
            }
            return;
        }

        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rmd_mul_assign_t!(self, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rmd_mul_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> MulAssign<&RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd_t, rmd_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign_t!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd_t, rmd, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign_t!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd, rmd_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd, rmd, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> MulAssign<&ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd_t, cmd_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign_t!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd_t, cmd, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign_t!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd, cmd_t, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::rmd::macros::simd_mul_assign!(rmd, cmd, self, rhs);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_mul_assign!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> MulAssign<&DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign,
{
    fn mul_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.mul_assign(&rhs.rmd);
    }
}

#[cfg(test)]
mod tests {

    use crate::matrix::cmd::data::*;
    use crate::matrix::cmd::macros::col_major_dataset;
    use crate::matrix::did::data::*;
    use crate::matrix::did::macros::dual_index_dataset;
    use crate::matrix::matrix::matrix;
    use crate::matrix::matrix::*;
    use crate::matrix::rmd::data::*;
    use crate::matrix::rmd::macros::row_major_dataset;
    use crate::matrix::traits::*;
    use std::any::Any;
    use std::ops::MulAssign;

    macro_rules! lhs {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 1,2,3;4,5,6)
        };
        (rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t, 3,2, $simd], 1,4;2,5;3,6);
                rmd.transpose();
                rmd
            }
        };
    }

    macro_rules! rhs {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t,2,3, $simd], 6,7,8;9,10,11)
        };
        (cmd, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
                cmd.transpose();
                cmd
            }
        };
        (did, $simd:ident, $t:ty) => {
            dual_index_dataset!([$t,2,3,false], 6,7,8;9,10,11)
        };
        (rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
                rmd.transpose();
                rmd
            }
        };
        (cmd_t, $simd:ident, $t:ty) => {
            col_major_dataset!([$t,2,3, false], 6,7,8;9,10,11)
        };
        (did_t, $simd:ident, $t:ty) => {
            {
                let mut did = dual_index_dataset!([$t,3,2, $simd], 6,9;7,10;8,11);
                did.transpose();
                did
            }
        };
    }

    macro_rules! result {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 6,14,24;36,50,66)
        };
        (val, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 3,6,9;12,15,18)
        };
    }

    macro_rules! test_mul_assign {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            lhs.mul_assign(&rhs);
            assert_eq!(lhs, result!(rmd, $simd, $t));
        };
    }

    macro_rules! test_mul_assign_val {
        ($t:ty, $simd: ident, $lhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            lhs.mul_assign(rhs);
            assert_eq!(lhs, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_mul_assign_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_assign_val!(u8, false, $lhs);
                test_mul_assign_val!(u16, false, $lhs);
                test_mul_assign_val!(u32, false, $lhs);
                test_mul_assign_val!(u64, false, $lhs);
                test_mul_assign_val!(u128, false, $lhs);
                test_mul_assign_val!(i8, false, $lhs);
                test_mul_assign_val!(i16, false, $lhs);
                test_mul_assign_val!(i32, false, $lhs);
                test_mul_assign_val!(i64, false, $lhs);
                test_mul_assign_val!(i128, false, $lhs);
                test_mul_assign_val!(f32, false, $lhs);
                test_mul_assign_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul_assign {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_assign!(u8, false, $lhs, $rhs);
                test_mul_assign!(u16, false, $lhs, $rhs);
                test_mul_assign!(u32, false, $lhs, $rhs);
                test_mul_assign!(u64, false, $lhs, $rhs);
                test_mul_assign!(u128, false, $lhs, $rhs);
                test_mul_assign!(i8, false, $lhs, $rhs);
                test_mul_assign!(i16, false, $lhs, $rhs);
                test_mul_assign!(i32, false, $lhs, $rhs);
                test_mul_assign!(i64, false, $lhs, $rhs);
                test_mul_assign!(i128, false, $lhs, $rhs);
                test_mul_assign!(f32, false, $lhs, $rhs);
                test_mul_assign!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_mul_assign_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_assign!(u8, true, $lhs, $rhs);
                test_mul_assign!(u16, true, $lhs, $rhs);
                test_mul_assign!(u32, true, $lhs, $rhs);
                test_mul_assign!(i8, true, $lhs, $rhs);
                test_mul_assign!(i16, true, $lhs, $rhs);
                test_mul_assign!(i32, true, $lhs, $rhs);
                test_mul_assign!(f32, true, $lhs, $rhs);
                test_mul_assign!(f64, true, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_mul_assign_simd_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_assign_val!(u8, true, $lhs);
                test_mul_assign_val!(u16, true, $lhs);
                test_mul_assign_val!(u32, true, $lhs);
                test_mul_assign_val!(i8, true, $lhs);
                test_mul_assign_val!(i16, true, $lhs);
                test_mul_assign_val!(i32, true, $lhs);
                test_mul_assign_val!(f32, true, $lhs);
                test_mul_assign_val!(f64, true, $lhs);
            }
        };
    }

    fn_test_mul_assign_val!(test_mul_assign_rmd_val, rmd);
    fn_test_mul_assign_val!(test_mul_assign_rmd_t_val, rmd_t);

    fn_test_mul_assign!(test_mul_assign_rmd_rmd, rmd, rmd);
    fn_test_mul_assign!(test_mul_assign_rmd_cmd, rmd, cmd);
    fn_test_mul_assign!(test_mul_assign_rmd_did, rmd, did);
    fn_test_mul_assign!(test_mul_assign_rmd_rmd_t, rmd, rmd_t);
    fn_test_mul_assign!(test_mul_assign_rmd_cmd_t, rmd, cmd_t);
    fn_test_mul_assign!(test_mul_assign_rmd_did_t, rmd, did_t);

    fn_test_mul_assign!(test_mul_assign_rmd_t_rmd, rmd_t, rmd);
    fn_test_mul_assign!(test_mul_assign_rmd_t_cmd, rmd_t, cmd);
    fn_test_mul_assign!(test_mul_assign_rmd_t_did, rmd_t, did);
    fn_test_mul_assign!(test_mul_assign_rmd_t_rmd_t, rmd_t, rmd_t);
    fn_test_mul_assign!(test_mul_assign_rmd_t_cmd_t, rmd_t, cmd_t);
    fn_test_mul_assign!(test_mul_assign_rmd_t_did_t, rmd_t, did_t);

    fn_test_mul_assign_simd_val!(test_mul_assign_simd_rmd_val, rmd);
    fn_test_mul_assign_simd_val!(test_mul_assign_simd_rmd_t_val, rmd_t);

    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_rmd, rmd, rmd);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_cmd, rmd, cmd);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_did, rmd, did);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_rmd_t, rmd, rmd_t);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_cmd_t, rmd, cmd_t);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_did_t, rmd, did_t);

    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_rmd, rmd_t, rmd);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_cmd, rmd_t, cmd);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_did, rmd_t, did);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_rmd_t, rmd_t, rmd_t);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_cmd_t, rmd_t, cmd_t);
    fn_test_mul_assign_simd!(test_mul_assign_simd_rmd_t_did_t, rmd_t, did_t);
}
