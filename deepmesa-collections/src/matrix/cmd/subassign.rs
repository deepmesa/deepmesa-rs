use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::simd_sub_assign;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdSubAssign;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use std::ops::SubAssign;

impl<T> SubAssign<T> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, val: T) {
        if self.use_simd() {
            unsafe {
                SimdKernel::simd_sub_assign(self.cm_data, val, self.cm_len);
            }
            return;
        }

        if self.is_transpose {
            iterate_col_major!(self, row, col, unsafe {
                cmd_sub_assign_t!(self, row, col, val);
            });
        } else {
            iterate_col_major!(self, row, col, unsafe {
                cmd_sub_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> SubAssign<&ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd_t, cmd_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign_t!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd_t, cmd, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign_t!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd, cmd_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd, cmd, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> SubAssign<&RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd_t, rmd_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign_t!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd_t, rmd, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign_t!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd, rmd_t, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_assign!(cmd, rmd, self, rhs);
                iterate_col_major!(self, row, col, unsafe {
                    cmd_sub_assign!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> SubAssign<&DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign,
{
    fn sub_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.sub_assign(&rhs.rmd);
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
    use std::ops::SubAssign;

    macro_rules! lhs {
        (cmd, $simd:ident, $t:ty) => {
            col_major_dataset!([$t, 2, 3, $simd], 10,20,30;40,50,60)
        };
        (cmd_t, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t, 3,2, $simd], 10,40;20,50;30,60);
                cmd.transpose();
                cmd
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
            row_major_dataset!([$t, 2, 3, $simd], 4,13,22;31,40,49)
        };
        (val, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 7,17,27;37,47,57)
        };
    }

    macro_rules! test_sub_assign {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            lhs.sub_assign(&rhs);
            assert_eq!(lhs, result!(rmd, $simd, $t));
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

    fn_test_sub_assign_val!(test_sub_assign_cmd_val, cmd);
    fn_test_sub_assign_val!(test_sub_assign_cmd_t_val, cmd_t);

    fn_test_sub_assign!(test_sub_assign_cmd_rmd, cmd, rmd);
    fn_test_sub_assign!(test_sub_assign_cmd_cmd, cmd, cmd);
    fn_test_sub_assign!(test_sub_assign_cmd_did, cmd, did);
    fn_test_sub_assign!(test_sub_assign_cmd_rmd_t, cmd, rmd_t);
    fn_test_sub_assign!(test_sub_assign_cmd_cmd_t, cmd, cmd_t);
    fn_test_sub_assign!(test_sub_assign_cmd_did_t, cmd, did_t);

    fn_test_sub_assign!(test_sub_assign_cmd_t_rmd, cmd_t, rmd);
    fn_test_sub_assign!(test_sub_assign_cmd_t_cmd, cmd_t, cmd);
    fn_test_sub_assign!(test_sub_assign_cmd_t_did, cmd_t, did);
    fn_test_sub_assign!(test_sub_assign_cmd_t_rmd_t, cmd_t, rmd_t);
    fn_test_sub_assign!(test_sub_assign_cmd_t_cmd_t, cmd_t, cmd_t);
    fn_test_sub_assign!(test_sub_assign_cmd_t_did_t, cmd_t, did_t);

    fn_test_sub_assign_simd_val!(test_sub_assign_simd_cmd_val, cmd);
    fn_test_sub_assign_simd_val!(test_sub_assign_simd_cmd_t_val, cmd_t);

    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_rmd, cmd, rmd);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_cmd, cmd, cmd);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_did, cmd, did);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_rmd_t, cmd, rmd_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_cmd_t, cmd, cmd_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_did_t, cmd, did_t);

    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_rmd, cmd_t, rmd);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_cmd, cmd_t, cmd);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_did, cmd_t, did);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_rmd_t, cmd_t, rmd_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_cmd_t, cmd_t, cmd_t);
    fn_test_sub_assign_simd!(test_sub_assign_simd_cmd_t_did_t, cmd_t, did_t);
}
