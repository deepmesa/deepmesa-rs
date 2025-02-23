use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::SubInto;
use std::ops::Sub;
use std::ops::SubAssign;

impl<T> Sub<T> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(mut self, rhs: T) -> RowMajorDataset<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<&RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(mut self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<&ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(mut self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<&DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(mut self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        self.sub_assign(rhs);
        return self;
    }
}

impl<T> Sub<T> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(self, rhs: T) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

impl<T> Sub<&RowMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(self, rhs: &RowMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

impl<T> Sub<&ColMajorDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(self, rhs: &ColMajorDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
    }
}

impl<T> Sub<&DualIndexDataset<T>> for &RowMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    type Output = RowMajorDataset<T>;
    fn sub(self, rhs: &DualIndexDataset<T>) -> RowMajorDataset<T> {
        let mut result = RowMajorDataset::from(&self);
        self.sub_into(rhs, &mut result);
        return result;
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
    use std::ops::Sub;

    macro_rules! lhs {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 10,20,30;40,50,60)
        };
        (rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t, 3,2, $simd], 10,40;20,50;30,60);
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
            row_major_dataset!([$t, 2, 3, $simd], 4,13,22;31,40,49)
        };
        (val, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 7,17,27;37,47,57)
        };
    }

    macro_rules! test_sub {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.sub(&rhs);
            assert_eq!(out, result!(rmd, $simd, $t));
        };
    }

    macro_rules! test_sub_val {
        ($t:ty, $simd:ident, $lhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            let out = lhs.sub(rhs);
            assert_eq!(out, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_sub_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_val!(u8, false, $lhs);
                test_sub_val!(u16, false, $lhs);
                test_sub_val!(u32, false, $lhs);
                test_sub_val!(u64, false, $lhs);
                test_sub_val!(u128, false, $lhs);
                test_sub_val!(i8, false, $lhs);
                test_sub_val!(i16, false, $lhs);
                test_sub_val!(i32, false, $lhs);
                test_sub_val!(i64, false, $lhs);
                test_sub_val!(i128, false, $lhs);
                test_sub_val!(f32, false, $lhs);
                test_sub_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub_val_simd {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_val!(u8, true, $lhs);
                test_sub_val!(u16, true, $lhs);
                test_sub_val!(u32, true, $lhs);
                test_sub_val!(i8, true, $lhs);
                test_sub_val!(i16, true, $lhs);
                test_sub_val!(i32, true, $lhs);
                test_sub_val!(f32, true, $lhs);
                test_sub_val!(f64, true, $lhs);
            }
        };
    }

    macro_rules! fn_test_sub {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub!(u8, false, $lhs, $rhs);
                test_sub!(u16, false, $lhs, $rhs);
                test_sub!(u32, false, $lhs, $rhs);
                test_sub!(u64, false, $lhs, $rhs);
                test_sub!(u128, false, $lhs, $rhs);
                test_sub!(i8, false, $lhs, $rhs);
                test_sub!(i16, false, $lhs, $rhs);
                test_sub!(i32, false, $lhs, $rhs);
                test_sub!(i64, false, $lhs, $rhs);
                test_sub!(i128, false, $lhs, $rhs);
                test_sub!(f32, false, $lhs, $rhs);
                test_sub!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_sub_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_sub!(u8, true, $lhs, $rhs);
                test_sub!(u16, true, $lhs, $rhs);
                test_sub!(u32, true, $lhs, $rhs);
                test_sub!(i8, true, $lhs, $rhs);
                test_sub!(i16, true, $lhs, $rhs);
                test_sub!(i32, true, $lhs, $rhs);
                test_sub!(f32, true, $lhs, $rhs);
                test_sub!(f64, true, $lhs, $rhs);
            }
        };
    }

    fn_test_sub_val!(test_sub_val_rmd, rmd);
    fn_test_sub_val!(test_sub_val_rmd_t, rmd_t);

    fn_test_sub_val_simd!(test_sub_simd_val_rmd, rmd);
    fn_test_sub_val_simd!(test_sub_simd_val_rmd_t, rmd_t);

    fn_test_sub!(test_sub_rmd_rmd, rmd, rmd);
    fn_test_sub!(test_sub_rmd_cmd, rmd, cmd);
    fn_test_sub!(test_sub_rmd_did, rmd, did);

    fn_test_sub!(test_sub_rmd_rmd_t, rmd, rmd_t);
    fn_test_sub!(test_sub_rmd_cmd_t, rmd, cmd_t);
    fn_test_sub!(test_sub_rmd_did_t, rmd, did_t);

    fn_test_sub!(test_sub_rmd_t_rmd, rmd_t, rmd);
    fn_test_sub!(test_sub_rmd_t_cmd, rmd_t, cmd);
    fn_test_sub!(test_sub_rmd_t_did, rmd_t, did);

    fn_test_sub!(test_sub_rmd_t_rmd_t, rmd_t, rmd_t);
    fn_test_sub!(test_sub_rmd_t_cmd_t, rmd_t, cmd_t);
    fn_test_sub!(test_sub_rmd_t_did_t, rmd_t, did_t);

    //
    fn_test_sub_simd!(test_sub_simd_rmd_rmd, rmd, rmd);
    fn_test_sub_simd!(test_sub_simd_rmd_cmd, rmd, cmd);
    fn_test_sub_simd!(test_sub_simd_rmd_did, rmd, did);

    fn_test_sub_simd!(test_sub_simd_rmd_rmd_t, rmd, rmd_t);
    fn_test_sub_simd!(test_sub_simd_rmd_cmd_t, rmd, cmd_t);
    fn_test_sub_simd!(test_sub_simd_rmd_did_t, rmd, did_t);

    fn_test_sub_simd!(test_sub_simd_rmd_t_rmd, rmd_t, rmd);
    fn_test_sub_simd!(test_sub_simd_rmd_t_cmd, rmd_t, cmd);
    fn_test_sub_simd!(test_sub_simd_rmd_t_did, rmd_t, did);

    fn_test_sub_simd!(test_sub_simd_rmd_t_rmd_t, rmd_t, rmd_t);
    fn_test_sub_simd!(test_sub_simd_rmd_t_cmd_t, rmd_t, cmd_t);
    fn_test_sub_simd!(test_sub_simd_rmd_t_did_t, rmd_t, did_t);
}
