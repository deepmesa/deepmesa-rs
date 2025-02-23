use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::MulInto;
use std::ops::Mul;
use std::ops::MulAssign;

impl<T> Mul<T> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(mut self, rhs: T) -> DualIndexDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(mut self, rhs: &RowMajorDataset<T>) -> DualIndexDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(mut self, rhs: &ColMajorDataset<T>) -> DualIndexDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<&DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(mut self, rhs: &DualIndexDataset<T>) -> DualIndexDataset<T> {
        self.mul_assign(rhs);
        return self;
    }
}

impl<T> Mul<T> for &DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(self, rhs: T) -> DualIndexDataset<T> {
        let mut result = DualIndexDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&RowMajorDataset<T>> for &DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(self, rhs: &RowMajorDataset<T>) -> DualIndexDataset<T> {
        let mut result = DualIndexDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&ColMajorDataset<T>> for &DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(self, rhs: &ColMajorDataset<T>) -> DualIndexDataset<T> {
        let mut result = DualIndexDataset::from(&self);
        self.mul_into(rhs, &mut result);
        return result;
    }
}

impl<T> Mul<&DualIndexDataset<T>> for &DualIndexDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    type Output = DualIndexDataset<T>;
    fn mul(self, rhs: &DualIndexDataset<T>) -> DualIndexDataset<T> {
        let mut result = DualIndexDataset::from(&self);
        self.mul_into(rhs, &mut result);
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
    use std::ops::Mul;

    macro_rules! lhs {
        (did, $simd:ident, $t:ty) => {
            dual_index_dataset!([$t, 2, 3, $simd], 2,3,4;5,6,7)
        };
        (did_t, $simd:ident, $t:ty) => {
            {
                let mut did = dual_index_dataset!([$t, 3,2, $simd], 2,5;3,6;4,7);
                did.transpose();
                did
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
            row_major_dataset!([$t, 2, 3, $simd], 12,21,32;45,60,77)
        };
        (val, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 6,9,12;15,18,21)
        };
    }

    macro_rules! test_mul {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let out = lhs.mul(&rhs);
            assert_eq!(out, result!(rmd, $simd, $t));
        };
    }

    macro_rules! test_mul_val {
        ($t:ty, $simd:ident, $lhs:ident) => {
            let lhs = lhs!($lhs, $simd, $t);
            let rhs = 3 as $t;
            let out = lhs.mul(rhs);
            assert_eq!(out, result!(val, $simd, $t));
        };
    }

    macro_rules! fn_test_mul_val {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_val!(u8, false, $lhs);
                test_mul_val!(u16, false, $lhs);
                test_mul_val!(u32, false, $lhs);
                test_mul_val!(u64, false, $lhs);
                test_mul_val!(u128, false, $lhs);
                test_mul_val!(i8, false, $lhs);
                test_mul_val!(i16, false, $lhs);
                test_mul_val!(i32, false, $lhs);
                test_mul_val!(i64, false, $lhs);
                test_mul_val!(i128, false, $lhs);
                test_mul_val!(f32, false, $lhs);
                test_mul_val!(f64, false, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul_val_simd {
        ($fn_name:ident, $lhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul_val!(u8, true, $lhs);
                test_mul_val!(u16, true, $lhs);
                test_mul_val!(u32, true, $lhs);
                test_mul_val!(i8, true, $lhs);
                test_mul_val!(i16, true, $lhs);
                test_mul_val!(i32, true, $lhs);
                test_mul_val!(f32, true, $lhs);
                test_mul_val!(f64, true, $lhs);
            }
        };
    }

    macro_rules! fn_test_mul {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul!(u8, false, $lhs, $rhs);
                test_mul!(u16, false, $lhs, $rhs);
                test_mul!(u32, false, $lhs, $rhs);
                test_mul!(u64, false, $lhs, $rhs);
                test_mul!(u128, false, $lhs, $rhs);
                test_mul!(i8, false, $lhs, $rhs);
                test_mul!(i16, false, $lhs, $rhs);
                test_mul!(i32, false, $lhs, $rhs);
                test_mul!(i64, false, $lhs, $rhs);
                test_mul!(i128, false, $lhs, $rhs);
                test_mul!(f32, false, $lhs, $rhs);
                test_mul!(f64, false, $lhs, $rhs);
            }
        };
    }

    macro_rules! fn_test_mul_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident) => {
            #[test]
            fn $fn_name() {
                test_mul!(u8, true, $lhs, $rhs);
                test_mul!(u16, true, $lhs, $rhs);
                test_mul!(u32, true, $lhs, $rhs);
                test_mul!(i8, true, $lhs, $rhs);
                test_mul!(i16, true, $lhs, $rhs);
                test_mul!(i32, true, $lhs, $rhs);
                test_mul!(f32, true, $lhs, $rhs);
                test_mul!(f64, true, $lhs, $rhs);
            }
        };
    }

    fn_test_mul_val!(test_mul_val_did, did);
    fn_test_mul_val!(test_mul_val_did_t, did_t);

    fn_test_mul_val_simd!(test_mul_simd_val_did, did);
    fn_test_mul_val_simd!(test_mul_simd_val_did_t, did_t);

    fn_test_mul!(test_mul_did_rmd, did, rmd);
    fn_test_mul!(test_mul_did_cmd, did, cmd);
    fn_test_mul!(test_mul_did_did, did, did);

    fn_test_mul!(test_mul_did_rmd_t, did, rmd_t);
    fn_test_mul!(test_mul_did_cmd_t, did, cmd_t);
    fn_test_mul!(test_mul_did_did_t, did, did_t);

    fn_test_mul!(test_mul_did_t_rmd, did_t, rmd);
    fn_test_mul!(test_mul_did_t_cmd, did_t, cmd);
    fn_test_mul!(test_mul_did_t_did, did_t, did);

    fn_test_mul!(test_mul_did_t_rmd_t, did_t, rmd_t);
    fn_test_mul!(test_mul_did_t_cmd_t, did_t, cmd_t);
    fn_test_mul!(test_mul_did_t_did_t, did_t, did_t);

    //
    fn_test_mul_simd!(test_mul_simd_did_rmd, did, rmd);
    fn_test_mul_simd!(test_mul_simd_did_cmd, did, cmd);
    fn_test_mul_simd!(test_mul_simd_did_did, did, did);

    fn_test_mul_simd!(test_mul_simd_did_rmd_t, did, rmd_t);
    fn_test_mul_simd!(test_mul_simd_did_cmd_t, did, cmd_t);
    fn_test_mul_simd!(test_mul_simd_did_did_t, did, did_t);

    fn_test_mul_simd!(test_mul_simd_did_t_rmd, did_t, rmd);
    fn_test_mul_simd!(test_mul_simd_did_t_cmd, did_t, cmd);
    fn_test_mul_simd!(test_mul_simd_did_t_did, did_t, did);

    fn_test_mul_simd!(test_mul_simd_did_t_rmd_t, did_t, rmd_t);
    fn_test_mul_simd!(test_mul_simd_did_t_cmd_t, did_t, cmd_t);
    fn_test_mul_simd!(test_mul_simd_did_t_did_t, did_t, did_t);
}
