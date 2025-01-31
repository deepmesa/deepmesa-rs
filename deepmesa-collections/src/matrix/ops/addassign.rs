use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::simd::traits::SimdAddAssign;
use crate::matrix::traits::MatrixElement;

macro_rules! dispatch_mut {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &mut $self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

macro_rules! dispatch {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &$self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

impl<T> std::ops::AddAssign<T> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: T) {
        // if self.is_simd_enabled() {
        //     #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        //     {
        //         self.simd_add_assign;
        //         return;
        //     }
        // }

        dispatch_mut!(self, ds, ds.add_assign(rhs));

        // match &mut self.data {
        //     MatrixData::ColMajor(ds) => ds.add_assign(rhs),
        //     MatrixData::RowMajor(ds) => ds.add_assign(rhs),
        //     MatrixData::DualIndex(ds) => ds.add_assign(rhs),
        // }
    }
}

impl<T> std::ops::AddAssign<&Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &Matrix<T>) {
        shape_check!(self, rhs);
        dispatch_mut!(self, ds, dispatch!(rhs, rhs, ds.add_assign(rhs)));

        // match &mut self.data {
        //     MatrixData::ColMajor(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        //     MatrixData::RowMajor(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        //     MatrixData::DualIndex(ds) => match &rhs.data {
        //         MatrixData::ColMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::RowMajor(rhs) => ds.add_assign(rhs),
        //         MatrixData::DualIndex(rhs) => ds.add_assign(rhs),
        //     },
        // }
    }
}
