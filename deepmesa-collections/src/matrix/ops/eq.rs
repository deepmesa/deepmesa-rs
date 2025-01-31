use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn eq(&self, other: &Matrix<T>) -> bool {
        match &self.data {
            MatrixData::ColMajor(ds) => match &other.data {
                MatrixData::ColMajor(other) => return ds.eq(other),
                MatrixData::RowMajor(other) => return ds.eq(other),
                MatrixData::DualIndex(other) => return ds.eq(other),
            },
            MatrixData::RowMajor(ds) => match &other.data {
                MatrixData::ColMajor(other) => return ds.eq(other),
                MatrixData::RowMajor(other) => return ds.eq(other),
                MatrixData::DualIndex(other) => return ds.eq(other),
            },

            MatrixData::DualIndex(ds) => match &other.data {
                MatrixData::ColMajor(other) => return ds.eq(other),
                MatrixData::RowMajor(other) => return ds.eq(other),
                MatrixData::DualIndex(other) => return ds.eq(other),
            },
        }
    }
}
