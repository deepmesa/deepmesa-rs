use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::matrix::MatrixType;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

use super::cmd::data::ColMajorDataset;
use super::iter::VectorIterator;
use super::rmd::data::RowMajorDataset;

pub struct Vector<T>
where
    T: MatrixElement<Output = T>,
{
    pub(in crate::matrix) m: Matrix<T>,
    pub(in crate::matrix) v_type: VectorType,
}

#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub enum VectorType {
    RowVector,
    ColVector,
}

impl<T> Vector<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(size: usize, v_type: VectorType, simd_optimized: bool) -> Vector<T> {
        match v_type {
            VectorType::RowVector => Vector {
                m: Matrix::new(1, size, MatrixType::RowMajor, simd_optimized),
                v_type,
            },
            VectorType::ColVector => Vector {
                m: Matrix::new(size, 1, MatrixType::ColMajor, simd_optimized),
                v_type,
            },
        }
    }

    // pub fn row_vector(src: &Vec<T>, simd_optimized: bool) -> Vector<T> {
    //     return Vector {
    //         m: Matrix::from_row_major(1, src.len(), MatrixType::RowMajor, simd_optimized, src),
    //     };
    // }

    // pub fn col_vector(src: &Vec<T>, simd_optimized: bool) -> Vector<T> {
    //     return Vector {
    //         m: Matrix::from_column_major(src.len(), 1, MatrixType::ColMajor, simd_optimized, src),
    //     };
    // }

    pub(in crate::matrix) fn get_cmd(&self) -> &ColMajorDataset<T> {
        match self.v_type {
            VectorType::ColVector => match &self.m.data {
                MatrixData::ColMajor(ds) => return ds,
                _ => {
                    panic!("invalid dataset in Col Vector");
                }
            },
            VectorType::RowVector => {
                panic!("Row Vector doesn't have a ColMajorDataset");
            }
        }
    }

    pub(in crate::matrix) fn get_rmd(&self) -> &RowMajorDataset<T> {
        match self.v_type {
            VectorType::RowVector => match &self.m.data {
                MatrixData::RowMajor(ds) => return ds,
                _ => {
                    panic!("invalid dataset in Col Vector");
                }
            },
            VectorType::ColVector => {
                panic!("Row Vector doesn't have a ColMajorDataset");
            }
        }
    }

    pub fn is_col_vector(&self) -> bool {
        return self.v_type == VectorType::ColVector;
    }

    pub fn is_row_vector(&self) -> bool {
        return self.v_type == VectorType::RowVector;
    }

    pub fn transpose(&mut self) {
        self.m.transpose();
    }

    // pub fn fill(&mut self, val: T) {
    //     self.m.fill(val);
    // }

    pub fn rows(&self) -> usize {
        return self.m.rows();
    }

    pub fn cols(&self) -> usize {
        return self.m.cols();
    }
    pub fn len(&self) -> usize {
        if self.m.cols() == 1 {
            return self.m.rows();
        }

        return self.m.cols();
    }

    pub fn set(&mut self, idx: usize, val: T) {
        if self.m.cols() == 1 {
            self.m.set(idx, 0, val);
        }
        self.m.set(0, idx, val);
    }

    //TODO: needs a bounds check
    pub fn get(&self, idx: usize) -> T {
        if self.m.cols() == 1 {
            return self.m.get(idx, 0);
        }
        return self.m.get(0, idx);
    }

    pub fn iter(&self) -> VectorIterator<T> {
        return VectorIterator::new(&self);
    }
}

impl<T> Vector<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    pub fn sum(&self) -> T {
        match self.v_type {
            VectorType::ColVector => {
                //                return self.m.sum_col(0);
            }
            VectorType::RowVector => {
                //                return self.m.sum_row(0);
            }
        }

        return T::zero();
    }

    pub fn power(&self, pow: u16) -> Vector<T> {
        match self.v_type {
            VectorType::ColVector => {
                //                return self.m.col_power(0, pow);
            }
            VectorType::RowVector => {
                //                return self.m.row_power(0, pow);
            }
        }

        //TODO: Don't return this here instead implement the col_power methods
        return Vector::new(self.len(), self.v_type, false);
    }
}

impl<T> Vector<T>
where
    T: MatrixElement<Output = T> + std::ops::Mul<Output = T> + std::ops::AddAssign,
{
    pub fn dot(&self, v: &Vector<T>) -> T {
        if self.len() != v.len() {
            panic!("Vector Dimension mismatch: Cannot compute dot product between self[{}x{}] and v[{}x{}].", self.rows(), self.cols(), v.rows(), v.cols());
        }

        let mut result: T = T::zero();
        for i in 0..self.len() {
            result += self.get(i) * v.get(i);
        }
        return result;
    }
}

impl<T> Debug for Vector<T>
where
    T: MatrixElement<Output = T>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.m)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    // //    #[test]
    // fn test_dot_product() {
    //     let v1: Vector<u16> = Vector::<u16>::row_vector(&vec![2, 4, 6, 8, 10], false);
    //     let v2: Vector<u16> = Vector::<u16>::col_vector(&vec![1, 3, 5, 7, 9], false);

    //     let scalar = v1.dot(&v2);
    //     assert_eq!(scalar, 190);
    // }
}
