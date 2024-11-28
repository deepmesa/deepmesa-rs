use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;
use crate::matrix::traits::MatrixElement;
use std::fmt;
use std::fmt::Debug;
//use std::fmt::Display;
use std::fmt::Formatter;

pub struct Vector<T>
where
    T: MatrixElement<Output = T>,
{
    m: Matrix<T>,
}

#[derive(Debug)]
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
            },
            VectorType::ColVector => Vector {
                m: Matrix::new(size, 1, MatrixType::ColMajor, simd_optimized),
            },
        }
    }

    pub fn row_vector(src: &Vec<T>, simd_optimized: bool) -> Vector<T> {
        return Vector {
            m: Matrix::from_row_major(1, src.len(), MatrixType::RowMajor, simd_optimized, src),
        };
    }

    pub fn col_vector(src: &Vec<T>, simd_optimized: bool) -> Vector<T> {
        return Vector {
            m: Matrix::from_column_major(src.len(), 1, MatrixType::ColMajor, simd_optimized, src),
        };
    }

    pub fn is_col_vector(&self) -> bool {
        return self.m.cols() == 1;
    }

    pub fn is_row_vector(&self) -> bool {
        return self.m.rows() == 1;
    }

    pub fn transpose(&mut self) {
        self.m.transpose();
    }

    pub fn fill(&mut self, val: T) {
        self.m.fill(val);
    }

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

    pub fn get(&self, idx: usize) -> T {
        if self.m.cols() == 1 {
            return self.m.get(idx, 0);
        }
        return self.m.get(0, idx);
    }
}

impl<T> Vector<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    pub fn sum(&self) -> T {
        if self.m.cols() == 1 {
            return self.m.sum_col(0);
        }
        return self.m.sum_row(0);
    }

    pub fn power(&self, pow: u16) -> Vector<T> {
        if self.m.cols() == 1 {
            return self.m.col_power(0, pow);
        }
        return self.m.row_power(0, pow);
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

    #[test]
    fn test_dot_product() {
        let v1: Vector<u16> = Vector::<u16>::row_vector(&vec![2, 4, 6, 8, 10], false);
        let v2: Vector<u16> = Vector::<u16>::col_vector(&vec![1, 3, 5, 7, 9], false);

        let scalar = v1.dot(&v2);
        assert_eq!(scalar, 190);
    }
}
