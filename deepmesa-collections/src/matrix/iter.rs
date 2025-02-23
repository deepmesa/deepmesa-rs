use crate::matrix::matrix::Matrix;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;
use crate::matrix::vector::Vector;

pub struct VectorIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    v: &'a Vector<T>,
    cursor: usize,
    len: usize,
}

impl<'a, T> VectorIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(vector: &Vector<T>) -> VectorIterator<T> {
        return VectorIterator {
            v: vector,
            cursor: 0,
            len: vector.len(),
        };
    }
}

impl<'a, T> Iterator for VectorIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.cursor >= self.len {
            return None;
        }

        let val = Some(self.v.get(self.cursor));
        self.cursor += 1;
        return val;
    }
}

pub enum IterType {
    IterRows,
    IterCols,
}

pub struct MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    m: &'a Matrix<T>,
    row: usize,
    col: usize,
    iter_type: IterType,
}

impl<'a, T> MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(matrix: &Matrix<T>, iter_type: IterType) -> MatrixIterator<T> {
        MatrixIterator {
            m: matrix,
            row: 0,
            col: 0,
            iter_type,
        }
    }
}

impl<'a, T> Iterator for MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self.iter_type {
            IterType::IterRows => {
                if self.row >= self.m.rows() {
                    return None;
                }
            }
            IterType::IterCols => {
                if self.col >= self.m.cols() {
                    return None;
                }
            }
        }
        let val = self.m.get(self.row, self.col);
        match self.iter_type {
            IterType::IterRows => {
                self.col += 1;
                if self.col >= self.m.cols() {
                    self.col = 0;
                    self.row += 1;
                }
            }
            IterType::IterCols => {
                self.row += 1;
                if self.row >= self.m.rows() {
                    self.row = 0;
                    self.col += 1;
                }
            }
        }

        return Some(val);
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::matrix::matrix;
    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixType;
    use crate::matrix::traits::FillRow;

    #[test]
    fn test_iter() {
        let m = matrix!(rm, [u64, 2, 3], 0, 1, 2; 3, 4, 5);

        let mut s = String::new();
        for elem in m.row_iter() {
            s.push_str(&format!("{},", elem));
        }
        assert_eq!(s, "0,1,2,3,4,5,");

        let mut s = String::new();
        for elem in m.col_iter() {
            s.push_str(&format!("{},", elem));
        }

        assert_eq!(s, "0,3,1,4,2,5,");
    }

    #[test]
    fn test_iter_transpose() {
        let mut m = matrix!(rm, [u64, 2, 3], 0, 1, 2; 3, 4, 5);
        m.transpose();
        let mut s = String::new();
        for elem in m.row_iter() {
            s.push_str(&format!("{},", elem));
        }
        assert_eq!(s, "0,3,1,4,2,5,");

        let mut s = String::new();
        for elem in m.col_iter() {
            s.push_str(&format!("{},", elem));
        }

        assert_eq!(s, "0,1,2,3,4,5,");
    }
}
