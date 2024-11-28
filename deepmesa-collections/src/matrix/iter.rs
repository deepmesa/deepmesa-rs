use crate::matrix::matrix::Matrix;
use crate::matrix::traits::MatrixElement;

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
    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixType;
    #[test]
    fn test_iter() {
        let m: Matrix<u64> =
            Matrix::from_row_major(2, 3, MatrixType::RowMajor, false, &vec![0, 1, 2, 3, 4, 5]);
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

        let mut m: Matrix<u64> = Matrix::new(2, 3, MatrixType::RowMajor, true);
        m.fill_row_major(&vec![0, 1, 2, 3, 4, 5]);
        assert_eq!(m.rmd.rows, 2);
        assert_eq!(m.rmd.row_stride, 8); //This assert is failing. Left = 3, right = 8
        assert_eq!(m.rmd.rm_len, 16);
        assert_eq!(m.rmd.row_pad, 5);

        assert_eq!(m.cmd.cols, 3);
        assert_eq!(m.cmd.col_stride, 8);
        assert_eq!(m.cmd.cm_len, 24);
        assert_eq!(m.cmd.col_pad, 6);

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
        let mut m: Matrix<u64> =
            Matrix::from_row_major(2, 3, MatrixType::RowMajor, false, &vec![0, 1, 2, 3, 4, 5]);
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

        let mut m: Matrix<u64> = Matrix::new(2, 3, MatrixType::RowMajor, true);
        m.fill_row_major(&vec![0, 1, 2, 3, 4, 5]);
        m.transpose();
        assert_eq!(m.rmd.rows, 2);
        assert_eq!(m.rmd.row_stride, 8); // This assert is failing. Left = 3, right = 8
        assert_eq!(m.rmd.rm_len, 16);
        assert_eq!(m.rmd.row_pad, 5);

        assert_eq!(m.cmd.cols, 3);
        assert_eq!(m.cmd.col_stride, 8);
        assert_eq!(m.cmd.cm_len, 24);
        assert_eq!(m.cmd.col_pad, 6);

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
