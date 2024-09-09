use std::marker::PhantomData;

use crate::matrix::matrix::Matrix;

use crate::matrix::traits::MatrixElement;

pub enum IterType {
    IterRows,
    IterCols,
}

pub struct MatrixIterator<'a, T: MatrixElement> {
    data: *mut T,
    cursor: usize,
    cursor_max: usize,
    stride: usize,
    padding: usize,
    phantom: PhantomData<&'a T>,
}

impl<'a, T> MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(matrix: &Matrix<T>, iter_type: IterType) -> MatrixIterator<T> {
        let data;
        let padding;
        let stride;
        let cursor_max;
        match iter_type {
            IterType::IterRows => {
                data = matrix.rmd.rm_data;
                padding = matrix.rmd.row_pad;
                stride = matrix.rmd.row_stride;
                cursor_max = matrix.rmd.rm_len;
            }
            IterType::IterCols => {
                data = matrix.cmd.cm_data;
                padding = matrix.cmd.col_pad;
                stride = matrix.cmd.col_stride;
                cursor_max = matrix.cmd.cm_len;
            }
        }
        MatrixIterator {
            data,
            cursor: 0,
            padding,
            stride,
            cursor_max,
            phantom: PhantomData,
        }
    }
}

impl<'a, T> Iterator for MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        if (self.cursor + self.padding) % self.stride == 0 {
            self.cursor += self.padding;
            if self.cursor >= self.cursor_max {
                return None;
            }
        }
        let val = unsafe { &*self.data.add(self.cursor) };
        self.cursor += 1;
        return Some(val);
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::matrix::Matrix;
    #[test]
    fn test_iter() {
        let m: Matrix<u64> = Matrix::from_row_major(2, 3, &vec![0, 1, 2, 3, 4, 5]);
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

        let mut m: Matrix<u64> = Matrix::simd_optimized(2, 3);
        m.fill_row_major(&vec![0, 1, 2, 3, 4, 5]);
        assert_eq!(m.rmd.rows, 2);
        assert_eq!(m.rmd.row_stride, 8);
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
        let mut m: Matrix<u64> = Matrix::from_row_major(2, 3, &vec![0, 1, 2, 3, 4, 5]);
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

        let mut m: Matrix<u64> = Matrix::simd_optimized(2, 3);
        m.fill_row_major(&vec![0, 1, 2, 3, 4, 5]);
        m.transpose();
        assert_eq!(m.rmd.rows, 2);
        assert_eq!(m.rmd.row_stride, 8);
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
