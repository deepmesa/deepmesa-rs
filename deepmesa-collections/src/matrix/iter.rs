use crate::matrix::matrix::Matrix;
use crate::matrix::traits::MatrixElement;

pub enum IterType {
    IterRows,
    IterCols,
}

pub struct MatrixIterator<'a, T: MatrixElement> {
    data: &'a Vec<T>,
    cursor: usize,
    iter_type: IterType,
    cursor_max: usize,
    c_cursor: usize,
    cols: usize,
}

impl<'a, T> MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(matrix: &'a Matrix<T>, iter_type: IterType) -> MatrixIterator<T> {
        MatrixIterator {
            data: &matrix.data,
            cursor: 0,
            iter_type,
            cursor_max: &matrix.data.len() + matrix.cols - 1,
            c_cursor: 0,
            cols: matrix.cols,
        }
    }
}

impl<'a, T> Iterator for MatrixIterator<'a, T>
where
    T: MatrixElement<Output = T>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        match self.iter_type {
            IterType::IterRows => {
                if self.cursor >= self.data.len() {
                    return None;
                }
                let val = &self.data[self.cursor];
                self.cursor += 1;
                return Some(val);
            }
            IterType::IterCols => {
                if self.cursor == self.cursor_max {
                    return None;
                }
                if self.cursor >= self.data.len() {
                    self.c_cursor += 1;
                    self.cursor = self.c_cursor;
                }

                let val = &self.data[self.cursor];
                self.cursor += self.cols;
                return Some(val);
            }
        }
    }
}
