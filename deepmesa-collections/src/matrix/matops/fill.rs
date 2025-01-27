use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;
use crate::matrix::traits::FillColumn;
use crate::matrix::traits::FillDiagonal;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;
use crate::matrix::vector::Vector;

impl<T> FillRow<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_row(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_row(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_row(row, val);
            }
        }
    }
}

impl<T> FillRow<&Vector<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: &Vector<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_row(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_row(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_row(row, val);
            }
        }
    }
}

impl<T> FillRow<&Vec<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: &Vec<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_row(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_row(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_row(row, val);
            }
        }
    }
}

impl<T> FillColumn<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, row: usize, val: T) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_column(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_column(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_column(row, val);
            }
        }
    }
}

impl<T> FillColumn<&Vector<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, row: usize, val: &Vector<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_column(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_column(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_column(row, val);
            }
        }
    }
}

impl<T> FillColumn<&Vec<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_column(&mut self, row: usize, val: &Vec<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_column(row, val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_column(row, val);
            }
            MatrixType::DualIndex => {
                self.did.fill_column(row, val);
            }
        }
    }
}

impl<T> FillDiagonal<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_diagonal(&mut self, val: T) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_diagonal(val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_diagonal(val);
            }
            MatrixType::DualIndex => {
                self.did.fill_diagonal(val);
            }
        }
    }
}

impl<T> FillDiagonal<&Vector<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_diagonal(&mut self, val: &Vector<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_diagonal(val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_diagonal(val);
            }
            MatrixType::DualIndex => {
                self.did.fill_diagonal(val);
            }
        }
    }
}

impl<T> FillDiagonal<&Vec<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_diagonal(&mut self, val: &Vec<T>) {
        match self.m_type {
            MatrixType::ColMajor => {
                self.cmd.fill_diagonal(val);
            }
            MatrixType::RowMajor => {
                self.rmd.fill_diagonal(val);
            }
            MatrixType::DualIndex => {
                self.did.fill_diagonal(val);
            }
        }
    }
}
