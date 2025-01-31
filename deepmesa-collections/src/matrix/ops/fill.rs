use std::marker::PhantomData;

use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixData;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::FillColumn;
use crate::matrix::traits::FillDiagonal;
use crate::matrix::traits::FillRow;
use crate::matrix::traits::MatrixElement;
use crate::matrix::vector::Vector;
use crate::matrix::DatasetColumn;
use crate::matrix::DatasetRow;

impl<T> FillRow<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: T) {
        bounds_check_row!(row, self);
        match &mut self.data {
            MatrixData::ColMajor(ds) => ds.fill_row(row, val),
            MatrixData::RowMajor(ds) => ds.fill_row(row, val),
            MatrixData::DualIndex(ds) => ds.fill_row(row, val),
        }
    }
}

impl<T> FillRow<&Vector<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, v: &Vector<T>) {
        bounds_check_row!(row, self);
        if v.is_col_vector() {
            //col major ds r x 1 (r rows, 1 column)
            let dc = DatasetColumn::<ColMajorDataset<T>, T>::from_cmd(&v.get_cmd(), 0);
            match &mut self.data {
                MatrixData::ColMajor(ds) => ds.fill_row(row, &dc),
                MatrixData::RowMajor(ds) => ds.fill_row(row, &dc),
                MatrixData::DualIndex(ds) => ds.fill_row(row, &dc),
            }
        } else {
            //row major ds 1 x c (1 rows, c column)
            let dr = DatasetRow::<RowMajorDataset<T>, T>::from_rmd(&v.get_rmd(), 0);

            match &mut self.data {
                MatrixData::ColMajor(ds) => ds.fill_row(row, &dr),
                MatrixData::RowMajor(ds) => ds.fill_row(row, &dr),
                MatrixData::DualIndex(ds) => ds.fill_row(row, &dr),
            }
        }
    }
}

impl<T> FillRow<&[T]> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: &[T]) {
        bounds_check_row!(row, self);
        match &mut self.data {
            MatrixData::ColMajor(ds) => ds.fill_row(row, val),
            MatrixData::RowMajor(ds) => ds.fill_row(row, val),
            MatrixData::DualIndex(ds) => ds.fill_row(row, val),
        }
    }
}

impl<T> FillRow<&Vec<T>> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fill_row(&mut self, row: usize, val: &Vec<T>) {
        bounds_check_row!(row, self);
        match &mut self.data {
            MatrixData::ColMajor(ds) => ds.fill_row(row, val),
            MatrixData::RowMajor(ds) => ds.fill_row(row, val),
            MatrixData::DualIndex(ds) => ds.fill_row(row, val),
        }
    }
}

// impl<T> FillColumn<T> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_column(&mut self, row: usize, val: T) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_column(row, val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_column(row, val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_column(row, val);
//             }
//         }
//     }
// }

// impl<T> FillColumn<&Vector<T>> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_column(&mut self, row: usize, val: &Vector<T>) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_column(row, val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_column(row, val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_column(row, val);
//             }
//         }
//     }
// }

// impl<T> FillColumn<&Vec<T>> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_column(&mut self, row: usize, val: &Vec<T>) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_column(row, val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_column(row, val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_column(row, val);
//             }
//         }
//     }
// }

// impl<T> FillDiagonal<T> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_diagonal(&mut self, val: T) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_diagonal(val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_diagonal(val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_diagonal(val);
//             }
//         }
//     }
// }

// impl<T> FillDiagonal<&Vector<T>> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_diagonal(&mut self, val: &Vector<T>) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_diagonal(val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_diagonal(val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_diagonal(val);
//             }
//         }
//     }
// }

// impl<T> FillDiagonal<&Vec<T>> for Matrix<T>
// where
//     T: MatrixElement<Output = T>,
// {
//     fn fill_diagonal(&mut self, val: &Vec<T>) {
//         match self.data {
//             MatrixData::ColMajor => {
//                 self.cmd.fill_diagonal(val);
//             }
//             MatrixData::RowMajor => {
//                 self.rmd.fill_diagonal(val);
//             }
//             MatrixData::DualIndex => {
//                 self.did.fill_diagonal(val);
//             }
//         }
//     }
// }
