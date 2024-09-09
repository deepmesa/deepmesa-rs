#![allow(unused_variables)]
#![allow(dead_code)]

use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::ops::Index;
extern crate alloc;
use super::dataset::ColMajorDataset;
use super::dataset::RowMajorDataset;
use crate::matrix::iter::{IterType, MatrixIterator};
use crate::matrix::traits::{CheckedMul, MatrixElement};

macro_rules! iterate_rows {
    ($self:ident, $row:ident, $e:expr) => {
        for $row in 0..$self.rows {
            $e;
        }
    };
}

macro_rules! iterate_cols {
    ($self:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            $e;
        }
    };
}

macro_rules! iterate_row_major {
    ($self:ident, $row:ident, $col:ident, $e:expr) => {
        for $row in 0..$self.rows {
            for $col in 0..$self.cols {
                $e
            }
        }
    };
}

macro_rules! iterate_column_major {
    ($self:ident, $row:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            for $row in 0..$self.rows {
                $e
            }
        }
    };
}

macro_rules! bounds_check_row {
    ($row:ident, $self:ident) => {
        if $row >= $self.rows {
            panic!("row index {} should be less than rows {}", $row, $self.rows);
        }
    };
}

macro_rules! bounds_check_col {
    ($col:ident, $self:ident) => {
        if $col >= $self.cols {
            panic!("Col index {} should be less than cols {}", $col, $self.cols);
        }
    };
}

macro_rules! bounds_check_len {
    ($len:expr, $self:ident) => {
        if $len != $self.len {
            panic!(
                "Data Length {} should be the same as Matrix Data Length {}",
                $len, $self.len
            );
        }
    };
}

pub(in crate::matrix) enum SyncDirection {
    CmdToRmd,
    RmdToCmd,
}

/*
RowMajorDataset: Row Major Contiguous
ColMajorDataset: ColMajor Contiguous

When transposed:
The RowMajorDataset is Col Contiguous (because it becomes the ColMajorDataSet)
The ColMajorDataset is Row Contiguous (becomes it becomes the RowMajorDataset)

For SIMD Purposes:
Row Operations use the RowMajorDataset because its Row Contiguous
Col Operations use the ColMajorDataset because its Col Contiguous

When Transposed:
RowOperations use the ColMajorDataset because its RowContiguous
ColOperations use the RowMajorDataset because its ColContiguous

 */

pub struct Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub(super) rows: usize,
    pub(super) cols: usize,
    pub(super) rmd: RowMajorDataset<T>,
    pub(super) cmd: ColMajorDataset<T>,
    pub(super) is_transpose: bool,
    pub is_square: bool,
    pub(super) simd_enabled: bool,
    pub(super) len: usize,
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(rows: usize, cols: usize) -> Matrix<T> {
        let mut simd_enabled = true;
        if !T::simd_supported() {
            simd_enabled = false;
        }
        Matrix {
            rows,
            cols,
            len: rows * cols,
            rmd: RowMajorDataset::new(rows, cols),
            cmd: ColMajorDataset::new(rows, cols),
            is_transpose: false,
            is_square: rows == cols,
            simd_enabled,
        }
    }

    pub fn simd_optimized(rows: usize, cols: usize) -> Matrix<T> {
        if !T::simd_supported() {
            return Self::new(rows, cols);
        }

        Matrix {
            rows,
            cols,
            len: rows * cols,
            rmd: RowMajorDataset::simd_optimized(rows, cols),
            cmd: ColMajorDataset::simd_optimized(rows, cols),
            is_transpose: false,
            is_square: rows == cols,
            simd_enabled: true,
        }
    }

    pub fn set_simd_enabled(&mut self, simd_enabled: bool) {
        if !T::simd_supported() {
            self.simd_enabled = false;
            return;
        }
        self.simd_enabled = simd_enabled;
    }

    pub fn is_simd_enabled(&self) -> bool {
        return self.simd_enabled;
    }

    pub fn identity(size: usize) -> Matrix<T> {
        let mut m = Matrix::new(size, size);
        m.fill_diagonal(T::one());
        return m;
    }

    pub fn from_val(rows: usize, cols: usize, val: T) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols);
        m.fill(val);
        return m;
    }

    pub fn from_row_major(rows: usize, cols: usize, src: &Vec<T>) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols);
        m.fill_row_major(src);
        return m;
    }

    pub fn from_column_major(rows: usize, cols: usize, src: &Vec<T>) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols);
        m.fill_column_major(src);
        return m;
    }

    pub fn fill(&mut self, val: T) {
        for row in 0..self.rows {
            self.fill_row(row, val);
        }
    }

    pub fn fill_diagonal(&mut self, val: T) {
        let max = std::cmp::min(self.rows, self.cols);
        if self.is_transpose {
            for idx in 0..max {
                unsafe {
                    rmd_assign_t!(self.rmd, idx, idx, val);
                    cmd_assign_t!(self.cmd, idx, idx, val);
                }
            }
        } else {
            for idx in 0..max {
                unsafe {
                    rmd_assign!(self.rmd, idx, idx, val);
                    cmd_assign!(self.cmd, idx, idx, val);
                }
            }
        }
    }

    pub fn fill_row(&mut self, row: usize, val: T) {
        bounds_check_row!(row, self);
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
            })
        } else {
            iterate_cols!(self, col, unsafe {
                rmd_assign!(self.rmd, row, col, val);
                cmd_assign!(self.cmd, row, col, val);
            })
        }
    }

    pub fn fill_col(&mut self, col: usize, val: T) {
        bounds_check_col!(col, self);
        if self.is_transpose {
            iterate_rows!(self, row, unsafe {
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
            })
        } else {
            iterate_rows!(self, row, unsafe {
                rmd_assign!(self.rmd, row, col, val);
                cmd_assign!(self.cmd, row, col, val);
            })
        }
    }

    pub fn fill_row_major(&mut self, src: &Vec<T>) {
        bounds_check_len!(src.len(), self);

        let mut idx = 0;
        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rmd_assign_t!(self.rmd, row, col, src[idx]);
                cmd_assign_t!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rmd_assign!(self.rmd, row, col, src[idx]);
                cmd_assign!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        }
    }

    pub fn fill_column_major(&mut self, src: &Vec<T>) {
        bounds_check_len!(src.len(), self);
        let mut idx = 0;
        if self.is_transpose {
            iterate_column_major!(self, row, col, unsafe {
                rmd_assign_t!(self.rmd, row, col, src[idx]);
                cmd_assign_t!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        } else {
            iterate_column_major!(self, row, col, unsafe {
                rmd_assign!(self.rmd, row, col, src[idx]);
                cmd_assign!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        }
    }

    pub fn set_row(&mut self, row: usize, src: &Vec<T>) {
        bounds_check_row!(row, self);
        let mut idx = 0;
        if self.is_transpose {
            iterate_cols!(self, col, unsafe {
                rmd_assign_t!(self.rmd, row, col, src[idx]);
                cmd_assign_t!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        } else {
            iterate_cols!(self, col, unsafe {
                rmd_assign!(self.rmd, row, col, src[idx]);
                cmd_assign!(self.cmd, row, col, src[idx]);
                idx += 1;
            })
        }
    }

    pub fn is_square(&self) -> bool {
        self.is_square
    }

    pub fn rows(&self) -> usize {
        if self.is_transpose {
            return self.cols;
        }
        return self.rows;
    }

    pub fn cols(&self) -> usize {
        if self.is_transpose {
            return self.rows;
        }
        return self.cols;
    }

    pub fn col_iter(&self) -> MatrixIterator<T> {
        if self.is_transpose {
            return MatrixIterator::new(&self, IterType::IterRows);
        }
        MatrixIterator::new(&self, IterType::IterCols)
    }

    pub fn row_iter(&self) -> MatrixIterator<T> {
        if self.is_transpose {
            return MatrixIterator::new(&self, IterType::IterCols);
        }
        MatrixIterator::new(&self, IterType::IterRows)
    }

    pub fn transpose(&mut self) {
        self.is_transpose = !self.is_transpose;
    }

    pub(in crate::matrix) fn sync_row(&mut self, row: usize, dir: SyncDirection) {
        if self.is_transpose {
            match dir {
                SyncDirection::CmdToRmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        rmd_assign_t!(self.rmd, row, col, val);
                    })
                }
                SyncDirection::RmdToCmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get_t!(self.rmd, row, col);
                        cmd_assign_t!(self.cmd, row, col, val);
                    })
                }
            }
        } else {
            match dir {
                SyncDirection::CmdToRmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        rmd_assign!(self.rmd, row, col, val);
                    })
                }
                SyncDirection::RmdToCmd => {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get!(self.rmd, row, col);
                        cmd_assign!(self.cmd, row, col, val);
                    })
                }
            }
        }
    }
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::MulAssign,
{
    fn use_simd(&self) -> bool {
        if !self.simd_enabled {
            return false;
        }

        #[cfg(target_arch = "aarch64")]
        {
            use std::arch::is_aarch64_feature_detected;
            if is_aarch64_feature_detected!("neon") {
                return true;
            }
        }

        return false;
    }

    pub fn scale_row(&mut self, row: usize, val: T) {
        bounds_check_row!(row, self);
        if self.use_simd() {
            self.scale_row_simd(row, val);
            return;
        }

        if self.is_transpose {
            for col in 0..self.cols() {
                unsafe {
                    let idx = rmd_index_t!(self.rmd, row, col);
                    if rmd_iget_t!(self.rmd, idx) != T::zero() {
                        rmd_mul_iassign_t!(self.rmd, idx, val);
                        cmd_mul_assign_t!(self.cmd, row, col, val);
                    }
                }
            }
        } else {
            for col in 0..self.cols() {
                unsafe {
                    let idx = rmd_index!(self.rmd, row, col);
                    if rmd_iget!(self.rmd, idx) != T::zero() {
                        rmd_mul_iassign!(self.rmd, idx, val);
                        cmd_mul_assign!(self.cmd, row, col, val);
                    }
                }
            }
        }
    }
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T> + CheckedMul,
{
    pub fn scale_row_checked(&mut self, row: usize, val: T) -> Result<(), &'static str> {
        if self.is_transpose {
            for col in 0..self.cols() {
                unsafe {
                    let idx = rmd_index_t!(self.rmd, row, col);
                    let v = rmd_iget_t!(self.rmd, idx);
                    if v != T::zero() {
                        match v.checked_mul(val) {
                            None => {
                                //TODO: Return a Matrix Error rather than this static junk
                                return Err("error");
                            }
                            Some(v) => {
                                rmd_iassign_t!(self.rmd, idx, v);
                                cmd_assign_t!(self.cmd, row, col, v);
                            }
                        }
                    }
                }
            }
        } else {
            for col in 0..self.cols() {
                unsafe {
                    let idx = rmd_index!(self.rmd, row, col);
                    let v = rmd_iget!(self.rmd, idx);
                    if v != T::zero() {
                        match v.checked_mul(val) {
                            None => {
                                //TODO: Return a Matrix Error rather than this static junk
                                return Err("error");
                            }
                            Some(v) => {
                                rmd_iassign!(self.rmd, idx, v);
                                cmd_assign!(self.cmd, row, col, v);
                            }
                        }
                    }
                }
            }
        }
        return Ok(());
    }
}

impl<T> Debug for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[{}x{}]:", self.rows(), self.cols())?;
        let mut ct = 0;
        let precision = f.precision().unwrap_or(1);
        for item in self.row_iter() {
            write!(f, "{:.*?}", precision, item)?;
            ct += 1;
            if ct == self.cols() {
                write!(f, ";")?;
                ct = 0;
            } else {
                write!(f, ",")?;
            }
        }

        Ok(())
    }
}

impl<T> Index<usize> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    type Output = [T];
    fn index(&self, row: usize) -> &Self::Output {
        let start = row * self.cols;

        unsafe { std::slice::from_raw_parts(self.rmd.rm_data.add(start), self.cols) }
    }
}

impl<T> Display for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}x{}:", self.rows(), self.cols())?;
        // let mut ct = 0;
        // for item in self.row_iter() {
        //     write!(f, "{:.1?}", item)?;
        //     ct += 1;
        //     if ct == self.cols() {
        //         write!(f, ";")?;
        //         ct = 0;
        //     } else {
        //         write!(f, ",")?;
        //     }
        // }
        let precision = f.precision().unwrap_or(1);
        write!(f, "{:.*?}", precision, 1.2345678)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Matrix;
    macro_rules! assert_matrix {
        ($m:ident, $rows:literal, $cols:literal, $data_len:literal, $transpose:literal, $square:literal) => {
            assert_eq!($m.rows, $rows);
            assert_eq!($m.cols, $cols);
            assert_eq!($m.len, $data_len);
            assert_eq!($m.is_transpose, $transpose);
            assert_eq!($m.is_square, $square);
        };
    }

    macro_rules! test_new {
        ($fn_name:ident,
         $t:ty,
         $rows:literal,
         $cols:literal,
         $data_len:literal) => {
            #[test]
            fn $fn_name() {
                let m: Matrix<$t> = Matrix::new($rows, $cols);
                assert_matrix!(m, $rows, $cols, $data_len, false, false);
            }
        };
    }

    test_new!(test_new_f32, f32, 3, 2, 6);
    test_new!(test_new_f64, f64, 3, 2, 6);
    test_new!(test_new_u8, u8, 3, 2, 6);
    test_new!(test_new_u16, u16, 3, 2, 6);
    test_new!(test_new_u32, u32, 3, 2, 6);
    test_new!(test_new_u64, u64, 3, 2, 6);
    test_new!(test_new_u128, u128, 3, 2, 6);
    test_new!(test_new_i8, i8, 3, 2, 6);
    test_new!(test_new_i16, i16, 3, 2, 6);
    test_new!(test_new_i32, i32, 3, 2, 6);
    test_new!(test_new_i64, i64, 3, 2, 6);
    test_new!(test_new_i128, i128, 3, 2, 6);

    macro_rules! test_identity_matrix {
        ($fn_name:ident,
         $t:ty,
         $size:literal,
         $data_len:literal,
         $precision:literal,
         $t_str:literal) => {
            #[test]
            fn $fn_name() {
                let m: Matrix<$t> = Matrix::identity($size);
                assert_matrix!(m, $size, $size, $data_len, false, true);
                let precision = $precision;
                assert_eq!(format!("{:.*?}", precision, m), $t_str);
            }
        };
    }

    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_u8,     u8, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_u16,   u16, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_u32,   u32, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_u64,   u64, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_u128, u128, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_i8,     i8, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_i16,   i16, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_i32,   i32, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_i64,   i64, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_identity_matrix_i128, i128, 3, 9, 0, "[3x3]:1,0,0;0,1,0;0,0,1;");
    #[rustfmt::skip]
    test_identity_matrix!(test_im_f32, f32, 3, 9, 1, "[3x3]:1.0,0.0,0.0;0.0,1.0,0.0;0.0,0.0,1.0;");
    #[rustfmt::skip]
    test_identity_matrix!(test_im_f64, f64, 3, 9, 1, "[3x3]:1.0,0.0,0.0;0.0,1.0,0.0;0.0,0.0,1.0;");

    macro_rules! test_from_row_major {
        ($fn_name:ident, $t:ty, $rows:literal, $cols:literal, $arr:expr, $data_len:literal, $precision:literal, $t_str:literal) => {
            #[test]
            fn $fn_name() {
                let m: Matrix<$t> = Matrix::from_row_major($rows, $cols, $arr);
                assert_matrix!(m, $rows, $cols, $data_len, false, false);
                let precision = $precision;
                assert_eq!(format!("{:.*?}", precision, m), $t_str);
            }
        };
    }

    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_u8,     u8, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;");
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_u16,   u16, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;");
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_u32,   u32, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_u64,   u64, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_u128, u128, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_i8,     i8, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_i16,   i16, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_i32,   i32, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_i64,   i64, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!(test_from_row_major_i128, i128, 2, 3, &vec![0, 1, 2, 3, 4, 5], 6, 0, "[2x3]:0,1,2;3,4,5;" );
    #[rustfmt::skip]
    test_from_row_major!( test_from_row_major_f32,  f32, 2, 3, &vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0], 6, 1, "[2x3]:0.0,1.0,2.0;3.0,4.0,5.0;" );
    #[rustfmt::skip]
    test_from_row_major!( test_from_row_major_f64,  f64, 2, 3, &vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0], 6, 1, "[2x3]:0.0,1.0,2.0;3.0,4.0,5.0;" );

    //TODO: Test Index & IndexMut
    macro_rules! test_scale_row {
        ($fn_name:ident,
         $t:ty,
         $rows:literal,
         $cols:literal,
         $arr:expr,
         $data_len:literal,
         $precision:literal,
         $scale_row:literal,
         $scale_factor:literal,
         $t_str:literal,
         $tt_str:literal) => {
            #[test]
            fn $fn_name() {
                let mut m: Matrix<$t> = Matrix::from_row_major($rows, $cols, $arr);
                //                m.set_simd_enabled(false);
                assert_matrix!(m, $rows, $cols, $data_len, false, true);
                m.scale_row($scale_row, $scale_factor);
                let precision = $precision;
                assert_eq!(format!("{:.*?}", precision, m), $t_str);
                m.transpose();
                m.scale_row($scale_row, $scale_factor);
                assert_eq!(format!("{:.*?}", precision, m), $tt_str);
            }
        };
    }

    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u8_0, u8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u8_1, u8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip] // scale_row_u8_2 has to use smaller values so that ut doesn't cause an overflow
    test_scale_row!(test_scale_row_u8_2, u8, 3, 3, &vec![2, 3, 4, 5, 6, 7, 8, 9, 10], 9, 0, 2, 3, "[3x3]:2,3,4;5,6,7;24,27,30;", "[3x3]:2,5,24;3,6,27;12,21,90;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u16_0, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u16_1, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u16_2, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u32_0, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u32_1, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u32_2, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u64_0, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u64_1, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u64_2, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u128_0, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u128_1, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_u128_2, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i8_0, i8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i8_1, i8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip] // scale_row_i8_2 has to use smaller values so that it doesn't cause an overflow
    test_scale_row!(test_scale_row_i8_2, i8, 3, 3, &vec![2, 3, 4, 5, 6, 7, 8, 9, 10], 9, 0, 2, 3, "[3x3]:2,3,4;5,6,7;24,27,30;", "[3x3]:2,5,24;3,6,27;12,21,90;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i16_0, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i16_1, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i16_2, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i32_0, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i32_1, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i32_2, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i64_0, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i64_1, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i64_2, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i128_0, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i128_1, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row!(test_scale_row_i128_2, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");

    // #[test]
    // fn test_overflow_f64() {
    //     let v1 = f64::MAX;
    //     let v2 = -2.0;
    //     let v3 = v1 * v2;
    //     println!("v3={}", v3);
    // }

    macro_rules! test_scale_row_checked {
        ($fn_name:ident,
         $t:ty,
         $rows:literal,
         $cols:literal,
         $arr:expr,
         $data_len:literal,
         $precision:literal,
         $scale_row:literal,
         $scale_factor:literal,
         $t_str:literal,
         $tt_str:literal) => {
            #[test]
            fn $fn_name() {
                let precision = $precision;
                let mut m: Matrix<u8> = Matrix::from_row_major($rows, $cols, $arr);
                assert_matrix!(m, $rows, $cols, $data_len, false, true);
                match m.scale_row_checked($scale_row, $scale_factor) {
                    Err(str) => {
                        panic!("{}", str);
                    }
                    Ok(()) => {
                        assert_eq!(format!("{:.*?}", precision, m), $t_str);
                    }
                }
                m.transpose();
                match m.scale_row_checked($scale_row, $scale_factor) {
                    Err(str) => {
                        panic!("{}", str);
                    }
                    Ok(()) => {
                        assert_eq!(format!("{:.*?}", precision, m), $tt_str);
                    }
                }
            }
        };
    }

    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u8_0, u8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u8_1, u8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip] // scale_row_checked_u8_2 has to use smaller values so that ut doesn't cause an overflow
    test_scale_row_checked!(test_scale_row_checked_u8_2, u8, 3, 3, &vec![2, 3, 4, 5, 6, 7, 8, 9, 10], 9, 0, 2, 3, "[3x3]:2,3,4;5,6,7;24,27,30;", "[3x3]:2,5,24;3,6,27;12,21,90;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u16_0, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u16_1, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u16_2, u16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u32_0, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u32_1, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u32_2, u32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u64_0, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u64_1, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u64_2, u64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u128_0, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u128_1, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_u128_2, u128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i8_0, i8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i8_1, i8, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip] // scale_row_checked_i8_2 has to use smaller values so that it doesn't cause an overflow
    test_scale_row_checked!(test_scale_row_checked_i8_2, i8, 3, 3, &vec![2, 3, 4, 5, 6, 7, 8, 9, 10], 9, 0, 2, 3, "[3x3]:2,3,4;5,6,7;24,27,30;", "[3x3]:2,5,24;3,6,27;12,21,90;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i16_0, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i16_1, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i16_2, i16, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i32_0, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i32_1, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i32_2, i32, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i64_0, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i64_1, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i64_2, i64, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i128_0, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 0, 3, "[3x3]:6,12,18;8,10,12;14,16,18;", "[3x3]:18,24,42;12,10,16;18,12,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i128_1, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 1, 3, "[3x3]:2,4,6;24,30,36;14,16,18;", "[3x3]:2,24,14;12,90,48;6,36,18;");
    #[rustfmt::skip]
    test_scale_row_checked!(test_scale_row_checked_i128_2, i128, 3, 3, &vec![2, 4, 6, 8, 10, 12, 14, 16, 18], 9, 0, 2, 3, "[3x3]:2,4,6;8,10,12;42,48,54;", "[3x3]:2,8,42;4,10,48;18,36,162;");

    macro_rules! test_scale_row_checked_panic {
        ($fn_name:ident,
         $t:ty,
         $rows:literal,
         $cols:literal,
         $data_len:literal,
         $precision:literal,
         $scale_row:literal,
         $scale_factor:literal) => {
            #[test]
            #[should_panic]
            fn $fn_name() {
                let precision = $precision;
                let mut m: Matrix<$t> = Matrix::new($rows, $cols);
                m.fill_row($scale_row, <$t>::MAX);
                assert_matrix!(m, $rows, $cols, $data_len, false, true);
                match m.scale_row_checked($scale_row, $scale_factor) {
                    Err(str) => {
                        panic!("{}", str);
                    }
                    Ok(()) => {}
                }
            }
        };
    }

    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_u8, u8, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_u16, u16, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_u32, u32, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_u64, u64, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_u128, u128, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_i8, i8, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_i16, i16, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_i32, i32, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_i64, i64, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_i128, i128, 3, 3, 9, 0, 0, 3);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_f32, f32, 3, 3, 9, 0, 0, 3.0);
    #[rustfmt::skip]
    test_scale_row_checked_panic!(test_scale_row_checked_panic_f64, f64, 3, 3, 9, 0, 0, 3.0);

    #[test]
    fn test_foo() {
        let rows = 12;
        let cols = 12;
        let mut m: Matrix<u8> = Matrix::simd_optimized(rows, cols);
        m.fill(3);
        assert_eq!(m.rmd.row_pad, 52);
        assert_eq!(m.cmd.col_pad, 52);
        let step = 64;
        println!(
            "RMLEN: {}, rm_len / step = {}, rm_len % step = {}",
            m.rmd.rm_len,
            m.rmd.rm_len / step,
            m.rmd.rm_len % step
        );

        for idx in (0..m.rmd.rm_len).step_by(step) {
            println!(
                "IDX: {} - {}, Rem: {}",
                idx,
                idx + step - 1,
                m.rmd.rm_len - (idx + step)
            );
        }
    }
}
