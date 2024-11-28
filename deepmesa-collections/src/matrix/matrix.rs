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
use crate::matrix::vector::Vector;
use crate::matrix::vector::VectorType;

pub(in crate::matrix) enum SyncDirection {
    CmdToRmd,
    RmdToCmd,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MatrixType {
    RowMajor,
    ColMajor,
    DualIndex,
}

macro_rules! mtype_expr_col_major {
    ($self:ident, $te:expr, $e:expr) => {
        if $self.is_transpose {
            unsafe { $te }
        } else {
            unsafe { $e }
        }
    };
}

macro_rules! mtype_expr_row_major {
    ($self:ident, $te:expr, $e:expr) => {
        if $self.is_transpose {
            unsafe { $te }
        } else {
            unsafe { $e }
        }
    };
}

macro_rules! mtype_expr_dual_index {
    ($self:ident, $te:expr, $e:expr) => {
        if $self.is_transpose {
            unsafe { $te }
        } else {
            unsafe { $e }
        }
    };
}

macro_rules! mtype_op {
    ($self:ident, $cm_e:expr, $rm_e: expr, $di_e:expr) => {
        match &$self.m_type {
            MatrixType::ColMajor => $cm_e,
            MatrixType::RowMajor => $rm_e,
            MatrixType::DualIndex => $di_e,
        }
    };
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
    pub(super) m_type: MatrixType,
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(rows: usize, cols: usize, m_type: MatrixType, simd_optimized: bool) -> Matrix<T> {
        let mut simd_enabled = true;
        if !T::simd_supported() {
            simd_enabled = false;
        }
        match m_type {
            MatrixType::RowMajor => {
                return Matrix {
                    rows,
                    cols,
                    len: rows * cols,
                    rmd: RowMajorDataset::new(rows, cols, simd_optimized),
                    cmd: ColMajorDataset::null(),
                    is_transpose: false,
                    is_square: rows == cols,
                    simd_enabled,
                    m_type,
                }
            }
            MatrixType::ColMajor => {
                return Matrix {
                    rows,
                    cols,
                    len: rows * cols,
                    rmd: RowMajorDataset::null(),
                    cmd: ColMajorDataset::new(rows, cols, simd_optimized),
                    is_transpose: false,
                    is_square: rows == cols,
                    simd_enabled,
                    m_type,
                }
            }
            MatrixType::DualIndex => {
                return Matrix {
                    rows,
                    cols,
                    len: rows * cols,
                    rmd: RowMajorDataset::new(rows, cols, simd_optimized),
                    cmd: ColMajorDataset::new(rows, cols, simd_optimized),
                    is_transpose: false,
                    is_square: rows == cols,
                    simd_enabled,
                    m_type,
                }
            }
        }
    }

    pub fn set_simd_enabled(&mut self, simd_enabled: bool) {
        if !T::simd_supported() {
            self.simd_enabled = false;
            return;
        }
        self.simd_enabled = simd_enabled;
    }

    //TODO: This should return a reference
    //TODO: Need to implement PartialEq for &MatrixType
    pub fn matrix_type(&self) -> MatrixType {
        return self.m_type;
    }

    pub fn is_simd_enabled(&self) -> bool {
        return self.simd_enabled;
    }

    pub fn is_simd_optimized(&self) -> bool {
        match &self.m_type {
            MatrixType::ColMajor => {
                return self.cmd.is_simd_optimized();
            }
            MatrixType::RowMajor => {
                return self.rmd.is_simd_optimized();
            }
            MatrixType::DualIndex => {
                return self.rmd.is_simd_optimized() && self.rmd.is_simd_optimized();
            }
        }
    }

    pub fn identity(size: usize, m_type: MatrixType, simd_optimized: bool) -> Matrix<T> {
        let mut m = Matrix::new(size, size, m_type, simd_optimized);
        m.fill_diagonal(T::one());
        return m;
    }

    pub fn from_val(
        rows: usize,
        cols: usize,
        m_type: MatrixType,
        simd_optimized: bool,
        val: T,
    ) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols, m_type, simd_optimized);
        m.fill(val);
        return m;
    }

    pub fn from_row_major(
        rows: usize,
        cols: usize,
        m_type: MatrixType,
        simd_optimized: bool,
        src: &Vec<T>,
    ) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols, m_type, simd_optimized);
        m.fill_row_major(src);
        return m;
    }

    pub fn from_column_major(
        rows: usize,
        cols: usize,
        m_type: MatrixType,
        simd_optimized: bool,
        src: &Vec<T>,
    ) -> Matrix<T> {
        let mut m = Matrix::new(rows, cols, m_type, simd_optimized);
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
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate!(self, idx, max, {
                    cmd_assign_t!(self.cmd, idx, idx, val);
                }),
                iterate!(self, idx, max, {
                    cmd_assign!(self.cmd, idx, idx, val);
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate!(self, idx, max, {
                    rmd_assign_t!(self.rmd, idx, idx, val);
                }),
                iterate!(self, idx, max, {
                    rmd_assign!(self.rmd, idx, idx, val);
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate!(self, idx, max, {
                    rmd_assign_t!(self.rmd, idx, idx, val);
                    cmd_assign_t!(self.cmd, idx, idx, val);
                }),
                iterate!(self, idx, max, {
                    rmd_assign!(self.rmd, idx, idx, val);
                    cmd_assign!(self.cmd, idx, idx, val);
                })
            )
        );
    }

    // pub fn fill_diagonal(&mut self, val: T) {
    //     let max = std::cmp::min(self.rows, self.cols);
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate!(self, idx, max, unsafe {
    //                     cmd_assign_t!(self.cmd, idx, idx, val);
    //                 })
    //             } else {
    //                 iterate!(self, idx, max, unsafe {
    //                     cmd_assign!(self.cmd, idx, idx, val);
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate!(self, idx, max, unsafe {
    //                     rmd_assign_t!(self.rmd, idx, idx, val);
    //                 })
    //             } else {
    //                 iterate!(self, idx, max, unsafe {
    //                     rmd_assign!(self.rmd, idx, idx, val);
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate!(self, idx, max, unsafe {
    //                     rmd_assign_t!(self.rmd, idx, idx, val);
    //                     cmd_assign_t!(self.cmd, idx, idx, val);
    //                 })
    //             } else {
    //                 iterate!(self, idx, max, unsafe {
    //                     rmd_assign!(self.rmd, idx, idx, val);
    //                     cmd_assign!(self.cmd, idx, idx, val);
    //                 })
    //             }
    //         }
    //     }
    // }

    pub fn fill_row(&mut self, row: usize, val: T) {
        bounds_check_row!(row, self);
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate_cols!(self, col, {
                    cmd_assign_t!(self.cmd, row, col, val);
                }),
                iterate_cols!(self, col, {
                    cmd_assign!(self.cmd, row, col, val);
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate_cols!(self, col, {
                    rmd_assign_t!(self.rmd, row, col, val);
                }),
                iterate_cols!(self, col, {
                    rmd_assign!(self.rmd, row, col, val);
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate_cols!(self, col, {
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                }),
                iterate_cols!(self, col, {
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                })
            )
        );
    }

    // pub fn fill_row(&mut self, row: usize, val: T) {
    //     bounds_check_row!(row, self);
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 })
    //             }
    //         }
    //     }
    // }

    pub fn fill_col(&mut self, col: usize, val: T) {
        bounds_check_col!(col, self);
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate_rows!(self, row, {
                    cmd_assign_t!(self.cmd, row, col, val);
                }),
                iterate_rows!(self, row, {
                    cmd_assign!(self.cmd, row, col, val);
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate_rows!(self, row, {
                    rmd_assign_t!(self.rmd, row, col, val);
                }),
                iterate_rows!(self, row, {
                    rmd_assign!(self.rmd, row, col, val);
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate_rows!(self, row, {
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                }),
                iterate_rows!(self, row, {
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                })
            )
        );
    }

    // pub fn fill_col(&mut self, col: usize, val: T) {
    //     bounds_check_col!(col, self);
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate_rows!(self, row, unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_rows!(self, row, unsafe {
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate_rows!(self, row, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_rows!(self, row, unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate_rows!(self, row, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 })
    //             } else {
    //                 iterate_rows!(self, row, unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 })
    //             }
    //         }
    //     }
    // }

    pub fn fill_row_major(&mut self, src: &Vec<T>) {
        bounds_check_len!(src.len(), self);
        //TODO: Check to see if the len of the src is equal to rows *
        // cols. Add a test
        let mut idx = 0;
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate_row_major!(self, row, col, {
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_row_major!(self, row, col, {
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate_row_major!(self, row, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_row_major!(self, row, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate_row_major!(self, row, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_row_major!(self, row, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            )
        );
    }

    // pub fn fill_row_major(&mut self, src: &Vec<T>) {
    //     bounds_check_len!(src.len(), self);
    //     //TODO: Check to see if the len of the src is equal to rows *
    //     // cols. Add a test
    //     let mut idx = 0;
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_row_major!(self, row, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //     }
    // }

    // pub fn fill_column_major(&mut self, src: &Vec<T>) {
    //     bounds_check_len!(src.len(), self);
    //     //TODO: Check to see if the len of the src is equal to rows *
    //     // cols. Add a test
    //     let mut idx = 0;
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_column_major!(self, row, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //     }
    // }

    pub fn fill_column_major(&mut self, src: &Vec<T>) {
        bounds_check_len!(src.len(), self);
        //TODO: Check to see if the len of the src is equal to rows *
        // cols. Add a test
        let mut idx = 0;
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate_column_major!(self, row, col, {
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_column_major!(self, row, col, {
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate_column_major!(self, row, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_column_major!(self, row, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate_column_major!(self, row, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_column_major!(self, row, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            )
        );
    }

    // pub fn set_row(&mut self, row: usize, src: &Vec<T>) {
    //     bounds_check_row!(row, self);
    //     //TODO: Check to see if the len of the src is equal to
    //     // rows. Add a test
    //     let mut idx = 0;
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, src[idx]);
    //                     cmd_assign_t!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             } else {
    //                 iterate_cols!(self, col, unsafe {
    //                     rmd_assign!(self.rmd, row, col, src[idx]);
    //                     cmd_assign!(self.cmd, row, col, src[idx]);
    //                     idx += 1;
    //                 })
    //             }
    //         }
    //     }
    // }

    pub fn set_row(&mut self, row: usize, src: &Vec<T>) {
        bounds_check_row!(row, self);
        //TODO: Check to see if the len of the src is equal to
        // rows. Add a test
        let mut idx = 0;
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                iterate_cols!(self, col, {
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_cols!(self, col, {
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_row_major!(
                self,
                iterate_cols!(self, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_cols!(self, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    idx += 1;
                })
            ),
            mtype_expr_dual_index!(
                self,
                iterate_cols!(self, col, {
                    rmd_assign_t!(self.rmd, row, col, src[idx]);
                    cmd_assign_t!(self.cmd, row, col, src[idx]);
                    idx += 1;
                }),
                iterate_cols!(self, col, {
                    rmd_assign!(self.rmd, row, col, src[idx]);
                    cmd_assign!(self.cmd, row, col, src[idx]);
                    idx += 1;
                })
            )
        );
    }

    pub fn set(&mut self, row: usize, col: usize, val: T) {
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                cmd_assign_t!(self.cmd, row, col, val),
                cmd_assign!(self.cmd, row, col, val)
            ),
            mtype_expr_row_major!(
                self,
                rmd_assign_t!(self.rmd, row, col, val),
                rmd_assign!(self.rmd, row, col, val)
            ),
            mtype_expr_dual_index!(
                self,
                {
                    rmd_assign_t!(self.rmd, row, col, val);
                    cmd_assign_t!(self.cmd, row, col, val);
                },
                {
                    rmd_assign!(self.rmd, row, col, val);
                    cmd_assign!(self.cmd, row, col, val);
                }
            )
        );
    }

    // pub fn set(&mut self, row: usize, col: usize, val: T) {
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 }
    //             } else {
    //                 unsafe {
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 }
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                 }
    //             } else {
    //                 unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                 }
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     rmd_assign_t!(self.rmd, row, col, val);
    //                     cmd_assign_t!(self.cmd, row, col, val);
    //                 }
    //             } else {
    //                 unsafe {
    //                     rmd_assign!(self.rmd, row, col, val);
    //                     cmd_assign!(self.cmd, row, col, val);
    //                 }
    //             }
    //         }
    //     }
    // }

    pub fn get(&self, row: usize, col: usize) -> T {
        mtype_op!(
            self,
            mtype_expr_col_major!(
                self,
                return cmd_get_t!(self.cmd, row, col),
                return cmd_get!(self.cmd, row, col)
            ),
            mtype_expr_row_major!(
                self,
                return rmd_get_t!(self.rmd, row, col),
                return rmd_get!(self.rmd, row, col)
            ),
            mtype_expr_dual_index!(
                self,
                return rmd_get_t!(self.rmd, row, col),
                return rmd_get!(self.rmd, row, col)
            )
        );

        // match &self.m_type {
        //     MatrixType::ColMajor => {
        //         if self.is_transpose {
        //             unsafe {
        //                 return cmd_get_t!(self.cmd, row, col);
        //             }
        //         } else {
        //             unsafe {
        //                 return cmd_get!(self.cmd, row, col);
        //             }
        //         }
        //     }
        //     MatrixType::RowMajor => {
        //         if self.is_transpose {
        //             unsafe {
        //                 return rmd_get_t!(self.rmd, row, col);
        //             }
        //         } else {
        //             unsafe {
        //                 return rmd_get!(self.rmd, row, col);
        //             }
        //         }
        //     }
        //     MatrixType::DualIndex => {
        //         if self.is_transpose {
        //             unsafe {
        //                 return rmd_get_t!(self.rmd, row, col);
        //             }
        //         } else {
        //             unsafe {
        //                 return rmd_get!(self.rmd, row, col);
        //             }
        //         }
        //     }
        // }
    }

    // pub fn get(&self, row: usize, col: usize) -> T {
    //     match &self.m_type {
    //         MatrixType::ColMajor => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     return cmd_get_t!(self.cmd, row, col);
    //                 }
    //             } else {
    //                 unsafe {
    //                     return cmd_get!(self.cmd, row, col);
    //                 }
    //             }
    //         }
    //         MatrixType::RowMajor => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     return rmd_get_t!(self.rmd, row, col);
    //                 }
    //             } else {
    //                 unsafe {
    //                     return rmd_get!(self.rmd, row, col);
    //                 }
    //             }
    //         }
    //         MatrixType::DualIndex => {
    //             if self.is_transpose {
    //                 unsafe {
    //                     return rmd_get_t!(self.rmd, row, col);
    //                 }
    //             } else {
    //                 unsafe {
    //                     return rmd_get!(self.rmd, row, col);
    //                 }
    //             }
    //         }
    //     }
    // }

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
        //TODO: Once partial Eq is implemented for &Matrix Type remove
        // this match and replace it with a !=
        match &self.m_type {
            MatrixType::DualIndex => {
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
            _ => {
                return;
            }
        }
    }
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    //TODO: What should the datatype of the exponent be? u16? u32? i32?
    //TODO: Find a way to abstract all these match and is_transpose statements into macros to reduce duplication
    pub fn col_power(&self, col: usize, pow: u16) -> Vector<T> {
        bounds_check_col!(col, self);
        let mut idx = 0;
        let mut result = Vector::new(self.rows(), VectorType::ColVector, self.is_simd_optimized());
        match &self.m_type {
            MatrixType::ColMajor => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
            MatrixType::RowMajor => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        let val = rmd_get_t!(self.rmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        let val = rmd_get!(self.rmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
            MatrixType::DualIndex => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
        }
        return result;
    }

    pub fn row_power(&self, row: usize, pow: u16) -> Vector<T> {
        bounds_check_row!(row, self);
        let mut idx = 0;
        let mut result = Vector::new(self.rows(), VectorType::RowVector, self.is_simd_optimized());
        match &self.m_type {
            MatrixType::ColMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
            MatrixType::RowMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get_t!(self.rmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        let val = rmd_get!(self.rmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
            MatrixType::DualIndex => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get_t!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        let val = cmd_get!(self.cmd, row, col);
                        result.set(idx, val.power(pow));
                        idx += 1;
                    })
                }
            }
        }
        return result;
    }
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign,
{
    pub fn sum_row(&self, row: usize) -> T {
        bounds_check_row!(row, self);
        let mut sum = T::zero();
        match &self.m_type {
            MatrixType::ColMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        sum += cmd_get_t!(self.cmd, row, col);
                    });
                } else {
                    iterate_cols!(self, col, unsafe {
                        sum += cmd_get!(self.cmd, row, col);
                    });
                }
            }
            MatrixType::RowMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        sum += rmd_get_t!(self.rmd, row, col);
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        sum += rmd_get!(self.rmd, row, col);
                    })
                }
            }
            MatrixType::DualIndex => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        sum += rmd_get_t!(self.rmd, row, col);
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        sum += rmd_get!(self.rmd, row, col);
                    })
                }
            }
        }
        return sum;
    }

    pub fn sum_col(&self, col: usize) -> T {
        bounds_check_col!(col, self);
        let mut sum = T::zero();
        match &self.m_type {
            MatrixType::ColMajor => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        sum += cmd_get_t!(self.cmd, row, col);
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        sum += cmd_get!(self.cmd, row, col);
                    })
                }
            }
            MatrixType::RowMajor => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        sum += rmd_get_t!(self.rmd, row, col);
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        sum += rmd_get!(self.rmd, row, col);
                    })
                }
            }
            MatrixType::DualIndex => {
                if self.is_transpose {
                    iterate_rows!(self, row, unsafe {
                        sum += cmd_get_t!(self.cmd, row, col);
                    })
                } else {
                    iterate_rows!(self, row, unsafe {
                        sum += cmd_get!(self.cmd, row, col);
                    })
                }
            }
        }
        return sum;
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

        match &self.m_type {
            MatrixType::ColMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let idx = cmd_index_t!(self.cmd, row, col);
                        if cmd_iget_t!(self.cmd, idx) != T::zero() {
                            cmd_mul_iassign_t!(self.cmd, idx, val);
                        }
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        let idx = cmd_index!(self.cmd, row, col);
                        if cmd_iget!(self.cmd, idx) != T::zero() {
                            cmd_mul_iassign!(self.cmd, idx, val);
                        }
                    })
                }
            }
            MatrixType::RowMajor => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let idx = rmd_index_t!(self.rmd, row, col);
                        if rmd_iget_t!(self.rmd, idx) != T::zero() {
                            rmd_mul_iassign_t!(self.rmd, idx, val);
                        }
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        let idx = rmd_index!(self.rmd, row, col);
                        if rmd_iget!(self.rmd, idx) != T::zero() {
                            rmd_mul_iassign!(self.rmd, idx, val);
                        }
                    })
                }
            }
            MatrixType::DualIndex => {
                if self.is_transpose {
                    iterate_cols!(self, col, unsafe {
                        let idx = rmd_index_t!(self.rmd, row, col);
                        if rmd_iget_t!(self.rmd, idx) != T::zero() {
                            rmd_mul_iassign_t!(self.rmd, idx, val);
                            cmd_mul_assign_t!(self.cmd, row, col, val);
                        }
                    })
                } else {
                    iterate_cols!(self, col, unsafe {
                        //            for col in 0..self.cols() {
                        //                unsafe {
                        let idx = rmd_index!(self.rmd, row, col);
                        if rmd_iget!(self.rmd, idx) != T::zero() {
                            rmd_mul_iassign!(self.rmd, idx, val);
                            cmd_mul_assign!(self.cmd, row, col, val);
                        }
                    })
                }
            }
        }
    }
}

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T> + CheckedMul,
{
    fn scale_row_checked_rmd(&mut self, row: usize, val: T) -> Result<(), &'static str> {
        if self.is_transpose {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
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
                            }
                        }
                    }
                }
            )
        } else {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
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
                            }
                        }
                    }
                }
            )
        }
        return Ok(());
    }

    fn scale_row_checked_cmd(&mut self, row: usize, val: T) -> Result<(), &'static str> {
        if self.is_transpose {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
                unsafe {
                    let idx = cmd_index_t!(self.cmd, row, col);
                    let v = cmd_iget_t!(self.cmd, idx);
                    if v != T::zero() {
                        match v.checked_mul(val) {
                            None => {
                                //TODO: Return a Matrix Error rather than this static junk
                                return Err("error");
                            }
                            Some(v) => {
                                cmd_iassign_t!(self.cmd, idx, v);
                            }
                        }
                    }
                }
            )
        } else {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
                unsafe {
                    let idx = cmd_index!(self.cmd, row, col);
                    let v = cmd_iget!(self.cmd, idx);
                    if v != T::zero() {
                        match v.checked_mul(val) {
                            None => {
                                //TODO: Return a Matrix Error rather than this static junk
                                return Err("error");
                            }
                            Some(v) => {
                                cmd_iassign!(self.cmd, idx, v);
                            }
                        }
                    }
                }
            )
        }
        return Ok(());
    }

    fn scale_row_checked_di(&mut self, row: usize, val: T) -> Result<(), &'static str> {
        if self.is_transpose {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
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
            )
        } else {
            iterate_cols!(
                self,
                col,
                //            for col in 0..self.cols() {
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
            )
        }
        return Ok(());
    }

    pub fn scale_row_checked(&mut self, row: usize, val: T) -> Result<(), &'static str> {
        match &self.m_type {
            MatrixType::ColMajor => return self.scale_row_checked_cmd(row, val),
            MatrixType::RowMajor => return self.scale_row_checked_rmd(row, val),
            MatrixType::DualIndex => return self.scale_row_checked_di(row, val),
        }
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
