use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::SyncDirection;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdPtrAddAssign;
use crate::matrix::traits::{Dataset, MatrixElement, SimdAddAssign};
use std::ops::AddAssign;

use super::data::DualIndexDataset;

impl<T> AddAssign<T> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, val: T) {
        if self.use_simd() {
            self.simd_add_assign(val);
            return;
        }

        if self.is_transpose {
            iterate_row_major!(self, row, col, unsafe {
                rmd_add_assign_t!(self.rmd, row, col, val);
                cmd_add_assign_t!(self.cmd, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rmd_add_assign!(self.rmd, row, col, val);
                cmd_add_assign!(self.cmd, row, col, val);
            });
        }
    }
}

impl<T> SimdAddAssign<T> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn simd_add_assign(&mut self, val: T) {
        let ptr = self.rmd.rm_data;
        let len = self.len();
        unsafe {
            SimdKernel::ptr_add_assign(ptr, len, val);
        }
        self.sync(SyncDirection::RmdToCmd);
    }
}

impl<T> AddAssign<&RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        match self.is_transpose {
            true => match rhs.is_transpose {
                true => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = rmd_get_t!(rhs, row, col);
                        rmd_add_assign_t!(self.rmd, row, col, val);
                        cmd_add_assign_t!(self.cmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = rmd_get!(rhs, row, col);
                        rmd_add_assign_t!(self.rmd, row, col, val);
                        cmd_add_assign_t!(self.cmd, row, col, val);
                    });
                }
            },
            false => match rhs.is_transpose {
                true => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = rmd_get_t!(rhs, row, col);
                        rmd_add_assign!(self.rmd, row, col, val);
                        cmd_add_assign!(self.cmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = rmd_get!(rhs, row, col);
                        rmd_add_assign!(self.rmd, row, col, val);
                        cmd_add_assign!(self.cmd, row, col, val);
                    });
                }
            },
        }
    }
}

impl<T> AddAssign<&ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        match self.is_transpose {
            true => match rhs.is_transpose {
                true => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = cmd_get_t!(rhs, row, col);
                        rmd_add_assign_t!(self.rmd, row, col, val);
                        cmd_add_assign_t!(self.cmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = cmd_get!(rhs, row, col);
                        rmd_add_assign_t!(self.rmd, row, col, val);
                        cmd_add_assign_t!(self.cmd, row, col, val);
                    });
                }
            },
            false => match rhs.is_transpose {
                true => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = cmd_get_t!(rhs, row, col);
                        rmd_add_assign!(self.rmd, row, col, val);
                        cmd_add_assign!(self.cmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self.rmd, row, col, unsafe {
                        let val = cmd_get!(rhs, row, col);
                        rmd_add_assign!(self.rmd, row, col, val);
                        cmd_add_assign!(self.cmd, row, col, val);
                    });
                }
            },
        }
    }
}

impl<T> AddAssign<&DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.add_assign(&rhs.rmd);
    }
}
