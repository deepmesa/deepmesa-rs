use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdPtrAddAssign;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::SimdAddAssign;

use std::ops::AddAssign;

impl<T> AddAssign<T> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, val: T) {
        if self.use_simd() {
            return self.simd_add_assign(val);
        }

        if self.is_transpose {
            iterate_col_major!(self, row, col, unsafe {
                cmd_add_assign_t!(self, row, col, val);
            });
        } else {
            iterate_col_major!(self, row, col, unsafe {
                cmd_add_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> AddAssign<&ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign_t!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign_t!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> AddAssign<&RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign_t!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign_t!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> AddAssign<&DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.add_assign(&rhs.rmd);
    }
}

impl<T> SimdAddAssign<T> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn simd_add_assign(&mut self, val: T) {
        let ptr = self.cm_data;
        let len = self.cm_len;
        unsafe {
            SimdKernel::ptr_add_assign(ptr, len, val);
        }
    }
}
