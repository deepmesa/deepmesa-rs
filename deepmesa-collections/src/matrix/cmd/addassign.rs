use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;
use std::ops::AddAssign;

impl<T> AddAssign<T> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, val: T) {
        match self.is_transpose {
            true => {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign_t!(self, row, col, val);
                });
            }
            false => {
                iterate_col_major!(self, row, col, unsafe {
                    cmd_add_assign!(self, row, col, val);
                });
            }
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

        match self.is_transpose {
            true => match rhs.is_transpose {
                true => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(self, row, col, cmd_get_t!(rhs, row, col));
                    });
                }
                false => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(self, row, col, cmd_get!(rhs, row, col));
                    });
                }
            },
            false => match rhs.is_transpose {
                true => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign!(self, row, col, cmd_get_t!(rhs, row, col));
                    });
                }
                false => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign!(self, row, col, cmd_get!(rhs, row, col));
                    });
                }
            },
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

        match self.is_transpose {
            true => match rhs.is_transpose {
                true => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(self, row, col, rmd_get_t!(rhs, row, col));
                    });
                }
                false => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(self, row, col, rmd_get!(rhs, row, col));
                    });
                }
            },
            false => match rhs.is_transpose {
                true => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign!(self, row, col, rmd_get_t!(rhs, row, col));
                    });
                }
                false => {
                    iterate_col_major!(self, row, col, unsafe {
                        cmd_add_assign!(self, row, col, rmd_get!(rhs, row, col));
                    });
                }
            },
        }
    }
}
