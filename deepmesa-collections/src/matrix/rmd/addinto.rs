use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::{AddInto, MatrixElement};

impl<T> AddInto<T, RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: T, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        match self.is_transpose {
            true => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(result, row, col, rmd_get_t!(self, row, col) + rhs);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(result, row, col, rmd_get!(self, row, col) + rhs);
                    });
                }
            },
            false => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(result, row, col, rmd_get_t!(self, row, col) + rhs);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(result, row, col, rmd_get!(self, row, col) + rhs);
                    });
                }
            },
        }
    }
}

impl<T> AddInto<T, ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: T, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        match self.is_transpose {
            true => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(result, row, col, rmd_get_t!(self, row, col) + rhs);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(result, row, col, rmd_get!(self, row, col) + rhs);
                    });
                }
            },
            false => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(result, row, col, rmd_get_t!(self, row, col) + rhs);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(result, row, col, rmd_get!(self, row, col) + rhs);
                    });
                }
            },
        }
    }
}

impl<T> AddInto<T, DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: T, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        match self.is_transpose {
            true => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rhs;
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rhs;
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                }
            },
            false => match result.is_transpose {
                true => {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rhs;
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
                false => {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rhs;
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            },
        }
    }
}

impl<T> AddInto<&RowMajorDataset<T>, RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> AddInto<&RowMajorDataset<T>, ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &RowMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> AddInto<&RowMajorDataset<T>, DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &RowMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rmd_get_t!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + rmd_get!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rmd_get_t!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rmd_get!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + rmd_get!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}

impl<T> AddInto<&ColMajorDataset<T>, RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &ColMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> AddInto<&ColMajorDataset<T>, ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &ColMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign_t!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_add_assign!(
                            result,
                            row,
                            col,
                            rmd_get!(self, row, col) + cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> AddInto<&ColMajorDataset<T>, DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &ColMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + cmd_get_t!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get_t!(self, row, col) + cmd_get!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + cmd_get_t!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + cmd_get!(rhs, row, col);
                        cmd_add_assign_t!(result.cmd, row, col, val);
                        rmd_add_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    iterate_row_major!(self, row, col, unsafe {
                        let val = rmd_get!(self, row, col) + cmd_get!(rhs, row, col);
                        cmd_add_assign!(result.cmd, row, col, val);
                        rmd_add_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}
