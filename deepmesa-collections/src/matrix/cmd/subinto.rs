use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::did::data::SyncDirection;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdSubInto;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::{MatrixElement, SubInto};

impl<T> SubInto<T, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(cmd_t, val, rmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign_t!(result, row, col, cmd_get_t!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(cmd_t, val, rmd, self, rhs, result); // SIMD WORKS
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign!(result, row, col, cmd_get_t!(self, row, col) - rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(cmd, val, rmd_t, self, rhs, result); //SIMD Works
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign_t!(result, row, col, cmd_get!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(cmd, val, rmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign!(result, row, col, cmd_get!(self, row, col) - rhs);
                });
            }
        }
    }
}

impl<T> SubInto<T, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(cmd_t, val, cmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign_t!(result, row, col, cmd_get_t!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(cmd_t, val, cmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign!(result, row, col, cmd_get_t!(self, row, col) - rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(cmd, val, cmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign_t!(result, row, col, cmd_get!(self, row, col) - rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(cmd, val, cmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign!(result, row, col, cmd_get!(self, row, col) - rhs);
                });
            }
        }
    }
}

impl<T> SubInto<T, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: T, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(
                    cmd_t,
                    val,
                    cmd_t,
                    self,
                    rhs,
                    result.cmd,
                    result.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get_t!(self, row, col) - rhs;
                    cmd_assign_t!(result.cmd, row, col, val);
                    rmd_assign_t!(result.rmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(
                    cmd_t,
                    val,
                    rmd,
                    self,
                    rhs,
                    result.rmd,
                    result.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get_t!(self, row, col) - rhs;
                    cmd_assign!(result.cmd, row, col, val);
                    rmd_assign!(result.rmd, row, col, val);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_sub_into!(
                    cmd,
                    val,
                    rmd_t,
                    self,
                    rhs,
                    result.rmd,
                    result.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get!(self, row, col) - rhs;
                    cmd_assign_t!(result.cmd, row, col, val);
                    rmd_assign_t!(result.rmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_sub_into!(
                    cmd,
                    val,
                    cmd,
                    self,
                    rhs,
                    result.cmd,
                    result.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get!(self, row, col) - rhs;
                    cmd_assign!(result.cmd, row, col, val);
                    rmd_assign!(result.rmd, row, col, val);
                });
            }
        }
    }
}

impl<T> SubInto<&RowMajorDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, rmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd_t, rmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, rmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd_t, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd, rmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&RowMajorDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &RowMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, cmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd_t, rmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, rmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd_t, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd, cmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, rmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&RowMajorDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &RowMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd_t, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - rmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t,
                        rmd,
                        cmd_t,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, rmd, rmd, self, rhs, result.rmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - rmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, rmd_t, rmd_t, self, rhs, result.rmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd,
                        rmd_t,
                        cmd,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - rmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, rmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - rmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, rmd, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - rmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&ColMajorDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &ColMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd_t, rmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd_t, cmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, cmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd_t, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd, rmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&ColMajorDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &ColMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd_t, cmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd_t, cmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, cmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd_t, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd, cmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(cmd, cmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) - cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&ColMajorDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &ColMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t,
                        cmd_t,
                        cmd_t,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t,
                        cmd_t,
                        rmd,
                        self,
                        rhs,
                        result.rmd,
                        result.sync(SyncDirection::RmdToCmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - cmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd_t, cmd, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) - cmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, cmd_t, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, cmd_t, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - cmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd, cmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - cmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_sub_into!(
                        cmd,
                        cmd,
                        cmd,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) - cmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}

impl<T> SubInto<&DualIndexDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &DualIndexDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.sub_into(&rhs.cmd, result);
    }
}

impl<T> SubInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &DualIndexDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.sub_into(&rhs.cmd, result);
    }
}

impl<T> SubInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::SubAssign + std::ops::Sub<Output = T>,
{
    fn sub_into(&self, rhs: &DualIndexDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.sub_into(&rhs.cmd, result);
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::cmd::data::*;
    use crate::matrix::cmd::macros::col_major_dataset;
    use crate::matrix::did::data::*;
    use crate::matrix::did::macros::dual_index_dataset;
    use crate::matrix::rmd::data::*;
    use crate::matrix::rmd::macros::row_major_dataset;
    use crate::matrix::traits::*;

    macro_rules! lhs {
        (cmd, $simd:ident, $t:ty) => {
            col_major_dataset!([$t, 2, 3, $simd], 50,60,70;80,90,100)
        };
        (cmd_t, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t, 3,2, $simd], 50,80;60,90;70,100);
                cmd.transpose();
                cmd
            }
        };
    }

    macro_rules! rhs {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t,2,3, $simd], 12,13,14;15,16,17)
        };
        (cmd, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
                cmd.transpose();
                cmd
            }
        };
        (did, $simd:ident, $t:ty) => {
            dual_index_dataset!([$t,2,3,false], 12,13,14;15,16,17)
        };
        (rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
                rmd.transpose();
                rmd
            }
        };
        (cmd_t, $simd:ident, $t:ty) => {
            col_major_dataset!([$t,2,3, false], 12,13,14;15,16,17)
        };
        (did_t, $simd:ident, $t:ty) => {
            {
                let mut did = dual_index_dataset!([$t,3,2, $simd], 12,15;13,16;14,17);
                did.transpose();
                did
            }
        };
    }

    macro_rules! out {
        (rmd, $simd:ident, $t:ty) => {
            RowMajorDataset::<$t>::new(2, 3, $simd, $simd)
        };
        (rmd_t, $simd:ident, $t:ty) => {{
            let mut rmd = RowMajorDataset::<$t>::new(3, 2, $simd, $simd);
            rmd.transpose();
            rmd
        }};
        (cmd, $simd:ident, $t:ty) => {
            ColMajorDataset::<$t>::new(2, 3, $simd, $simd)
        };
        (cmd_t, $simd:ident, $t:ty) => {{
            let mut cmd = ColMajorDataset::<$t>::new(3, 2, $simd, $simd);
            cmd.transpose();
            cmd
        }};
        (did, $simd:ident, $t:ty) => {
            DualIndexDataset::<$t>::new(2, 3, $simd, $simd)
        };
        (did_t, $simd:ident, $t:ty) => {{
            let mut did = DualIndexDataset::<$t>::new(3, 2, $simd, $simd);
            did.transpose();
            did
        }};
    }

    macro_rules! result {
        (rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 38,47,56;65,74,83)
        };
        (rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 38,65;47,74;56,83);
                rmd.transpose();
                rmd
            }
        };
        (did, $simd:ident, $t:ty) => {
            dual_index_dataset!([$t, 2, 3, $simd], 38,47,56;65,74,83)
        };
        (did_t, $simd:ident, $t:ty) => {
            {
                let mut did = dual_index_dataset!([$t, 3, 2, $simd], 38,65;47,74;56,83);
                did.transpose();
                did
            }
        };
        (cmd, $simd:ident, $t:ty) => {
            col_major_dataset!([$t, 2, 3, $simd], 38,47,56;65,74,83)
        };
        (cmd_t, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 38,65;47,74;56,83);
                cmd.transpose();
                cmd
            }
        };
        (val, rmd, $simd:ident, $t:ty) => {
            row_major_dataset!([$t, 2, 3, $simd], 43,53,63;73,83,93)
        };
        (val, rmd_t, $simd:ident, $t:ty) => {
            {
                let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 43,73;53,83;63,93);
                rmd.transpose();
                rmd
            }
        };
        (val, did, $simd:ident, $t:ty) => {
            dual_index_dataset!([$t, 2, 3, $simd], 43,53,63;73,83,93)
        };
        (val, did_t, $simd:ident, $t:ty) => {
            {
                let mut did = dual_index_dataset!([$t, 3, 2, $simd], 43,73;53,83;63,93);
                did.transpose();
                did
            }
        };
        (val, cmd, $simd:ident, $t:ty) => {
            col_major_dataset!([$t, 2, 3, $simd], 43,53,63;73,83,93)
        };
        (val, cmd_t, $simd:ident, $t:ty) => {
            {
                let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 43,73;53,83;63,93);
                cmd.transpose();
                cmd
            }
        };
    }

    macro_rules! test_sub_into_val {
        ($t:ty, $simd:ident, $lhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = 7 as $t;
            let mut out = out!($out, $simd, $t);
            lhs.sub_into(rhs, &mut out);
            assert_eq!(out, result!(val, $out, $simd, $t));
        };
    }

    macro_rules! test_sub_into {
        ($t:ty, $simd:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            let mut lhs = lhs!($lhs, $simd, $t);
            let rhs = rhs!($rhs, $simd, $t);
            let mut out = out!($out, $simd, $t);
            lhs.sub_into(&rhs, &mut out);
            assert_eq!(out, result!($out, $simd, $t));
        };
    }

    macro_rules! fn_test_sub_into_val {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!(u8, false, $lhs, $out);
                test_sub_into_val!(u16, false, $lhs, $out);
                test_sub_into_val!(u32, false, $lhs, $out);
                test_sub_into_val!(u64, false, $lhs, $out);
                test_sub_into_val!(u128, false, $lhs, $out);
                test_sub_into_val!(i8, false, $lhs, $out);
                test_sub_into_val!(i16, false, $lhs, $out);
                test_sub_into_val!(i32, false, $lhs, $out);
                test_sub_into_val!(i64, false, $lhs, $out);
                test_sub_into_val!(i128, false, $lhs, $out);
                test_sub_into_val!(f32, false, $lhs, $out);
                test_sub_into_val!(f64, false, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into_val_simd {
        ($fn_name:ident, $lhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into_val!(u8, true, $lhs, $out);
                test_sub_into_val!(u16, true, $lhs, $out);
                test_sub_into_val!(u32, true, $lhs, $out);
                test_sub_into_val!(i8, true, $lhs, $out);
                test_sub_into_val!(i16, true, $lhs, $out);
                test_sub_into_val!(i32, true, $lhs, $out);
                test_sub_into_val!(f32, true, $lhs, $out);
                test_sub_into_val!(f64, true, $lhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!(u8, false, $lhs, $rhs, $out);
                test_sub_into!(u16, false, $lhs, $rhs, $out);
                test_sub_into!(u32, false, $lhs, $rhs, $out);
                test_sub_into!(u64, false, $lhs, $rhs, $out);
                test_sub_into!(u128, false, $lhs, $rhs, $out);
                test_sub_into!(i8, false, $lhs, $rhs, $out);
                test_sub_into!(i16, false, $lhs, $rhs, $out);
                test_sub_into!(i32, false, $lhs, $rhs, $out);
                test_sub_into!(i64, false, $lhs, $rhs, $out);
                test_sub_into!(i128, false, $lhs, $rhs, $out);
                test_sub_into!(f32, false, $lhs, $rhs, $out);
                test_sub_into!(f64, false, $lhs, $rhs, $out);
            }
        };
    }

    macro_rules! fn_test_sub_into_simd {
        ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
            #[test]
            fn $fn_name() {
                test_sub_into!(u8, true, $lhs, $rhs, $out);
                test_sub_into!(u16, true, $lhs, $rhs, $out);
                test_sub_into!(u32, true, $lhs, $rhs, $out);
                test_sub_into!(i8, true, $lhs, $rhs, $out);
                test_sub_into!(i16, true, $lhs, $rhs, $out);
                test_sub_into!(i32, true, $lhs, $rhs, $out);
                test_sub_into!(f32, true, $lhs, $rhs, $out);
                test_sub_into!(f64, true, $lhs, $rhs, $out);
            }
        };
    }

    fn_test_sub_into_val!(test_sub_into_val_cmd_rmd, cmd, rmd);
    fn_test_sub_into_val!(test_sub_into_val_cmd_cmd, cmd, cmd);
    fn_test_sub_into_val!(test_sub_into_val_cmd_did, cmd, did);

    fn_test_sub_into_val!(test_sub_into_val_cmd_t_rmd, cmd_t, rmd);
    fn_test_sub_into_val!(test_sub_into_val_cmd_t_cmd, cmd_t, cmd);
    fn_test_sub_into_val!(test_sub_into_val_cmd_t_did, cmd_t, did);

    fn_test_sub_into_val!(test_sub_into_val_cmd_rmd_t, cmd, rmd_t);
    fn_test_sub_into_val!(test_sub_into_val_cmd_cmd_t, cmd, cmd_t);
    fn_test_sub_into_val!(test_sub_into_val_cmd_did_t, cmd, did_t);

    fn_test_sub_into_val!(test_sub_into_val_cmd_t_rmd_t, cmd_t, rmd_t);
    fn_test_sub_into_val!(test_sub_into_val_cmd_t_cmd_t, cmd_t, cmd_t);
    fn_test_sub_into_val!(test_sub_into_val_cmd_t_did_t, cmd_t, did_t);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_rmd, cmd, rmd);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_cmd, cmd, cmd);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_did, cmd, did);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_rmd, cmd_t, rmd);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_cmd, cmd_t, cmd);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_did, cmd_t, did);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_rmd_t, cmd, rmd_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_cmd_t, cmd, cmd_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_did_t, cmd, did_t);

    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_rmd_t, cmd_t, rmd_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_cmd_t, cmd_t, cmd_t);
    fn_test_sub_into_val_simd!(test_sub_into_val_simd_cmd_t_did_t, cmd_t, did_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_rmd_rmd, cmd, rmd, rmd);
    fn_test_sub_into!(test_sub_into_cmd_rmd_rmd_t, cmd, rmd, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_rmd_t_rmd, cmd, rmd_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_rmd_t_rmd_t, cmd, rmd_t, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_rmd, cmd_t, rmd, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_rmd_t, cmd_t, rmd, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_rmd, cmd_t, rmd_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_rmd_t, cmd_t, rmd_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_rmd_cmd, cmd, rmd, cmd);
    fn_test_sub_into!(test_sub_into_cmd_rmd_cmd_t, cmd, rmd, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_rmd_t_cmd, cmd, rmd_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_rmd_t_cmd_t, cmd, rmd_t, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_cmd, cmd_t, rmd, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_cmd_t, cmd_t, rmd, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_cmd, cmd_t, rmd_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_cmd_t, cmd_t, rmd_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_rmd_did, cmd, rmd, did);
    fn_test_sub_into!(test_sub_into_cmd_rmd_did_t, cmd, rmd, did_t);

    fn_test_sub_into!(test_sub_into_cmd_rmd_t_did, cmd, rmd_t, did);
    fn_test_sub_into!(test_sub_into_cmd_rmd_t_did_t, cmd, rmd_t, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_did, cmd_t, rmd, did);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_did_t, cmd_t, rmd, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_did, cmd_t, rmd_t, did);
    fn_test_sub_into!(test_sub_into_cmd_t_rmd_t_did_t, cmd_t, rmd_t, did_t);

    ////////////////////////
    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_cmd_rmd, cmd, cmd, rmd);
    fn_test_sub_into!(test_sub_into_cmd_cmd_rmd_t, cmd, cmd, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_cmd_t_rmd, cmd, cmd_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_cmd_t_rmd_t, cmd, cmd_t, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_rmd, cmd_t, cmd, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_rmd_t, cmd_t, cmd, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_rmd, cmd_t, cmd_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_rmd_t, cmd_t, cmd_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_cmd_cmd, cmd, cmd, cmd);
    fn_test_sub_into!(test_sub_into_cmd_cmd_cmd_t, cmd, cmd, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_cmd_t_cmd, cmd, cmd_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_cmd_t_cmd_t, cmd, cmd_t, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_cmd, cmd_t, cmd, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_cmd_t, cmd_t, cmd, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_cmd, cmd_t, cmd_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_cmd_t, cmd_t, cmd_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_cmd_did, cmd, cmd, did);
    fn_test_sub_into!(test_sub_into_cmd_cmd_did_t, cmd, cmd, did_t);

    fn_test_sub_into!(test_sub_into_cmd_cmd_t_did, cmd, cmd_t, did);
    fn_test_sub_into!(test_sub_into_cmd_cmd_t_did_t, cmd, cmd_t, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_did, cmd_t, cmd, did);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_did_t, cmd_t, cmd, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_did, cmd_t, cmd_t, did);
    fn_test_sub_into!(test_sub_into_cmd_t_cmd_t_did_t, cmd_t, cmd_t, did_t);

    ////////////////////////
    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_did_rmd, cmd, did, rmd);
    fn_test_sub_into!(test_sub_into_cmd_did_rmd_t, cmd, did, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_did_t_rmd, cmd, did_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_did_t_rmd_t, cmd, did_t, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_rmd, cmd_t, did, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_did_rmd_t, cmd_t, did, rmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_t_rmd, cmd_t, did_t, rmd);
    fn_test_sub_into!(test_sub_into_cmd_t_did_t_rmd_t, cmd_t, did_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_did_cmd, cmd, did, cmd);
    fn_test_sub_into!(test_sub_into_cmd_did_cmd_t, cmd, did, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_did_t_cmd, cmd, did_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_did_t_cmd_t, cmd, did_t, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_cmd, cmd_t, did, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_did_cmd_t, cmd_t, did, cmd_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_t_cmd, cmd_t, did_t, cmd);
    fn_test_sub_into!(test_sub_into_cmd_t_did_t_cmd_t, cmd_t, did_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into!(test_sub_into_cmd_did_did, cmd, did, did);
    fn_test_sub_into!(test_sub_into_cmd_did_did_t, cmd, did, did_t);

    fn_test_sub_into!(test_sub_into_cmd_did_t_did, cmd, did_t, did);
    fn_test_sub_into!(test_sub_into_cmd_did_t_did_t, cmd, did_t, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_did, cmd_t, did, did);
    fn_test_sub_into!(test_sub_into_cmd_t_did_did_t, cmd_t, did, did_t);

    fn_test_sub_into!(test_sub_into_cmd_t_did_t_did, cmd_t, did_t, did);
    fn_test_sub_into!(test_sub_into_cmd_t_did_t_did_t, cmd_t, did_t, did_t);

    //////////////////////////////////////////////////////////////////////////////
    // SIMD Tests
    //////////////////////////////////////////////////////////////////////////////
    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_rmd, cmd, rmd, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_rmd_t, cmd, rmd, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_rmd, cmd, rmd_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_rmd_t, cmd, rmd_t, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_rmd, cmd_t, rmd, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_rmd_t, cmd_t, rmd, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_rmd, cmd_t, rmd_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_rmd_t, cmd_t, rmd_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_cmd, cmd, rmd, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_cmd_t, cmd, rmd, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_cmd, cmd, rmd_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_cmd_t, cmd, rmd_t, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_cmd, cmd_t, rmd, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_cmd_t, cmd_t, rmd, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_cmd, cmd_t, rmd_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_cmd_t, cmd_t, rmd_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&RowMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_did, cmd, rmd, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_did_t, cmd, rmd, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_did, cmd, rmd_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_rmd_t_did_t, cmd, rmd_t, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_did, cmd_t, rmd, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_did_t, cmd_t, rmd, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_did, cmd_t, rmd_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_rmd_t_did_t, cmd_t, rmd_t, did_t);

    ////////////////////////
    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_rmd, cmd, cmd, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_rmd_t, cmd, cmd, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_rmd, cmd, cmd_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_rmd_t, cmd, cmd_t, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_rmd, cmd_t, cmd, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_rmd_t, cmd_t, cmd, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_rmd, cmd_t, cmd_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_rmd_t, cmd_t, cmd_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_cmd, cmd, cmd, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_cmd_t, cmd, cmd, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_cmd, cmd, cmd_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_cmd_t, cmd, cmd_t, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_cmd, cmd_t, cmd, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_cmd_t, cmd_t, cmd, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_cmd, cmd_t, cmd_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_cmd_t, cmd_t, cmd_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&ColMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_did, cmd, cmd, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_did_t, cmd, cmd, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_did, cmd, cmd_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_cmd_t_did_t, cmd, cmd_t, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_did, cmd_t, cmd, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_did_t, cmd_t, cmd, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_did, cmd_t, cmd_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_cmd_t_did_t, cmd_t, cmd_t, did_t);

    ////////////////////////
    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_rmd, cmd, did, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_rmd_t, cmd, did, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_rmd, cmd, did_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_rmd_t, cmd, did_t, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_rmd, cmd_t, did, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_rmd_t, cmd_t, did, rmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_rmd, cmd_t, did_t, rmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_rmd_t, cmd_t, did_t, rmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_cmd, cmd, did, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_cmd_t, cmd, did, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_cmd, cmd, did_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_cmd_t, cmd, did_t, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_cmd, cmd_t, did, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_cmd_t, cmd_t, did, cmd_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_cmd, cmd_t, did_t, cmd);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_cmd_t, cmd_t, did_t, cmd_t);

    //                Rhs              , Result                   Lhs
    // Test SubInto<&DualIndexDataset<T>, DualndexDataset<T>> for ColMajordataset<T>
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_did, cmd, did, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_did_t, cmd, did, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_did, cmd, did_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_did_t_did_t, cmd, did_t, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_did, cmd_t, did, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_did_t, cmd_t, did, did_t);

    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_did, cmd_t, did_t, did);
    fn_test_sub_into_simd!(test_sub_into_simd_cmd_t_did_t_did_t, cmd_t, did_t, did_t);
}
