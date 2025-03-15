use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::did::data::SyncDirection;
use crate::matrix::macros::*;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdMulInto;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::{MatrixElement, MulInto};

impl<T> MulInto<T, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: T, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(cmd_t, val, rmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign_t!(result, row, col, cmd_get_t!(self, row, col) * rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(cmd_t, val, rmd, self, rhs, result); // SIMD WORKS
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign!(result, row, col, cmd_get_t!(self, row, col) * rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(cmd, val, rmd_t, self, rhs, result); //SIMD Works
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign_t!(result, row, col, cmd_get!(self, row, col) * rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(cmd, val, rmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    rmd_assign!(result, row, col, cmd_get!(self, row, col) * rhs);
                });
            }
        }
    }
}

impl<T> MulInto<T, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: T, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(cmd_t, val, cmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign_t!(result, row, col, cmd_get_t!(self, row, col) * rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(cmd_t, val, cmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign!(result, row, col, cmd_get_t!(self, row, col) * rhs);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(cmd, val, cmd_t, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign_t!(result, row, col, cmd_get!(self, row, col) * rhs);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(cmd, val, cmd, self, rhs, result);
                iterate_row_major!(self, row, col, unsafe {
                    cmd_assign!(result, row, col, cmd_get!(self, row, col) * rhs);
                });
            }
        }
    }
}

impl<T> MulInto<T, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: T, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        if self.is_transpose {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(
                    cmd_t,
                    val,
                    cmd_t,
                    self,
                    rhs,
                    result.cmd,
                    result.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get_t!(self, row, col) * rhs;
                    cmd_assign_t!(result.cmd, row, col, val);
                    rmd_assign_t!(result.rmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(
                    cmd_t,
                    val,
                    rmd,
                    self,
                    rhs,
                    result.rmd,
                    result.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get_t!(self, row, col) * rhs;
                    cmd_assign!(result.cmd, row, col, val);
                    rmd_assign!(result.rmd, row, col, val);
                });
            }
        } else {
            if result.is_transpose {
                crate::matrix::cmd::macros::simd_mul_into!(
                    cmd,
                    val,
                    rmd_t,
                    self,
                    rhs,
                    result.rmd,
                    result.sync(SyncDirection::RmdToCmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get!(self, row, col) * rhs;
                    cmd_assign_t!(result.cmd, row, col, val);
                    rmd_assign_t!(result.rmd, row, col, val);
                });
            } else {
                crate::matrix::cmd::macros::simd_mul_into!(
                    cmd,
                    val,
                    cmd,
                    self,
                    rhs,
                    result.cmd,
                    result.sync(SyncDirection::CmdToRmd)
                );
                iterate_row_major!(self, row, col, unsafe {
                    let val = cmd_get!(self, row, col) * rhs;
                    cmd_assign!(result.cmd, row, col, val);
                    rmd_assign!(result.rmd, row, col, val);
                });
            }
        }
    }
}

impl<T> MulInto<&RowMajorDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, rmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd_t, rmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, rmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd_t, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd, rmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&RowMajorDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &RowMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, cmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd_t, rmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, rmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd_t, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd, cmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, rmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * rmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&RowMajorDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &RowMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd_t, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * rmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t,
                        rmd,
                        cmd_t,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, rmd, rmd, self, rhs, result.rmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * rmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, rmd_t, rmd_t, self, rhs, result.rmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd,
                        rmd_t,
                        cmd,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * rmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, rmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * rmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, rmd, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * rmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&ColMajorDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &ColMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd_t, rmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd_t, cmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, cmd_t, rmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd_t, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd, rmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd, rmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        rmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&ColMajorDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &ColMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd_t, cmd, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd_t, cmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, cmd_t, cmd_t, self, rhs, result
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd_t, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col)
                        );
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd, cmd_t, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign_t!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(cmd, cmd, cmd, self, rhs, result);
                    iterate_row_major!(self, row, col, unsafe {
                        cmd_assign!(
                            result,
                            row,
                            col,
                            cmd_get!(self, row, col) * cmd_get!(rhs, row, col)
                        );
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&ColMajorDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &ColMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t,
                        cmd_t,
                        cmd_t,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t,
                        cmd_t,
                        rmd,
                        self,
                        rhs,
                        result.rmd,
                        result.sync(SyncDirection::RmdToCmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * cmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd_t, cmd, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get_t!(self, row, col) * cmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, cmd_t, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, cmd_t, cmd, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * cmd_get_t!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            } else {
                if result.is_transpose {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd, cmd, cmd_t, self, rhs, result.cmd
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * cmd_get!(rhs, row, col);
                        cmd_assign_t!(result.cmd, row, col, val);
                        rmd_assign_t!(result.rmd, row, col, val);
                    });
                } else {
                    crate::matrix::cmd::macros::simd_mul_into!(
                        cmd,
                        cmd,
                        cmd,
                        self,
                        rhs,
                        result.cmd,
                        result.sync(SyncDirection::CmdToRmd)
                    );
                    iterate_row_major!(self, row, col, unsafe {
                        let val = cmd_get!(self, row, col) * cmd_get!(rhs, row, col);
                        cmd_assign!(result.cmd, row, col, val);
                        rmd_assign!(result.rmd, row, col, val);
                    });
                }
            }
        }
    }
}

impl<T> MulInto<&DualIndexDataset<T>, DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &DualIndexDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.mul_into(&rhs.cmd, result);
    }
}

impl<T> MulInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &DualIndexDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.mul_into(&rhs.cmd, result);
    }
}

impl<T> MulInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement + std::ops::MulAssign + std::ops::Mul<Output = T>,
{
    fn mul_into(&self, rhs: &DualIndexDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        self.mul_into(&rhs.cmd, result);
    }
}

// #[cfg(test)]
// mod tests {
//     use crate::matrix::cmd::data::*;
//     use crate::matrix::cmd::macros::col_major_dataset;
//     use crate::matrix::did::data::*;
//     use crate::matrix::did::macros::dual_index_dataset;
//     use crate::matrix::rmd::data::*;
//     use crate::matrix::rmd::macros::row_major_dataset;
//     use crate::matrix::traits::*;

//     macro_rules! lhs {
//         (cmd, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t, 2, 3, $simd], 5,6,7;8,9,10)
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t, 3,2, $simd], 5,8;6,9;7,10);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//     }

//     macro_rules! rhs {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t,2,3, $simd], 2,3,4;5,6,7)
//         };
//         (cmd, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t,3,2, $simd], 2,5;3,6;4,7);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t,2,3,false], 2,3,4;5,6,7)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t,3,2, $simd], 2,5;3,6;4,7);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t,2,3, false], 2,3,4;5,6,7)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t,3,2, $simd], 2,5;3,6;4,7);
//                 did.transpose();
//                 did
//             }
//         };
//     }

//     macro_rules! out {
//         (rmd, $simd:ident, $t:ty) => {
//             RowMajorDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {{
//             let mut rmd = RowMajorDataset::<$t>::new(3, 2, $simd, $simd);
//             rmd.transpose();
//             rmd
//         }};
//         (cmd, $simd:ident, $t:ty) => {
//             ColMajorDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (cmd_t, $simd:ident, $t:ty) => {{
//             let mut cmd = ColMajorDataset::<$t>::new(3, 2, $simd, $simd);
//             cmd.transpose();
//             cmd
//         }};
//         (did, $simd:ident, $t:ty) => {
//             DualIndexDataset::<$t>::new(2, 3, $simd, $simd)
//         };
//         (did_t, $simd:ident, $t:ty) => {{
//             let mut did = DualIndexDataset::<$t>::new(3, 2, $simd, $simd);
//             did.transpose();
//             did
//         }};
//     }

//     macro_rules! result {
//         (rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 10,18,28;40,54,70)
//         };
//         (rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 10,40;18,54;28,70);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 10,18,28;40,54,70)
//         };
//         (did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3, 2, $simd], 10,40;18,54;28,70);
//                 did.transpose();
//                 did
//             }
//         };
//         (cmd, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t, 2, 3, $simd], 10,18,28;40,54,70)
//         };
//         (cmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 10,40;18,54;28,70);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//         (val, rmd, $simd:ident, $t:ty) => {
//             row_major_dataset!([$t, 2, 3, $simd], 35,42,49;56,63,70)
//         };
//         (val, rmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut rmd = row_major_dataset!([$t, 3, 2, $simd], 35,56;42,63;49,70);
//                 rmd.transpose();
//                 rmd
//             }
//         };
//         (val, did, $simd:ident, $t:ty) => {
//             dual_index_dataset!([$t, 2, 3, $simd], 35,42,49;56,63,70)
//         };
//         (val, did_t, $simd:ident, $t:ty) => {
//             {
//                 let mut did = dual_index_dataset!([$t, 3, 2, $simd], 35,56;42,63;49,70);
//                 did.transpose();
//                 did
//             }
//         };
//         (val, cmd, $simd:ident, $t:ty) => {
//             col_major_dataset!([$t, 2, 3, $simd], 35,42,49;56,63,70)
//         };
//         (val, cmd_t, $simd:ident, $t:ty) => {
//             {
//                 let mut cmd = col_major_dataset!([$t, 3, 2, $simd], 35,56;42,63;49,70);
//                 cmd.transpose();
//                 cmd
//             }
//         };
//     }

//     macro_rules! test_mul_into_val {
//         ($t:ty, $simd:ident, $lhs:ident, $out:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = 7 as $t;
//             let mut out = out!($out, $simd, $t);
//             lhs.mul_into(rhs, &mut out);
//             assert_eq!(out, result!(val, $out, $simd, $t));
//         };
//     }

//     macro_rules! test_mul_into {
//         ($t:ty, $simd:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             let mut lhs = lhs!($lhs, $simd, $t);
//             let rhs = rhs!($rhs, $simd, $t);
//             let mut out = out!($out, $simd, $t);
//             lhs.mul_into(&rhs, &mut out);
//             assert_eq!(out, result!($out, $simd, $t));
//         };
//     }

//     macro_rules! fn_test_mul_into_val {
//         ($fn_name:ident, $lhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_into_val!(u8, false, $lhs, $out);
//                 test_mul_into_val!(u16, false, $lhs, $out);
//                 test_mul_into_val!(u32, false, $lhs, $out);
//                 test_mul_into_val!(u64, false, $lhs, $out);
//                 test_mul_into_val!(u128, false, $lhs, $out);
//                 test_mul_into_val!(i8, false, $lhs, $out);
//                 test_mul_into_val!(i16, false, $lhs, $out);
//                 test_mul_into_val!(i32, false, $lhs, $out);
//                 test_mul_into_val!(i64, false, $lhs, $out);
//                 test_mul_into_val!(i128, false, $lhs, $out);
//                 test_mul_into_val!(f32, false, $lhs, $out);
//                 test_mul_into_val!(f64, false, $lhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_into_val_simd {
//         ($fn_name:ident, $lhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_into_val!(u8, true, $lhs, $out);
//                 test_mul_into_val!(u16, true, $lhs, $out);
//                 test_mul_into_val!(u32, true, $lhs, $out);
//                 test_mul_into_val!(i8, true, $lhs, $out);
//                 test_mul_into_val!(i16, true, $lhs, $out);
//                 test_mul_into_val!(i32, true, $lhs, $out);
//                 test_mul_into_val!(f32, true, $lhs, $out);
//                 test_mul_into_val!(f64, true, $lhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_into {
//         ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_into!(u8, false, $lhs, $rhs, $out);
//                 test_mul_into!(u16, false, $lhs, $rhs, $out);
//                 test_mul_into!(u32, false, $lhs, $rhs, $out);
//                 test_mul_into!(u64, false, $lhs, $rhs, $out);
//                 test_mul_into!(u128, false, $lhs, $rhs, $out);
//                 test_mul_into!(i8, false, $lhs, $rhs, $out);
//                 test_mul_into!(i16, false, $lhs, $rhs, $out);
//                 test_mul_into!(i32, false, $lhs, $rhs, $out);
//                 test_mul_into!(i64, false, $lhs, $rhs, $out);
//                 test_mul_into!(i128, false, $lhs, $rhs, $out);
//                 test_mul_into!(f32, false, $lhs, $rhs, $out);
//                 test_mul_into!(f64, false, $lhs, $rhs, $out);
//             }
//         };
//     }

//     macro_rules! fn_test_mul_into_simd {
//         ($fn_name:ident, $lhs:ident, $rhs:ident, $out:ident) => {
//             #[test]
//             fn $fn_name() {
//                 test_mul_into!(u8, true, $lhs, $rhs, $out);
//                 test_mul_into!(u16, true, $lhs, $rhs, $out);
//                 test_mul_into!(u32, true, $lhs, $rhs, $out);
//                 test_mul_into!(i8, true, $lhs, $rhs, $out);
//                 test_mul_into!(i16, true, $lhs, $rhs, $out);
//                 test_mul_into!(i32, true, $lhs, $rhs, $out);
//                 test_mul_into!(f32, true, $lhs, $rhs, $out);
//                 test_mul_into!(f64, true, $lhs, $rhs, $out);
//             }
//         };
//     }

//     fn_test_mul_into_val!(test_mul_into_val_cmd_rmd, cmd, rmd);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_cmd, cmd, cmd);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_did, cmd, did);

//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_rmd, cmd_t, rmd);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_cmd, cmd_t, cmd);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_did, cmd_t, did);

//     fn_test_mul_into_val!(test_mul_into_val_cmd_rmd_t, cmd, rmd_t);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_cmd_t, cmd, cmd_t);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_did_t, cmd, did_t);

//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_rmd_t, cmd_t, rmd_t);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_cmd_t, cmd_t, cmd_t);
//     fn_test_mul_into_val!(test_mul_into_val_cmd_t_did_t, cmd_t, did_t);

//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_rmd, cmd, rmd);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_cmd, cmd, cmd);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_did, cmd, did);

//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_rmd, cmd_t, rmd);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_cmd, cmd_t, cmd);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_did, cmd_t, did);

//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_rmd_t, cmd, rmd_t);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_cmd_t, cmd, cmd_t);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_did_t, cmd, did_t);

//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_rmd_t, cmd_t, rmd_t);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_cmd_t, cmd_t, cmd_t);
//     fn_test_mul_into_val_simd!(test_mul_into_val_simd_cmd_t_did_t, cmd_t, did_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_rmd_rmd, cmd, rmd, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_rmd_t, cmd, rmd, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_rmd, cmd, rmd_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_rmd_t, cmd, rmd_t, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_rmd, cmd_t, rmd, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_rmd_t, cmd_t, rmd, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_rmd, cmd_t, rmd_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_rmd_t, cmd_t, rmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_rmd_cmd, cmd, rmd, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_cmd_t, cmd, rmd, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_cmd, cmd, rmd_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_cmd_t, cmd, rmd_t, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_cmd, cmd_t, rmd, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_cmd_t, cmd_t, rmd, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_cmd, cmd_t, rmd_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_cmd_t, cmd_t, rmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_rmd_did, cmd, rmd, did);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_did_t, cmd, rmd, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_did, cmd, rmd_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_rmd_t_did_t, cmd, rmd_t, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_did, cmd_t, rmd, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_did_t, cmd_t, rmd, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_did, cmd_t, rmd_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_rmd_t_did_t, cmd_t, rmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_cmd_rmd, cmd, cmd, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_rmd_t, cmd, cmd, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_rmd, cmd, cmd_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_rmd_t, cmd, cmd_t, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_rmd, cmd_t, cmd, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_rmd_t, cmd_t, cmd, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_rmd, cmd_t, cmd_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_rmd_t, cmd_t, cmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_cmd_cmd, cmd, cmd, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_cmd_t, cmd, cmd, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_cmd, cmd, cmd_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_cmd_t, cmd, cmd_t, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_cmd, cmd_t, cmd, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_cmd_t, cmd_t, cmd, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_cmd, cmd_t, cmd_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_cmd_t, cmd_t, cmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_cmd_did, cmd, cmd, did);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_did_t, cmd, cmd, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_did, cmd, cmd_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_cmd_t_did_t, cmd, cmd_t, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_did, cmd_t, cmd, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_did_t, cmd_t, cmd, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_did, cmd_t, cmd_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_cmd_t_did_t, cmd_t, cmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_did_rmd, cmd, did, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_did_rmd_t, cmd, did, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_did_t_rmd, cmd, did_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_did_t_rmd_t, cmd, did_t, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_rmd, cmd_t, did, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_rmd_t, cmd_t, did, rmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_rmd, cmd_t, did_t, rmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_rmd_t, cmd_t, did_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_did_cmd, cmd, did, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_did_cmd_t, cmd, did, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_did_t_cmd, cmd, did_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_did_t_cmd_t, cmd, did_t, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_cmd, cmd_t, did, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_cmd_t, cmd_t, did, cmd_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_cmd, cmd_t, did_t, cmd);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_cmd_t, cmd_t, did_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into!(test_mul_into_cmd_did_did, cmd, did, did);
//     fn_test_mul_into!(test_mul_into_cmd_did_did_t, cmd, did, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_did_t_did, cmd, did_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_did_t_did_t, cmd, did_t, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_did, cmd_t, did, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_did_t, cmd_t, did, did_t);

//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_did, cmd_t, did_t, did);
//     fn_test_mul_into!(test_mul_into_cmd_t_did_t_did_t, cmd_t, did_t, did_t);

//     //////////////////////////////////////////////////////////////////////////////
//     // SIMD Tests
//     //////////////////////////////////////////////////////////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_rmd, cmd, rmd, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_rmd_t, cmd, rmd, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_rmd, cmd, rmd_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_rmd_t, cmd, rmd_t, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_rmd, cmd_t, rmd, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_rmd_t, cmd_t, rmd, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_rmd, cmd_t, rmd_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_rmd_t, cmd_t, rmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_cmd, cmd, rmd, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_cmd_t, cmd, rmd, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_cmd, cmd, rmd_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_cmd_t, cmd, rmd_t, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_cmd, cmd_t, rmd, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_cmd_t, cmd_t, rmd, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_cmd, cmd_t, rmd_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_cmd_t, cmd_t, rmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&RowMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_did, cmd, rmd, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_did_t, cmd, rmd, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_did, cmd, rmd_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_rmd_t_did_t, cmd, rmd_t, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_did, cmd_t, rmd, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_did_t, cmd_t, rmd, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_did, cmd_t, rmd_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_rmd_t_did_t, cmd_t, rmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_rmd, cmd, cmd, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_rmd_t, cmd, cmd, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_rmd, cmd, cmd_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_rmd_t, cmd, cmd_t, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_rmd, cmd_t, cmd, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_rmd_t, cmd_t, cmd, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_rmd, cmd_t, cmd_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_rmd_t, cmd_t, cmd_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_cmd, cmd, cmd, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_cmd_t, cmd, cmd, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_cmd, cmd, cmd_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_cmd_t, cmd, cmd_t, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_cmd, cmd_t, cmd, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_cmd_t, cmd_t, cmd, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_cmd, cmd_t, cmd_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_cmd_t, cmd_t, cmd_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&ColMajordataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_did, cmd, cmd, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_did_t, cmd, cmd, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_did, cmd, cmd_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_cmd_t_did_t, cmd, cmd_t, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_did, cmd_t, cmd, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_did_t, cmd_t, cmd, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_did, cmd_t, cmd_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_cmd_t_did_t, cmd_t, cmd_t, did_t);

//     ////////////////////////
//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, RowMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_rmd, cmd, did, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_rmd_t, cmd, did, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_rmd, cmd, did_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_rmd_t, cmd, did_t, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_rmd, cmd_t, did, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_rmd_t, cmd_t, did, rmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_rmd, cmd_t, did_t, rmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_rmd_t, cmd_t, did_t, rmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, ColMajorDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_cmd, cmd, did, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_cmd_t, cmd, did, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_cmd, cmd, did_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_cmd_t, cmd, did_t, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_cmd, cmd_t, did, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_cmd_t, cmd_t, did, cmd_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_cmd, cmd_t, did_t, cmd);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_cmd_t, cmd_t, did_t, cmd_t);

//     //                Rhs              , Result                   Lhs
//     // Test MulInto<&DualIndexDataset<T>, DualndexDataset<T>> for ColMajordataset<T>
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_did, cmd, did, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_did_t, cmd, did, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_did, cmd, did_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_did_t_did_t, cmd, did_t, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_did, cmd_t, did, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_did_t, cmd_t, did, did_t);

//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_did, cmd_t, did_t, did);
//     fn_test_mul_into_simd!(test_mul_into_simd_cmd_t_did_t_did_t, cmd_t, did_t, did_t);
// }
