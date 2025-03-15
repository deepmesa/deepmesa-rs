use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::macros::*;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::MatMul;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::MulInto;
use std::ops::Mul;
use std::ops::MulAssign;

impl<T> MatMul<RowMajorDataset<T>, RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement<Output = T> + std::ops::Mul<Output = T> + std::ops::AddAssign,
{
    fn mat_mul(&self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        if self.is_transpose {
            if rhs.is_transpose {
                if result.is_transpose {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get_t!(self, row, idx) * rmd_get_t!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign_t!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                } else {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get_t!(self, row, idx) * rmd_get_t!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                }
            } else {
                if result.is_transpose {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get_t!(self, row, idx) * rmd_get!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign_t!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                } else {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get_t!(self, row, idx) * rmd_get!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                }
            }
        } else {
            if rhs.is_transpose {
                if result.is_transpose {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get!(self, row, idx) * rmd_get_t!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign_t!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                } else {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get!(self, row, idx) * rmd_get_t!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                }
            } else {
                if result.is_transpose {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get!(self, row, idx) * rmd_get!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign_t!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                } else {
                    let mut accum = T::zero();
                    #[rustfmt::skip]
                    iterate_matmul!(self, rhs, row, col, idx,
                        unsafe {
                            let mul = rmd_get!(self, row, idx) * rmd_get!(rhs, col, idx);
                            accum += mul;
                        },
                        unsafe {
                            rmd_assign!(result, row, col, accum);
                            accum = T::zero();
                        }
                    );
                }
            }
        }
    }
}
