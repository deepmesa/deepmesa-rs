use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::{AddInto, MatrixElement};
use std::ops::AddAssign;

impl<T> AddInto<T, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: T, result: &mut Matrix<T>) {
        match self.m_type {
            MatrixType::ColMajor => match result.m_type {
                MatrixType::ColMajor => {
                    self.cmd.add_into(rhs, &mut result.cmd);
                }
                MatrixType::RowMajor => {
                    self.cmd.add_into(rhs, &mut result.rmd);
                }
                MatrixType::DualIndex => {
                    self.cmd.add_into(rhs, &mut result.did);
                }
            },
            MatrixType::RowMajor => match result.m_type {
                MatrixType::ColMajor => {
                    self.rmd.add_into(rhs, &mut result.cmd);
                }
                MatrixType::RowMajor => {
                    self.rmd.add_into(rhs, &mut result.rmd);
                }
                MatrixType::DualIndex => {
                    self.rmd.add_into(rhs, &mut result.did);
                }
            },
            MatrixType::DualIndex => match result.m_type {
                MatrixType::ColMajor => {
                    self.did.add_into(rhs, &mut result.cmd);
                }
                MatrixType::RowMajor => {
                    self.did.add_into(rhs, &mut result.rmd);
                }
                MatrixType::DualIndex => {
                    self.did.add_into(rhs, &mut result.did);
                }
            },
        }
    }
}

impl<T> AddInto<&Matrix<T>, Matrix<T>> for Matrix<T>
where
    T: MatrixElement<Output = T> + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(self, rhs: &Matrix<T>, result: &mut Matrix<T>) {
        match self.m_type {
            //Self: ColMajor
            MatrixType::ColMajor => match result.m_type {
                //Result: ColMajor
                MatrixType::ColMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.cmd.add_into(&rhs.cmd, &mut result.cmd),
                    MatrixType::RowMajor => self.cmd.add_into(&rhs.rmd, &mut result.cmd),
                    MatrixType::DualIndex => self.cmd.add_into(&rhs.did, &mut result.cmd),
                },
                //Result: RowMajor
                MatrixType::RowMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.cmd.add_into(&rhs.cmd, &mut result.rmd),
                    MatrixType::RowMajor => self.cmd.add_into(&rhs.rmd, &mut result.rmd),
                    MatrixType::DualIndex => self.cmd.add_into(&rhs.did, &mut result.rmd),
                },
                //Result: DualIndex
                MatrixType::DualIndex => match rhs.m_type {
                    MatrixType::ColMajor => self.cmd.add_into(&rhs.cmd, &mut result.did),
                    MatrixType::RowMajor => self.cmd.add_into(&rhs.rmd, &mut result.did),
                    MatrixType::DualIndex => self.cmd.add_into(&rhs.rmd, &mut result.did),
                },
            },
            //Self: RowMajor
            MatrixType::RowMajor => match result.m_type {
                //Result ColMajor
                MatrixType::ColMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.rmd.add_into(&rhs.cmd, &mut result.cmd),
                    MatrixType::RowMajor => self.rmd.add_into(&rhs.rmd, &mut result.cmd),
                    MatrixType::DualIndex => self.rmd.add_into(&rhs.did.rmd, &mut result.cmd),
                },
                //Result RowMajor
                MatrixType::RowMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.rmd.add_into(&rhs.cmd, &mut result.rmd),
                    MatrixType::RowMajor => self.rmd.add_into(&rhs.rmd, &mut result.rmd),
                    MatrixType::DualIndex => self.rmd.add_into(&rhs.did.rmd, &mut result.rmd),
                },
                //Result DualIndex
                MatrixType::DualIndex => match rhs.m_type {
                    MatrixType::ColMajor => self.rmd.add_into(&rhs.cmd, &mut result.did),
                    MatrixType::RowMajor => self.rmd.add_into(&rhs.rmd, &mut result.did),
                    MatrixType::DualIndex => self.rmd.add_into(&rhs.did.rmd, &mut result.did),
                },
            },
            //Self: DualIndex
            MatrixType::DualIndex => match result.m_type {
                //Result ColMajor
                MatrixType::ColMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.did.rmd.add_into(&rhs.cmd, &mut result.cmd),
                    MatrixType::RowMajor => self.did.rmd.add_into(&rhs.rmd, &mut result.cmd),
                    MatrixType::DualIndex => self.did.rmd.add_into(&rhs.did.rmd, &mut result.cmd),
                },
                //Result RowMajor
                MatrixType::RowMajor => match rhs.m_type {
                    MatrixType::ColMajor => self.did.rmd.add_into(&rhs.cmd, &mut result.rmd),
                    MatrixType::RowMajor => self.did.rmd.add_into(&rhs.rmd, &mut result.rmd),
                    MatrixType::DualIndex => self.did.rmd.add_into(&rhs.did.rmd, &mut result.rmd),
                },
                //Result DualIndex
                MatrixType::DualIndex => match rhs.m_type {
                    MatrixType::ColMajor => self.did.rmd.add_into(&rhs.cmd, &mut result.did),
                    MatrixType::RowMajor => self.did.rmd.add_into(&rhs.rmd, &mut result.did),
                    MatrixType::DualIndex => self.did.rmd.add_into(&rhs.did.rmd, &mut result.did),
                },
            },
        }
    }
}
