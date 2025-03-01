use crate::matrix::cmd::macros::*;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::Set;

impl<T> Set<T> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn set(&mut self, row: usize, col: usize, val: T) {
        match self.is_transpose {
            true => unsafe {
                rmd_assign_t!(self.rmd, row, col, val);
                cmd_assign_t!(self.cmd, row, col, val);
            },
            false => unsafe {
                rmd_assign!(self.rmd, row, col, val);
                cmd_assign!(self.cmd, row, col, val);
            },
        }
    }
}
