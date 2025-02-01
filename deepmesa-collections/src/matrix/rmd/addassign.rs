use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::simd::kernel::SimdKernel;
use crate::matrix::simd::traits::SimdPtrAddAssign;
use crate::matrix::traits::Dataset;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::SimdAddAssign;
use std::ops::AddAssign;

impl<T> AddAssign<T> for RowMajorDataset<T>
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
                rmd_add_assign_t!(self, row, col, val);
            });
        } else {
            iterate_row_major!(self, row, col, unsafe {
                rmd_add_assign!(self, row, col, val);
            });
        }
    }
}

impl<T> AddAssign<&RowMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &RowMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);
        if self.is_transpose {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign_t!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign_t!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign!(self, row, col, rmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign!(self, row, col, rmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> SimdAddAssign<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn simd_add_assign(&mut self, val: T) {
        let ptr = self.rm_data;
        let len = self.rm_len;
        unsafe {
            SimdKernel::ptr_add_assign(ptr, len, val);
        }
    }
}

impl<T> AddAssign<&ColMajorDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &ColMajorDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        if self.is_transpose {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign_t!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign_t!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        } else {
            if rhs.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign!(self, row, col, cmd_get_t!(rhs, row, col));
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    rmd_add_assign!(self, row, col, cmd_get!(rhs, row, col));
                });
            }
        }
    }
}

impl<T> AddAssign<&DualIndexDataset<T>> for RowMajorDataset<T>
where
    T: MatrixElement + std::ops::AddAssign,
{
    fn add_assign(&mut self, rhs: &DualIndexDataset<T>) {
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.add_assign(&rhs.rmd);
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixType;
    use std::ops::AddAssign;

    #[test]
    fn test_add() {
        let mut m = Matrix::new(3, 2, MatrixType::RowMajor, true);
        let v = vec![1, 2, 3, 4, 5, 6];
        m.fill_row_major(&v);

        let mut m2 = Matrix::new(2, 3, MatrixType::RowMajor, true);
        m2.fill_row_major(&v);

        m.transpose();
        //m2.transpose();
        //        println!("m': {:?}", m);

        println!("adding M={:?} and M2={:?}", m, m2);
        m.add_assign(&m2);
        println!("Matrix after add: {:?}", m);
    }
}
