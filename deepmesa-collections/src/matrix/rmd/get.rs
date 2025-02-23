use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::rmd::macros::*;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < self.rows);
        debug_assert!(col < self.cols);
        if self.is_transpose {
            unsafe {
                return rmd_get_t!(self, row, col);
            }
        } else {
            unsafe {
                return rmd_get!(self, row, col);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::rmd::data::*;
    use crate::matrix::rmd::macros::row_major_dataset;
    use crate::matrix::traits::*;
    #[test]
    fn test_get() {
        let mut rmd = row_major_dataset!([u8, 2, 3, false], 3,4,5;6,7,8);
        assert_eq!(3, rmd.get(0, 0));
        assert_eq!(4, rmd.get(0, 1));
        assert_eq!(5, rmd.get(0, 2));
        assert_eq!(6, rmd.get(1, 0));
        assert_eq!(7, rmd.get(1, 1));
        assert_eq!(8, rmd.get(1, 2));

        rmd.transpose();
        assert_eq!(3, rmd.get(0, 0));
        assert_eq!(6, rmd.get(0, 1));
        assert_eq!(4, rmd.get(1, 0));
        assert_eq!(7, rmd.get(1, 1));
        assert_eq!(5, rmd.get(2, 0));
        assert_eq!(8, rmd.get(2, 1));
    }
}
