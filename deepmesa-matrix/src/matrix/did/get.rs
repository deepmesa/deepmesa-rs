use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::traits::Get;
use crate::matrix::traits::MatrixElement;

impl<T> Get<T> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < self.rows);
        debug_assert!(col < self.cols);
        return self.rmd.get(row, col);
    }
}
