use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::{AddInto, MatrixElement};

impl<T> AddInto<T, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<T, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<T, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: T, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&RowMajorDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &RowMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&ColMajorDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &ColMajorDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut RowMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut ColMajorDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}

impl<T> AddInto<&DualIndexDataset<T>, DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement + std::ops::AddAssign + std::ops::Add<Output = T>,
{
    fn add_into(&self, rhs: &DualIndexDataset<T>, result: &mut DualIndexDataset<T>) {
        debug_assert!(self.rows == result.rows);
        debug_assert!(self.cols == result.cols);
        debug_assert!(self.rows == rhs.rows);
        debug_assert!(self.cols == rhs.cols);

        self.rmd.add_into(rhs, result);
    }
}
