use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq<RowMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &RowMajorDataset<T>) -> bool {
        return other.eq(&self.rmd);
    }
}

impl<T> PartialEq<ColMajorDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &ColMajorDataset<T>) -> bool {
        return other.eq(&self.rmd);
    }
}

impl<T> PartialEq<DualIndexDataset<T>> for DualIndexDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &DualIndexDataset<T>) -> bool {
        return other.eq(&self.rmd);
    }
}
