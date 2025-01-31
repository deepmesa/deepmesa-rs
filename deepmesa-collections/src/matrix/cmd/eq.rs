use crate::matrix::cmd::data::ColMajorDataset;
use crate::matrix::did::data::DualIndexDataset;
use crate::matrix::rmd::data::RowMajorDataset;
use crate::matrix::traits::MatrixElement;

impl<T> PartialEq<RowMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &RowMajorDataset<T>) -> bool {
        if self.rows != other.rows {
            return false;
        }

        if self.cols != other.cols {
            return false;
        }

        if self.is_transpose {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get_t!(self, row, col) != rmd_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get_t!(self, row, col) != rmd_get!(other, row, col) {
                        return false;
                    }
                });
            }
        } else {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get!(self, row, col) != rmd_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get!(self, row, col) != rmd_get!(other, row, col) {
                        return false;
                    }
                });
            }
        }
        return true;
    }
}

impl<T> PartialEq<ColMajorDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &ColMajorDataset<T>) -> bool {
        if self.rows != other.rows {
            return false;
        }

        if self.cols != other.cols {
            return false;
        }

        if self.is_transpose {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get_t!(self, row, col) != cmd_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get_t!(self, row, col) != cmd_get!(other, row, col) {
                        return false;
                    }
                });
            }
        } else {
            if other.is_transpose {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get!(self, row, col) != cmd_get_t!(other, row, col) {
                        return false;
                    }
                });
            } else {
                iterate_row_major!(self, row, col, unsafe {
                    if cmd_get!(self, row, col) != cmd_get!(other, row, col) {
                        return false;
                    }
                });
            }
        }
        return true;
    }
}

impl<T> PartialEq<DualIndexDataset<T>> for ColMajorDataset<T>
where
    T: MatrixElement,
{
    fn eq(&self, other: &DualIndexDataset<T>) -> bool {
        return self.eq(&other.rmd);
    }
}
