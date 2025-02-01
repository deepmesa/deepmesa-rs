macro_rules! dispatch_mut {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &mut $self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

macro_rules! dispatch {
    ($self:ident, $ds: ident, $fn:expr) => {
        match &$self.data {
            MatrixData::ColMajor($ds) => $fn,
            MatrixData::RowMajor($ds) => $fn,
            MatrixData::DualIndex($ds) => $fn,
        }
    };
}

pub(in crate::matrix) use dispatch;
pub(in crate::matrix) use dispatch_mut;
