#[allow(unused_macros)]
macro_rules! matrix_rm {
    ([$t:ty, $r:literal,$c:literal], $($($x:literal),*);*) => {
        {
            let mut m = MatrixRowMajor::<$t>::new($r, $c);
            let mut _row = 0;
            $(
                m.fill_row(_row, &[$($x as $t,)*][..]);
                _row += 1;
            )* m
        }
    }
}

#[allow(unused_imports)]
pub(in crate::matrix::rm) use matrix_rm;

macro_rules! rm_index {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.row_stride + $col
    };
}
pub(in crate::matrix::rm) use rm_index;

macro_rules! rm_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.row_stride + $row
    };
}
pub(in crate::matrix::rm) use rm_index_t;

macro_rules! rm_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rm_index!($self, $row, $col)))
    };
}
pub(in crate::matrix::rm) use rm_get;

macro_rules! rm_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rm_index_t!($self, $row, $col)))
    };
}
pub(in crate::matrix::rm) use rm_get_t;

macro_rules! rm_sub_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index!($self, $row, $col))) -= $val
    };
}

pub(in crate::matrix) use rm_sub_assign;

macro_rules! rm_sub_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index_t!($self, $row, $col))) -= $val
    };
}

pub(in crate::matrix::rm) use rm_sub_assign_t;

macro_rules! rm_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index!($self, $row, $col))) *= $val
    };
}

pub(in crate::matrix) use rm_mul_assign;

macro_rules! rm_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index_t!($self, $row, $col))) *= $val
    };
}

pub(in crate::matrix) use rm_mul_assign_t;

macro_rules! rm_add_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index!($self, $row, $col))) += $val
    };
}

pub(in crate::matrix::rm) use rm_add_assign;

macro_rules! rm_add_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index_t!($self, $row, $col))) += $val
    };
}

pub(in crate::matrix::rm) use rm_add_assign_t;

macro_rules! rm_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use rm_assign;

macro_rules! rm_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rm_index_t!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use rm_assign_t;
