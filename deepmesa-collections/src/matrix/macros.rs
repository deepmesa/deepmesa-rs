macro_rules! iterate {
    ($self:ident, $idx:ident, $max:ident, $e:expr) => {
        for $idx in 0..$max {
            $e
        }
    };
}

macro_rules! iterate_rows {
    ($self:ident, $row:ident, $e:expr) => {
        for $row in 0..$self.rows {
            $e;
        }
    };
}

macro_rules! iterate_cols {
    ($self:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            $e;
        }
    };
}

macro_rules! iterate_row_major {
    ($self:ident, $row:ident, $col:ident, $e:expr) => {
        for $row in 0..$self.rows {
            for $col in 0..$self.cols {
                $e
            }
        }
    };
}

macro_rules! iterate_column_major {
    ($self:ident, $row:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            for $row in 0..$self.rows {
                $e
            }
        }
    };
}

macro_rules! bounds_check_row {
    ($row:ident, $self:ident) => {
        if $row >= $self.rows {
            panic!("row index {} should be less than rows {}", $row, $self.rows);
        }
    };
}

macro_rules! bounds_check_col {
    ($col:ident, $self:ident) => {
        if $col >= $self.cols {
            panic!("Col index {} should be less than cols {}", $col, $self.cols);
        }
    };
}

macro_rules! bounds_check_len {
    ($len:expr, $self:ident) => {
        if $len != $self.len {
            panic!(
                "Data Length {} should be the same as Matrix Data Length {}",
                $len, $self.len
            );
        }
    };
}


#[allow(unused_macros)]
macro_rules! rmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iptr {
    ($self:expr, $index:expr) => {
        $self.rm_data.add($index)
    };
}
#[allow(unused_macros)]
macro_rules! cmd_iptr {
    ($self:expr, $index:expr) => {
        $self.cm_data.add($index)
    };
}

#[allow(unused_macros)]
macro_rules! rmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.row_stride + $col
    };
}

#[allow(unused_macros)]
macro_rules! cmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.col_stride + $row
    };
}

#[allow(unused_macros)]
macro_rules! rmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.row_stride + $row
    };
}

#[allow(unused_macros)]
macro_rules! cmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        //Col Major Dataset with Row Major Indexing
        $row * $self.col_stride + $col
    };
}

#[allow(unused_macros)]
macro_rules! rmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.rm_data.add(rmd_index!($self, $row, $col)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index!($self, $row, $col)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.rm_data.add($index) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.rm_data.add($index)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.cm_data.add($index)) = $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.rm_data.add(rmd_index!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.rm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_mul_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *($self.rm_data.add($index)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_iassign {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *$self.cm_data.add(cmd_index_t!($self, $row, $col)) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! cmd_mul_iassign_t {
    ($self:expr, $index:expr, $val:expr) => {
        *$self.cm_data.add($index) *= $val
    };
}

#[allow(unused_macros)]
macro_rules! rmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col)))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iget {
    ($self:expr, $index:expr) => {
        *($self.rm_data.add($index))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *$self.rm_data.add(rmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! rmd_iget_t {
    ($self:expr, $index:expr) => {
        *$self.rm_data.add($index)
    };
}

#[allow(unused_macros)]
macro_rules! cmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col)))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iget {
    ($self:expr, $index:expr) => {
        *($self.cm_data.add($index))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *$self.cm_data.add(cmd_index_t!($self, $row, $col))
    };
}

#[allow(unused_macros)]
macro_rules! cmd_iget_t {
    ($self:expr, $index:expr) => {
        *$self.cm_data.add($index)
    };
}
