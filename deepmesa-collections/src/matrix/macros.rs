macro_rules! fn_transpose {
    ($self:ident) => {
        $self.is_transpose = !$self.is_transpose;
        let tmp = $self.rows;
        $self.rows = $self.cols;
        $self.cols = tmp;
    };
}

macro_rules! shape_check {
    ($self:ident, $rhs:ident) => {
        if $self.rows != $rhs.rows {
            panic!(
                "Matrix Shape Mismatch: self.rows {} must equal rhs.rows {}",
                $self.rows, $rhs.rows
            );
        }
        if $self.cols != $rhs.cols {
            panic!(
                "Matrix Shape Mismatch: self.cols {} must equal rhs.cols {}",
                $self.cols, $rhs.cols
            );
        }
    };
}

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
    ($self:expr, $row:ident, $col:ident, $e:expr) => {
        for $row in 0..$self.rows {
            for $col in 0..$self.cols {
                $e
            }
        }
    };
}

macro_rules! iterate_col_major {
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
