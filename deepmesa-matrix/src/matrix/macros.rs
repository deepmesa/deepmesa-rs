macro_rules! fn_transpose {
    ($self:ident) => {
        $self.is_transpose = !$self.is_transpose;
        let tmp = $self.rows;
        $self.rows = $self.cols;
        $self.cols = tmp;
    };
}

pub(in crate::matrix) use fn_transpose;

macro_rules! impl_simd_fn {
    ($self:ident) => {
        #[inline(always)]
        fn is_simd_enabled(&$self) -> bool {
            return $self.simd_enabled;
        }

        fn use_simd(&$self) -> bool {
            if !$self.is_simd_enabled() {
                return false;
            }

            #[cfg(target_arch = "aarch64")]
            {
                use std::arch::is_aarch64_feature_detected;
                if is_aarch64_feature_detected!("neon") {
                    return true;
                }
            }

            return false;
        }
    };
}

pub(in crate::matrix) use impl_simd_fn;

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

pub(in crate::matrix) use shape_check;

macro_rules! iterate {
    ($self:ident, $idx:ident, $max:ident, $e:expr) => {
        for $idx in 0..$max {
            $e
        }
    };
}

pub(in crate::matrix) use iterate;

macro_rules! iterate_rows {
    ($self:ident, $row:ident, $e:expr) => {
        for $row in 0..$self.rows {
            $e;
        }
    };
}

pub(in crate::matrix) use iterate_rows;

macro_rules! iterate_cols {
    ($self:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            $e;
        }
    };
}

pub(in crate::matrix) use iterate_cols;

macro_rules! iterate_row_major {
    ($self:expr, $row:ident, $col:ident, $e:expr) => {
        for $row in 0..$self.rows {
            for $col in 0..$self.cols {
                $e
            }
        }
    };
}

pub(in crate::matrix) use iterate_row_major;

macro_rules! iterate_col_major {
    ($self:ident, $row:ident, $col:ident, $e:expr) => {
        for $col in 0..$self.cols {
            for $row in 0..$self.rows {
                $e
            }
        }
    };
}

pub(in crate::matrix) use iterate_col_major;

macro_rules! iterate_matmul {
    ($lhs:ident, $rhs:ident, $row:ident, $col:ident, $idx: ident, $e_inner:expr, $e_outer:expr) => {
        for $row in 0..$lhs.rows {
            for $col in 0..$rhs.cols {
                for $idx in 0..$lhs.cols {
                    $e_inner
                }
                $e_outer
            }
        }
    };
}

pub(in crate::matrix) use iterate_matmul;

macro_rules! bounds_check_row {
    ($row:ident, $self:ident) => {
        if $row >= $self.rows {
            panic!("row index {} should be less than rows {}", $row, $self.rows);
        }
    };
}

pub(in crate::matrix) use bounds_check_row;

macro_rules! bounds_check_col {
    ($col:ident, $self:ident) => {
        if $col >= $self.cols {
            panic!("Col index {} should be less than cols {}", $col, $self.cols);
        }
    };
}

pub(in crate::matrix) use bounds_check_col;

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

pub(in crate::matrix) use bounds_check_len;

macro_rules! impl_iter {
    ($iter:ident, $matrix:ident) => {
        pub struct $iter<'a, T>
        where
            T: MatrixElement,
        {
            m: &'a $matrix<T>,
            row: usize,
            col: usize,
            iter_type: IterType,
        }

        impl<'a, T> $iter<'a, T>
        where
            T: MatrixElement<Output = T>,
        {
            pub fn new(matrix: &$matrix<T>, iter_type: IterType) -> $iter<T> {
                $iter {
                    m: matrix,
                    row: 0,
                    col: 0,
                    iter_type,
                }
            }
        }

        impl<'a, T> Iterator for $iter<'a, T>
        where
            T: MatrixElement<Output = T>,
        {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                match self.iter_type {
                    IterType::IterRows => {
                        if self.row >= self.m.rows {
                            return None;
                        }
                    }
                    IterType::IterCols => {
                        if self.col >= self.m.cols {
                            return None;
                        }
                    }
                }
                let val = self.m.get(self.row, self.col);
                match self.iter_type {
                    IterType::IterRows => {
                        self.col += 1;
                        if self.col >= self.m.cols {
                            self.col = 0;
                            self.row += 1;
                        }
                    }
                    IterType::IterCols => {
                        self.row += 1;
                        if self.row >= self.m.rows {
                            self.row = 0;
                            self.col += 1;
                        }
                    }
                }

                return Some(val);
            }
        }
    };
}

pub(in crate::matrix) use impl_iter;
