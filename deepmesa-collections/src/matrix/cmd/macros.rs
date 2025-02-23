macro_rules! debug_assert_cmd {
    ($d:expr) => {
        debug_assert!(!$d.is_transpose);
        debug_assert!($d.is_col_major());
    };
}
pub(in crate::matrix) use debug_assert_cmd;

macro_rules! debug_assert_cmd_t {
    ($d:expr) => {
        debug_assert!($d.is_transpose);
        debug_assert!($d.is_col_major());
    };
}
pub(in crate::matrix) use debug_assert_cmd_t;

#[cfg(test)]
macro_rules! col_major_dataset {
    ([$t:ty, $r:literal,$c:literal, $simd: ident], $($($x:literal),*);*) => {
        {
            let mut cmd = ColMajorDataset::<$t>::new($r, $c, $simd, $simd);
            let mut row = 0;
            $(
                cmd.fill_row(row, &[$($x as $t,)*][..]);
                row += 1;
            )* cmd
        }
    }
}

#[cfg(test)]
pub(in crate::matrix) use col_major_dataset;

macro_rules! simd_add_assign {
    (cmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
    };
    (cmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
    };
    (cmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
    };
    (cmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
    };
}

pub(in crate::matrix) use simd_add_assign;

macro_rules! simd_sub_assign {
    (cmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
    };
    (cmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
    };
    (cmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
    };
    (cmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
    };
}

pub(in crate::matrix) use simd_sub_assign;

macro_rules! cmd_add_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col))) += $val
    };
}
pub(in crate::matrix) use cmd_add_assign;

macro_rules! cmd_add_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) += $val
    };
}
pub(in crate::matrix) use cmd_add_assign_t;

macro_rules! cmd_sub_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col))) -= $val
    };
}
pub(in crate::matrix) use cmd_sub_assign;

macro_rules! cmd_sub_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) -= $val
    };
}
pub(in crate::matrix) use cmd_sub_assign_t;

macro_rules! cmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col))) *= $val
    };
}
pub(in crate::matrix) use cmd_mul_assign;

macro_rules! cmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) *= $val
    };
}
pub(in crate::matrix) use cmd_mul_assign_t;

macro_rules! cmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index!($self, $row, $col))
    };
}
pub(in crate::matrix) use cmd_ptr;

macro_rules! cmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cmd_index_t!($self, $row, $col))
    };
}
pub(in crate::matrix) use cmd_ptr_t;

macro_rules! cmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.col_stride + $row
    };
}
pub(in crate::matrix) use cmd_index;

macro_rules! cmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.col_stride + $col
    };
}
pub(in crate::matrix) use cmd_index_t;

macro_rules! cmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use cmd_assign;

macro_rules! cmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use cmd_assign_t;

// macro_rules! cmd_mul_assign {
//     ($self:expr, $row:expr, $col:expr, $val:expr) => {
//         *($self.cm_data.add(cmd_index!($self, $row, $col))) *= $val
//     };
// }

// macro_rules! cmd_mul_assign_t {
//     ($self:expr, $row:expr, $col:expr, $val:expr) => {
//         *($self.cm_data.add(cmd_index_t!($self, $row, $col))) *= $val
//     };
// }

macro_rules! cmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cmd_index!($self, $row, $col)))
    };
}
pub(in crate::matrix) use cmd_get;

macro_rules! cmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cmd_index_t!($self, $row, $col)))
    };
}
pub(in crate::matrix) use cmd_get_t;

macro_rules! simd_add_into {
    (cmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($dst);
    };
    (cmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($dst);
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($dst);
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix) use simd_add_into;

macro_rules! simd_sub_into {
    (cmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($dst);
    };
    (cmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($dst);
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($dst);
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix) use simd_sub_into;

macro_rules! simd_mul_assign {
    (cmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
    };
    (cmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
    };
    (cmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
    };
    (cmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cmd, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.rm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
    };
}

pub(in crate::matrix) use simd_mul_assign;

macro_rules! simd_mul_into {
    (cmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($dst);
    };
    (cmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($dst);
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.rm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($dst);
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (cmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.rm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);

        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
    (cmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (cmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            return;
        }
    };
    (cmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.cm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.cm_len,
                );
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix) use simd_mul_into;
