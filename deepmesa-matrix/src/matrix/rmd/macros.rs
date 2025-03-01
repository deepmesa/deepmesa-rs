macro_rules! debug_assert_rmd {
    ($d:expr) => {
        debug_assert!(!$d.is_transpose);
        debug_assert!($d.is_row_major());
    };
}
pub(in crate::matrix) use debug_assert_rmd;

macro_rules! debug_assert_rmd_t {
    ($d:expr) => {
        debug_assert!($d.is_transpose);
        debug_assert!($d.is_row_major());
    };
}
pub(in crate::matrix) use debug_assert_rmd_t;

//#[cfg(test)]
macro_rules! row_major_dataset {
    ([$t:ty, $r:literal,$c:literal, $simd:ident], $($($x:literal),*);*) => {
        {
            let mut rmd = RowMajorDataset::<$t>::new($r, $c, $simd, $simd);
            let mut row = 0;
            $(
                rmd.fill_row(row, &[$($x as $t,)*][..]);
                row += 1;
            )* rmd
        }
    }
}

//#[cfg(test)]
pub(in crate::matrix) use row_major_dataset;

macro_rules! simd_add_assign {
    (rmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
    };
    (rmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
    };
    (rmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
    };
}

pub(in crate::matrix) use simd_add_assign;

macro_rules! simd_sub_assign {
    (rmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
    };
    (rmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
    };
    (rmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
    };
}

pub(in crate::matrix) use simd_sub_assign;

macro_rules! rmd_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use rmd_assign;

// macro_rules! rmd_iassign {
//     ($self:expr, $index:expr, $val:expr) => {
//         *($self.rm_data.add($index)) = $val
//     };
// }

macro_rules! rmd_sub_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col))) -= $val
    };
}

pub(in crate::matrix) use rmd_sub_assign;

macro_rules! rmd_sub_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) -= $val
    };
}

pub(in crate::matrix) use rmd_sub_assign_t;

macro_rules! rmd_add_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col))) += $val
    };
}

pub(in crate::matrix) use rmd_add_assign;

macro_rules! rmd_add_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) += $val
    };
}

pub(in crate::matrix) use rmd_add_assign_t;

macro_rules! rmd_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col))) *= $val
    };
}

pub(in crate::matrix) use rmd_mul_assign;

macro_rules! rmd_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) *= $val
    };
}

pub(in crate::matrix) use rmd_mul_assign_t;

macro_rules! rmd_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index!($self, $row, $col))
    };
}
pub(in crate::matrix) use rmd_ptr;

macro_rules! rmd_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.rm_data.add(rmd_index_t!($self, $row, $col))
    };
}
pub(in crate::matrix) use rmd_ptr_t;

macro_rules! rmd_index {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.row_stride + $col
    };
}
pub(in crate::matrix) use rmd_index;

macro_rules! rmd_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.row_stride + $row
    };
}
pub(in crate::matrix) use rmd_index_t;

macro_rules! rmd_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix) use rmd_assign_t;

// macro_rules! rmd_mul_assign {
//     ($self:expr, $row:expr, $col:expr, $val:expr) => {
//         *($self.rm_data.add(rmd_index!($self, $row, $col))) *= $val
//     };
// }

// macro_rules! rmd_mul_assign_t {
//     ($self:expr, $row:expr, $col:expr, $val:expr) => {
//         *($self.rm_data.add(rmd_index_t!($self, $row, $col))) *= $val
//     };
// }

macro_rules! rmd_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rmd_index!($self, $row, $col)))
    };
}
pub(in crate::matrix) use rmd_get;

macro_rules! rmd_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.rm_data.add(rmd_index_t!($self, $row, $col)))
    };
}
pub(in crate::matrix) use rmd_get_t;

macro_rules! simd_add_into {
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($dst);
    };
    (rmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($dst);
    };
    (rmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($dst);
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };

    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };

    (rmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
}

pub(in crate::matrix::rmd) use simd_add_into;

macro_rules! simd_sub_into {
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($dst);
    };
    (rmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($dst);
    };
    (rmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($dst);
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };

    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };

    (rmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
}

pub(in crate::matrix::rmd) use simd_sub_into;

macro_rules! simd_mul_assign {
    (rmd, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, rmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
    };
    (rmd, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
    };
    (rmd, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd, cmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, rmd_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, cmd, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.cm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd_t, $self:expr, $rhs:ident) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
    };
}

pub(in crate::matrix) use simd_mul_assign;

macro_rules! simd_mul_into {
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd, val, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($dst);
    };
    (rmd, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($dst);
    };
    (rmd_t, val, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($dst);
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            return;
        }
    };
    (rmd_t, val, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.cm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rmd_t, val, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };

    (rmd_t, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };

    (rmd_t, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, rmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_rmd!($dst);

        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, rmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, rmd, cmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.rm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, rmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_rmd!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd_t, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd_t, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd_t, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd, cmd_t, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, rmd, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_rmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.rm_data,
                    $self.rm_len,
                );
            }
            $sync;
            return;
        }
    };
    (rmd, cmd, rmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd_t!($dst);
    };
    (rmd, cmd, rmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_rmd!($dst);
    };
    (rmd_t, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd_t, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd_t, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd_t!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.cm_len && $self.rm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_into(
                    $self.rm_data as *const T,
                    $rhs.cm_data as *const T,
                    $dst.cm_data,
                    $self.rm_len,
                );
            }
            return;
        }
    };
    (rmd, cmd_t, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd_t!($rhs);
        debug_assert_cmd!($dst);
    };
    (rmd, cmd, cmd_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd_t!($dst);
    };
    (rmd, cmd, cmd, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rmd!($self);
        debug_assert_cmd!($rhs);
        debug_assert_cmd!($dst);
    };
}

pub(in crate::matrix::rmd) use simd_mul_into;
