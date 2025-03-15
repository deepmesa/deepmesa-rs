macro_rules! matrix_rm {
    ([$t:ty, $r:literal,$c:literal, $simd:ident], $($($x:literal),*);*) => {
        {
            let mut m = MatrixRowMajor::<$t>::new($r, $c, $simd);
            let mut row = 0;
            $(
                m.fill_row(row, &[$($x as $t,)*][..]);
                row += 1;
            )* m
        }
    }
}

pub(in crate::matrix) use matrix_rm;

macro_rules! debug_assert_rm {
    ($d:expr) => {
        debug_assert!(!$d.is_transpose);
    };
}
pub(in crate::matrix::rm) use debug_assert_rm;

macro_rules! debug_assert_rm_t {
    ($d:expr) => {
        debug_assert!($d.is_transpose);
    };
}
pub(in crate::matrix::rm) use debug_assert_rm_t;

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

macro_rules! simd_add_assign {
    (rm, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm, rm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
    };
    (rm_t, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
    };
    (rm_t, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, rm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::rm) use simd_add_assign;

macro_rules! simd_add_into {
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($dst);
    };
    (rm_t, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($dst);
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_add_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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

    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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

    (rm_t, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm_t, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm_t, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
}

pub(in crate::matrix::rm) use simd_add_into;

macro_rules! simd_mul_assign {
    (rm, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm, rm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
    };
    (rm_t, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
    };
    (rm_t, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, rm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::rm) use simd_mul_assign;

macro_rules! simd_mul_into {
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($dst);
    };
    (rm_t, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($dst);
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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

    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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

    (rm_t, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm_t, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm_t, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
}

pub(in crate::matrix::rm) use simd_mul_into;

macro_rules! simd_sub_assign {
    (rm, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm, rm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
    };
    (rm_t, rm, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
    };
    (rm_t, rm_t, $self:expr, $rhs:ident) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, rm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        if $self.use_simd() && $self.rm_len == $rhs.rm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.rm_data, $rhs.rm_data as *const T, $self.rm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::rm) use simd_sub_assign;

macro_rules! simd_sub_into {
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm, val, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($dst);
    };
    (rm_t, val, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($dst);
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            return;
        }
    };
    (rm_t, val, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($dst);
        if $self.use_simd() && $self.rm_len == $dst.rm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.rm_data, $rhs, $dst.rm_data, $self.rm_len);
            }
            $sync;
            return;
        }
    };
    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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
    (rm_t, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);

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

    (rm_t, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm_t, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm_t, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm_t!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm_t, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm_t, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm_t!($rhs);
        debug_assert_rm!($dst);
    };
    (rm, rm, rm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm_t!($dst);
    };
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
    (rm, rm, rm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_rm!($self);
        debug_assert_rm!($rhs);
        debug_assert_rm!($dst);

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
}

pub(in crate::matrix::rm) use simd_sub_into;
