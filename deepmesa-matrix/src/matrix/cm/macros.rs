macro_rules! matrix_cm {
    ([$t:ty, $r:literal,$c:literal, $simd: ident], $($($x:literal),*);*) => {
        {
            let mut m = MatrixColMajor::<$t>::new($r, $c, $simd);
            let mut row = 0;
            $(
                m.fill_row(row, &[$($x as $t,)*][..]);
                row += 1;
            )* m
        }
    }
}

pub(in crate::matrix::cm) use matrix_cm;

macro_rules! debug_assert_cm {
    ($d:expr) => {
        debug_assert!(!$d.is_transpose);
    };
}
pub(in crate::matrix::cm) use debug_assert_cm;

macro_rules! debug_assert_cm_t {
    ($d:expr) => {
        debug_assert!($d.is_transpose);
    };
}
pub(in crate::matrix::cm) use debug_assert_cm_t;

macro_rules! simd_add_assign {
    (cm_t, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, cm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
    };
    (cm, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
    };
    (cm, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm, cm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_add_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::cm) use simd_add_assign;

macro_rules! simd_sub_assign {
    (cm_t, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, cm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
    };
    (cm, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
    };
    (cm, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm, cm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_sub_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::cm) use simd_sub_assign;

macro_rules! cm_add_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index!($self, $row, $col))) += $val
    };
}
pub(in crate::matrix::cm) use cm_add_assign;

macro_rules! cm_add_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index_t!($self, $row, $col))) += $val
    };
}
pub(in crate::matrix::cm) use cm_add_assign_t;

macro_rules! cm_sub_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index!($self, $row, $col))) -= $val
    };
}
pub(in crate::matrix::cm) use cm_sub_assign;

macro_rules! cm_sub_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index_t!($self, $row, $col))) -= $val
    };
}
pub(in crate::matrix::cm) use cm_sub_assign_t;

macro_rules! cm_mul_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index!($self, $row, $col))) *= $val
    };
}
pub(in crate::matrix::cm) use cm_mul_assign;

macro_rules! cm_mul_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index_t!($self, $row, $col))) *= $val
    };
}
pub(in crate::matrix::cm) use cm_mul_assign_t;

macro_rules! cm_ptr {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cm_index!($self, $row, $col))
    };
}
pub(in crate::matrix::cm) use cm_ptr;

macro_rules! cm_ptr_t {
    ($self:expr, $row:expr, $col:expr) => {
        $self.cm_data.add(cm_index_t!($self, $row, $col))
    };
}
pub(in crate::matrix::cm) use cm_ptr_t;

macro_rules! cm_index {
    ($self:expr, $row:expr, $col:expr) => {
        $col * $self.col_stride + $row
    };
}
pub(in crate::matrix::cm) use cm_index;

macro_rules! cm_index_t {
    ($self:expr, $row:expr, $col:expr) => {
        $row * $self.col_stride + $col
    };
}
pub(in crate::matrix::cm) use cm_index_t;

macro_rules! cm_assign {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix::cm) use cm_assign;

macro_rules! cm_assign_t {
    ($self:expr, $row:expr, $col:expr, $val:expr) => {
        *($self.cm_data.add(cm_index_t!($self, $row, $col))) = $val
    };
}
pub(in crate::matrix::cm) use cm_assign_t;

macro_rules! cm_get {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cm_index!($self, $row, $col)))
    };
}
pub(in crate::matrix::cm) use cm_get;

macro_rules! cm_get_t {
    ($self:expr, $row:expr, $col:expr) => {
        *($self.cm_data.add(cm_index_t!($self, $row, $col)))
    };
}
pub(in crate::matrix::cm) use cm_get_t;

macro_rules! simd_add_into {
    (cm, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($dst);
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($dst);
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_add_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm_t, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm_t, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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

pub(in crate::matrix::cm) use simd_add_into;

macro_rules! simd_sub_into {
    (cm, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($dst);
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($dst);
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_sub_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm_t, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm_t, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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

pub(in crate::matrix::cm) use simd_sub_into;

macro_rules! simd_mul_assign {
    (cm_t, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, cm_t, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
    };
    (cm, cm_t, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
    };
    (cm, cm, $self:expr, $rhs:ident) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            return;
        }
    };
    (cm, cm, $self:expr, $rhs:ident, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        if $self.use_simd() && $self.cm_len == $rhs.cm_len {
            unsafe {
                SimdKernel::simd_mul_assign($self.cm_data, $rhs.cm_data as *const T, $self.cm_len);
            }
            $sync;
            return;
        }
    };
}

pub(in crate::matrix::cm) use simd_mul_assign;

macro_rules! simd_mul_into {
    (cm, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($dst);
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm, val, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, val, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($dst);
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            return;
        }
    };
    (cm_t, val, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($dst);
        if $self.use_simd() && $self.cm_len == $dst.cm_len {
            unsafe {
                SimdKernel::simd_mul_into($self.cm_data, $rhs, $dst.cm_data, $self.cm_len);
            }
            $sync;
            return;
        }
    };
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);

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
    (cm_t, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm_t, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm_t, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm_t!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm_t, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm_t, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm_t!($rhs);
        debug_assert_cm!($dst);
    };
    (cm, cm, cm_t, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm_t!($dst);
    };
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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
    (cm, cm, cm, $self:ident, $rhs:ident, $dst:expr, $sync:expr) => {
        debug_assert_cm!($self);
        debug_assert_cm!($rhs);
        debug_assert_cm!($dst);
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

pub(in crate::matrix::cm) use simd_mul_into;
