#[cfg(test)]
macro_rules! dual_index_dataset {
    ([$t:ty, $r:literal,$c:literal, $simd:ident], $($($x:literal),*);*) => {
        {
            let mut did = DualIndexDataset::<$t>::new($r, $c, $simd, $simd);
            let mut row = 0;
            $(
                did.fill_row(row, &[$($x as $t,)*][..]);
                row += 1;
            )* did
        }
    }
}

#[cfg(test)]
pub(in crate::matrix) use dual_index_dataset;

macro_rules! simd_add_assign {
    (rmd_t, rmd_t, $self:expr, $rhs:expr, $sync:expr) => {
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
    (rmd, rmd, $self:expr, $rhs:expr, $sync:expr) => {
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
    (cmd, rmd_t, $self:expr, $rhs:expr, $sync:expr) => {
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
    (cmd_t, rmd, $self:expr, $rhs:expr, $sync:expr) => {
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
    (cmd_t, cmd_t, $self:expr, $rhs:expr, $sync:expr) => {
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
    (rmd_t, cmd, $self:expr, $rhs:expr, $sync:expr) => {
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
    (rmd, cmd_t, $self:expr, $rhs:expr, $sync:expr) => {
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
    (rmd_t, cmd, $self:expr, $rhs:expr, $sync:expr) => {
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
}

pub(in crate::matrix::did) use simd_add_assign;
