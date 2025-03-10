macro_rules! bounds_check {
    ($self:ident, $idx:ident, $e:expr) => {
        if $idx >= $self.len {
            $e;
        }
    };
}

pub(in crate::queue::cdeque) use bounds_check;

macro_rules! bounds_check_panic {
    ($self:ident, $idx:ident, $i:literal) => {
        bounds_check!(
            $self,
            $idx,
            panic!("index out of bounds: {}={}, len={}", $i, $idx, $self.len)
        );
    };
    ($self:ident, $idx:ident) => {
        bounds_check!(
            $self,
            $idx,
            panic!("index out of bounds: index={}, len={}", $idx, $self.len)
        );
    };
}

pub(in crate::queue::cdeque) use bounds_check_panic;

macro_rules! bounds_check_none {
    ($self:ident, $idx:ident) => {
        bounds_check!($self, $idx, return None);
    };
}

pub(in crate::queue::cdeque) use bounds_check_none;

macro_rules! len_zero_none {
    ($self:ident) => {
        if $self.len == 0 {
            return None;
        }
    };
}

pub(in crate::queue::cdeque) use len_zero_none;
