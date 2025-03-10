use crate::queue::cdeque::macros::*;
use crate::queue::cdeque::CircularDeque;
use std::cmp::PartialEq;
use std::fmt::Debug;
use std::ops::Index;
use std::ops::IndexMut;

impl<T> Index<usize> for CircularDeque<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        bounds_check_panic!(self, index);
        let ptr = self.ptr_at(index);
        unsafe {
            return &(*ptr);
        }
    }
}

impl<T> IndexMut<usize> for CircularDeque<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        return self.get_mut(index).unwrap();
    }
}

impl<T> Eq for CircularDeque<T> where T: Eq + Debug {}
impl<T> PartialEq<CircularDeque<T>> for CircularDeque<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &CircularDeque<T>) -> bool {
        if self.len != other.len {
            return false;
        }

        let mut idx: usize = 0;
        loop {
            if idx >= self.len() {
                break;
            }

            unsafe {
                let val = &*self.ptr_at(idx);
                let val_rhs = &*other.ptr_at(idx);

                if val.ne(&val_rhs) {
                    return false;
                }
                idx += 1;
            }
        }

        return true;
    }
}

impl<T: Debug> Debug for CircularDeque<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{},{}]:", self.len(), self.capacity())?;
        let mut idx: usize = 0;
        if self.len == 0 {
            write!(f, "()")?;
            return Ok(());
        }

        loop {
            unsafe {
                let val = &*self.ptr_at(idx);
                if idx < self.len - 1 {
                    write!(f, "{:?},", val);
                } else if idx == self.len - 1 {
                    write!(f, "{:?}", val);
                    break;
                } else {
                    break;
                }

                idx += 1;
            }
        }
        return Ok(());
    }
}
