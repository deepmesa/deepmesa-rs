/*
   CircularDeque: A Double Ended Queue circular implementation backed
   by contiguous memory

   Copyright 2021 "Rahul Singh <rsingh@arrsingh.com>"

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/// Performs bounds checking and executes the provided expression if the index is out of bounds.
///
/// This macro checks if the provided index is greater than or equal to the length of the
/// collection and executes the given expression if the bounds check fails.
///
/// # Parameters
/// - `$self`: The collection instance
/// - `$idx`: The index to check
/// - `$e`: The expression to execute if bounds check fails
#[doc(hidden)]
macro_rules! bounds_check {
    ($self:ident, $idx:ident, $e:expr) => {
        if $idx >= $self.len {
            $e;
        }
    };
}

pub(in crate::queue::cdeque) use bounds_check;

/// Performs bounds checking and panics with a descriptive message if the index is out of bounds.
///
/// This macro uses the `bounds_check` macro to check bounds and panics with a formatted
/// error message if the index is invalid. It supports two variants: one with a custom
/// identifier string and one without.
///
/// # Parameters
/// - `$self`: The collection instance
/// - `$idx`: The index to check
/// - `$i`: Optional literal string to include in the panic message
#[doc(hidden)]
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

/// Performs bounds checking and returns `None` if the index is out of bounds.
///
/// This macro uses the `bounds_check` macro to check bounds and returns `None`
/// if the index is invalid. This is useful for methods that return `Option<T>`.
///
/// # Parameters
/// - `$self`: The collection instance
/// - `$idx`: The index to check
#[doc(hidden)]
macro_rules! bounds_check_none {
    ($self:ident, $idx:ident) => {
        bounds_check!($self, $idx, return None);
    };
}

pub(in crate::queue::cdeque) use bounds_check_none;

/// Returns `None` if the collection is empty.
///
/// This macro checks if the collection's length is zero and returns `None` if it is.
/// This is useful for methods that return `Option<T>` and need to handle empty collections.
///
/// # Parameters
/// - `$self`: The collection instance
#[doc(hidden)]
macro_rules! len_zero_none {
    ($self:ident) => {
        if $self.len == 0 {
            return None;
        }
    };
}

pub(in crate::queue::cdeque) use len_zero_none;
