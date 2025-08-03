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
pub use crate::cdeque::iter::{Drain, IntoIter, Iter, IterMut};
pub(crate) mod cdeque;
pub(in crate::cdeque) mod iter;
pub(in crate::cdeque) mod macros;
pub(in crate::cdeque) mod traits;

/// A convenience macro for creating a `CircularDeque` from a list of elements.
///
/// # Examples
///
/// Create an empty CircularDeque
///
/// ```
/// # use deepmesa_collections::CircularDeque;
/// # use deepmesa_collections::cdeque::cdq;
/// let mut empty_cdq = cdq!();
///
/// assert_eq!(empty_cdq.len(), 0);
/// empty_cdq.push_back(1);
/// empty_cdq.push_back(2);
/// empty_cdq.push_back(3);
/// assert_eq!(empty_cdq.len(), 3);
/// assert_eq!(empty_cdq.get(0), Some(&1));
/// assert_eq!(empty_cdq.get(1), Some(&2));
/// assert_eq!(empty_cdq.get(2), Some(&3));
/// ```
/// Create a Circular Deque initialized with 3 elements
///
/// ```
/// # use deepmesa_collections::CircularDeque;
/// # use deepmesa_collections::cdeque::cdq;
/// let mut cdq = cdq!(1, 2, 3);
///
/// assert_eq!(cdq.len(), 3);
/// assert_eq!(cdq.get(0), Some(&1));
/// assert_eq!(cdq.get(1), Some(&2));
/// assert_eq!(cdq.get(2), Some(&3));
/// ```
#[macro_export]
macro_rules! cdq {
    () => {
        CircularDeque::new()
    };
    ($($x:literal),+) => {
        CircularDeque::from_slice(&[$($x,)*][..])
    };
}

pub use cdq;
