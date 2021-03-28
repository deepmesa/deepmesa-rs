/*
   Fast Linked List: A fast and flexible doubly linked list that
   allows for O(1) inserts and removes from the middle of the
   list. This list preallocates memory and doesn't have to allocate
   and deallocate memory on every insert / remove operation

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

//! A doubly linked list that owns the nodes and can pre-allocate
//! memory for performance. This linked list allows pushing and
//! popping elements at either end in constant time with the same API
//! as `std::collections::LinkedList`.
//!
//! In contrast to `std::collections::LinkedList`, however this list
//! also allows pushing and popping elements from the middle of the
//! list in constant time.
//!
pub mod fl;
pub mod iter;
pub mod list;
pub mod node;
