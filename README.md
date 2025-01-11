[![0 dependencies!](https://0dependencies.dev/0dependencies.svg)](https://0dependencies.dev)

# High Performance Algorithms & Data Structures for Rust

![License](https://img.shields.io/badge/License-Apache--2.0-blue)

This crate provides fast Data Structures and Algorithms in Rust. Every data structure is hand crafted for performance, well tested and has an extensive API.

### Maps:
* [LinkedHashMap](https://www.deepmesa.com/linkedhashmap): A fast and flexible map that combines a HashMap and a LinkedList for *O(1)* inserts, lookups and deletes along with a predictable iteration order.

### Lists:
* [LinkedList](https://www.deepmesa.com/linkedlist): A fast and flexible doubly linked list that allows for *O(1)* inserts, deletes and updates in the middle or at either end of the list. 2x faster than the std::collections::LinkedList

### Collections:
* [BitVector](https://www.deepmesa.com/bitvector): A fast contiguous growable array of bits allocated on the heap that allows storing and manipulating an arbitrary number of bits.

## Usage

Add this to your Cargo.toml:

```toml
[dependencies]
deepmesa = "0.*.*"
```

# Contributing

Contributions in any form (suggestions, bug reports, pull requests, and feedback)are welcome. If you've found a bug, you can submit and issue or email me at deepmesa@arrsingh.com.

## License

Licensed under the [Apache License, Version 2.0](LICENSE)

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be licensed as above, without any additional terms or conditions.

https://www.deepmesa.com
