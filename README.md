# DeepMesa Collections

[![0 dependencies!](https://0dependencies.dev/0dependencies.svg)](https://0dependencies.dev)
![License](https://img.shields.io/badge/License-Apache--2.0-blue)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A Rust crate providing fundamental data structures with zero external dependencies.

## Overview

DeepMesa Collections provides:
- **Zero Dependencies**: Pure Rust implementations
- **Memory Safety**: Safe implementations with comprehensive testing
- **Rich APIs**: Iterator support and flexible configurations

## Data Structures

### Maps
- **[LinkedHashMap](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.LinkedHashMap.html)** - Map with predictable iteration order. Supports insertion order and access order.

### Lists
- **[LinkedList](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.LinkedList.html)** - Doubly-linked list with handle-based access for stable references.

### Bit Manipulation
- **[BitVector](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.BitVector.html)** - Growable bit array with bitwise operations and multiple bit order support (LSB0/MSB0).

## Features

- **Iterator Support**: Full iterator ecosystem
- **Handle-Based Access**: Stable references that survive collection mutations
- **Error Handling**: Comprehensive error types for allocation failures

## Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
deepmesa-collections = "^0.*.*"
```

### Quick Start Examples

```rust
use deepmesa_collections::{LinkedHashMap, LinkedList, BitVector};
use deepmesa_collections::lhmap::Order;

// LinkedHashMap with access order
let mut map = LinkedHashMap::new(16, Order::AccessOrder, None);
map.put("key1", "value1");
map.put("key2", "value2");

// LinkedList with handle-based access
let mut list = LinkedList::with_capacity(100);
let handle = list.push_back(42);
list.insert_after(&handle, 84);

// BitVector with macro support
let mut bits = bitvector![1, 0, 1, 1, 0, 1];
bits.push(true);
let (value, count) = bits.read_u8(0);
```

## Performance Characteristics

- **HashMap Operations**: get, put, remove - O(1) average case
- **List Operations**: push, pop, insert, remove - O(1) with handles
- **Bit Operations**: Individual bit access - O(1)

## Building and Testing

The project uses `just` for build automation:

```bash
# Build all components
just build

# Run comprehensive test suite
just test

# Generate documentation
just doc

# Clean build artifacts
just clean
```

Run specific test categories:
```bash
# Run all tests with backtrace
RUST_BACKTRACE=1 cargo test

# Run specific module tests
cargo test bitvec::tests --nocapture

# Run documentation tests
cargo test --doc
```

## Contributing

Contributions in any form (suggestions, bug reports, pull requests, and feedback) are welcome. If you've found a bug, you can submit an issue or email me at rsingh@arrsingh.com.

## License

This project is dual-licensed under the MIT LICENSE or the Apache-2 LICENSE:

- [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
- [MIT License](http://opensource.org/licenses/MIT)

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

Contact: rsingh@arrsingh.com
Website: https://www.arrsingh.com/deepmesa-collections
