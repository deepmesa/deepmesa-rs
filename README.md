# DeepMesa Collections

[![0 dependencies!](https://0dependencies.dev/0dependencies.svg)](https://0dependencies.dev)
![License](https://img.shields.io/badge/License-Apache--2.0-blue)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A high-performance Rust crate providing hand-crafted data structures and algorithms optimized for speed and memory efficiency. Each data structure is designed with zero external dependencies and extensive benchmarking to deliver superior performance over standard library alternatives.

## Overview

DeepMesa Collections implements fundamental data structures from scratch, focusing on:
- **Zero Dependencies**: Pure Rust implementations with no external crate dependencies
- **Performance**: Hand-optimized algorithms that outperform standard library equivalents
- **Memory Efficiency**: Custom memory management with pre-allocation and freelists
- **Safety**: Memory-safe implementations with extensive testing
- **Rich APIs**: Comprehensive feature sets with iterator support and flexible configurations

## Data Structures

### Maps
- **[LinkedHashMap](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.LinkedHashMap.html)** - A high-performance map combining HashMap and LinkedList for O(1) operations with predictable iteration order. Supports both insertion order and access order with customizable eviction policies.

### Lists
- **[LinkedList](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.LinkedList.html)** - A doubly-linked list with O(1) insertions/deletions anywhere in the list. Features pre-allocated node pools and handle-based access. Approximately 2x faster than `std::collections::LinkedList`.

### Queues
- **[CircularDeque](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.CircularDeque.html)** - A double-ended queue with circular buffer implementation using contiguous memory allocation for optimal cache performance and O(1) operations at both ends.

### Bit Manipulation
- **[BitVector](https://docs.rs/deepmesa-collections/latest/deepmesa_collections/struct.BitVector.html)** - A growable bit array with comprehensive bitwise operations, multiple bit order support (LSB0/MSB0), and efficient bulk operations on u8, u16, u32, u64, and u128 chunks.

## Technical Features

### Memory Management
- **Pre-allocation**: Structures support initial capacity specification to minimize allocations
- **Free Lists**: Reusable node pools eliminate allocation overhead during operations
- **Custom Allocators**: Direct memory management using system allocators for optimal performance
- **Zero-Copy Operations**: Efficient data movement and manipulation without unnecessary copying

### Performance Optimizations
- **Pointer Arithmetic**: Direct pointer manipulation for cache-friendly memory access patterns
- **Bulk Operations**: Optimized batch processing for multiple elements
- **Macro-Based Code Generation**: Compile-time optimizations for repetitive operations
- **Minimal Indirection**: Reduced pointer chasing through careful data structure design

### API Design
- **Iterator Support**: Full iterator ecosystem with mutable, immutable, and specialized iterators
- **Handle-Based Access**: Stable references to elements that survive collection mutations
- **Flexible Ordering**: Support for insertion order, access order, and custom ordering schemes
- **Error Handling**: Comprehensive error types for allocation failures and capacity limits

### Bit Operations
The BitVector provides extensive bitwise functionality:
- **Bit Manipulation**: Set, clear, flip individual bits with bounds checking
- **Bulk Reading/Writing**: Read/write u8-u128 values at arbitrary bit positions
- **Bitwise Logic**: AND, OR, XOR, NOT operations with assignment variants
- **Bit Counting**: Count ones, zeros, and find first/last set bits
- **Multiple Bit Orders**: LSB0 and MSB0 bit ordering support

## Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
deepmesa-collections = "^0.*.*"
```

### Quick Start Examples

```rust
use deepmesa_collections::{LinkedHashMap, LinkedList, BitVector, CircularDeque};
use deepmesa_collections::lhmap::Order;

// LinkedHashMap with access order
let mut map = LinkedHashMap::new(16, Order::AccessOrder, None);
map.put("key1", "value1");
map.put("key2", "value2");

// High-performance LinkedList
let mut list = LinkedList::with_capacity(100);
let handle = list.push_back(42);
list.insert_after(&handle, 84);

// BitVector with macro support
let mut bits = bitvector![1, 0, 1, 1, 0, 1];
bits.push(true);
let (value, count) = bits.read_u8(0);

// CircularDeque for queue operations
let mut deque = CircularDeque::new();
deque.push_back(1);
deque.push_front(0);
```

## Performance Characteristics

All primary operations achieve O(1) time complexity:
- **HashMap Operations**: get, put, remove - O(1) average case
- **List Operations**: push, pop, insert, remove - O(1) with handles
- **Deque Operations**: push_front, push_back, pop_front, pop_back - O(1)
- **Bit Operations**: Individual bit access and bulk operations - O(1) or O(k) for k bits

Memory usage is optimized through:
- Pre-allocated capacity to reduce growth overhead
- Memory pooling for frequently allocated/deallocated objects
- Compact bit storage (8 bits per byte)
- Minimal metadata overhead per element

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
