# EntryHandle Feature Implementation

## Overview

The EntryHandle feature provides a mechanism to obtain handles to entries in a `LinkedHashMap` and manipulate their position within the iteration order without affecting the key-value mapping. This enables users to move specific entries to the end of the iteration order in O(1) time.

## What was implemented

### 1. EntryHandle struct (`src/lhmap/entry.rs`)

A new public struct that wraps a `NodeHandle<Entry<K, V>>` from the underlying linked list:

```rust
#[derive(Debug, Clone)]
pub struct EntryHandle<K, V> {
    pub(crate) node_handle: NodeHandle<Entry<K, V>>,
}
```

**Features:**
- Implements `Debug`, `Clone`, `PartialEq`, `Eq`, `Default` traits
- Thread-safe with `Send` and `Sync` implementations
- Can be copied and passed around by value regardless of map lifetime
- Safe to use - invalid handles return `false` or `None` from operations

### 2. move_to_end method

The core functionality that moves an entry to the end of the LinkedHashMap's iteration order:

```rust
pub fn move_to_end(&self, map: &mut crate::LinkedHashMap<K, V>) -> bool
```

**Properties:**
- O(1) time complexity
- Works with both `InsertionOrder` and `AccessOrder` maps
- Returns `true` on success, `false` for invalid handles
- No effect if entry is already at the end
- Does not affect key-value mappings, only iteration order

### 3. entry_handle method (`src/lhmap/lhmap.rs`)

A new method on `LinkedHashMap` to obtain handles for existing entries:

```rust
pub fn entry_handle(&self, key: &K) -> Option<EntryHandle<K, V>>
```

**Properties:**
- O(1) lookup time
- Returns `Some(EntryHandle)` for existing keys
- Returns `None` for non-existent keys
- Does not modify the map or iteration order

### 4. Module exports

Updated `src/lhmap/mod.rs` to export `EntryHandle` publicly, making it available to users of the library.

## Key Insights Discovered

### LinkedHashMap Iteration Order Architecture

During implementation, several important insights about the LinkedHashMap's internal structure were discovered:

1. **Iteration Direction**: LinkedHashMap iteration goes from **tail to head** in the underlying linked list, not head to tail as might be expected.

2. **Element Insertion**: New elements are added to the **head** of the linked list via `push_head()`, making them the most recently inserted items.

3. **Order Semantics**: 
   - In a sequence like `put(1), put(2), put(3)`:
     - The linked list structure is: `[1] <- [2] <- [3]` (tail to head)
     - Iteration yields: `[1, 2, 3]` (tail to head)
     - Element 1 is at the tail (oldest), element 3 is at the head (newest)

4. **move_to_end Implementation**: To move an element to the "end" of iteration order, we must use `make_head()` on the underlying linked list, **not** `make_tail()`. This moves the element to the head of the list, making it the last element in iteration order.

### AccessOrder vs InsertionOrder Compatibility

The EntryHandle feature works seamlessly with both ordering modes:

- **InsertionOrder**: The handle-based `move_to_end()` operation does not interfere with insertion-based ordering
- **AccessOrder**: The handle-based operation is independent of access-based reordering (via `get()`, `get_mut()`, etc.)

This allows users to have fine-grained control over element positioning regardless of the map's ordering policy.

## Usage Examples

### Basic Usage

```rust
use deepmesa_collections::LinkedHashMap;
use deepmesa_collections::lhmap::Order;

let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
lhm.put(1, "a");
lhm.put(2, "b");
lhm.put(3, "c");

// Initial iteration order: [1, 2, 3]

if let Some(handle) = lhm.entry_handle(&1) {
    handle.move_to_end(&mut lhm);
}

// New iteration order: [2, 3, 1]
let keys: Vec<_> = lhm.keys().copied().collect();
assert_eq!(keys, vec![2, 3, 1]);
```

### Working with AccessOrder

```rust
let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
lhm.put(1, "a");
lhm.put(2, "b");
lhm.put(3, "c");

// Access an element (moves it to end in AccessOrder)
lhm.get(&1); // Order becomes: [2, 3, 1]

// Use handle to move another element to end
if let Some(handle) = lhm.entry_handle(&2) {
    handle.move_to_end(&mut lhm);
}
// Order becomes: [3, 1, 2]
```

### Error Handling

```rust
// Handle for non-existent key
assert_eq!(lhm.entry_handle(&99), None);

// Using invalid handle (after entry removal)
let handle = lhm.entry_handle(&1).unwrap();
lhm.remove(&1); // Invalidates the handle
assert_eq!(handle.move_to_end(&mut lhm), false);
```

## Test Coverage

The implementation includes comprehensive tests covering:

- **Basic functionality**: Handle creation and validation
- **Move operations**: Moving entries to end with different order types  
- **Edge cases**: Already at end, invalid handles, multiple operations
- **Integration**: Compatibility with existing AccessOrder behavior
- **Error handling**: Invalid handles return appropriate values

All 267 existing tests pass, plus 8 new EntryHandle-specific tests, ensuring no regression in existing functionality.

## Performance Characteristics

- **entry_handle()**: O(1) - Single HashMap lookup
- **move_to_end()**: O(1) - Direct linked list manipulation
- **Memory overhead**: Minimal - EntryHandle is a lightweight wrapper around existing NodeHandle
- **Thread safety**: Full Send/Sync support for concurrent usage

## Use Cases

This feature is particularly useful for:

1. **Custom LRU implementations**: Fine-grained control over element positioning
2. **Priority systems**: Moving high-priority items to specific positions
3. **Cache management**: Explicit control over eviction order
4. **Algorithm implementations**: Data structures requiring precise element ordering

The EntryHandle feature provides a powerful, efficient, and safe way to manipulate LinkedHashMap iteration order while maintaining all existing functionality and performance characteristics.