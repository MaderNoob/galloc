# galloc

The good allocator.

This is a linked list allocator, inspired by the dlmalloc algorithm.

The overhead for each allocation is a single `usize`.

The implementation prioritizes runtime efficiency over memory efficiency.

The allocation uses a first fit strategy to find a valid chunk. Deallocation is `O(1)`.

## Usage

Create a static allocator:

```rust
use galloc::SpinLockedAllocator;

#[global_allocator]
static ALLOCATOR: SpinLockedAllocator = SpinLockedAllocator::empty();
```

Before using this allocator, you need to initialize it:

```rust
pub fn init_heap() {
    unsafe {
        ALLOCATOR.init(heap_start, heap_size);
    }
}
```

## Features

- **`spin`** (default): Provide a `SpinLockedAllocator` type that implements the `GlobalAlloc` trait by using a spinlock.
