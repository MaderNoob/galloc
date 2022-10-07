# galloc

The *g*ood *alloc*ator.

This is a linked list allocator, inspired by the dlmalloc algorithm, to be used in `no_std` environments, for example in operating system kernels.
The overhead for each allocation is a single `usize`.
The implementation prioritizes runtime efficiency over memory efficiency, but also provides very good memory utilization.
The allocator is heavily tested with tests cases covering almost all code paths, and fuzzing is used to cover the rest.
The performance of the allocator is really good, and it provides much better runtime perforamce and memory utilization than all existing solutions.

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

## Performance

Allocation will most of the time be `O(1)`, mostly for relatively small allocations with relatively small alignment.
Deallocation is always `O(1)`.
Reallocaiton has a specialized algorithm which tries to prevent copying of memory as much as possible, by reallocating in place.

The overall performance of the allocator is really good, and it performs better than all other alternative allocators which we could find `crates.io`.
