use rand::seq::SliceRandom;

use super::*;

#[test]
fn dealloc_prev_used_next_used() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(perfect_fit, 1).unwrap())
    };
    unsafe { guard.allocator.dealloc(allocated) };

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}

#[test]
fn dealloc_prev_used_next_free() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    // a size that will leave end padding that is large enough to fit a free chunk.
    let size_with_large_enough_end_padding = perfect_fit - MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(size_with_large_enough_end_padding, 1).unwrap())
    };

    unsafe {
        guard.allocator.dealloc(allocated);
    }

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}

#[test]
fn dealloc_prev_free_next_used() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    let allocated1 = unsafe {
        guard.allocator.alloc(
            Layout::from_size_align(MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE, 1).unwrap(),
        )
    };

    let allocated2 = unsafe {
        guard.allocator.alloc(
            Layout::from_size_align(MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE, 1).unwrap(),
        )
    };

    // allocate the rest of the heap
    let third_chunk_size = MEM_SIZE - 2 * MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;
    let allocated3 = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(third_chunk_size, 1).unwrap())
    };

    unsafe {
        guard.allocator.dealloc(allocated1);
    }

    assert_only_1_free_chunk_which_is_at_heap_start(
        &mut guard,
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
    );

    unsafe {
        guard.allocator.dealloc(allocated2);
    }

    // treat it as if the 2 first chunks are now the entire heap
    assert_only_1_free_chunk_which_is_at_heap_start(
        &mut guard,
        2 * MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
    );

    // make sure the prev in use and size of the third chunk is correct
    let third_chunk_addr = (allocated3 as usize) - HEADER_SIZE;
    let third_chunk = unsafe {
        match Chunk::from_addr(third_chunk_addr) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => {
                panic!("the third chunk is marked free even though it wasn't deallocated")
            }
        }
    };

    assert_eq!(
        third_chunk.prev_size_if_free(),
        Some(2 * MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE)
    );

    assert_eq!(third_chunk.0.size(), third_chunk_size);

    unsafe {
        guard.allocator.dealloc(allocated3);
    }

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}

#[test]
fn dealloc_prev_free_next_free() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    let allocated1 = unsafe {
        guard.allocator.alloc(
            Layout::from_size_align(MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE, 1).unwrap(),
        )
    };

    let allocated2 = unsafe {
        guard.allocator.alloc(
            Layout::from_size_align(MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE, 1).unwrap(),
        )
    };

    // allocate the rest of the heap
    let third_chunk_size = MEM_SIZE - 2 * MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;
    let allocated3 = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(third_chunk_size, 1).unwrap())
    };

    unsafe {
        guard.allocator.dealloc(allocated1);
    }

    assert_only_1_free_chunk_which_is_at_heap_start(
        &mut guard,
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
    );

    unsafe {
        guard.allocator.dealloc(allocated3);
    }

    unsafe {
        guard.allocator.dealloc(allocated2);
    }

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}

#[test]
fn dealloc_lots_of_allocations() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    let mut allocations = Vec::new();

    let smallest_chunk_size = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;

    // allocate the entire heap
    loop {
        let allocated = unsafe {
            guard
                .allocator
                .alloc(Layout::from_size_align(smallest_chunk_size, 1).unwrap())
        };
        if allocated.is_null() {
            break;
        }

        allocations.push(allocated);
    }

    for allocation in allocations {
        unsafe {
            guard.allocator.dealloc(allocation);
        }
    }

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}

#[test]
fn dealloc_lots_of_allocations_dealloc_in_random_order() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

    let mut allocations = Vec::new();

    let smallest_chunk_size = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;

    // allocate the entire heap
    loop {
        let allocated = unsafe {
            guard
                .allocator
                .alloc(Layout::from_size_align(smallest_chunk_size, 1).unwrap())
        };
        if allocated.is_null() {
            break;
        }

        allocations.push(allocated);
    }

    let mut rng = rand::thread_rng();

    allocations.shuffle(&mut rng);

    for allocation in allocations {
        unsafe {
            guard.allocator.dealloc(allocation);
        }
    }

    assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
}
