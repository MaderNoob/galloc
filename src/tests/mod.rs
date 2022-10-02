use rand::{prelude::SliceRandom, Rng};
mod alloc_tests;
mod dealloc_tests;

use core::alloc::Layout;
use std::vec::Vec;

use super::*;

#[test]
fn random_alloc_dealloc_realloc() {
    const MEM_SIZE: usize = USIZE_SIZE * 113;
    const RANDOM_ACTIONS_AMOUNT: usize = 10000;
    const TRIALS_AMOUNT: usize = 100;

    for _ in 0..TRIALS_AMOUNT {
        let mut guard = AllocatorInitGuard::empty();
        guard.init(MEM_SIZE);

        let mut allocations = Vec::new();

        let mut size_left = MEM_SIZE;

        let mut rng = rand::thread_rng();

        for _ in 0..RANDOM_ACTIONS_AMOUNT {
            fn random_size(rng: &mut impl Rng, size_left: usize) -> usize {
                let max_chunk_size = size_left - HEADER_SIZE;
                let min_chunk_size = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;
                let unaligned_size = rng.gen_range(min_chunk_size..=max_chunk_size);
                let aligned_size = unsafe { align_up(unaligned_size, CHUNK_SIZE_ALIGNMENT) };
                aligned_size
            }

            let rng_chose_allocation_over_deallocation: bool = rng.gen_bool(0.75);
            // if there are no allocations, or the next action was chosen to be an
            // allocation and there is enough size left for at least another chunk, do an
            // allocation.
            let mut allocation_worked = false;
            if allocations.is_empty()
                || (rng_chose_allocation_over_deallocation
                    && size_left >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER)
            {
                let size = random_size(&mut rng, size_left);
                let alignment = 1 << rng.gen_range(0..=10);
                let ptr = unsafe {
                    guard
                        .allocator
                        .alloc(Layout::from_size_align(size, alignment).unwrap())
                };

                if !ptr.is_null() {
                    allocations.push((ptr, size, alignment));

                    // adjust the size left
                    size_left -= size + HEADER_SIZE;

                    allocation_worked = true;
                }
            }

            if !allocation_worked && !allocations.is_empty() {
                // decide randomly whether to realloc or dealloc
                if rng.gen::<bool>() && size_left >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
                    let random_index = rng.gen_range(0..allocations.len());
                    let (ptr, allocation_size, alignment) = &mut allocations[random_index];
                    let new_size = random_size(&mut rng, size_left + *allocation_size);
                    let new_ptr = unsafe {
                        guard.allocator.realloc(
                            *ptr,
                            Layout::from_size_align(*allocation_size, *alignment).unwrap(),
                            new_size,
                        )
                    };

                    if !new_ptr.is_null() {
                        // realloc succeeded
                        *allocation_size = new_size;
                        *ptr = new_ptr;
                    }
                } else {
                    // deallocate a random chunk.
                    let random_index = rng.gen_range(0..allocations.len());
                    let (ptr, allocation_size, _alignment) = allocations.swap_remove(random_index);
                    unsafe { guard.allocator.dealloc(ptr) }

                    size_left += allocation_size + HEADER_SIZE;
                }
            }
        }

        // once we are done, deallocate all allocations, in random order.
        allocations.shuffle(&mut rng);
        for (allocation, _size, _alignment) in allocations {
            unsafe { guard.allocator.dealloc(allocation) }
        }

        // make sure that the heap is only 1 big free chunk.
        assert_only_1_free_chunk(&mut guard, MEM_SIZE);
    }
}

fn assert_only_1_free_chunk(guard: &mut AllocatorInitGuard, mem_size: usize) {
    let addr = guard.addr();

    let free_chunk = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(_) => panic!("first chunk in heap is marked used after dealloc"),
            ChunkRef::Free(free) => free,
        }
    };

    // the first chunk's prev in use flag must be `true`.
    assert_eq!(free_chunk.header.prev_in_use(), true);

    assert_eq!(free_chunk.size(), mem_size - HEADER_SIZE);

    // it is the only free chunk, so it points back to the allocator
    assert_eq!(free_chunk.fd, guard.allocator.fake_chunk_ptr());

    // it is the only free chunk, so back should point to the allocator
    assert_eq!(
        free_chunk.ptr_to_fd_of_bk,
        guard.allocator.ptr_to_fd_of_fake_chunk(),
    );

    // make sure the allocator points to that free chunk
    assert_eq!(guard.allocator.first_free_chunk(), unsafe {
        NonNull::new_unchecked(free_chunk as *mut _)
    });
    assert_eq!(
        guard.allocator.fake_chunk.ptr_to_fd_of_bk,
        &mut free_chunk.fd as *mut _
    );
}

/// A guard that initializes the allocator with a region of memory on
/// creation, and frees that memory when dropped.
struct AllocatorInitGuard {
    addr: usize,
    layout: Layout,
    allocator: Allocator,
}
impl AllocatorInitGuard {
    /// Creates an empty allocator init guard.
    const fn empty() -> Self {
        Self {
            addr: 0,
            layout: Layout::new::<u8>(),
            allocator: Allocator::empty(),
        }
    }

    /// Initializes the heap allocator and returns a guard for it.
    fn init(&mut self, mem_size: usize) {
        // allocate enough size, make sure to align the allocation to the alignment of
        // the heap allocator.
        self.layout = Layout::from_size_align(mem_size, MIN_ALIGNMENT).unwrap();

        self.addr = unsafe { std::alloc::alloc(self.layout) as usize };

        unsafe { self.allocator.init(self.addr, mem_size) }
    }

    /// Initializes the allocator and makes sure that calling alloc with an
    /// alignment greater than `MIN_ALIGNMENT` won't be aligned.
    ///
    /// Returns the actual mem size of the memory region.
    fn init_unaligned(&mut self, mem_size: usize) -> usize {
        // allocate enough size, make sure to align the allocation to the alignment of
        // the heap allocator.
        self.layout = Layout::from_size_align(mem_size, MIN_ALIGNMENT).unwrap();

        let raw_addr = unsafe { std::alloc::alloc(self.layout) as usize };

        let alignment = MIN_ALIGNMENT * 2;

        // sometimes by accident, `addr+HEADER_SIZE`, which is where our chunk's content
        // will be, will be aligned to the chosen `alignment`, which is not what we want
        // because we want the content to be unaligned in order for a start padding
        // chunk to be created.
        //
        // so if `addr+HEADER_SIZE` is already aligned, we just add `MIN_ALIGNMENT` to
        // `addr`, and we will thus make sure that `addr+HEADER_SIZE` is now not
        // aligned.
        let (addr, mem_size) = if unsafe { is_aligned(raw_addr + HEADER_SIZE, alignment) } {
            // if the content address is aligned, change addr to make sure it is not
            // aligned, but make sure to adjust the mem size accordingly.
            (raw_addr + MIN_ALIGNMENT, mem_size - MIN_ALIGNMENT)
        } else {
            // the content address is not aligned, no need to change addr and mem size
            (raw_addr, mem_size)
        };

        self.addr = addr;

        unsafe { self.allocator.init(addr, mem_size) }

        mem_size
    }

    /// Returns the address of the allocated heap memory region.
    fn addr(&self) -> usize {
        self.addr
    }
}
impl Drop for AllocatorInitGuard {
    fn drop(&mut self) {
        unsafe { std::alloc::dealloc(self.addr as *mut u8, self.layout) }
    }
}