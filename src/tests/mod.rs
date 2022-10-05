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
        assert_only_1_free_chunk_which_is_at_heap_start(&mut guard, MEM_SIZE);
    }
}

/// Asserts that there is only 1 free chunk in the bin of the chunk at the given addr.
fn assert_only_1_free_chunk_in_bin(guard: &mut AllocatorInitGuard, addr: usize, size: usize) {
    let free_chunk = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(_) => panic!("first chunk in heap is marked used after dealloc"),
            ChunkRef::Free(free) => free,
        }
    };

    // the first chunk's prev in use flag must be `true`.
    assert_eq!(free_chunk.header.prev_in_use(), true);

    assert_eq!(free_chunk.size(), size);

    // find the desired fd and bk of the free chunk.
    let (fd, bk) = get_expected_fd_and_bk_for_chunk_with_size(
        free_chunk.size(),
        free_chunk.content_addr(),
        guard,
    );

    // it is the only free chunk, so it points back to the allocator
    assert_eq!(free_chunk.fd, fd);

    // it is the only free chunk, so back should point to the allocator
    assert_eq!(free_chunk.ptr_to_fd_of_bk, bk);

    // make sure fd points back to free chunk
    if let Some(mut fd_ptr) = fd {
        let fd_ref = unsafe { fd_ptr.as_mut() };
        assert_eq!(fd_ref.ptr_to_fd_of_bk, &mut free_chunk.fd as *mut _)
    }

    // make sure bk points to the free chunk.
    assert_eq!(
        unsafe { *bk },
        Some(unsafe { NonNull::new_unchecked(free_chunk as *mut _) })
    );
}

/// Asserts that there is only 1 free chunk.
fn assert_only_1_free_chunk_which_is_at_heap_start(
    guard: &mut AllocatorInitGuard,
    mem_size: usize,
) {
    assert_only_1_free_chunk_in_bin(guard, guard.addr(), mem_size - HEADER_SIZE)
}

/// Returns the expected fd and bk for a chunk with the given size and content address, assuming that it's the only free chunk in its bin.
fn get_expected_fd_and_bk_for_chunk_with_size(
    size: usize,
    content_addr: usize,
    guard: &mut AllocatorInitGuard,
) -> (Option<FreeChunkPtr>, *mut Option<FreeChunkPtr>) {
    match unsafe { SmallBins::smallbin_index(size) } {
        Some(smallbin_index) => {
            let alignment_index =
                unsafe { SmallBins::alignment_index_of_chunk_content_addr(content_addr) };
            let sub_bin = &mut guard.allocator.smallbins.small_bins[smallbin_index]
                .alignment_sub_bins[alignment_index];
            (None, &mut sub_bin.fd as *mut _)
        }
        None => {
            // the chunk is in the other bin
            (
                Some(unsafe { guard.allocator.fake_chunk_of_other_bin_ptr() }),
                guard.allocator.ptr_to_fd_of_fake_chunk_of_other_bin(),
            )
        }
    }
}

/// A guard that initializes the allocator with a region of memory on
/// creation, and frees that memory when dropped.
#[derive(Debug)]
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

    /// Initializes the heap allocator.
    fn init(&mut self, mem_size: usize) {
        // make sure to align the allocation to the alignment of the heap allocator.
        self.init_with_alignment(mem_size, MIN_ALIGNMENT);
    }

    /// Initializes the heap allocator, such that the heap start address is
    /// aligned to the given alignment.
    fn init_with_alignment(&mut self, mem_size: usize, alignment: usize) {
        // allocate enough size, make sure to align the allocation to the alignment of
        // the heap allocator.
        self.layout = Layout::from_size_align(mem_size, alignment).unwrap();

        self.addr = unsafe { std::alloc::alloc(self.layout) as usize };

        unsafe { self.allocator.init(self.addr, mem_size) }
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
