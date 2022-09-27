use core::alloc::Layout;

use super::*;

/// A guard that initializes the allocator with a region of memory on
/// creation, and frees that memory when dropped.
struct AllocatorInitGuard<const MEM_SIZE: usize> {
    addr: usize,
    layout: Layout,
    allocator: Allocator,
}
impl<const MEM_SIZE: usize> AllocatorInitGuard<MEM_SIZE> {
    /// Creates an empty allocator init guard.
    const fn empty() -> Self {
        Self {
            addr: 0,
            layout: Layout::new::<u8>(),
            allocator: Allocator::empty(),
        }
    }

    /// Initializes the heap allocator and returns a guard for it.
    fn init(&mut self) {
        // allocate enough size, make sure to align the allocation to the alignment of
        // the heap allocator.
        self.layout = Layout::from_size_align(MEM_SIZE, MIN_ALIGNMENT).unwrap();

        self.addr = unsafe { std::alloc::alloc(self.layout) as usize };

        unsafe { self.allocator.init(self.addr, MEM_SIZE) }
    }

    /// Initializes the allocator and makes sure that calling alloc with an
    /// alignment greater than `MIN_ALIGNMENT` won't be aligned.
    ///
    /// Returns the mem size of the memory region.
    fn init_unaligned(&mut self) -> usize {
        // allocate enough size, make sure to align the allocation to the alignment of
        // the heap allocator.
        self.layout = Layout::from_size_align(MEM_SIZE, MIN_ALIGNMENT).unwrap();

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
            (raw_addr + MIN_ALIGNMENT, MEM_SIZE - MIN_ALIGNMENT)
        } else {
            // the content address is not aligned, no need to change addr and mem size
            (raw_addr, MEM_SIZE)
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
impl<const MEM_SIZE: usize> Drop for AllocatorInitGuard<MEM_SIZE> {
    fn drop(&mut self) {
        unsafe { std::alloc::dealloc(self.addr as *mut u8, self.layout) }
    }
}

#[test]
fn alloc_not_enough_space_returns_null() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    guard.init();

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    // add 1 to make an allocation size that will not fit.
    let no_fit = perfect_fit + 1;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(no_fit, 1).unwrap())
    };

    assert!(allocated.is_null())
}

#[test]
fn alloc_perfect_fit() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    guard.init();

    let addr = guard.addr();

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(perfect_fit, 1).unwrap())
    };

    // make sure it points to where it should
    assert_eq!(allocated as usize, addr + HEADER_SIZE);

    // make sure that the chunk header is correct.
    let chunk_header = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => panic!("allocated chunk is marked as free"),
        }
    };

    // the prev in use of the first chunk in the heap should be `true`.
    assert_eq!(chunk_header.0.prev_in_use(), true);
    assert_eq!(chunk_header.0.size(), perfect_fit);
}

#[test]
fn alloc_aligned_with_end_padding_not_large_enough_to_fit_chunk() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    guard.init();
    let addr = guard.addr();

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    // a chunk size which when allocate will leave `USIZE_SIZE` bytes of end
    // padding, which is the minimal amount due to alignment.
    //
    // the `USIZE_SIZE` bytes of padding are not enough to store a chunk there, so
    // the end padding should be included in the allocated chunk.
    let size_with_minimal_end_padding = perfect_fit - USIZE_SIZE;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(size_with_minimal_end_padding, 1).unwrap())
    };

    // make sure it points to where it should
    assert_eq!(allocated as usize, addr + HEADER_SIZE);

    // make sure that the chunk header is correct.
    let chunk_header = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => panic!("allocated chunk is marked as free"),
        }
    };

    // the prev in use of the first chunk in the heap should be `true`.
    assert_eq!(chunk_header.0.prev_in_use(), true);

    // the size of the chunk should include the end padding, and will thus be larger
    // than the actual allocated size. it will be the size of a chunk as if we
    // allocated all the space.
    assert_eq!(chunk_header.0.size(), perfect_fit);
}

#[test]
fn alloc_aligned_end_padding() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    guard.init();
    let addr = guard.addr();

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    // a size that will leave end padding that is large enough to fit a free chunk.
    let size_with_large_enough_end_padding = perfect_fit - MIN_FREE_CHUNK_SIZE;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(size_with_large_enough_end_padding, 1).unwrap())
    };

    // make sure it points to where it should
    assert_eq!(allocated as usize, addr + HEADER_SIZE);

    // make sure that the chunk header is correct.
    let chunk_header = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => panic!("allocated chunk is marked as free"),
        }
    };

    // the prev in use of the first chunk in the heap should be `true`.
    assert_eq!(chunk_header.0.prev_in_use(), true);

    // the size of the chunk should include the end padding, and will thus be larger
    // than the actual allocated size. it will be the size of a chunk as if we
    // allocated all the space.
    assert_eq!(chunk_header.0.size(), size_with_large_enough_end_padding);

    // check the end padding chunk
    let end_padding_chunk = unsafe {
        match Chunk::from_addr(allocated as usize + size_with_large_enough_end_padding) {
            ChunkRef::Used(_) => panic!("end padding chunk is marked as used"),
            ChunkRef::Free(free) => free,
        }
    };

    // the prev chunk is the allocated chunk, which is in use.
    assert_eq!(end_padding_chunk.header.prev_in_use(), true);

    // we left enough space for `MIN_FREE_CHUNK_SIZE`.
    // subtracting `HEADER_SIZE` because `MIN_FREE_CHUNK_SIZE` includes the header.
    assert_eq!(
        end_padding_chunk.header.size(),
        MIN_FREE_CHUNK_SIZE - HEADER_SIZE
    );

    // the end padding chunk is the only free chunk
    assert_eq!(end_padding_chunk.fd, None,);
    assert_eq!(
        end_padding_chunk.ptr_to_fd_of_bk,
        (&mut guard.allocator.free_chunk) as *mut _,
    );

    // make sure that the end padding size has written its postfix size
    assert_eq!(
        *end_padding_chunk.postfix_size(),
        MIN_FREE_CHUNK_SIZE - HEADER_SIZE
    );

    // make sure that the allocator points to the end padding chunk.
    assert_eq!(
        guard.allocator.free_chunk,
        Some(unsafe { NonNull::new_unchecked(end_padding_chunk as *mut _) })
    )
}

#[test]
fn alloc_unaligned_not_enough_space_returns_null() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    let mem_size = guard.init_unaligned();

    // an alignment that will cause the chunk to be unaligned.
    let alignment = MIN_ALIGNMENT * 2;

    // calculate the allocation size that will fit perfectly
    let perfect_fit = mem_size - HEADER_SIZE;

    // add 1 to make an allocation size that will not fit.
    let no_fit = perfect_fit + 1;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(no_fit, alignment).unwrap())
    };

    assert!(allocated.is_null())
}

#[test]
fn alloc_unaligned_no_end_padding() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    let mem_size = guard.init_unaligned();
    let addr = guard.addr();

    // choose an alignment that will cause the chunk to be unaligned.
    let alignment = MIN_ALIGNMENT * 2;

    // calculate the minimal aligned address at which the content can start so that
    // we have enough space for an entire free chunk for the start padding, and for
    // the header of the allocated chunk.
    let aligned_content_addr =
        unsafe { align_up(addr + MIN_FREE_CHUNK_SIZE + HEADER_SIZE, alignment) };

    // find the end of the heap
    let heap_end_addr = addr + mem_size;

    // calculate a perfect fit size for the chunk
    let perfect_fit = heap_end_addr - aligned_content_addr;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(perfect_fit, alignment).unwrap())
    };

    // make sure it points to where it should
    assert_eq!(allocated as usize, aligned_content_addr);

    // make sure that the start padding chunk is correct
    let start_padding_chunk = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(_) => panic!("start padding chunk is marked as used"),
            ChunkRef::Free(free) => free,
        }
    };

    // the prev in use of the first chunk in the heap should be `true`.
    assert_eq!(start_padding_chunk.header.prev_in_use(), true);

    // check the size of the start padding chunk
    let content_chunk_addr = aligned_content_addr - HEADER_SIZE;
    let start_padding_chunk_size = content_chunk_addr - addr - HEADER_SIZE;
    assert_eq!(start_padding_chunk.header.size(), start_padding_chunk_size);

    // make sure that the start padding chunk is the last chunk in the freelist.
    assert_eq!(start_padding_chunk.fd, None);

    // make sure that the start padding chunk is the first chunk in the freelist and
    // points back to the allocator.
    assert_eq!(
        start_padding_chunk.ptr_to_fd_of_bk,
        &mut guard.allocator.free_chunk as *mut _
    );

    // make sure that the allocated chunk is correct
    let allocated_chunk = unsafe {
        match Chunk::from_addr(allocated as usize - HEADER_SIZE) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => panic!("allocated chunk is marked as free"),
        }
    };

    // make sure that the allocated chunk properly knows that the prev chunk which
    // is the start padding chunk is free, and properly knows its size.
    assert_eq!(
        allocated_chunk.prev_size_if_free(),
        Some(start_padding_chunk_size)
    );

    // check the size
    assert_eq!(allocated_chunk.0.size(), perfect_fit);

    // make sure that the allocator's freelist points to the start padding chunk
    assert_eq!(
        guard.allocator.free_chunk,
        Some(unsafe { NonNull::new_unchecked(addr as *mut _) })
    )
}

#[test]
fn alloc_unaligned_end_padding() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::<MEM_SIZE>::empty();
    let mem_size = guard.init_unaligned();
    let addr = guard.addr();

    // choose an alignment that will cause the chunk to be unaligned.
    let alignment = MIN_ALIGNMENT * 2;

    // calculate the minimal aligned address at which the content can start so that
    // we have enough space for an entire free chunk for the start padding, and for
    // the header of the allocated chunk.
    let aligned_content_addr =
        unsafe { align_up(addr + MIN_FREE_CHUNK_SIZE + HEADER_SIZE, alignment) };

    // find the end of the heap
    let heap_end_addr = addr + mem_size;

    // calculate a perfect fit size for the chunk
    let perfect_fit = heap_end_addr - aligned_content_addr;

    // a size that will leave end padding that is large enough to fit a free chunk.
    let size_with_large_enough_end_padding = perfect_fit - MIN_FREE_CHUNK_SIZE;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(size_with_large_enough_end_padding, alignment).unwrap())
    };

    // make sure it points to where it should
    assert_eq!(allocated as usize, aligned_content_addr);

    // make sure that the start padding chunk and the end padding chunk are correct
    let start_padding_chunk = unsafe {
        match Chunk::from_addr(addr) {
            ChunkRef::Used(_) => panic!("start padding chunk is marked as used"),
            ChunkRef::Free(free) => free,
        }
    };

    let end_padding_chunk = unsafe {
        match Chunk::from_addr(allocated as usize + size_with_large_enough_end_padding) {
            ChunkRef::Used(_) => panic!("end padding chunk is marked as used"),
            ChunkRef::Free(free) => free,
        }
    };

    // the prev in use of the first chunk in the heap should be `true`.
    assert_eq!(start_padding_chunk.header.prev_in_use(), true);

    // check the size of the start padding chunk
    let content_chunk_addr = aligned_content_addr - HEADER_SIZE;
    let start_padding_chunk_size = content_chunk_addr - addr - HEADER_SIZE;
    assert_eq!(start_padding_chunk.header.size(), start_padding_chunk_size);

    // the start padding chunk should point to the end padding chunk.
    assert_eq!(
        start_padding_chunk.fd,
        Some(unsafe { NonNull::new_unchecked(end_padding_chunk as *mut _) })
    );

    // make sure that the start padding chunk is the first chunk in the freelist and
    // points back to the allocator.
    assert_eq!(
        start_padding_chunk.ptr_to_fd_of_bk,
        &mut guard.allocator.free_chunk as *mut _
    );

    // the prev chunk is the allocated chunk, which is in use.
    assert_eq!(end_padding_chunk.header.prev_in_use(), true);

    // we left enough space for `MIN_FREE_CHUNK_SIZE`.
    // subtracting `HEADER_SIZE` because `MIN_FREE_CHUNK_SIZE` includes the header.
    assert_eq!(
        end_padding_chunk.header.size(),
        MIN_FREE_CHUNK_SIZE - HEADER_SIZE
    );

    // the end padding chunk is the last free chunk
    assert_eq!(end_padding_chunk.fd, None);

    // the bk of the end padding chunk is the start padding chunk.
    assert_eq!(
        end_padding_chunk.ptr_to_fd_of_bk,
        (&mut start_padding_chunk.fd) as *mut _,
    );

    // make sure that the end padding size has written its postfix size
    assert_eq!(
        *end_padding_chunk.postfix_size(),
        MIN_FREE_CHUNK_SIZE - HEADER_SIZE
    );

    // make sure that the allocated chunk is correct
    let allocated_chunk = unsafe {
        match Chunk::from_addr(allocated as usize - HEADER_SIZE) {
            ChunkRef::Used(used) => used,
            ChunkRef::Free(_) => panic!("allocated chunk is marked as free"),
        }
    };

    // make sure that the allocated chunk properly knows that the prev chunk which
    // is the start padding chunk is free, and properly knows its size.
    assert_eq!(
        allocated_chunk.prev_size_if_free(),
        Some(start_padding_chunk_size)
    );

    // check the size
    assert_eq!(allocated_chunk.0.size(), size_with_large_enough_end_padding);

    // make sure that the allocator's freelist points to the start padding chunk
    assert_eq!(
        guard.allocator.free_chunk,
        Some(unsafe { NonNull::new_unchecked(addr as *mut _) })
    )
}
