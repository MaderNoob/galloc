use core::alloc::Layout;

use super::*;

#[test]
fn alloc_no_memory() {
    let mut allocator = Allocator::empty();
    let allocated = unsafe { allocator.alloc(Layout::from_size_align(1, 1).unwrap()) };

    assert!(allocated.is_null())
}

#[test]
fn alloc_not_enough_space_returns_null() {
    const MEM_SIZE: usize = USIZE_SIZE * 17;

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

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

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);

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

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);
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

    let mut guard = AllocatorInitGuard::empty();
    guard.init(MEM_SIZE);
    let addr = guard.addr();

    // calculate the allocation size that will fit perfectly
    let perfect_fit = MEM_SIZE - HEADER_SIZE;

    // a size that will leave end padding that is large enough to fit a free chunk.
    let size_with_large_enough_end_padding = perfect_fit - MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER;

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
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE
    );

    // the end padding chunk is the only free chunk so it points back to the
    // allocator.
    assert_eq!(
        end_padding_chunk.fd,
        Some(unsafe { guard.allocator.fake_chunk_of_other_bin_ptr() })
    );
    assert_eq!(
        end_padding_chunk.ptr_to_fd_of_bk,
        (guard.allocator.ptr_to_fd_of_fake_chunk_of_other_bin()) as *mut _,
    );

    // make sure that the end padding size has written its postfix size
    assert_eq!(
        *end_padding_chunk.postfix_size(),
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE
    );

    // make sure that the allocator points to the end padding chunk.
    assert_eq!(
        guard.allocator.first_free_chunk_in_other_bin(),
        Some(unsafe { NonNull::new_unchecked(end_padding_chunk as *mut _) })
    );
    assert_eq!(
        guard.allocator.fake_chunk_of_other_bin.ptr_to_fd_of_bk,
        &mut end_padding_chunk.fd as *mut _
    )
}

#[test]
fn alloc_unaligned_not_enough_space_returns_null() {
    const MEM_SIZE: usize = 128;

    let mut guard = AllocatorInitGuard::empty();
    guard.init_with_alignment(MEM_SIZE, MEM_SIZE);

    // choose an alignment that will cause the chunk to be unaligned.
    let alignment = MEM_SIZE >> 1;

    // calculate a perfect fit size for the chunk
    let perfect_fit = MEM_SIZE >> 1;

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
    const MEM_SIZE: usize = 128;

    let mut guard = AllocatorInitGuard::empty();
    guard.init_with_alignment(MEM_SIZE, MEM_SIZE);
    let addr = guard.addr();

    println!("addr: {:x}", addr);

    // choose an alignment that will cause the chunk to be unaligned.
    let alignment = MEM_SIZE >> 1;

    // calculate a perfect fit size for the chunk
    let perfect_fit = MEM_SIZE >> 1;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(perfect_fit, alignment).unwrap())
    };

    let aligned_content_addr = addr + perfect_fit;

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

    // make sure that the start padding chunk is the last chunk in the freelist,
    // so it points back to the allocator.
    assert_eq!(
        start_padding_chunk.fd,
        Some(unsafe { guard.allocator.fake_chunk_of_other_bin_ptr() })
    );

    // make sure that the start padding chunk is the first chunk in the freelist and
    // points back to the allocator.
    assert_eq!(
        start_padding_chunk.ptr_to_fd_of_bk,
        guard.allocator.ptr_to_fd_of_fake_chunk_of_other_bin(),
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
        guard.allocator.first_free_chunk_in_other_bin(),
        Some(unsafe { NonNull::new_unchecked(addr as *mut _) })
    );
    assert_eq!(
        guard.allocator.fake_chunk_of_other_bin.ptr_to_fd_of_bk,
        &mut start_padding_chunk.fd as *mut _
    );
}

#[test]
fn alloc_unaligned_end_padding() {
    const MEM_SIZE: usize = 128;

    let mut guard = AllocatorInitGuard::empty();
    guard.init_with_alignment(MEM_SIZE, MEM_SIZE);
    let addr = guard.addr();

    // choose an alignment that will cause the chunk to be unaligned.
    let alignment = MEM_SIZE >> 1;

    // calculate a perfect fit size for the chunk
    let perfect_fit = MEM_SIZE >> 1;

    // a size that will leave end padding that is large enough to fit a free chunk.
    let size_with_large_enough_end_padding = perfect_fit - MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER;

    let allocated = unsafe {
        guard
            .allocator
            .alloc(Layout::from_size_align(size_with_large_enough_end_padding, alignment).unwrap())
    };

    let aligned_content_addr = addr + perfect_fit;

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
        guard.allocator.ptr_to_fd_of_fake_chunk_of_other_bin(),
    );

    // the prev chunk is the allocated chunk, which is in use.
    assert_eq!(end_padding_chunk.header.prev_in_use(), true);

    // we left enough space for `MIN_FREE_CHUNK_SIZE`.
    // subtracting `HEADER_SIZE` because `MIN_FREE_CHUNK_SIZE` includes the header.
    assert_eq!(
        end_padding_chunk.header.size(),
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE
    );

    // the end padding chunk is the last free chunk so it points back to the
    // allocator.
    assert_eq!(
        end_padding_chunk.fd,
        Some(unsafe { guard.allocator.fake_chunk_of_other_bin_ptr() })
    );

    // the bk of the end padding chunk is the start padding chunk.
    assert_eq!(
        end_padding_chunk.ptr_to_fd_of_bk,
        (&mut start_padding_chunk.fd) as *mut _,
    );

    // make sure that the end padding size has written its postfix size
    assert_eq!(
        *end_padding_chunk.postfix_size(),
        MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE
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
        guard.allocator.first_free_chunk_in_other_bin(),
        Some(unsafe { NonNull::new_unchecked(addr as *mut _) })
    );

    assert_eq!(
        guard.allocator.fake_chunk_of_other_bin.ptr_to_fd_of_bk,
        &mut end_padding_chunk.fd as *mut _
    );
}
