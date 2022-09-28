mod alignment;
mod chunks;
mod divisible_by_4_usize;

#[cfg(test)]
mod tests;

use core::{alloc::Layout, ptr::NonNull};

use alignment::*;
use chunks::*;

pub const USIZE_ALIGNMENT: usize = core::mem::align_of::<usize>();
pub const USIZE_SIZE: usize = core::mem::size_of::<usize>();
pub const MIN_ALIGNMENT: usize = USIZE_ALIGNMENT;
pub const MIN_FREE_CHUNK_SIZE: usize = core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
pub const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

/// Chunk size must be divible by 4, even if `MIN_ALIGNMENT` is smaller than
/// 4, but if `MIN_ALIGNMENT` is bigger than 4 then size must be a multiple of
/// it.
const CHUNK_SIZE_ALIGNMENT: usize = if MIN_ALIGNMENT < 4 { 4 } else { MIN_ALIGNMENT };

/// A linked list memory allocator.
pub struct Allocator {
    heap_region: HeapRegion,
    free_chunk: Option<FreeChunkPtr>,
}
impl Allocator {
    /// Creates an empty heap allocator without any heap memory region, which
    /// will always return null on allocation requests.
    ///
    /// To intiialize this allocator, use the `init` method.
    pub const fn empty() -> Self {
        Self {
            heap_region: HeapRegion {
                heap_start_addr: 0,
                heap_end_addr: 0,
            },
            free_chunk: None,
        }
    }

    /// Checks if the heap memory region was already initialized by calling
    /// `init`.
    pub fn was_initialized(&self) -> bool {
        !(self.heap_region.heap_start_addr == 0 && self.heap_region.heap_end_addr == 0)
    }

    /// Initializes the heap allocator with the given memory region.
    ///
    /// # Safety
    ///
    /// If the allocator was already initialized, this function will panic.
    ///
    /// The `Allocator` on which this was called must not be moved, and its
    /// address in memory must not change, otherwise undefined behaviour
    /// will occur. This is because the heap region now contains pointers to
    /// fields of this struct, and if this struct will move, the address of
    /// its fields will change, and those pointers will now be invalid.
    ///
    /// The provided memory region must be valid and non-null, and must not be
    /// used by anything else.
    ///
    /// If after aligning the start and end addresses, the size of the heap is
    /// 0, the function panics.
    pub unsafe fn init(&mut self, heap_start_addr: usize, heap_size: usize) {
        if self.was_initialized() {
            panic!("the heap was already initialized");
        }

        let aligned_heap_start_addr = align_up(heap_start_addr, MIN_ALIGNMENT);
        let heap_end_addr = heap_start_addr + heap_size;
        let aligned_heap_end_addr = align_down(heap_end_addr, MIN_ALIGNMENT);
        let aligned_size = aligned_heap_end_addr.saturating_sub(aligned_heap_start_addr);

        // if after aligning the start and end addresses, the heap size is 0
        if aligned_size == 0 {
            panic!("heap size is 0 after aligning heap start and end addresses");
        }

        // create a free chunk for the entire heap.
        // no need to update the next chunk because there is no next chunk, this chunk
        // covers the entire heap.
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            aligned_heap_start_addr,
            aligned_size - HEADER_SIZE,
            None,
            &mut self.free_chunk,
        );

        // update the heap region.
        self.heap_region = HeapRegion {
            heap_start_addr: aligned_heap_start_addr,
            heap_end_addr: aligned_heap_end_addr,
        }
    }

    /// Allocates memory.
    pub unsafe fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        let layout_size = align_up(
            core::cmp::max(layout.size(), 2 * USIZE_SIZE),
            CHUNK_SIZE_ALIGNMENT,
        );
        let layout_align = core::cmp::max(layout.align(), MIN_ALIGNMENT);

        let mut maybe_cur_chunk_ptr = self.free_chunk;
        while let Some(mut cur_chunk_ptr) = maybe_cur_chunk_ptr {
            let cur_chunk = cur_chunk_ptr.as_mut();
            if is_aligned(cur_chunk.content_addr(), layout_align) {
                // already aligned
                if let Some(ptr) = self
                    .heap_region
                    .alloc_aligned(layout_size, cur_chunk_ptr.as_mut())
                {
                    return ptr.as_ptr();
                }
            } else {
                // the chunk is not aligned
                if let Some(ptr) = self.heap_region.alloc_unaligned(
                    layout_size,
                    layout_align,
                    cur_chunk_ptr.as_mut(),
                ) {
                    return ptr.as_ptr();
                }
            }

            maybe_cur_chunk_ptr = cur_chunk.fd();
        }

        core::ptr::null_mut()
    }

    /// Deallocates memory.
    pub unsafe fn dealloc(&mut self, ptr: *mut u8) {
        let chunk = UsedChunk::from_addr(ptr as usize - HEADER_SIZE);
        match (
            chunk.prev_chunk_if_free(),
            chunk.next_chunk_if_free(self.heap_region.heap_end_addr),
        ) {
            (None, None) => {
                // mark the chunk as free, and adds it to the start of the linked list of free chunks.
                let _ = chunk.mark_as_free(
                    self.free_chunk,
                    &mut self.free_chunk,
                    self.heap_region.heap_end_addr,
                );
            }
            (None, Some(next_chunk_free)) => {
                // for this case, we create a free chunk where the deallocated chunk is,
                // which will consolidate itself and the next chunk into one big free chunk.

                // first resize the chunk (before marking it as free), so that we won't write
                // the postfix size twice.
                //
                // the chunk should include itself, and the entire next free chunk,
                // which is made up of its header, and its content.
                chunk.set_size(chunk.0.size() + HEADER_SIZE + next_chunk_free.size());

                // mark the chunk as free.
                //
                // this will also unlink the next chunk and replace it with this deallocated
                // chunk, in the linked list of free chunks.
                let _ = chunk.mark_as_free_without_updating_next_chunk(
                    next_chunk_free.fd,
                    next_chunk_free.ptr_to_fd_of_bk,
                    self.heap_region.heap_end_addr,
                );
            }
            (Some(prev_chunk_free), None) => {
                // for this case, just resize the prev chunk to consolidate it with the current chunk.
                // in other words, make it large enough so that it includes the entire current chunk,
                //
                // which means that it should include itself, the current chunk's header, and the
                // current chunk's content.
                prev_chunk_free.set_size(prev_chunk_free.size() + HEADER_SIZE + chunk.0.size());

                // we must also update the prev in use bit of the next chunk, if any, because its
                // prev is now free.
                if let Some(next_chunk_addr) =
                    chunk.0.next_chunk_addr(self.heap_region.heap_end_addr)
                {
                    Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_addr, false);
                }
            }
            (Some(prev_chunk_free), Some(next_chunk_free)) => {
                // for this case, we want to make the prev chunk large enough to include both this
                // and the next chunk.
                //
                // we must also make sure to unlink the next chunk since it's now part of another
                // chunk.

                // SAFETY: this is safe because this chunk will now be incorporated in the prev chunk,
                // so no memory is lost.
                next_chunk_free.unlink();

                // the prev chunk will now include the following:
                // - itself
                // - the current chunk's header
                // - the current chunk's content
                // - the next chunk's header
                // - the next chunk's content
                prev_chunk_free.set_size(
                    prev_chunk_free.size()
                        + HEADER_SIZE
                        + chunk.0.size()
                        + HEADER_SIZE
                        + next_chunk_free.size(),
                );
            }
        }
    }
}

pub struct HeapRegion {
    heap_start_addr: usize,
    heap_end_addr: usize,
}

impl HeapRegion {
    /// Allocates an unaligned chunk by splitting a start padding chunk from it,
    /// and then proceeding as usual.
    fn alloc_unaligned(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        cur_chunk: FreeChunkRef,
    ) -> Option<NonNull<u8>> {
        // find an aligned start address which leaves enough space for a free chunk of
        // padding plus a header for the created chunk before the content chunk that is
        // returned to the user.
        let aligned_content_start_addr = unsafe {
            align_up(
                cur_chunk.addr() + MIN_FREE_CHUNK_SIZE + HEADER_SIZE,
                layout_align,
            )
        };

        let aligned_start_addr = aligned_content_start_addr - HEADER_SIZE;

        // calculate the size left from the aligned start addr to the end of the chunk.
        let left_size = cur_chunk
            .end_addr()
            .saturating_sub(aligned_content_start_addr);

        if left_size < layout_size {
            // chunk is not big enough
            return None;
        }

        // shrink the current chunk to leave some space for the new aligned allocated
        // chunk.
        let cur_chunk_new_size = aligned_start_addr - cur_chunk.content_addr();
        cur_chunk.set_size(cur_chunk_new_size);

        Some(self.alloc_unaligned_after_splitting_start_padding(
            layout_size,
            aligned_start_addr,
            left_size,
            cur_chunk,
        ))
    }

    /// Allocates an unaligned chunk after splitting its start padding to a
    /// different chunk, given the address and size of the allocated chunk that
    /// is next to the start padding chunk.
    fn alloc_unaligned_after_splitting_start_padding(
        &mut self,
        layout_size: usize,
        allocated_chunk_addr: usize,
        allocated_chunk_size: usize,
        start_padding_chunk: FreeChunkRef,
    ) -> NonNull<u8> {
        // check if we need any end padding
        let end_padding = allocated_chunk_size - layout_size;
        if end_padding > 0 {
            // check if the end padding is large enough to hold a free chunk
            if end_padding >= MIN_FREE_CHUNK_SIZE {
                // if the end padding is large enough to hold a free chunk, create a chunk
                // there.
                unsafe {
                    // this is safe because we checked that `end_padding` is big enough
                    self.alloc_unaligned_after_splitting_start_padding_split_end_padding_chunk(
                        layout_size,
                        end_padding,
                        allocated_chunk_addr,
                        start_padding_chunk,
                    )
                }
            } else {
                // if the end padding is not large enough to hold a free chunk, consider it a
                // part of the allocated chunk. this is a little wasteful, but
                // it prevents us from returning `null` from the allocator even
                // when we have enough space.

                // this case can be considered the same as allocating without any end padding.
                unsafe {
                    self.alloc_unaligned_after_splitting_start_padding_no_end_padding(
                        allocated_chunk_addr,
                        allocated_chunk_size,
                    )
                }
            }
        } else {
            // if there is no end padding
            unsafe {
                self.alloc_unaligned_after_splitting_start_padding_no_end_padding(
                    allocated_chunk_addr,
                    allocated_chunk_size,
                )
            }
        }
    }

    /// Allocates an unaligned chunk after splitting its start padding, without
    /// splitting the end padding.
    ///
    /// # Safety
    ///
    ///  - `allocated_chunk_addr` must be a valid non-null memory address.
    ///  - `allocated_chunk_size` must be aligned to [`CHUNK_SIZE_ALIGNMENT`]
    ///  - the range of memory
    ///    `allocated_chunk_addr..allocated_chunk_addr+allocated_chunk_size`
    ///    must be valid and must not be used by any other chunk.
    unsafe fn alloc_unaligned_after_splitting_start_padding_no_end_padding(
        &mut self,
        allocated_chunk_addr: usize,
        allocated_chunk_size: usize,
    ) -> NonNull<u8> {
        // we already split of the start padding and we don't need no end padding, so
        // just create a used chunk in the available space.
        //
        // third argument is the `prev_in_use` bit of the created chunk. the chunk
        // before the allocated chunk is the start padding chunk, which is not in
        // use, thus the third argument is `false`.
        let chunk = UsedChunk::create_new(
            allocated_chunk_addr,
            allocated_chunk_size,
            false,
            self.heap_end_addr,
        );

        NonNull::new_unchecked(chunk.content_addr() as *mut _)
    }

    /// Allocates an unaligned chunk after splitting its start padding, and
    /// splits an end padding chunk from it.
    ///
    /// # Safety
    ///
    ///  - `end_padding` must be greater than or equal to
    ///    [`MIN_FREE_CHUNK_SIZE`].
    ///  - `allocated_chunk_addr` must be a valid non-null memory address.
    ///  - `allocated_chunk_size` must be aligned to [`CHUNK_SIZE_ALIGNMENT`]
    ///  - the range of memory
    ///    `allocated_chunk_addr..allocated_chunk_addr+allocated_chunk_size`
    ///    must be valid and must not be used by any other chunk.
    unsafe fn alloc_unaligned_after_splitting_start_padding_split_end_padding_chunk(
        &mut self,
        layout_size: usize,
        end_padding: usize,
        allocated_chunk_addr: usize,
        start_padding_chunk: FreeChunkRef,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let allocated_chunk_end_addr = allocated_chunk_addr + HEADER_SIZE + layout_size;

        // create an end padding chunk.
        //
        // this chunk will be put between the start padding and the start padding's fd
        // chunk, so its fd will be the start padding's fd, and its bk will be the start
        // padding chunk.
        //
        // there is no need to update the next chunk because it's prev in use bit is
        // already set to false, as it should be.
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            allocated_chunk_end_addr,
            end_padding - HEADER_SIZE,
            start_padding_chunk.fd(),
            start_padding_chunk.fd_ref_mut(),
        );

        // now create a used chunk for the allocated chunk.
        //
        // note that there is no need to update the next chunk, which will be the end
        // padding chunk, because when creating a free chunk the prev in use flag is
        // already set to false.
        //
        // also note that the chunk before the allocated chunk is the start padding
        // chunk which is free and not in use, thus the third argument is `false`.
        let allocated_chunk = UsedChunk::create_new_without_updating_next_chunk(
            allocated_chunk_addr,
            layout_size,
            false,
        );

        NonNull::new_unchecked(allocated_chunk.content_addr() as *mut _)
    }

    /// Allocates a chunk that is already aligned to the desired alignment of
    /// the content.
    fn alloc_aligned(
        &mut self,
        layout_size: usize,
        cur_chunk: FreeChunkRef,
    ) -> Option<NonNull<u8>> {
        let cur_chunk_size = cur_chunk.size();

        // first make sure that the chunk is big enough to hold the allocation.
        if cur_chunk_size < layout_size {
            return None;
        }

        // check if we need any end padding
        let end_padding = cur_chunk_size - layout_size;
        if end_padding > 0 {
            // check if the end padding is large enough to hold a free chunk
            if end_padding >= MIN_FREE_CHUNK_SIZE {
                // if the end padding is large enough to hold a free chunk, create a chunk
                // there.
                Some(unsafe {
                    // this is safe because we checked that `end_padding` is big enough
                    self.alloc_aligned_split_end_padding_chunk(layout_size, end_padding, cur_chunk)
                })
            } else {
                // if the end padding is not large enough to hold a free chunk, consider it a
                // part of the allocated chunk. this is a little wasteful, but
                // it prevents us from returning `null` from the allocator even
                // when we have enough space.

                // this case can be considered the same as allocating without any end padding.
                Some(self.alloc_aligned_no_end_padding(cur_chunk))
            }
        } else {
            // if there is no end padding
            Some(self.alloc_aligned_no_end_padding(cur_chunk))
        }
    }

    /// Allocates an aligned chunk without any end padding.
    fn alloc_aligned_no_end_padding(&mut self, cur_chunk: FreeChunkRef) -> NonNull<u8> {
        // mark the chunk as used and make the necessary updates
        cur_chunk.mark_as_used_unlink(self.heap_end_addr);

        // retrun the chunk to the user
        unsafe { NonNull::new_unchecked(cur_chunk.content_addr() as *mut u8) }
    }

    /// Allocates the given aligned chunk and splits an end padding chunk from
    /// it.
    ///
    /// # Safety
    ///
    /// `end_padding` must be greater than or equal to [`MIN_FREE_CHUNK_SIZE`].
    unsafe fn alloc_aligned_split_end_padding_chunk(
        &mut self,
        layout_size: usize,
        end_padding: usize,
        cur_chunk: FreeChunkRef,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let allocated_chunk_end_addr = cur_chunk.content_addr() + layout_size;

        // create a free chunk for the end padding.
        // this will also unlink `cur_chunk` from the linked list and put the end
        // padding chunk in place of it.
        //
        // there is no need to update the next chunk because it's prev in use bit is
        // already set to false, as it should be.
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            allocated_chunk_end_addr,
            end_padding - HEADER_SIZE,
            cur_chunk.fd(),
            cur_chunk.ptr_to_fd_of_bk(),
        );

        // this is safe because we already removed `cur_chunk` from the freelist, so
        // there's no need to update the freelist again.
        let cur_chunk_as_used =
            cur_chunk.mark_as_used_without_updating_freelist(self.heap_end_addr);

        // shrink cur chunk to only include the content and not the end padding.
        cur_chunk_as_used.set_size(layout_size);

        // return a pointer to the allocated chunk
        NonNull::new_unchecked(cur_chunk.content_addr() as *mut u8)
    }
}

unsafe impl Send for Allocator {}

/// A spin locked memory allocator that can be used as the global allocator.
#[cfg(feature = "spin")]
pub struct SpinLockedAllocator(spin::Mutex<Allocator>);

#[cfg(feature = "spin")]
impl SpinLockedAllocator {
    /// Creates an empty locked heap allocator without any heap memory region, which
    /// will always return null on allocation requests.
    ///
    /// To intiialize this allocator, use the `init` method.
    pub const fn empty() -> Self {
        Self(spin::Mutex::new(Allocator::empty()))
    }

    /// Initializes the heap allocator with the given memory region.
    ///
    /// # Safety
    ///
    /// If the allocator was already initialized, this function will panic.
    ///
    /// The `SpinLockedAllocator` on which this was called must not be moved, and its
    /// address in memory must not change, otherwise undefined behaviour
    /// will occur. This is because the heap region now contains pointers to
    /// fields of this struct, and if this struct will move, the address of
    /// its fields will change, and those pointers will now be invalid.
    ///
    /// The provided memory region must be valid and non-null, and must not be
    /// used by anything else.
    ///
    /// If after aligning the start and end addresses, the size of the heap is
    /// 0, the function panics.
    pub unsafe fn init(&self, heap_start_addr: usize, heap_size: usize) {
        let mut allocator = self.0.lock();
        allocator.init(heap_start_addr, heap_size);
    }
}

#[cfg(feature = "spin")]
unsafe impl core::alloc::GlobalAlloc for SpinLockedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut allocator = self.0.lock();
        allocator.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let mut allocator = self.0.lock();
        allocator.dealloc(ptr)
    }
}
