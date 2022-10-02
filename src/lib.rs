#![no_std]

#[cfg(test)]
#[macro_use]
extern crate std;

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
pub const MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER: usize =
    core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
pub const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

/// Chunk size must be divible by 4, even if `MIN_ALIGNMENT` is smaller than
/// 4, but if `MIN_ALIGNMENT` is bigger than 4 then size must be a multiple of
/// it.
const CHUNK_SIZE_ALIGNMENT: usize = if MIN_ALIGNMENT < 4 { 4 } else { MIN_ALIGNMENT };

/// A linked list memory allocator.
pub struct Allocator {
    heap_end_addr: usize,
    fake_chunk: FreeChunk,
}
impl Allocator {
    /// Creates an empty heap allocator without any heap memory region, which
    /// will always return null on allocation requests.
    ///
    /// To intiialize this allocator, use the `init` method.
    pub const fn empty() -> Self {
        Self {
            heap_end_addr: 0,
            fake_chunk: FreeChunk {
                header: unsafe { Chunk::new_unchecked(CHUNK_SIZE_ALIGNMENT, true, true) },
                fd: NonNull::dangling(),
                ptr_to_fd_of_bk: core::ptr::null_mut(),
            },
        }
    }

    /// Checks if the heap memory region was already initialized by calling
    /// `init`.
    pub fn was_initialized(&self) -> bool {
        self.heap_end_addr != 0
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
            NonNull::new_unchecked(&mut self.fake_chunk),
            &mut self.fake_chunk.fd,
        );

        // update the heap end address.
        self.heap_end_addr = aligned_heap_end_addr;
    }

    /// Returns a pointer to the fake chunk.
    fn fake_chunk_ptr(&mut self) -> FreeChunkPtr {
        unsafe { NonNull::new_unchecked(&mut self.fake_chunk) }
    }

    /// Returns a pointer to the first free chunk.
    fn first_free_chunk(&self) -> FreeChunkPtr {
        self.fake_chunk.fd
    }

    /// Returns a pointer to the fd of the fake chunk.
    fn ptr_to_fd_of_fake_chunk(&mut self) -> *mut FreeChunkPtr {
        &mut self.fake_chunk.fd
    }

    /// Prepares an allocation size according to the requirements of
    /// the allocator. Returns the prepared size.
    fn prepare_size(size: usize) -> usize {
        unsafe {
            align_up(
                core::cmp::max(size, MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE),
                CHUNK_SIZE_ALIGNMENT,
            )
        }
    }

    /// Prepares a layout's size and alignment according to the requirements of
    /// the allocator. Returns the prepared size and alignment.
    fn prepare_layout(layout: Layout) -> (usize, usize) {
        let layout_size = Self::prepare_size(layout.size());
        let layout_align = core::cmp::max(layout.align(), MIN_ALIGNMENT);

        (layout_size, layout_align)
    }

    /// Allocates memory.
    pub unsafe fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        if !self.was_initialized() {
            return core::ptr::null_mut();
        }

        let (layout_size, layout_align) = Self::prepare_layout(layout);

        let fake_chunk_ptr = self.fake_chunk_ptr();
        let mut cur_chunk_ptr = self.first_free_chunk();

        while cur_chunk_ptr != fake_chunk_ptr {
            let cur_chunk = cur_chunk_ptr.as_mut();
            if is_aligned(cur_chunk.content_addr(), layout_align) {
                // already aligned
                if let Some(ptr) = self.alloc_aligned(layout_size, cur_chunk_ptr.as_mut()) {
                    return ptr.as_ptr();
                }
            } else {
                // the chunk is not aligned
                if let Some(ptr) =
                    self.alloc_unaligned(layout_size, layout_align, cur_chunk_ptr.as_mut())
                {
                    return ptr.as_ptr();
                }
            }

            cur_chunk_ptr = cur_chunk.fd();
        }

        core::ptr::null_mut()
    }

    /// Deallocates memory.
    pub unsafe fn dealloc(&mut self, ptr: *mut u8) {
        let chunk = UsedChunk::from_addr(ptr as usize - HEADER_SIZE);
        match (
            chunk.prev_chunk_if_free(),
            chunk.next_chunk_if_free(self.heap_end_addr),
        ) {
            (None, None) => {
                // mark the chunk as free, and adds it to the start of the linked list of free
                // chunks.
                let _ = chunk.mark_as_free(
                    self.first_free_chunk(),
                    self.ptr_to_fd_of_fake_chunk(),
                    self.heap_end_addr,
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
                );
            }
            (Some(prev_chunk_free), None) => {
                // for this case, just resize the prev chunk to consolidate it with the current
                // chunk. in other words, make it large enough so that it
                // includes the entire current chunk,
                //
                // which means that it should include itself, the current chunk's header, and
                // the current chunk's content.
                prev_chunk_free.set_size(prev_chunk_free.size() + HEADER_SIZE + chunk.0.size());

                // we must also update the prev in use bit of the next chunk, if any, because
                // its prev is now free.
                if let Some(next_chunk_addr) = chunk.0.next_chunk_addr(self.heap_end_addr) {
                    Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_addr, false);
                }
            }
            (Some(prev_chunk_free), Some(next_chunk_free)) => {
                // for this case, we want to make the prev chunk large enough to include both
                // this and the next chunk.
                //
                // we must also make sure to unlink the next chunk since it's now part of
                // another chunk.

                // SAFETY: this is safe because this chunk will now be incorporated in the prev
                // chunk, so no memory is lost.
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

    /// Resizes an allocation previously returned from `alloc` or `realloc`.
    /// The alignment of the content will stay the same.
    pub unsafe fn realloc(&mut self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let previously_requested_size = Self::prepare_size(layout.size());
        let new_size = Self::prepare_size(new_size);

        let chunk = UsedChunk::from_addr(ptr as usize - HEADER_SIZE);

        // first try to realloc in place, to avoid copying memory.
        if self.try_realloc_in_place(chunk, previously_requested_size, new_size) {
            return ptr;
        }

        // if reallocation in place fails, use the default implementation of realloc.
        //
        // SAFETY: the caller must ensure that the `new_size` does not overflow.
        // `layout.align()` comes from a `Layout` and is thus guaranteed to be valid.
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        // SAFETY: the caller must ensure that `new_layout` is greater than zero.
        let new_ptr = self.alloc(new_layout);
        if !new_ptr.is_null() {
            // SAFETY: the previously allocated block cannot overlap the newly allocated
            // block. The safety contract for `dealloc` must be upheld by the
            // caller.
            core::ptr::copy_nonoverlapping(ptr, new_ptr, core::cmp::min(layout.size(), new_size));
            self.dealloc(ptr);
        }
        new_ptr
    }

    /// Tries to reallocate the given chunk to the given new size, in place.
    ///
    /// # Safety
    ///
    /// `previously_requested_size` and `new_size` must have been prepared.
    unsafe fn try_realloc_in_place(
        &mut self,
        chunk: UsedChunkRef,
        previously_requested_size: usize,
        new_size: usize,
    ) -> bool {
        let chunk_size = chunk.0.size();

        if new_size > previously_requested_size {
            // the user requested to grow his allocation.

            // sometimes chunks are bigger than their content due to end padding that's not
            // big enough to fit a chunk, check if that's the case.
            if chunk_size >= new_size {
                // if the chunk is already large enough, no need to do anything.
                return true;
            }

            // if the chunk is not large enough, try to grow it in place.
            self.try_grow_in_place(chunk, new_size)
        } else {
            // the user requested to shrink his allocation, shrink in place.
            self.try_shrink_in_place(chunk, new_size)
        }
    }

    /// Tries to grow the given chunk in place, to the given new size. Please
    /// note that this means that the alignment of the content of this chunk
    /// will stay exactly the same.
    ///
    /// Returns whether or not the operation was successful.
    ///
    /// # Safety
    ///
    /// `new_size` must be greater than the chunk's size, and must have been
    /// prepared.
    unsafe fn try_grow_in_place(&self, chunk: UsedChunkRef, new_size: usize) -> bool {
        // to grow this chunk we need its next chunk to be free, make sure that the next
        // chunk is free.
        let next_chunk_free = match chunk.next_chunk_if_free(self.heap_end_addr) {
            Some(next_chunk_free) => next_chunk_free,

            // if the next chunk is not free, we can't grow this chunk in place.
            None => {
                return false;
            }
        };

        // calculate the new end addresss of the chunk.
        let new_end_addr = chunk.content_addr() + new_size;

        // make sure that if we grow this chunk in place using the next chunk,
        // the chunk's end address stays within the bounds of the next chunk and
        // doesn't go beyound it.
        //
        // if the new end address is beyond the next free chunk, we can't grow in place,
        // because the chunk after the next chunk must be used because there are no 2
        // adjacent free chunks.
        let next_chunk_end_addr = next_chunk_free.end_addr();
        if new_end_addr > next_chunk_end_addr {
            return false;
        }

        // we can grow in place using the next free chunk.
        //
        // we now need to check if the space left in the next chunk after
        // growing (if there even is any space left) is large enough to store a
        // free chunk there.
        let space_left_at_end_of_next_free_chunk = next_chunk_end_addr - new_end_addr;
        if space_left_at_end_of_next_free_chunk > MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
            // the space left at the end of the next free chunk is enough to
            // store a free chunk, so we must create a new free chunk for it
            // while unlinking `next_chunk_free`, and then we can resize `chunk`
            // to include the space between it and the new free chunk.
            //
            // also note that there is no need to update the prev in use of the
            // next chunk of the next chunk, because its prev will be the new
            // free chunk that we're creating, and its prev in use bit is
            // already set to false.

            // create a new free chunk where the resized chunk ends, for the
            // space left there, no need to update the next chunk as explained above.
            //
            // this will also unlink `next_chunk_free` and put itself in place of it in the
            // freelist.
            let _ = FreeChunk::create_new_without_updating_next_chunk(
                new_end_addr,
                space_left_at_end_of_next_free_chunk - HEADER_SIZE,
                next_chunk_free.fd,
                next_chunk_free.ptr_to_fd_of_bk,
            );

            // resize `chunk` to the desired size. this will make `chunk` include all the
            // space up to where the new free chunk was just created.
            chunk.set_size(new_size);

            // we have successfully grew the chunk in place.
            true
        } else {
            // the space left at the end of the next free chunk is not enough to
            // store a free chunk, so just include that space when growing this
            // chunk.

            // now we should just unlink the next free chunk and increase the
            // size of the current chunk to include all of it.
            //
            // we must also update the prev in use bit of the next chunk of the
            // next chunk, because its prev is now `chunk`, which is in use,
            // while before calling this function its prev was
            // `next_chunk_free`, which is free.
            if let Some(next_chunk_of_next_chunk_addr) =
                next_chunk_free.header.next_chunk_addr(self.heap_end_addr)
            {
                // its prev is now `chunk`, which is used.
                Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_of_next_chunk_addr, true);
            }
            next_chunk_free.unlink();
            // make sure that it includes all of the next chunk
            chunk.set_size(next_chunk_end_addr - chunk.content_addr());

            // we have successfully grew the chunk in place.
            true
        }
    }

    /// Tries to grow the given chunk in place, to the given new size. Please
    /// note that this means that the alignment of the content of this chunk
    /// will stay exactly the same.
    ///
    /// Returns whether or not the operation was successful.
    ///
    /// # Safety
    ///
    /// `new_size` must be lower than the chunk's size, and must have been
    /// prepared.
    unsafe fn try_shrink_in_place(&mut self, chunk: UsedChunkRef, new_size: usize) -> bool {
        // calculate the new end addresss of the chunk.
        let new_end_addr = chunk.content_addr() + new_size;

        match chunk.next_chunk_if_free(self.heap_end_addr) {
            Some(next_chunk_free) => {
                // if the next chunk is free, we can just move it back and shrink `chunk`.
                // no need to update the next chunk, because it already knows that its prev
                // chunk is free.
                let _ = FreeChunk::create_new_without_updating_next_chunk(
                    new_end_addr,
                    // the size is calculated by subtracting the new start address of the free
                    // chunk from its current end address, and subtracting the header size because
                    // we only want the size of the content, excluding the header.
                    next_chunk_free.end_addr() - new_end_addr - HEADER_SIZE,
                    next_chunk_free.fd,
                    next_chunk_free.ptr_to_fd_of_bk,
                );

                // resize `chunk` to the desired size.
                chunk.set_size(new_size);

                // we have successfully shrinked the chunk in place.
                true
            }
            None => {
                // calculate how much space we have left at the end of this chunk after
                // shrinking.
                let space_left_at_end = chunk.0.size() - new_size;

                // check if we now have enough space at the end to create an entire free chunk.
                if space_left_at_end >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
                    // if we have enough space at the end, create a free chunk there.
                    //
                    // we must also update the next chunk of the free chunk that we create, because
                    // before creating this free chunk, its prev chunk was `chunk`, which is used,
                    // but now its prev is a free chunk.
                    let _ = FreeChunk::create_new_and_update_next_chunk(
                        new_end_addr,
                        space_left_at_end - HEADER_SIZE,
                        self.first_free_chunk(),
                        self.ptr_to_fd_of_fake_chunk(),
                        self.heap_end_addr,
                    );

                    // resize `chunk` to the desired size.
                    chunk.set_size(new_size);

                    true
                } else {
                    // if we don't have enough space to create a free chunk there, just leave it
                    // there. this prioritizes runtime efficiency over memory
                    // efficiency, because it prevents copying the entire memory, but it wastes a
                    // little bit of memory (up to 32 bytes).
                    true
                }
            }
        }
    }

    /// Allocates an unaligned chunk by splitting a start padding chunk from it,
    /// and then proceeding as usual.
    ///
    /// # Safety
    ///
    /// The provided size and align must have been prepared.
    unsafe fn alloc_unaligned(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        cur_chunk: FreeChunkRef,
    ) -> Option<NonNull<u8>> {
        // find an aligned start address which leaves enough space for a free chunk of
        // padding plus a header for the created chunk before the content chunk that is
        // returned to the user.
        let aligned_content_start_addr = align_up(
            cur_chunk.addr() + MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER + HEADER_SIZE,
            layout_align,
        );

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
    ///
    /// # Safety
    ///
    /// The provided size and align must have been prepared.
    unsafe fn alloc_unaligned_after_splitting_start_padding(
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
            if end_padding >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
                // if the end padding is large enough to hold a free chunk, create a chunk
                // there.
                //
                // this is safe because we checked that `end_padding` is big enough
                self.alloc_unaligned_after_splitting_start_padding_split_end_padding_chunk(
                    layout_size,
                    end_padding,
                    allocated_chunk_addr,
                    start_padding_chunk,
                )
            } else {
                // if the end padding is not large enough to hold a free chunk, consider it a
                // part of the allocated chunk. this is a little wasteful, but
                // it prevents us from returning `null` from the allocator even
                // when we have enough space.

                // this case can be considered the same as allocating without any end padding.
                self.alloc_unaligned_after_splitting_start_padding_no_end_padding(
                    allocated_chunk_addr,
                    allocated_chunk_size,
                )
            }
        } else {
            // if there is no end padding
            self.alloc_unaligned_after_splitting_start_padding_no_end_padding(
                allocated_chunk_addr,
                allocated_chunk_size,
            )
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
    ///  - the provided size must have been prepared.
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
    ///
    /// # Safety
    ///
    /// The provided size must have been prepared.
    unsafe fn alloc_aligned(
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
            if end_padding >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
                // if the end padding is large enough to hold a free chunk, create a chunk
                // there.
                Some(
                    // this is safe because we checked that `end_padding` is big enough
                    self.alloc_aligned_split_end_padding_chunk(layout_size, end_padding, cur_chunk),
                )
            } else {
                // if the end padding is not large enough to hold a free chunk, consider it a
                // part of the allocated chunk. this is a little wasteful, but
                // it prevents us from returning `null` from the allocator even
                // when we have enough space.
                //
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
    ///  - `end_padding` must be greater than or equal to
    ///    [`MIN_FREE_CHUNK_SIZE`].
    ///  - the provided size must have been prepared.
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
        //
        // also, the next chunk is the end padding chunk, and was just created as a free
        // chunk, and when creating a free chunk its prev in use bit is
        // automatically set to true, so no need to update it.
        //
        // also please note that if we tried to update the next chunk here it would
        // update the chunk *after* the end padding chunk and not the end padding chunk
        // itself, because we haven't yet updated the size of `cur_chunk`.
        let cur_chunk_as_used = cur_chunk.mark_as_used_without_updating_freelist_and_next_chunk();

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
    /// Creates an empty locked heap allocator without any heap memory region,
    /// which will always return null on allocation requests.
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
    /// The `SpinLockedAllocator` on which this was called must not be moved,
    /// and its address in memory must not change, otherwise undefined
    /// behaviour will occur. This is because the heap region now contains
    /// pointers to fields of this struct, and if this struct will move, the
    /// address of its fields will change, and those pointers will now be
    /// invalid.
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

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let mut allocator = self.0.lock();
        allocator.realloc(ptr, layout, new_size)
    }
}
