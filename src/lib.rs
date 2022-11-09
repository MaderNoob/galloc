#![no_std]
#![cfg_attr(
    feature = "allocator",
    feature(allocator_api, nonnull_slice_from_raw_parts, slice_ptr_get)
)]

//! This is a linked list allocator, inspired by the dlmalloc algorithm, to be
//! used in `no_std` environments such as operating system kernels. The overhead
//! for each allocation is a single `usize`. The implementation prioritizes
//! runtime efficiency over memory efficiency, but also provides very good
//! memory utilization. The allocator is heavily tested with test cases covering
//! almost all code paths; fuzzing is used to cover the rest.
//!
//! ## Usage
//!
//! Create a static allocator:
//!
//! ```ignore
//! use good_memory_allocator::SpinLockedAllocator;
//!
//! #[global_allocator]
//! static ALLOCATOR: SpinLockedAllocator = SpinLockedAllocator::empty();
//! ```
//!
//! Before using this allocator, you need to initialize it:
//!
//! ```ignore
//! pub fn init_heap() {
//!     unsafe {
//!         ALLOCATOR.init(heap_start, heap_size);
//!     }
//! }
//! ```
//!
//! ## `SMALLBINS_AMOUNT` and `ALIGNMENT_SUB_BINS_AMOUNT`.
//!
//! The allocator allows configuring the amount of smallbins and alignment
//! sub-bins that it uses. For those of you not familiar with smallbins, they
//! are data structures used by the allocator to keep track of free chunks. Each
//! smallbin is made up of multiple alignment sub-bins. The default amounts of
//! smallbins and alignment sub-bins used by the allocator are stored in their
//! respective constant [`DEFAULT_SMALLBINS_AMOUNT`] and
//! [`DEFAULT_ALIGNMENT_SUB_BINS_AMOUNT`].
//!
//! Increasing the amount of smallbins will improve runtime performance and
//! memory utilization, especially when you are making a lot of relatively small
//! allocation, but it will also increase the size of the [`Allocator`] struct.
//!
//! Increasing the amount of alignment sub-bins will will also improve runtime
//! performance and memory utilization, especially when you are making a lot of
//! allocations with relatively large alignments, but it will also increase the
//! size of the [`Allocator`] struct.
//! It is recommended to choose a value that is a power of 2 for the alignemnt
//! sub-bins amount, since that will improve the memory utilization of the
//! smallbins' memory.
//! The amount of alignment sub bins must be at least 2, otherwise you will get
//! a compilation error.
//!
//! If you are in a memory constrained environment, you might want to use lower
//! values for these constants, since the size of the [`Allocator`] struct using
//! the default values is relatively large.
//!
//! ## Features
//!
//! - **`spin`** (default): Provide a `SpinLockedAllocator` type that implements
//!   the `GlobalAlloc` trait by using a spinlock.
//! - **`allocator`**: Provides an implementation of the unstable `Allocator`
//!   trait for the `SpinLockedAllocator` type.

#[cfg(test)]
#[macro_use]
extern crate std;

mod alignment;
mod bins;
mod chunks;
mod divisible_by_4_usize;
mod smallest_type_which_has_at_least_n_bits;

#[cfg(test)]
mod tests;

use core::{alloc::Layout, ptr::NonNull};

use alignment::*;
use bins::SmallBins;
pub use bins::{DEFAULT_ALIGNMENT_SUB_BINS_AMOUNT, DEFAULT_SMALLBINS_AMOUNT};
use chunks::*;
use smallest_type_which_has_at_least_n_bits::{
    SmallestTypeWhichHasAtLeastNBitsStruct, SmallestTypeWhichHasAtLeastNBitsTrait,
};

const USIZE_ALIGNMENT: usize = core::mem::align_of::<usize>();
const USIZE_SIZE: usize = core::mem::size_of::<usize>();

// IMPORTANT:
// `MIN_ALIGNMENT` must be larger than 4, so that storing the size as a
// `DivisibleBy4Usize` is safe.
const MIN_ALIGNMENT: usize = if USIZE_ALIGNMENT < 8 {
    8
} else {
    USIZE_ALIGNMENT
};
const MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER: usize = core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

/// A linked list memory allocator.
///
/// This allocator allows configuring the amount of smallbins and alignment
/// sub-bins that it uses. For more information about this value, read the
/// crate's top level documentation.
#[derive(Debug)]
pub struct Allocator<
    const SMALLBINS_AMOUNT: usize = DEFAULT_SMALLBINS_AMOUNT,
    const ALIGNMENT_SUB_BINS_AMOUNT: usize = DEFAULT_ALIGNMENT_SUB_BINS_AMOUNT,
> where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    smallbins: SmallBins<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>,
    heap_end_addr: usize,
    fake_chunk_of_other_bin: FakeFreeChunk,
}
impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
    Allocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    /// Creates an empty heap allocator without any heap memory region, which
    /// will always return null on allocation requests.
    ///
    /// To intiialize this allocator, use the `init` method.
    pub const fn empty() -> Self {
        Self {
            heap_end_addr: 0,
            fake_chunk_of_other_bin: FakeFreeChunk {
                fd: None,
                ptr_to_fd_of_bk: core::ptr::null_mut(),
            },
            smallbins: SmallBins::new(),
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

        // make the fake chunk point to itself.
        self.fake_chunk_of_other_bin.fd = Some(self.fake_chunk_of_other_bin_ptr());
        self.fake_chunk_of_other_bin.ptr_to_fd_of_bk = self.ptr_to_fd_of_fake_chunk_of_other_bin();

        // create a free chunk for the entire heap.
        // no need to update the next chunk because there is no next chunk, this chunk
        // covers the entire heap.
        let chunk_size = aligned_size - HEADER_SIZE;
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            aligned_heap_start_addr,
            chunk_size,
            self,
        );

        // update the heap end address.
        self.heap_end_addr = aligned_heap_end_addr;
    }

    /// Returns a pointer to the fake chunk of the other bin.
    ///
    /// # Safety
    ///
    /// This chunk is missing the chunk header, so when using it as a free
    /// chunk, you must make sure that you never access its header.
    unsafe fn fake_chunk_of_other_bin_ptr(&self) -> FreeChunkPtr {
        self.fake_chunk_of_other_bin.free_chunk_ptr()
    }

    /// Returns a pointer to the first free chunk in the other bin, if any.
    fn first_free_chunk_in_other_bin(&self) -> Option<FreeChunkPtr> {
        let fd_of_fake_chunk = self.fake_chunk_of_other_bin.fd?;
        if fd_of_fake_chunk == unsafe { self.fake_chunk_of_other_bin_ptr() } {
            return None;
        }

        Some(fd_of_fake_chunk)
    }

    /// Returns a pointer to the fd of the fake chunk of the other bin.
    fn ptr_to_fd_of_fake_chunk_of_other_bin(&mut self) -> *mut Option<FreeChunkPtr> {
        &mut self.fake_chunk_of_other_bin.fd
    }

    /// Prepares an allocation size according to the requirements of
    /// the allocator. Returns the prepared size.
    fn prepare_size(size: usize) -> usize {
        unsafe {
            align_up(
                core::cmp::max(size, MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE),
                MIN_ALIGNMENT,
            )
        }
    }

    /// Returns fd and bk pointers for inserting a new free chunk to its
    /// matching bin.
    ///
    /// In case the chunk should be inserted into a smallbin, updates the
    /// smallbin's bitmap to indicate that it now contains that chunk.
    ///
    /// # Safety
    ///
    ///  - `chunk_size` must be the size of an actual chunk.
    ///  - After calling this function, the free chunk must be inserted using
    ///    the fd and bk pointers, otherwise the smallbins' bitmaps might be in
    ///    an invalid state.
    unsafe fn get_fd_and_bk_pointers_for_inserting_new_free_chunk(
        &mut self,
        chunk_size: usize,
        alignment_index_of_chunk_content_addr: usize,
    ) -> (Option<FreeChunkPtr>, *mut Option<FreeChunkPtr>) {
        // SAFETY: this is safe because `chunk_size` is the size of an actual chunk, so
        // it must have already been prepared.
        if let Some(smallbin_index) =
            SmallBins::<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>::smallbin_index(chunk_size)
        {
            self.smallbins
                .get_fd_and_bk_pointers_for_inserting_to_smallbin(
                    smallbin_index,
                    alignment_index_of_chunk_content_addr,
                )
        } else {
            // if this chunk does not fit in the smallbins, put it in the other bin
            self.get_fd_and_bk_pointers_for_inserting_new_free_chunk_in_other_bin(chunk_size)
        }
    }

    /// Returns fd and bk pointers for inserting a new free chunk to the
    /// other bin.
    fn get_fd_and_bk_pointers_for_inserting_new_free_chunk_in_other_bin(
        &mut self,
        chunk_size: usize,
    ) -> (Option<FreeChunkPtr>, *mut Option<FreeChunkPtr>) {
        match self.first_free_chunk_in_other_bin() {
            // if the other bin is not empty
            Some(mut first_free_chunk) => {
                // check if the given chunk size is bigger than the current first chunk,
                // and if so, put the given chunk at the start of the bin.
                //
                // otherwise if the given chunk is smaller than the current first chunk,
                // then put the given chunk at the end of the bin.
                if chunk_size > unsafe { first_free_chunk.as_mut() }.size() {
                    (
                        Some(first_free_chunk),
                        self.ptr_to_fd_of_fake_chunk_of_other_bin(),
                    )
                } else {
                    (
                        // SAFETY: the fake chunk will be used as the fd of some other chunk, but
                        // chunks never access the header of their fd, only their fd and bk, so
                        // this is safe.
                        Some(unsafe { self.fake_chunk_of_other_bin_ptr() }),
                        self.fake_chunk_of_other_bin.ptr_to_fd_of_bk,
                    )
                }
            }
            // if the other bin is empty, put this chunk as the first chunk in the bin.
            None => (
                // SAFETY: the fake chunk will be used as the fd of some other chunk, but chunks
                // never access the header of their fd, only their fd and bk, so this is safe.
                Some(unsafe { self.fake_chunk_of_other_bin_ptr() }),
                self.ptr_to_fd_of_fake_chunk_of_other_bin(),
            ),
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

        let alignment_index_if_size_is_smallbin_size =
            if SmallBins::<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>::is_smallbin_size(
                layout_size,
            ) {
                Some(
                    SmallBins::<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>::alignment_index(
                        layout_align,
                    ),
                )
            } else {
                None
            };

        // if the allocation size is the size of a smallbin, allocate from optimal
        // chunks from the smallbins.
        if let Some(alignment_index) = alignment_index_if_size_is_smallbin_size {
            if let Some(ptr) =
                self.alloc_from_optimal_chunk(layout_size, layout_align, alignment_index)
            {
                return ptr.as_ptr();
            }
        }

        if let Some(ptr) = self.alloc_from_other_bin(layout_size, layout_align) {
            return ptr.as_ptr();
        }

        // if the allocation size is the size of a smallbin, allocate from suboptimal
        // chunks from the smallbins.
        if let Some(alignment_index) = alignment_index_if_size_is_smallbin_size {
            if let Some(ptr) = self.alloc_from_aligned_suboptimal_chunks(
                layout_size,
                layout_align,
                alignment_index,
            ) {
                return ptr.as_ptr();
            }

            if let Some(ptr) = self.alloc_from_unaligned_suboptimal_chunks(
                layout_size,
                layout_align,
                alignment_index,
            ) {
                return ptr.as_ptr();
            }
        }

        core::ptr::null_mut()
    }

    /// Tries to allocate an optimal chunks for the given allocation
    /// requirements.
    ///
    /// # Safety
    ///
    ///  - The size and align must have been prepared.
    ///  - The size must be the size of a small bin.
    unsafe fn alloc_from_optimal_chunk(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        alignment_index: usize,
    ) -> Option<NonNull<u8>> {
        let mut optimal_chunk =
            self.smallbins
                .optimal_chunk(layout_size, layout_align, alignment_index)?;
        let chunk = optimal_chunk.as_mut();
        Some(self.alloc_aligned_no_end_padding(chunk))
    }

    /// Tries to allocate a chunk from the other bin for the given allocation
    /// requirements.
    ///
    /// # Safety
    ///
    /// The size and align must have been prepared.
    unsafe fn alloc_from_other_bin(
        &mut self,
        layout_size: usize,
        layout_align: usize,
    ) -> Option<NonNull<u8>> {
        // try to allocate from the other bin.
        let fake_chunk_of_other_bin_ptr = self.fake_chunk_of_other_bin_ptr();

        // the other bin is circular so the fd will never be `None`.
        let mut cur_chunk_ptr = self.fake_chunk_of_other_bin.fd.unwrap();

        loop {
            // if the current chunk is the fake chunk of the other bin, we reached the end
            // of the list.
            if cur_chunk_ptr == fake_chunk_of_other_bin_ptr {
                break;
            }
            let cur_chunk = cur_chunk_ptr.as_mut();

            // check if the chunk is large enough
            if cur_chunk.size() >= layout_size {
                if is_aligned(cur_chunk.content_addr(), layout_align) {
                    // the chunk is already aligned
                    //
                    // SAFETY: we know that the chunk is large enough
                    return Some(self.alloc_aligned(layout_size, cur_chunk_ptr.as_mut()));
                } else {
                    // the chunk is not aligned

                    // check if we can use the current chunk for an unaligned allocation.
                    let cur_chunk_ref = cur_chunk_ptr.as_mut();
                    if let Some(aligned_start_addr) =
                        self.can_alloc_unaligned(layout_size, layout_align, cur_chunk_ref)
                    {
                        return Some(self.alloc_unaligned(
                            layout_size,
                            cur_chunk_ptr.as_mut(),
                            aligned_start_addr,
                        ));
                    }
                }
            }

            // the other bin is circular so the fd will never be `None`.
            cur_chunk_ptr = cur_chunk.fd().unwrap();
        }

        None
    }

    /// Tries to allocate a chunk from the aligned sub-optimal chunks for the
    /// given allocation requirements.
    ///
    /// This strategy should be called after trying the other bin.
    ///
    /// # Safety
    ///
    ///  - The size and align must have been prepared.
    ///  - The size must be the size of a small bin.
    unsafe fn alloc_from_aligned_suboptimal_chunks(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        alignment_index: usize,
    ) -> Option<NonNull<u8>> {
        let mut aligned_suboptimal_chunk =
            self.smallbins
                .aligned_suboptimal_chunk(layout_size, layout_align, alignment_index)?;

        // the aligned suboptimal chunks are aligned, but are also large enough so that
        // an end padding chunk must be created.
        Some(self.alloc_aligned_split_end_padding_chunk(
            layout_size,
            aligned_suboptimal_chunk.end_padding,
            aligned_suboptimal_chunk.chunk_ptr.as_mut(),
        ))
    }

    /// Tries to allocate a chunk from the unaligned sub-optimal chunks for the
    /// given allocation requirements.
    ///
    /// This strategy should be called after trying to find an aligned
    /// suboptimal chunk.
    ///
    /// # Safety
    ///
    ///  - The size and align must have been prepared.
    ///  - The size must be the size of a small bin.
    unsafe fn alloc_from_unaligned_suboptimal_chunks(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        alignment_index: usize,
    ) -> Option<NonNull<u8>> {
        let (allocated_chunk, aligned_start_addr) = {
            let mut chunks_that_can_allocate_unaligned = self
                .smallbins
                .unaligned_suboptimal_chunks(layout_size, layout_align, alignment_index)?
                .filter_map(|mut chunk_ptr| {
                    // for each unaligned suboptimal chunk, check if it can fit the allocation
                    // requirements.

                    let chunk = chunk_ptr.as_mut();

                    if let Some(aligned_start_addr) =
                        self.can_alloc_unaligned(layout_size, layout_align, chunk_ptr.as_mut())
                    {
                        Some((chunk, aligned_start_addr))
                    } else {
                        None
                    }
                });

            // get the first chunk which can fit the allocation requirements.
            chunks_that_can_allocate_unaligned.next()?
        };

        Some(self.alloc_unaligned(layout_size, allocated_chunk, aligned_start_addr))
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
                //
                // SAFETY: the provided chunk size is the size of an actual chunk, and the
                // alignment returned from `Chunk::alignment` is always a power of 2.
                let (fd, bk) = self.get_fd_and_bk_pointers_for_inserting_new_free_chunk(
                    chunk.0.size(),
                    SmallBins::<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>::alignment_index_of_chunk_content_addr(
                        chunk.content_addr(),
                    ),
                );
                let _ = chunk.mark_as_free(fd, bk, self.heap_end_addr);
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

                // unlink the next free chunk, because we include its memory region in `chunk`.
                next_chunk_free.unlink(&mut self.smallbins);

                // mark the chunk as free.
                //
                // no need to update the next chunk, because it already knows that its prev is
                // free, because before marking `chunk` as free, the next chunk's previous chunk
                // was `next_chunk_free`.
                let (fd, bk) = self.get_fd_and_bk_pointers_for_inserting_new_free_chunk(
                    chunk.0.size(),
                    SmallBins::<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>::alignment_index_of_chunk_content_addr(
                        chunk.content_addr(),
                    ),
                );
                let _ = chunk.mark_as_free_without_updating_next_chunk(fd, bk);
            }
            (Some(prev_chunk_free), None) => {
                // for this case, just resize the prev chunk to consolidate it with the current
                // chunk. in other words, make it large enough so that it includes the entire
                // current chunk.
                //
                // the resized prev chunk should include itself, the current chunk's header, and
                // the current chunk's content.
                prev_chunk_free.set_size_and_update_bin(
                    prev_chunk_free.size() + HEADER_SIZE + chunk.0.size(),
                    self,
                );

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
                next_chunk_free.unlink(&mut self.smallbins);

                // the prev chunk will now include the following:
                // - itself
                // - the current chunk's header
                // - the current chunk's content
                // - the next chunk's header
                // - the next chunk's content
                prev_chunk_free.set_size_and_update_bin(
                    prev_chunk_free.size()
                        + HEADER_SIZE
                        + chunk.0.size()
                        + HEADER_SIZE
                        + next_chunk_free.size(),
                    self,
                );

                // also, there's no need to update the next chunk of
                // `next_free_chunk`, because that chunk already knows that its
                // prev is free.
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

        // if reallocation in place fails, realloc a new region for and copy the data
        // there.
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        self.realloc_new_region(ptr, layout, new_layout)
    }

    /// Resizes an allocation previously returned from `alloc` or `realloc`, by
    /// allocating a new memory region for it, copying the memory, and
    /// dealloacting the provided pointer.
    unsafe fn realloc_new_region(
        &mut self,
        ptr: *mut u8,
        old_layout: Layout,
        new_layout: Layout,
    ) -> *mut u8 {
        // SAFETY: the caller must ensure that `new_layout` is greater than zero.
        let new_ptr = self.alloc(new_layout);
        if !new_ptr.is_null() {
            // SAFETY: the previously allocated block cannot overlap the newly allocated
            // block. The safety contract for `dealloc` must be upheld by the
            // caller.
            core::ptr::copy_nonoverlapping(
                ptr,
                new_ptr,
                core::cmp::min(old_layout.size(), new_layout.size()),
            );
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
        if new_size > previously_requested_size {
            // the user requested to grow his allocation.
            self.try_grow_in_place(chunk, new_size)
        } else {
            // the user requested to shrink his allocation, shrink in place.
            self.shrink_in_place(chunk, new_size);
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
    /// `new_size` must have been prepared.
    unsafe fn try_grow_in_place(&mut self, chunk: UsedChunkRef, new_size: usize) -> bool {
        // sometimes chunks are bigger than their content due to end padding that's not
        // big enough to fit a chunk, check if the chunk is already large enough for the
        // new size.
        if chunk.0.size() >= new_size {
            // if the chunk is already large enough, no need to do anything.
            return true;
        }

        // to grow this chunk in place we need its next chunk to be free, make sure that
        // the next chunk is free.
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
        // adjacent free chunks, and the next chunk alone is not enough.
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
            // store a free chunk, so we must move the next free chunk forward to the new
            // end address and resize it accordingly, and then we can resize `chunk`
            // to include the space between it and the new free chunk.
            //
            // also note that there is no need to update the prev in use of the
            // next chunk of the next chunk, because its prev will be the new
            // free chunk that we're creating, and its prev in use bit is
            // already set to false.

            next_chunk_free.move_and_resize_chunk_without_updating_next_chunk(
                new_end_addr,
                space_left_at_end_of_next_free_chunk - HEADER_SIZE,
                self,
            );

            // resize `chunk` to the desired size. this will make `chunk` include all the
            // space up to where the new free chunk was just created.
            chunk.set_size(new_size);
        } else {
            // the space left at the end of the next free chunk is not enough to
            // store a free chunk, so just include that space when growing this
            // chunk.

            // now we should just unlink the next free chunk and increase the
            // size of the current chunk to include all of it.
            //
            // we must also update the prev in use bit of the next chunk of the
            // next chunk, because its prev is now `chunk`, which is in use,
            // while before calling this function its prev was `next_chunk_free`, which is
            // free.
            if let Some(next_chunk_of_next_chunk_addr) =
                next_chunk_free.header.next_chunk_addr(self.heap_end_addr)
            {
                // its prev is now `chunk`, which is used.
                Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_of_next_chunk_addr, true);
            }

            next_chunk_free.unlink(&mut self.smallbins);

            // make sure that it includes all of the next chunk
            chunk.set_size(next_chunk_end_addr - chunk.content_addr());
        }

        // we have successfully grew the chunk in place.
        true
    }

    /// Shrinks the given chunk in place, to the given new size. Please note
    /// that this means that the alignment of the content of this chunk will
    /// stay exactly the same.
    ///
    /// # Safety
    ///
    /// `new_size` must be lower than the chunk's size, and must have been
    /// prepared.
    unsafe fn shrink_in_place(&mut self, chunk: UsedChunkRef, new_size: usize) {
        // calculate the new end addresss of the chunk.
        let new_end_addr = chunk.content_addr() + new_size;

        match chunk.next_chunk_if_free(self.heap_end_addr) {
            Some(next_chunk_free) => {
                // we can just move the next chunk backwards to include the extra space that's
                // left due to shrinking in place.
                next_chunk_free.move_and_resize_chunk_without_updating_next_chunk(
                    new_end_addr,
                    // the size is calculated by subtracting the new start address of the free
                    // chunk from its current end address, and subtracting the header size because
                    // we only want the size of the content, excluding the header.
                    next_chunk_free.end_addr() - new_end_addr - HEADER_SIZE,
                    self,
                );

                // resize `chunk` to the desired size.
                chunk.set_size(new_size);
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
                    let end_padding_chunk_size = space_left_at_end - HEADER_SIZE;

                    let _ = FreeChunk::create_new_and_update_next_chunk(
                        // the end padding chunk starts right where the new end address is, and the
                        // content comes right after the header.
                        new_end_addr,
                        end_padding_chunk_size,
                        self,
                    );

                    // resize `chunk` to the desired size.
                    chunk.set_size(new_size);
                } else {
                    // if we don't have enough space to create a free chunk
                    // there, just leave it there. this prioritizes runtime
                    // efficiency over memory efficiency, because it prevents
                    // copying the entire memory, but it wastes a little bit of
                    // memory (up to 32 bytes).
                }
            }
        }
    }

    /// Checks if the given chunk can be used to allocate the given allocation
    /// requirements, knowing that the chunk's content start address is not well
    /// aligned to the required alignment.
    ///
    /// If the chunk can be used for the allocation, returns the aligned start
    /// address of the allocated chunk, which can then be used to allocate the
    /// chunk by calling `alloc_unaligned`. Otherwise, if the chunk can't be
    /// used, returns `None`.
    ///
    /// # Safety
    ///
    /// The size and alignment must have been prepared.
    unsafe fn can_alloc_unaligned(
        &self,
        layout_size: usize,
        layout_align: usize,
        chunk: FreeChunkRef,
    ) -> Option<usize> {
        // find an aligned start address starting from the end of the chunk which leaves
        // enough space for the content to fit.
        let aligned_content_start_addr = align_down(chunk.end_addr() - layout_size, layout_align);

        let aligned_start_addr = aligned_content_start_addr - HEADER_SIZE;

        // make sure that after aligning the start address, there is enough space left
        // at the start of `cur_chunk` to store a free chunk there.
        //
        // note that we must store a chunk there because there's no way that the
        // `aligned_start_addr` fits exactly into `cur_chunk`, otherwise alloc aligned
        // would have been called, so there must be space left at the start.
        let space_left_at_start = aligned_start_addr.saturating_sub(chunk.addr());
        if space_left_at_start < MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
            return None;
        }

        Some(aligned_start_addr)
    }

    /// Allocates an unaligned chunk by splitting a start padding chunk from it,
    /// and then proceeding as usual.
    ///
    /// # Safety
    ///
    ///  - The provided size and align must have been prepared.
    ///  - The provided `aligned_start_addr` must have been returned from a call
    ///    to `can_alloc_unaligned` with the same parameters given to this
    ///    function call.
    unsafe fn alloc_unaligned(
        &mut self,
        layout_size: usize,
        chunk: FreeChunkRef,
        aligned_start_addr: usize,
    ) -> NonNull<u8> {
        let aligned_content_start_addr = aligned_start_addr + HEADER_SIZE;

        // calculate the size left from the aligned start addr to the end of the chunk.
        let left_size = chunk.end_addr().saturating_sub(aligned_content_start_addr);

        // shrink the current chunk to leave some space for the new aligned allocated
        // chunk.
        let cur_chunk_new_size = aligned_start_addr - chunk.content_addr();
        chunk.set_size_and_update_bin(cur_chunk_new_size, self);

        self.alloc_unaligned_after_splitting_start_padding(
            layout_size,
            aligned_start_addr,
            left_size,
        )
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
    ) -> NonNull<u8> {
        // check if we need any end padding, and if that padding is large enough to
        // store an entire free chunk there.
        let end_padding = allocated_chunk_size - layout_size;
        if end_padding >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
            // if the end padding is large enough to hold a free chunk, create a chunk
            // there and allocate the rest.
            //
            // this is safe because we checked that `end_padding` is big enough
            self.alloc_unaligned_after_splitting_start_padding_split_end_padding_chunk(
                layout_size,
                end_padding,
                allocated_chunk_addr,
            )
        } else {
            // if there is no end padding, or the end padding is not large enough to store
            // an entire free chunk there, just include it in the allocated chunk instead of
            // splitting an end padding chunk for it.
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
    ///  - `allocated_chunk_size` must be aligned.
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
    ///    [`MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER`].
    ///  - `allocated_chunk_addr` must be a valid non-null memory address.
    ///  - the range of memory
    ///    `allocated_chunk_addr..allocated_chunk_addr+allocated_chunk_size`
    ///    must be valid and must not be used by any other chunk.
    ///  - the provided size must have been prepared.
    unsafe fn alloc_unaligned_after_splitting_start_padding_split_end_padding_chunk(
        &mut self,
        layout_size: usize,
        end_padding: usize,
        allocated_chunk_addr: usize,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let end_padding_chunk_start_addr = allocated_chunk_addr + HEADER_SIZE + layout_size;

        // create an end padding chunk.
        //
        // there is no need to update the next chunk because it's prev in use bit is
        // already set to false, as it should be.
        let end_padding_chunk_size = end_padding - HEADER_SIZE;
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            end_padding_chunk_start_addr,
            end_padding_chunk_size,
            self,
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
    /// The provided size must have been prepared, and the provided chunk must
    /// be large enough to fit the allocation.
    unsafe fn alloc_aligned(&mut self, layout_size: usize, chunk: FreeChunkRef) -> NonNull<u8> {
        let cur_chunk_size = chunk.size();

        // check if we need any end padding, and if that end padding is large enough to
        // store an entire free chunk there.
        let end_padding = cur_chunk_size - layout_size;
        if end_padding >= MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER {
            // if the end padding is large enough to hold a free chunk, create a chunk
            // there.
            //
            // this is safe because we checked that `end_padding` is big enough
            self.alloc_aligned_split_end_padding_chunk(layout_size, end_padding, chunk)
        } else {
            // if there is no end padding, or the end padding is not large enough to store
            // an entire free chunk there, consider the end padding a part of the allocated
            // chunk.
            self.alloc_aligned_no_end_padding(chunk)
        }
    }

    /// Allocates an aligned chunk without any end padding.
    fn alloc_aligned_no_end_padding(&mut self, chunk: FreeChunkRef) -> NonNull<u8> {
        // mark the chunk as used and make the necessary updates
        chunk.mark_as_used_unlink(self.heap_end_addr, &mut self.smallbins);

        // retrun the chunk to the user
        unsafe { NonNull::new_unchecked(chunk.content_addr() as *mut u8) }
    }

    /// Allocates the given aligned chunk and splits an end padding chunk from
    /// it.
    ///
    /// # Safety
    ///
    ///  - `end_padding` must be greater than or equal to
    ///    [`MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER`].
    ///  - the provided size must have been prepared.
    unsafe fn alloc_aligned_split_end_padding_chunk(
        &mut self,
        layout_size: usize,
        end_padding: usize,
        chunk: FreeChunkRef,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let end_padding_chunk_start_addr = chunk.content_addr() + layout_size;

        // unlink the current chunk and mark it as used.
        //
        // SAFETY: the next chunk is the end padding chunk, and will soon be created as
        // a free chunk, and when creating a free chunk its prev in use bit is
        // automatically set to true, so no need to update it.
        //
        // also please note that if we tried to update the next chunk here it would
        // update the chunk *after* the end padding chunk and not the end padding chunk
        // itself, because we haven't yet updated the size of `cur_chunk`.
        chunk.unlink(&mut self.smallbins);
        let cur_chunk_as_used = chunk.mark_as_used_without_updating_freelist_and_next_chunk();

        // create a free chunk for the end padding.
        //
        // there is no need to update the next chunk because it's prev in use bit is
        // already set to false, as it should be.
        let end_padding_chunk_size = end_padding - HEADER_SIZE;
        let _ = FreeChunk::create_new_without_updating_next_chunk(
            end_padding_chunk_start_addr,
            end_padding_chunk_size,
            self,
        );

        // shrink cur chunk to only include the content and not the end padding.
        cur_chunk_as_used.set_size(layout_size);

        // return a pointer to the allocated chunk
        NonNull::new_unchecked(chunk.content_addr() as *mut u8)
    }
}

unsafe impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize> Send
    for Allocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
}

/// A spin locked memory allocator that can be used as the global allocator.
#[cfg(feature = "spin")]
pub struct SpinLockedAllocator<
    const SMALLBINS_AMOUNT: usize = DEFAULT_SMALLBINS_AMOUNT,
    const ALIGNMENT_SUB_BINS_AMOUNT: usize = DEFAULT_ALIGNMENT_SUB_BINS_AMOUNT,
>(spin::Mutex<Allocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>>)
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait;

#[cfg(feature = "spin")]
impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
    SpinLockedAllocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
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

    /// Checks if the heap memory region was already initialized by calling init.
    pub fn was_initialized(&self) -> bool {
        let allocator = self.0.lock();
        allocator.was_initialized()
    }
}

#[cfg(feature = "spin")]
unsafe impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
    core::alloc::GlobalAlloc for SpinLockedAllocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
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

#[cfg(feature = "allocator")]
unsafe impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
    core::alloc::Allocator for SpinLockedAllocator<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let mut allocator = self.0.lock();

        let ptr =
            NonNull::new(unsafe { allocator.alloc(layout) }).ok_or(core::alloc::AllocError)?;

        Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
        let mut allocator = self.0.lock();
        allocator.dealloc(ptr.as_ptr());
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let mut allocator = self.0.lock();
        let chunk_content_addr = ptr.as_ptr() as usize;
        if is_aligned(chunk_content_addr, new_layout.align()) {
            let chunk = UsedChunk::from_addr(chunk_content_addr - HEADER_SIZE);
            allocator.shrink_in_place(chunk, new_layout.size());

            return Ok(NonNull::slice_from_raw_parts(ptr, new_layout.size()));
        }

        // we can't shrink in place, so realloc a new region and copy the data there.
        let ptr = NonNull::new(allocator.realloc_new_region(ptr.as_ptr(), old_layout, new_layout))
            .ok_or(core::alloc::AllocError)?;

        Ok(NonNull::slice_from_raw_parts(ptr, new_layout.size()))
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let mut allocator = self.0.lock();
        let chunk_content_addr = ptr.as_ptr() as usize;
        if is_aligned(chunk_content_addr, new_layout.align()) {
            let chunk = UsedChunk::from_addr(chunk_content_addr - HEADER_SIZE);
            if allocator.try_grow_in_place(chunk, new_layout.size()) {
                return Ok(NonNull::slice_from_raw_parts(ptr, new_layout.size()));
            }
        }
        // we can't grow in place, so realloc a new region and copy the data there.
        let ptr = NonNull::new(allocator.realloc_new_region(ptr.as_ptr(), old_layout, new_layout))
            .ok_or(core::alloc::AllocError)?;

        Ok(NonNull::slice_from_raw_parts(ptr, new_layout.size()))
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, core::alloc::AllocError> {
        let result = self.grow(ptr, old_layout, new_layout)?;
        let ptr = result.as_mut_ptr() as *mut u8;
        ptr.add(old_layout.size())
            .write_bytes(0, new_layout.size() - old_layout.size());

        Ok(result)
    }
}
