mod alignment;
mod chunks;
mod divisible_by_4_usize;

use core::{pin::Pin, ptr::NonNull};

use alignment::*;
use chunks::*;
use divisible_by_4_usize::*;

fn main() {}

pub const USIZE_ALIGNMENT: usize = core::mem::align_of::<usize>();
pub const USIZE_SIZE: usize = core::mem::size_of::<usize>();
pub const MIN_ALIGNMENT: usize = USIZE_ALIGNMENT;
pub const MIN_FREE_CHUNK_SIZE: usize = core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
pub const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

/// Chunk size must be divible by 4, even if `MIN_ALIGNMENT` is smaller than
/// 4, but if `MIN_ALIGNMENT` is bigger than 4 then size must be a multiple of
/// it.
const CHUNK_SIZE_ALIGNMENT: usize = if MIN_ALIGNMENT < 4 { 4 } else { MIN_ALIGNMENT };

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
            end_padding,
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
            end_padding,
            cur_chunk.fd(),
            cur_chunk.ptr_to_fd_of_bk(),
        );

        // this is safe because we already removed `cur_chunk` from the freelist, so
        // there's no need to update the freelist again.
        cur_chunk.mark_as_used_without_updating_freelist(self.heap_end_addr);

        // return a pointer to the allocated chunk
        NonNull::new_unchecked(cur_chunk.content_addr() as *mut u8)
    }
}

#[cfg(test)]
mod tests {
    use core::alloc::Layout;

    use super::*;

    static mut ALLOCATOR: Allocator = Allocator::empty();

    /// A guard that initializes the allocator with a region of memory on
    /// creation, and frees that memory when dropped.
    struct AllocatorInitGuard<const MEM_SIZE: usize> {
        addr: usize,
        layout: Layout,
    }
    impl<const MEM_SIZE: usize> AllocatorInitGuard<MEM_SIZE> {
        /// Initializes the heap allocator and returns a guard for it.
        fn init() -> Self {
            // allocate enough size, make sure to align the allocation to the alignment of
            // the heap allocator.
            let layout = Layout::from_size_align(MEM_SIZE, MIN_ALIGNMENT).unwrap();

            let addr = unsafe { std::alloc::alloc(layout) as usize };

            unsafe { ALLOCATOR.init(addr, MEM_SIZE) }

            Self { addr, layout }
        }

        /// Initializes the allocator and makes sure that calling alloc with an
        /// alignment greater than `MIN_ALIGNMENT` won't be aligned.
        ///
        /// Returns the guard, and the mem size of the memory region.
        fn init_unaligned() -> (Self, usize) {
            // allocate enough size, make sure to align the allocation to the alignment of
            // the heap allocator.
            let layout = Layout::from_size_align(MEM_SIZE, MIN_ALIGNMENT).unwrap();

            let raw_addr = unsafe { std::alloc::alloc(layout) as usize };

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

            unsafe { ALLOCATOR.init(addr, mem_size) }

            (Self { addr, layout }, mem_size)
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

        let _guard = AllocatorInitGuard::<MEM_SIZE>::init();

        // calculate the allocation size that will fit perfectly
        let perfect_fit = MEM_SIZE - HEADER_SIZE;

        // add 1 to make an allocation size that will not fit.
        let no_fit = perfect_fit + 1;

        let allocated = unsafe { ALLOCATOR.alloc(Layout::from_size_align(no_fit, 1).unwrap()) };

        assert!(allocated.is_null())
    }

    #[test]
    fn alloc_perfect_fit() {
        const MEM_SIZE: usize = USIZE_SIZE * 17;

        let guard = AllocatorInitGuard::<MEM_SIZE>::init();
        let addr = guard.addr();

        // calculate the allocation size that will fit perfectly
        let perfect_fit = MEM_SIZE - HEADER_SIZE;

        let allocated =
            unsafe { ALLOCATOR.alloc(Layout::from_size_align(perfect_fit, 1).unwrap()) };

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
    fn alloc_aligned_end_padding_not_large_enough_to_fit_chunk() {
        const MEM_SIZE: usize = USIZE_SIZE * 17;

        let guard = AllocatorInitGuard::<MEM_SIZE>::init();
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
            ALLOCATOR.alloc(Layout::from_size_align(size_with_minimal_end_padding, 1).unwrap())
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
    fn alloc_unaligned_not_enough_space_returns_null() {
        const MEM_SIZE: usize = USIZE_SIZE * 17;

        let (guard, mem_size) = AllocatorInitGuard::<MEM_SIZE>::init_unaligned();
        let addr = guard.addr();

        // an alignment that will cause the chunk to be unaligned.
        let alignment = MIN_ALIGNMENT * 2;

        // calculate the allocation size that will fit perfectly
        let perfect_fit = mem_size - HEADER_SIZE;

        // add 1 to make an allocation size that will not fit.
        let no_fit = perfect_fit + 1;

        let allocated =
            unsafe { ALLOCATOR.alloc(Layout::from_size_align(no_fit, alignment).unwrap()) };

        assert!(allocated.is_null())
    }

    #[test]
    fn alloc_unaligned_no_end_padding() {
        const MEM_SIZE: usize = USIZE_SIZE * 17;

        let (guard, mem_size) = AllocatorInitGuard::<MEM_SIZE>::init_unaligned();
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

        let allocated =
            unsafe { ALLOCATOR.alloc(Layout::from_size_align(perfect_fit, alignment).unwrap()) };

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
        assert_eq!(start_padding_chunk.ptr_to_fd_of_bk, unsafe {
            &mut ALLOCATOR.free_chunk as *mut _
        });

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
            unsafe { ALLOCATOR.free_chunk },
            Some(unsafe { NonNull::new_unchecked(addr as *mut _) })
        )
    }
}
