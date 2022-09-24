use core::ptr::NonNull;

fn main() {}

const USIZE_ALIGNMENT: usize = core::mem::align_of::<usize>();
const USIZE_SIZE: usize = core::mem::size_of::<usize>();
const MIN_ALIGNMENT: usize = USIZE_ALIGNMENT;
const MIN_FREE_CHUNK_SIZE: usize = core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

/// Chunk size must be divible by 4, even if `MIN_ALIGNMENT` is smaller than
/// 4, but if `MIN_ALIGNMENT` is bigger than 4 then size must be a multiple of
/// it.
const CHUNK_SIZE_ALIGNMENT: usize = if MIN_ALIGNMENT < 4 { 4 } else { MIN_ALIGNMENT };

pub struct Allocator {
    heap_region: HeapRegion,
    free_chunk: Option<FreeChunkPtr>,
}
impl Allocator {
    fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        let layout_size = unsafe {
            align_up(
                core::cmp::max(layout.size(), 2 * USIZE_SIZE),
                CHUNK_SIZE_ALIGNMENT,
            )
        };
        let layout_align = core::cmp::max(layout.align(), MIN_ALIGNMENT);

        let cur_chunk_ref_from_back = &mut self.free_chunk;
        while let Some(cur_chunk_ptr) = cur_chunk_ref_from_back {
            let cur_chunk = unsafe { cur_chunk_ptr.as_mut() };
            // if the chunk is not aligned, fix the alignment
            if unsafe { is_aligned(cur_chunk.header.content_addr(), layout_align) } {
                // already aligned
                if let Some(ptr) =
                    self.heap_region
                        .alloc_aligned(layout_size, cur_chunk, cur_chunk_ref_from_back)
                {
                    return ptr.as_ptr();
                }
            } else {
                if let Some(ptr) =
                    self.heap_region
                        .alloc_unaligned(layout_size, layout_align, cur_chunk)
                {
                    return ptr.as_ptr();
                }
            }
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
                cur_chunk.header.addr() + MIN_FREE_CHUNK_SIZE + HEADER_SIZE,
                layout_align,
            )
        };
        let aligned_start_addr = aligned_content_start_addr - HEADER_SIZE;

        // calculate the size left from the aligned start addr to the end of the chunk.
        let left_size = cur_chunk
            .header
            .end_addr()
            .saturating_sub(aligned_content_start_addr);

        if left_size < layout_size {
            // chunk is not big enough
            return None;
        }

        // shrink the current chunk to leave some space for the new aligned allocated
        // chunk.
        let cur_chunk_new_size = aligned_start_addr - cur_chunk.header.content_addr();
        cur_chunk.set_size(cur_chunk_new_size);

        todo!()
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
                        allocated_chunk_size,
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
        // third argument is the `prev_in_use` bit of the created chunk. the chunk
        // before the allocated chunk is the start padding chunk, which is not in use,
        // thus the third argument is `false`.
        let chunk = unsafe {
            UsedChunk::create_new_and_update_next_chunk(
                allocated_chunk_addr,
                allocated_chunk_size,
                false,
                self.heap_end_addr,
            )
        };

        unsafe { NonNull::new_unchecked(chunk as *mut _ as *mut u8) }
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
        allocated_chunk_size: usize,
        start_padding_chunk: FreeChunkRef,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let allocated_chunk_end_addr = allocated_chunk_addr + HEADER_SIZE + layout_size;

        // this unsafe block created an end padding chunk and links it to the linked
        // list of free chunks.
        unsafe {
            // this new chunk will be put between the start padding chunk and its fd chunk,
            // so it should point to the fd of the start padding chunk.
            let end_padding_chunk = FreeChunk::create_new(
                allocated_chunk_end_addr,
                end_padding,
                start_padding_chunk.fd,
            );

            // there is no need to update the next chunk because it's prev in use bit is
            // already set to false, as it should be.

            // we must now make sure that some free chunk points to the created end padding
            // chunk, to make sure that it's part of the linked list.
            // we do that by making the start padding chunk point to this chunk.
            start_padding_chunk.fd = Some(end_padding_chunk);
        };

        // we must now create a used chunk for the allocated chunk.
        // note that there is no need to update the next chunk that its prev is in use,
        // because the next chunk was created using `FreeChunk::create_new`, which
        // automatically sets the prev in use flag to true.
        //
        // also, the prev chunk before the new created chunk is the start padding chunk,
        // which is not in use, so the third argument is `false`.
        let allocated_chunk =
            UsedChunk::create_new(allocated_chunk_addr, allocated_chunk_size, false);

        NonNull::new_unchecked(allocated_chunk as *mut _ as *mut u8)
    }

    /// Allocates a chunk that is already aligned to the desired alignment of
    /// the content.
    fn alloc_aligned(
        &mut self,
        layout_size: usize,
        cur_chunk: FreeChunkRef,
        cur_chunk_ref_from_back: &mut Option<FreeChunkPtr>,
    ) -> Option<NonNull<u8>> {
        let cur_chunk_size = cur_chunk.header.size();
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
                    self.alloc_aligned_split_end_padding_chunk(
                        layout_size,
                        end_padding,
                        cur_chunk,
                        cur_chunk_ref_from_back,
                    )
                })
            } else {
                // if the end padding is not large enough to hold a free chunk, consider it a
                // part of the allocated chunk. this is a little wasteful, but
                // it prevents us from returning `null` from the allocator even
                // when we have enough space.

                // this case can be considered the same as allocating without any end padding.
                Some(self.alloc_aligned_no_end_padding(cur_chunk, cur_chunk_ref_from_back))
            }
        } else {
            // if there is no end padding
            Some(self.alloc_aligned_no_end_padding(cur_chunk, cur_chunk_ref_from_back))
        }
    }

    /// Allocates an aligned chunk without any end padding.
    fn alloc_aligned_no_end_padding(
        &mut self,
        cur_chunk: FreeChunkRef,
        cur_chunk_ref_from_back: &mut Option<FreeChunkPtr>,
    ) -> NonNull<u8> {
        // mark the chunk as used and make the necessary updates
        cur_chunk.mark_as_used_unlink(cur_chunk_ref_from_back, self.heap_end_addr);

        // retrun the chunk to the user
        unsafe { NonNull::new_unchecked(cur_chunk as *mut _ as *mut u8) }
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
        cur_chunk_ref_from_back: &mut Option<FreeChunkPtr>,
    ) -> NonNull<u8> {
        // the end address of the allocated chunk that will be returned to the user.
        // this is also the start address of the end padding chunk.
        let allocated_chunk_end_addr = cur_chunk.header.content_addr() + layout_size;

        // this unsafe block splits an end padding chunk from the current chunk and
        // marks it as used. it returns a reference to `cur_chunk` but as a
        // `UsedChunkRef`.
        let allocated_chunk = unsafe {
            // this new chunk will be put inside the linked list of free chunks in place
            // of the current chunk, so its `fd` should be the `fd` of the current chunk.
            let end_padding_chunk =
                FreeChunk::create_new(allocated_chunk_end_addr, end_padding, cur_chunk.fd);

            // there is no need to update the next chunk because it's prev in use bit is
            // already set to false, as it should be.

            // we must now make sure that some free chunk points to the created end padding
            // chunk, to make sure that it's part of the linked list.
            // we can do that by marking the current chunk as used, and placing the end
            // padding chunk in place of it.
            cur_chunk.mark_as_used(
                cur_chunk_ref_from_back,
                Some(end_padding_chunk),
                self.heap_end_addr,
            )
        };

        NonNull::new_unchecked(allocated_chunk as *mut _ as *mut u8)
    }
}

#[repr(transparent)]
pub struct Chunk(DivisbleBy4Usize);

#[repr(transparent)]
pub struct UsedChunk(Chunk);

#[repr(C)]
pub struct FreeChunk {
    header: Chunk,
    fd: Option<FreeChunkPtr>,
}

pub type FreeChunkRef = &'static mut FreeChunk;
pub type FreeChunkPtr = NonNull<FreeChunk>;
pub type UsedChunkRef = &'static mut UsedChunk;

pub enum ChunkRef {
    Used(UsedChunkRef),
    Free(FreeChunkRef),
}

impl Chunk {
    /// Returns a [`ChunkRef`] for the chunk pointed to by the given pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk.
    pub unsafe fn from_addr(addr: usize) -> ChunkRef {
        let chunk = &mut *(addr as *mut Chunk);
        if chunk.is_free() {
            ChunkRef::Free(core::mem::transmute(chunk))
        } else {
            ChunkRef::Used(core::mem::transmute(chunk))
        }
    }

    /// Sets the `prev_in_use` flag of the chunk at the given address to the
    /// given value.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk.
    pub unsafe fn set_prev_in_use_for_chunk_with_addr(addr: usize, prev_in_use: bool) {
        let chunk = &mut *(addr as *mut Chunk);
        chunk.set_prev_in_use(prev_in_use)
    }

    /// Creates a new chunk header, if the size is divisible by 4.
    fn new(size: usize, is_free: bool, prev_in_use: bool) -> Option<Self> {
        DivisbleBy4Usize::new(size, is_free, prev_in_use).map(Self)
    }

    /// Creates a new chunk header.
    ///
    /// # Safety
    ///
    /// `size` must be aligned to `CHUNK_SIZE_ALIGNMENT`.
    unsafe fn new_unchecked(size: usize, is_free: bool, prev_in_use: bool) -> Self {
        Self(DivisbleBy4Usize::new_unchecked(size, is_free, prev_in_use))
    }

    /// The size of the chunk.
    fn size(&self) -> usize {
        self.0.value()
    }

    /// Sets the size of the chunk to the given value. The size must be aligned
    /// to `CHUNK_SIZE_ALIGNMENT`.
    ///
    /// # Safety
    ///
    /// Panics if the new size is not divisble by 4.
    fn set_size(&mut self, new_size: usize) {
        self.0.set_value(new_size);
    }

    /// Is this chunk free?
    fn is_free(&self) -> bool {
        self.0.additional_bit1()
    }

    /// Sets whether this chunk is considered free or not.
    fn set_is_free(&mut self, is_free: bool) {
        self.0.set_additional_bit1(is_free)
    }

    /// Is the previous chunk free?
    fn prev_in_use(&self) -> bool {
        self.0.additional_bit2()
    }

    /// Sets whether the previous chunk is considered free or not.
    fn set_prev_in_use(&mut self, prev_in_use: bool) {
        self.0.set_additional_bit2(prev_in_use)
    }

    /// The address where this chunk starts.
    fn addr(&self) -> usize {
        self as *const _ as usize
    }

    /// The address where the content of this chunk starts.
    fn content_addr(&self) -> usize {
        self as *const _ as usize + HEADER_SIZE
    }

    /// The address where this chunk ends.
    fn end_addr(&self) -> usize {
        self as *const _ as usize + self.size()
    }

    /// Checks if this chunk is the last chunk.
    fn is_last_chunk(&self, heap_end_addr: usize) -> bool {
        self.end_addr() == heap_end_addr
    }

    /// Returns the address of the next chunk in memory, if the current chunk is
    /// not the last chunk.
    fn next_chunk_addr(&self, heap_end_addr: usize) -> Option<usize> {
        let end = self.end_addr();
        if end == heap_end_addr {
            return None;
        }
        Some(end)
    }
}

impl UsedChunk {
    /// Returns a [`UsedChunkRef`] for the chunk pointed to by the given
    /// pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk that is used.
    pub unsafe fn from_addr(addr: usize) -> UsedChunkRef {
        &mut *(addr as *mut UsedChunk)
    }

    /// Creates a new used chunk at the given address, with the given size.
    ///
    /// # Safety
    ///
    ///  - `addr` must be a valid non-null memory address which is not used by
    ///    any other chunk.
    ///  - `size` must be aligned to `CHUNK_SIZE_ALIGNMENT`.
    ///  - The chunk's next chunk, if any, must be updated that its previous
    ///    chunk is now in use.
    pub unsafe fn create_new(addr: usize, size: usize, prev_in_use: bool) -> UsedChunkRef {
        let ptr = addr as *mut UsedChunk;

        // write the chunk header and content
        *ptr = UsedChunk(Chunk::new_unchecked(size, false, prev_in_use));

        &mut *ptr
    }

    /// Creates a new used chunk at the given address, with the given size, and
    /// updates its next chunk, if any, that its prev chunk is now used.
    ///
    /// # Safety
    ///
    ///  - `addr` must be a valid non-null memory address which is not used by
    ///    any other chunk.
    ///  - `size` must be aligned to `CHUNK_SIZE_ALIGNMENT`.
    pub unsafe fn create_new_and_update_next_chunk(
        addr: usize,
        size: usize,
        prev_in_use: bool,
        heap_end_addr: usize,
    ) -> UsedChunkRef {
        // create a new used chunk
        let chunk = UsedChunk::create_new(addr, size, prev_in_use);

        // update the next chunk
        if let Some(next_chunk_addr) = chunk.0.next_chunk_addr(heap_end_addr) {
            Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_addr, true)
        }

        // return the created chunk
        chunk
    }
}

impl FreeChunk {
    /// Returns a [`FreeChunkRef`] for the chunk pointed to by the given
    /// pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk that is free.
    pub unsafe fn from_addr(addr: usize) -> FreeChunkRef {
        &mut *(addr as *mut FreeChunk)
    }

    /// Sets the size of this free chunk and updates the postfix size.
    pub fn set_size(&mut self, new_size: usize) {
        self.header.set_size(new_size);
        let postfix_size_ptr = (self.header.end_addr() - USIZE_SIZE) as *mut usize;
        unsafe { *postfix_size_ptr = new_size }
    }

    /// Marks this free chunk as used, updates its next chunk, and replaces
    /// the current chunk in the linked list of free chunks with
    /// `replace_in_linked_list_with`.
    pub fn mark_as_used(
        &mut self,
        cur_chunk_ref_from_back: &mut Option<FreeChunkPtr>,
        replace_in_linked_list_with: Option<FreeChunkPtr>,
        heap_end_addr: usize,
    ) -> UsedChunkRef {
        // mark as used
        self.header.set_is_free(false);

        // update next chunk, if there is one
        if let Some(next_chunk_addr) = self.header.next_chunk_addr(heap_end_addr) {
            let next_chunk = unsafe { UsedChunk::from_addr(next_chunk_addr) };
            next_chunk.0.set_prev_in_use(true);
        }

        // unlink the current chunk from the linked list
        *cur_chunk_ref_from_back = replace_in_linked_list_with;

        unsafe { core::mem::transmute(self) }
    }

    /// Marks this free chunk as used, updates its next chunk, and unlinks this
    /// chunk from the linked list of free chunks.
    pub fn mark_as_used_unlink(
        &mut self,
        cur_chunk_ref_from_back: &mut Option<FreeChunkPtr>,
        heap_end_addr: usize,
    ) -> UsedChunkRef {
        self.mark_as_used(cur_chunk_ref_from_back, self.fd, heap_end_addr)
    }

    /// Creates a new free chunk at the given address, with the given size.
    /// The new chunk will point to `fd`, will be marked as free, and its
    /// `prev_in_use` flag will be set to `true`, because no 2 free chunks
    /// can be adjacent.
    ///
    /// # Safety
    ///
    ///  - `addr` must be a valid non-null memory address which is not used by
    ///    any other chunk.
    ///  - `size` must be aligned to `CHUNK_SIZE_ALIGNMENT`.
    ///  - The chunk must be pointed at from a back chunk that is in the linked
    ///    list of free chunks.
    ///  - The chunk's next chunk, if any, must be updated that its previous
    ///    chunk is now free.
    pub unsafe fn create_new(addr: usize, size: usize, fd: Option<FreeChunkPtr>) -> FreeChunkPtr {
        let ptr = addr as *mut FreeChunk;

        // write the chunk header and content
        *ptr = FreeChunk {
            // last argument is the `prev_in_use` flag, and there are no 2 adjacent free
            // chunks, so the previous chunk is surely unused, thus last argument is `false`.
            header: Chunk::new_unchecked(size, true, false),
            fd,
        };

        // dont forget to write the postfix size at the end of the chunk
        //
        // first find the end address of this chunk
        let end_addr = addr + HEADER_SIZE + size;
        // use the end address to find the address of the posfix size
        let postfix_size_ptr = (end_addr - USIZE_SIZE) as *mut usize;
        // write the posfix size
        unsafe { *postfix_size_ptr = size }

        FreeChunkPtr::new_unchecked(ptr)
    }
}

/// A usize that is guaranteed to be divisible by 4, which allows storing 2
/// additional bits of information in it.
#[repr(transparent)]
struct DivisbleBy4Usize(usize);

impl DivisbleBy4Usize {
    /// Creates divisble by 4 usize if the given value is divisble by 4, and
    /// stores the given additional bits in it.
    pub fn new(n: usize, additional_bit1: bool, additional_bit2: bool) -> Option<Self> {
        if n & 0b11 != 0 {
            return None;
        }
        unsafe {
            // SAFETY: we just checked that this is safe
            Some(Self::new_unchecked(n, additional_bit1, additional_bit2))
        }
    }

    /// Creates a divisible by 4 usize without checking if the given value is
    /// divisible by 4, and stores the given additional bits in it.
    /// This results in undefined behaviour if the value is not divisible by 4.
    pub unsafe fn new_unchecked(n: usize, additional_bit1: bool, additional_bit2: bool) -> Self {
        Self(n | usize::from(additional_bit1) | usize::from(additional_bit2) << 1)
    }

    /// Returns the divisble by 4 value as a `usize`.
    pub fn value(&self) -> usize {
        self.0 & (!1)
    }

    /// Returns the first additional bit of information stored within the
    /// number.
    pub fn additional_bit1(&self) -> bool {
        self.0 & 1 != 0
    }

    /// Returns the second additional bit of information stored within the
    /// number.
    pub fn additional_bit2(&self) -> bool {
        (self.0 >> 1) & 1 != 0
    }

    /// Sets the value of this divisble by 4 usize to the given value, without
    /// changing the additional bits stored within the number.
    ///
    /// # Safety
    ///
    /// The new value must be divisble by 4, otherwise the function panics.
    pub fn set_value(&mut self, new_value: usize) {
        if new_value & 0b11 != 0 {
            panic!("the value of a divisible by 4 usize must be divisble by 4");
        }
        self.0 = new_value | self.0 & 0b11;
    }

    /// Sets the first additional bit of information atores within the number.
    pub fn set_additional_bit1(&mut self, new_value: bool) {
        self.0 = (self.0 | 1) & usize::from(new_value)
    }

    /// Sets the second additional bit of information atores within the number.
    pub fn set_additional_bit2(&mut self, new_value: bool) {
        self.0 = (self.0 | 0b10) & (usize::from(new_value) << 1)
    }
}

/// Align downwards. Returns the greatest x with alignment `align`
/// so that x <= addr.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn align_down(n: usize, align: usize) -> usize {
    if align.is_power_of_two() {
        n & !(align - 1)
    } else if align == 0 {
        n
    } else {
        panic!("`align` must be a power of 2");
    }
}

/// Align upwards. Returns the smallest x with alignment `align`
/// so that x >= addr.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn align_up(n: usize, align: usize) -> usize {
    align_down(n + align - 1, align)
}

/// Checks if the given value is aligned to the given alignment.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn is_aligned(n: usize, align: usize) -> bool {
    n & (align - 1) == 0
}
