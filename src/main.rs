use core::ptr::NonNull;

fn main() {}

const USIZE_ALIGNMENT: usize = core::mem::align_of::<usize>();
const USIZE_SIZE: usize = core::mem::size_of::<usize>();
const MIN_ALIGNMENT: usize = USIZE_ALIGNMENT;
const MIN_FREE_CHUNK_SIZE: usize = core::mem::size_of::<FreeChunk>() + USIZE_SIZE;
const HEADER_SIZE: usize = core::mem::size_of::<Chunk>();

pub struct Allocator {
    heap_region: HeapRegion,
    free_chunk: Option<FreeChunkPtr>,
}
impl Allocator {
    fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        let layout_size = unsafe { align_up(core::cmp::max(layout.size(), 2 * USIZE_SIZE), 4) };
        let layout_align = core::cmp::max(layout.align(), MIN_ALIGNMENT);

        let cur_chunk_ref_from_back = &mut self.free_chunk;
        while let Some(cur_chunk_ptr) = cur_chunk_ref_from_back {
            let cur_chunk = unsafe { cur_chunk_ptr.as_mut() };
            // if the chunk is not aligned, fix the alignment
            if unsafe { is_aligned(cur_chunk.header.content_addr(), layout_align) } {
                // already aligned
                if let Some(ptr) =
                    self.heap_region
                        .alloc_aligned(layout_size, layout_align, cur_chunk)
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
    heap_start: usize,
    heap_end: usize,
}

impl HeapRegion {
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

    fn alloc_aligned(
        &mut self,
        layout_size: usize,
        layout_align: usize,
        cur_chunk: FreeChunkRef,
    ) -> Option<NonNull<u8>> {
        todo!()
    }
}

#[repr(transparent)]
pub struct Chunk(DivisbleBy4Usize);

#[repr(transparent)]
pub struct UsedChunk(Chunk);

#[repr(C)]
pub struct FreeChunk {
    header: Chunk,
    fd: Option<FreeChunkRef>,
    // bk: Option<FreeChunkRef>,
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

    /// The size of the chunk.
    fn size(&self) -> usize {
        self.0.value()
    }

    /// Sets the size of the chunk to the given value. The size must be divisble
    /// by 4.
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
    fn set_prev_in_use(&mut self, is_prev_chunk_free: bool) {
        self.0.set_additional_bit2(is_prev_chunk_free)
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
