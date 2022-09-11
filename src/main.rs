use std::num::NonZeroUsize;

fn main() {}

/// A usize that is guaranteed to be divisible by 4, which allows storing 2 additional bits of information in it.
#[repr(transparent)]
struct DivisbleBy4Usize(usize);

impl DivisbleBy4Usize {
    /// Creates divisble by 4 usize if the given value is divisble by 4, and stores the given additional bits in it.
    pub fn new(n: usize, additional_bit1: bool, additional_bit2: bool) -> Option<Self> {
        if n & 0b11 != 0 {
            return None;
        }
        unsafe {
            // SAFETY: we just checked that this is safe
            Some(Self::new_unchecked(n, additional_bit1, additional_bit2))
        }
    }

    /// Creates a divisible by 4 usize without checking if the given value is divisible by 4, and stores the given additional bits in it.
    /// This results in undefined behaviour if the value is not divisible by 4.
    pub unsafe fn new_unchecked(n: usize, additional_bit1: bool, additional_bit2: bool) -> Self {
        Self(n | usize::from(additional_bit1) | usize::from(additional_bit2) << 1)
    }

    /// Returns the divisble by 4 value as a `usize`.
    pub fn value(&self) -> usize {
        self.0 & (!1)
    }

    /// Returns the first additional bit of information stored within the number.
    pub fn additional_bit1(&self) -> bool {
        self.0 & 1 != 0
    }

    /// Returns the second additional bit of information stored within the number.
    pub fn additional_bit2(&self) -> bool {
        (self.0 >> 1) & 1 != 0
    }

    /// Sets the value of this divisble by 4 usize to the given value, without changing the additional bits stored within the number.
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

#[repr(transparent)]
pub struct Chunk(DivisbleBy4Usize);

impl Chunk {
    /// Returns a [`ChunkRef`] for the chunk pointed to by the given pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk.
    pub unsafe fn from_ptr(ptr: *mut Chunk) -> ChunkRef {
        &mut *ptr
    }

    /// The size of the chunk.
    pub fn size(&self) -> usize {
        self.0.value()
    }

    /// Sets the size of the chunk to the given value. The size must be divisble by 4.
    ///
    /// # Safety
    ///
    /// Panics if the new size is not divisble by 4.
    pub fn set_size(&mut self, new_size: usize) {
        self.0.set_value(new_size);
    }

    /// Is this chunk free?
    fn is_free(&self) -> bool {
        self.0.additional_bit1()
    }

    /// Marks this chunk as non-free, and updates the next adjacent chunk that this chunk
    /// is not free anymore.
    pub fn mark_as_non_free(&mut self) {
        // set the is free bit to false.
        self.0.set_additional_bit1(false);

        todo!("update next adjacent chunk")
    }

    /// Is the previous adjacent chunk free?
    fn is_prev_adj_chunk_free(&self) -> bool {
        self.0.additional_bit2()
    }

    /// Sets whether the previous adjacent chunk is considered free or not.
    fn set_is_prev_adj_chunk_free(&mut self, is_free: bool) {
        self.0.set_additional_bit2(is_free)
    }

    /// Converts a non-free chunk to a free chunk, and updates the next adjacent chunk that this
    /// chunk is now free.
    fn convert_to_free_chunk(
        &mut self,
        freelist_forward: Option<FreeChunkRef>,
        freelist_backwards: Option<FreeChunkRef>,
    ) -> FreeChunkRef {
        let free_chunk: FreeChunkRef = unsafe { std::mem::transmute(self) };

        free_chunk.freelist_forward = freelist_forward;
        free_chunk.freelist_backwards = freelist_backwards;

        todo!("update next adjacent chunk");

        free_chunk
    }
}

type ChunkRef = &'static mut Chunk;

#[repr(C)]
struct FreeChunk {
    chunk: Chunk,
    freelist_forward: Option<FreeChunkRef>,
    freelist_backwards: Option<FreeChunkRef>,
}

impl FreeChunk {
    /// Returns a [`FreeChunkRef`] for the chunk pointed to by the given pointer, if that chunk is free.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk.
    unsafe fn from_ptr(ptr: *mut FreeChunk) -> Option<FreeChunkRef> {
        // this is considered safe even if this chunk is not a free chunk, as long as we only
        // access the `chunk` field, and not the other fields that only free chunks have, until
        // we make sure that the chunk is indeed free.
        //
        // that is because the way that the free chunk is laid out in memory is that first it
        // contains the chunk itself, and then all the other fields that are only for free chunks,
        // due to the `#[repr(c)]` attribute.
        let free_chunk: FreeChunkRef = &mut *ptr;
        if !free_chunk.chunk.is_free() {
            return None;
        }

        Some(free_chunk)
    }

    /// Returns a [`FreeChunkRef`] for the free chunk pointed to by the given pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid chunk, and the chunk must be free.
    unsafe fn from_ptr_unchecked(ptr: *mut FreeChunk) -> FreeChunkRef {
        // this is considered safe even if this chunk is not a free chunk, as long as we only
        // access the `chunk` field, and not the other fields that only free chunks have, until
        // we make sure that the chunk is indeed free.
        //
        // that is because the way that the free chunk is laid out in memory is that first it
        // contains the chunk itself, and then all the other fields that are only for free chunks,
        // due to the `#[repr(c)]` attribute.
        &mut *ptr
    }
}

type FreeChunkRef = &'static mut FreeChunk;
