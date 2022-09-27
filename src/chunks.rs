use core::ptr::NonNull;

use crate::{divisible_by_4_usize::DivisbleBy4Usize, HEADER_SIZE, USIZE_SIZE};

/// A chunk in the heap.
#[repr(transparent)]
pub struct Chunk(DivisbleBy4Usize);

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
    pub fn size(&self) -> usize {
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
    pub fn is_free(&self) -> bool {
        self.0.additional_bit1()
    }

    /// Sets whether this chunk is considered free or not.
    fn set_is_free(&mut self, is_free: bool) {
        self.0.set_additional_bit1(is_free)
    }

    /// Is the previous chunk free?
    pub fn prev_in_use(&self) -> bool {
        self.0.additional_bit2()
    }

    /// Sets whether the previous chunk is considered free or not.
    fn set_prev_in_use(&mut self, prev_in_use: bool) {
        self.0.set_additional_bit2(prev_in_use)
    }

    /// The address where this chunk starts.
    pub fn addr(&self) -> usize {
        self as *const _ as usize
    }

    /// The address where the content of this chunk starts.
    pub fn content_addr(&self) -> usize {
        self as *const _ as usize + HEADER_SIZE
    }

    /// The address where this chunk ends.
    pub fn end_addr(&self) -> usize {
        self.content_addr() + self.size()
    }

    /// Checks if this chunk is the last chunk.
    pub fn is_last_chunk(&self, heap_end_addr: usize) -> bool {
        self.end_addr() == heap_end_addr
    }

    /// Returns the address of the next chunk in memory, if the current chunk is
    /// not the last chunk.
    pub fn next_chunk_addr(&self, heap_end_addr: usize) -> Option<usize> {
        let end = self.end_addr();
        if end == heap_end_addr {
            return None;
        }
        Some(end)
    }
}

/// A used chunk in the heap.
#[repr(transparent)]
pub struct UsedChunk(pub(crate) Chunk);

pub type UsedChunkRef = &'static mut UsedChunk;

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

    /// The address where the content of this chunk starts.
    pub fn content_addr(&self) -> usize {
        self.0.content_addr()
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
    pub unsafe fn create_new_without_updating_next_chunk(
        addr: usize,
        size: usize,
        prev_in_use: bool,
    ) -> UsedChunkRef {
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
    pub unsafe fn create_new(
        addr: usize,
        size: usize,
        prev_in_use: bool,
        heap_end_addr: usize,
    ) -> UsedChunkRef {
        // create a new used chunk
        let chunk = UsedChunk::create_new_without_updating_next_chunk(addr, size, prev_in_use);

        // update the next chunk
        if let Some(next_chunk_addr) = chunk.0.next_chunk_addr(heap_end_addr) {
            Chunk::set_prev_in_use_for_chunk_with_addr(next_chunk_addr, true)
        }

        // return the created chunk
        chunk
    }

    /// The size of the previous chunk, if it is free.
    pub fn prev_size_if_free(&self) -> Option<usize> {
        if self.0.prev_in_use() {
            return None;
        }

        let prev_chunk_postfix_size_ptr = (self.0.addr() - USIZE_SIZE) as *mut usize;

        Some(unsafe { *prev_chunk_postfix_size_ptr })
    }

    /// Sets the size of this used chunk to the given value. The size must be
    /// aligned to `CHUNK_SIZE_ALIGNMENT`.
    ///
    /// # Safety
    ///
    /// Panics if the new size is not divisble by 4.
    pub fn set_size(&mut self, new_size: usize) {
        self.0.set_size(new_size)
    }
}

/// A free chunk in the heap.
#[repr(C)]
pub struct FreeChunk {
    pub(crate) header: Chunk,
    pub(crate) fd: Option<FreeChunkPtr>,

    /// A pointer to the `fd` field of the back chunk.
    pub(crate) ptr_to_fd_of_bk: *mut Option<FreeChunkPtr>,
}

pub type FreeChunkRef = &'static mut FreeChunk;
pub type FreeChunkPtr = NonNull<FreeChunk>;

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

    /// The address where this chunk starts.
    pub fn addr(&self) -> usize {
        self.header.addr()
    }

    /// The size of this chunk.
    pub fn size(&self) -> usize {
        self.header.size()
    }

    /// The address where the content of this chunk starts.
    pub fn content_addr(&self) -> usize {
        self.header.content_addr()
    }

    /// The address where this chunk ends.
    pub fn end_addr(&self) -> usize {
        self.header.end_addr()
    }

    /// Returns the fd pointer of this chunk.
    pub fn fd(&mut self) -> Option<FreeChunkPtr> {
        self.fd
    }

    /// Returns a mutable reference the fd pointer of this chunk.
    pub fn fd_ref_mut(&mut self) -> &mut Option<FreeChunkPtr> {
        &mut self.fd
    }

    /// Returns a mutable reference to the fd chunk.
    pub fn fd_chunk_ref(&mut self) -> Option<FreeChunkRef> {
        self.fd.map(|mut fd| unsafe { fd.as_mut() })
    }

    /// Returns a pointer to the fd of this chunk's bk chunk.
    pub fn ptr_to_fd_of_bk(&mut self) -> *mut Option<FreeChunkPtr> {
        self.ptr_to_fd_of_bk
    }

    /// Returns a mutable reference to this chunk's postfix size.
    pub fn postfix_size(&mut self) -> &mut usize {
        let postfix_size_ptr = (self.header.end_addr() - USIZE_SIZE) as *mut usize;
        unsafe { &mut *postfix_size_ptr }
    }

    /// Sets the size of this free chunk and updates the postfix size.
    pub fn set_size(&mut self, new_size: usize) {
        self.header.set_size(new_size);
        *self.postfix_size() = new_size;
    }

    /// Marks this free chunk as used and updates its next chunk, but without
    /// updating the linked list of free chunks.
    ///
    /// # Safety
    ///
    /// You must make sure to remove this chunk from the linked list of free
    /// chunks, since it is now used.
    pub unsafe fn mark_as_used_without_updating_freelist(
        &mut self,
        heap_end_addr: usize,
    ) -> UsedChunkRef {
        // mark as used
        self.header.set_is_free(false);

        // update next chunk, if there is one
        if let Some(next_chunk_addr) = self.header.next_chunk_addr(heap_end_addr) {
            let next_chunk = unsafe { UsedChunk::from_addr(next_chunk_addr) };
            next_chunk.0.set_prev_in_use(true);
        }

        core::mem::transmute(self)
    }

    /// Marks this free chunk as used, updates its next chunk, and unlinks this
    /// chunk from the linked list of free chunks.
    pub fn mark_as_used_unlink(&mut self, heap_end_addr: usize) -> UsedChunkRef {
        // this is safe because we then unlink it.
        let _ = unsafe { self.mark_as_used_without_updating_freelist(heap_end_addr) };

        // unlink this chunk from the linked list of free chunks, to do that we
        // need to change the state:
        // ```
        // bk <-> self <-> fd
        // ```
        // to the state:
        // ```
        // bk <-> fd
        // ```

        // make bk point to fd
        unsafe { *self.ptr_to_fd_of_bk = self.fd };

        // make fd point back to bk
        if let Some(fd) = self.fd_chunk_ref() {
            fd.ptr_to_fd_of_bk = self.ptr_to_fd_of_bk;
        }

        unsafe { core::mem::transmute(self) }
    }

    /// Creates a new free chunk at the given address, with the given size.
    ///
    /// The new chunk will be marked as free, and its `prev_in_use` flag will be
    /// set to `true`, because no 2 free chunks can be adjacent.
    ///
    /// The new chunk will also be linked into the linked list between fd and
    /// bk.
    ///
    /// # Safety
    ///
    ///  - `addr` must be a valid non-null memory address which is not used by
    ///    any other chunk.
    ///  - `size` must be aligned to `CHUNK_SIZE_ALIGNMENT`.
    ///  - The chunk's next chunk, if any, must be updated that its previous
    ///    chunk is now free.
    pub unsafe fn create_new_without_updating_next_chunk(
        addr: usize,
        size: usize,
        fd: Option<FreeChunkPtr>,
        ptr_to_fd_of_bk: *mut Option<FreeChunkPtr>,
    ) -> FreeChunkPtr {
        let created_chunk_ref = FreeChunk::from_addr(addr);

        // write the chunk header and content
        *created_chunk_ref = FreeChunk {
            // last argument is the `prev_in_use` flag, and there are no 2 adjacent free chunks, so
            // the previous chunk is surely used, thus last argument is `true`.
            header: Chunk::new_unchecked(size, true, true),
            fd,
            ptr_to_fd_of_bk,
        };

        // write the postfix size at the end of the chunk
        *created_chunk_ref.postfix_size() = size;

        // update the freelist.
        //
        // make `fd` point back to this chunk
        if let Some(mut fd) = fd {
            let fd_ref = fd.as_mut();
            fd_ref.ptr_to_fd_of_bk = &mut created_chunk_ref.fd;
        }
        // make `bk` point to this chunk
        *ptr_to_fd_of_bk = Some(FreeChunkPtr::new_unchecked(addr as *mut _));

        FreeChunkPtr::new_unchecked(addr as *mut _)
    }
}

/// A reference to a used or free chunk.
pub enum ChunkRef {
    Used(UsedChunkRef),
    Free(FreeChunkRef),
}
