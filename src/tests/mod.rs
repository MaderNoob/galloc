mod alloc_tests;
mod dealloc_tests;

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
