#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(iter_intersperse)]
#![feature(const_mut_refs)]

use std::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
    time::{Duration, Instant},
};

use rand::{seq::SliceRandom, Rng};

const CHUNKS_AMOUNT: usize = 1 << 20;
const CHUNK_SIZE: usize = 256;
const HEAP_SIZE: usize = CHUNKS_AMOUNT * CHUNK_SIZE;

static mut HEAP: simple_chunk_allocator::PageAligned<[u8; HEAP_SIZE]> =
    simple_chunk_allocator::heap!(chunks = CHUNKS_AMOUNT, chunksize = CHUNK_SIZE);
static mut HEAP_BITMAP: simple_chunk_allocator::PageAligned<[u8; CHUNKS_AMOUNT / 8]> =
    simple_chunk_allocator::heap_bitmap!(chunks = CHUNKS_AMOUNT);

const TIME_STEPS_AMOUNT: usize = 10;
const MILLIS_PER_SECOND: usize = 1000;
const TIME_STEP_MILLIS: usize = MILLIS_PER_SECOND / TIME_STEPS_AMOUNT;

#[derive(Debug)]
pub struct GlobalChunkAllocator<
    'a,
    const CHUNK_SIZE: usize = { simple_chunk_allocator::DEFAULT_CHUNK_SIZE },
>(spin::Mutex<simple_chunk_allocator::ChunkAllocator<'a, CHUNK_SIZE>>);

impl<'a, const CHUNK_SIZE: usize> GlobalChunkAllocator<'a, CHUNK_SIZE> {
    #[inline]
    pub const fn new(heap: &'a mut [u8], bitmap: &'a mut [u8]) -> Self {
        let inner_alloc =
            simple_chunk_allocator::ChunkAllocator::<CHUNK_SIZE>::new_const(heap, bitmap);
        let inner_alloc = spin::Mutex::new(inner_alloc);
        Self(inner_alloc)
    }
}

unsafe impl<'a, const CHUNK_SIZE: usize> GlobalAlloc for GlobalChunkAllocator<'a, CHUNK_SIZE> {
    #[inline]
    #[must_use = "The pointer must be used and freed eventually to prevent memory leaks."]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.0
            .lock()
            .allocate(layout)
            .map(|p| p.as_mut_ptr())
            .unwrap_or(core::ptr::null_mut())
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.0.lock().deallocate(NonNull::new(ptr).unwrap(), layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        self.0
            .lock()
            .realloc(NonNull::new(ptr).unwrap(), layout, new_size)
            .map(|p| p.as_mut_ptr())
            .unwrap_or(core::ptr::null_mut())
    }
}

/// Helper struct generated by [`GlobalChunkAllocator`] that can be used in structs that accept
/// a custom instance of a specific allocator implementation.

fn main() {
    let galloc_line =
        benchmark_allocator(galloc::SpinLockedAllocator::empty, init_galloc, "galloc");

    let linked_list_allocator_line = benchmark_allocator(
        linked_list_allocator::LockedHeap::empty,
        init_linked_list_allocator,
        "linked list allocator",
    );

    let chunk_allocator_line = benchmark_allocator(
        || {
            GlobalChunkAllocator::<'static, CHUNK_SIZE>::new(
                unsafe { HEAP.deref_mut_const() },
                unsafe { HEAP_BITMAP.deref_mut_const() },
            )
        },
        init_chunk_allocator,
        "chunk allocator",
    );

    std::fs::write(
        "benchmark_results/all3.csv",
        galloc_line + "\n" + &linked_list_allocator_line + "\n" + &chunk_allocator_line,
    )
    .unwrap();
}

fn benchmark_allocator<A: GlobalAlloc>(
    new: fn() -> A,
    init: fn(&A),
    allocator_name: impl Into<String>,
) -> String {
    let scores_as_strings = (TIME_STEP_MILLIS..=MILLIS_PER_SECOND)
        .step_by(TIME_STEP_MILLIS)
        .map(|i| {
            let allocator = new();
            let duration = Duration::from_millis(i as u64);
            init(&allocator);
            random_actions(duration, &allocator)
        })
        .map(|score| score.to_string());

    std::iter::once(allocator_name.into())
        .chain(scores_as_strings)
        .intersperse(",".to_owned())
        .collect()
}

fn init_linked_list_allocator(allocator: &linked_list_allocator::LockedHeap) {
    let mut a = allocator.lock();
    unsafe { a.init(HEAP.as_mut_ptr(), HEAP_SIZE) }
}

fn init_galloc(allocator: &galloc::SpinLockedAllocator) {
    unsafe { allocator.init(HEAP.as_ptr() as usize, HEAP_SIZE) }
}

fn init_chunk_allocator(allocator: &GlobalChunkAllocator) {
    let mut a = allocator.0.lock();
    unsafe {
        *a = simple_chunk_allocator::ChunkAllocator::new(
            HEAP.deref_mut_const(),
            HEAP_BITMAP.deref_mut_const(),
        )
        .unwrap();
    }
}

pub fn random_actions(duration: Duration, allocator: &impl GlobalAlloc) -> usize {
    let mut rng = rand::thread_rng();

    let start = Instant::now();

    let mut score = 0;
    let mut v = Vec::new();

    while start.elapsed() < duration {
        let action = rng.gen_range(0..3);

        match action {
            0 => {
                let size = rng.gen_range(100..=1000);
                let alignment = 1 << rng.gen_range(0..=10);
                if let Some(allocation) = AllocationWrapper::new(size, alignment, allocator) {
                    v.push(allocation)
                }
            }
            1 => {
                if !v.is_empty() {
                    let index = rng.gen_range(0..v.len());
                    v.swap_remove(index);
                }
            }
            2 => {
                if let Some(random_allocation) = v.choose_mut(&mut rng) {
                    let size = rng.gen_range(100..=10000);
                    random_allocation.realloc(size);
                }
            }
            _ => unreachable!(),
        }

        score += 1
    }

    score
}

struct AllocationWrapper<'a, A: GlobalAlloc> {
    ptr: *mut u8,
    layout: Layout,
    allocator: &'a A,
}
impl<'a, A: GlobalAlloc> AllocationWrapper<'a, A> {
    fn new(size: usize, align: usize, allocator: &'a A) -> Option<Self> {
        let layout = Layout::from_size_align(size, align).unwrap();

        let ptr = unsafe { allocator.alloc(layout) };

        if ptr.is_null() {
            return None;
        }

        Some(Self {
            ptr,
            layout,
            allocator,
        })
    }

    fn realloc(&mut self, new_size: usize) {
        let new_ptr = unsafe { self.allocator.realloc(self.ptr, self.layout, new_size) };
        if new_ptr.is_null() {
            return;
        }
        self.ptr = new_ptr;
        self.layout = Layout::from_size_align(new_size, self.layout.align()).unwrap();
    }
}

impl<'a, A: GlobalAlloc> Drop for AllocationWrapper<'a, A> {
    fn drop(&mut self) {
        unsafe { self.allocator.dealloc(self.ptr, self.layout) }
    }
}