#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(iter_intersperse)]
#![feature(const_mut_refs)]

use std::{
    alloc::{GlobalAlloc, Layout},
    ptr::NonNull,
    time::{Duration, Instant},
};

use average::Mean;
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

// We need to create a wrapper over chunk allocator and implement
// `GlobalAllocator` manually for it, because the implementation provided by the
// `simple-chunk-allocator` crate just panics on memory exhasution instead of
// returning `null`.
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
        Self(spin::Mutex::new(inner_alloc))
    }
}

unsafe impl<'a, const CHUNK_SIZE: usize> GlobalAlloc for GlobalChunkAllocator<'a, CHUNK_SIZE> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.0
            .lock()
            .allocate(layout)
            .map(|p| p.as_mut_ptr())
            .unwrap_or(core::ptr::null_mut())
    }

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

struct NamedBenchmark {
    benchmark_fn: fn(Duration, &dyn GlobalAlloc) -> usize,
    name: &'static str,
}

macro_rules! benchmark_list {
    ($($benchmark_fn: path),+) => {
        &[
            $(
                NamedBenchmark {
                    benchmark_fn: $benchmark_fn,
                    name: stringify!($benchmark_fn),
                }
            ),+
        ]
    }
}

struct NamedAllocator {
    name: &'static str,
    init_fn: fn() -> &'static dyn GlobalAlloc,
}

macro_rules! allocator_list {
    ($($init_fn: path),+) => {
        &[
            $(
                NamedAllocator {
                    init_fn: $init_fn,
                    name: {
                        const INIT_FN_NAME:&'static str = stringify!($init_fn);
                        &INIT_FN_NAME["init_".len()..]
                    },
                }
            ),+
        ]
    }
}

static mut GALLOC_ALLOCATOR: good_memory_allocator::SpinLockedAllocator =
    good_memory_allocator::SpinLockedAllocator::empty();
static LINKED_LIST_ALLOCATOR: linked_list_allocator::LockedHeap =
    linked_list_allocator::LockedHeap::empty();
static CHUNK_ALLOCATOR: GlobalChunkAllocator<'static, CHUNK_SIZE> =
    GlobalChunkAllocator::new(unsafe { HEAP.deref_mut_const() }, unsafe {
        HEAP_BITMAP.deref_mut_const()
    });

fn main() {
    const BENCHMARK_RESULTS_DIR: &str = "./benchmark_results";
    const TRIALS_AMOUNT: usize = 50;

    let _ = std::fs::remove_dir_all(BENCHMARK_RESULTS_DIR);

    // create a directory for the benchmark results.
    let _ = std::fs::create_dir(BENCHMARK_RESULTS_DIR);

    let benchmarks = benchmark_list!(random_actions, heap_exhaustion);
    let allocators = allocator_list!(
        init_galloc,
        init_linked_list_allocator,
        init_chunk_allocator
    );
    for benchmark in benchmarks {
        let mut csv = String::new();
        for allocator in allocators {
            let scores_as_strings = (TIME_STEP_MILLIS..=MILLIS_PER_SECOND)
                .step_by(TIME_STEP_MILLIS)
                .map(|i| {
                    let duration = Duration::from_millis(i as u64);
                    let mean: Mean = (0..TRIALS_AMOUNT)
                        .map(|_| {
                            let allocator_ref = (allocator.init_fn)();
                            (benchmark.benchmark_fn)(duration, allocator_ref) as f64
                        })
                        .collect();
                    mean.mean()
                })
                .map(|score| score.to_string());

            let csv_line = std::iter::once(allocator.name.to_owned())
                .chain(scores_as_strings)
                .intersperse(",".to_owned())
                .chain(std::iter::once("\n".to_owned()));
            csv.extend(csv_line);
        }
        // remove the last newline.
        csv.pop();

        std::fs::write(
            format!("{}/{}.csv", BENCHMARK_RESULTS_DIR, benchmark.name),
            csv,
        )
        .unwrap();
    }
}

fn init_linked_list_allocator() -> &'static dyn GlobalAlloc {
    let mut a = LINKED_LIST_ALLOCATOR.lock();
    *a = linked_list_allocator::Heap::empty();
    unsafe { a.init(HEAP.as_mut_ptr(), HEAP_SIZE) }
    &LINKED_LIST_ALLOCATOR
}

fn init_galloc() -> &'static dyn GlobalAlloc {
    unsafe {
        GALLOC_ALLOCATOR = good_memory_allocator::SpinLockedAllocator::empty();
    }
    unsafe { GALLOC_ALLOCATOR.init(HEAP.as_ptr() as usize, HEAP_SIZE) }
    unsafe { &GALLOC_ALLOCATOR }
}

fn init_chunk_allocator() -> &'static dyn GlobalAlloc {
    let mut a = CHUNK_ALLOCATOR.0.lock();
    unsafe {
        *a = simple_chunk_allocator::ChunkAllocator::new(
            HEAP.deref_mut_const(),
            HEAP_BITMAP.deref_mut_const(),
        )
        .unwrap();
    }
    &CHUNK_ALLOCATOR
}

pub fn random_actions(duration: Duration, allocator: &dyn GlobalAlloc) -> usize {
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
            },
            1 => {
                if !v.is_empty() {
                    let index = rng.gen_range(0..v.len());
                    v.swap_remove(index);
                }
            },
            2 => {
                if let Some(random_allocation) = v.choose_mut(&mut rng) {
                    let size = rng.gen_range(100..=10000);
                    random_allocation.realloc(size);
                }
            },
            _ => unreachable!(),
        }

        score += 1
    }

    score
}

pub fn heap_exhaustion(duration: Duration, allocator: &dyn GlobalAlloc) -> usize {
    let start = Instant::now();

    let mut score = 0;
    let mut rng = rand::thread_rng();

    let mut v = Vec::new();

    while start.elapsed() < duration {
        let size = rng.gen_range(10000..=300000);
        let alignment = 1 << rng.gen_range(0..=10);
        match AllocationWrapper::new(size, alignment, allocator) {
            Some(allocation) => {
                v.push(allocation);
                score += 1
            },
            None => {
                // heap was exhausted, penalize the score by sleeping.
                std::thread::sleep(Duration::from_millis(30));

                // free all allocation to empty the heap.
                v = Vec::new();
            },
        }
    }

    score
}
struct AllocationWrapper<'a> {
    ptr: *mut u8,
    layout: Layout,
    allocator: &'a dyn GlobalAlloc,
}
impl<'a> AllocationWrapper<'a> {
    fn new(size: usize, align: usize, allocator: &'a dyn GlobalAlloc) -> Option<Self> {
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

impl<'a> Drop for AllocationWrapper<'a> {
    fn drop(&mut self) {
        unsafe { self.allocator.dealloc(self.ptr, self.layout) }
    }
}
