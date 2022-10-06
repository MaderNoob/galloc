use std::ops::DerefMut;
mod benchmarks;

use std::{
    alloc::{GlobalAlloc, System},
    path::Path,
    ptr::NonNull,
};

use arrayvec::{ArrayString, ArrayVec};
use strum_macros::Display;

const CHUNKS_AMOUNT: usize = 1 << 20;
const CHUNK_SIZE: usize = 256;
const HEAP_SIZE: usize = CHUNKS_AMOUNT * CHUNK_SIZE;

static mut HEAP: simple_chunk_allocator::PageAligned<[u8; HEAP_SIZE]> =
    simple_chunk_allocator::heap!(chunks = CHUNKS_AMOUNT, chunksize = CHUNK_SIZE);
static mut HEAP_BITMAP: simple_chunk_allocator::PageAligned<[u8; CHUNKS_AMOUNT / 8]> =
    simple_chunk_allocator::heap_bitmap!(chunks = CHUNKS_AMOUNT);

#[allow(dead_code)]
#[derive(Display)]
enum AnyAllocator {
    System(System),
    // we wanted to also compare linked list allocator, but sadly it didnt work...
    LinkedListAllocator(linked_list_allocator::Heap),
    Galloc(galloc::Allocator),
    ChunkAllocator(simple_chunk_allocator::ChunkAllocator<'static>),
}

struct SpinLockedAnyAllocator(spin::Mutex<AnyAllocator>);

impl SpinLockedAnyAllocator {
    const fn system() -> Self {
        Self(spin::Mutex::new(AnyAllocator::System(System)))
    }
}

unsafe impl GlobalAlloc for SpinLockedAnyAllocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let mut allocator = self.0.lock();

        match allocator.deref_mut() {
            AnyAllocator::System(allocator) => allocator.alloc(layout),
            AnyAllocator::LinkedListAllocator(allocator) => {
                match allocator.allocate_first_fit(layout) {
                    Ok(ptr) => ptr.as_ptr(),
                    Err(()) => std::ptr::null_mut(),
                }
            }
            AnyAllocator::Galloc(allocator) => allocator.alloc(layout),
            AnyAllocator::ChunkAllocator(allocator) => match allocator.allocate(layout) {
                Ok(ptr) => ptr.as_ptr() as *mut u8,
                Err(_) => std::ptr::null_mut(),
            },
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        let mut allocator = self.0.lock();

        match allocator.deref_mut() {
            AnyAllocator::System(allocator) => allocator.dealloc(ptr, layout),
            AnyAllocator::LinkedListAllocator(allocator) => {
                allocator.deallocate(NonNull::new_unchecked(ptr), layout)
            }
            AnyAllocator::Galloc(allocator) => allocator.dealloc(ptr),
            AnyAllocator::ChunkAllocator(allocator) => {
                allocator.deallocate(NonNull::new_unchecked(ptr), layout)
            }
        }
    }

    unsafe fn alloc_zeroed(&self, layout: std::alloc::Layout) -> *mut u8 {
        let size = layout.size();
        // SAFETY: the safety contract for `alloc` must be upheld by the caller.
        let ptr = self.alloc(layout);
        if !ptr.is_null() {
            // SAFETY: as allocation succeeded, the region from `ptr`
            // of size `size` is guaranteed to be valid for writes.
            std::ptr::write_bytes(ptr, 0, size);
        }
        ptr
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: std::alloc::Layout, new_size: usize) -> *mut u8 {
        let mut allocator = self.0.lock();

        match allocator.deref_mut() {
            AnyAllocator::System(allocator) => allocator.realloc(ptr, layout, new_size),
            AnyAllocator::LinkedListAllocator(allocator) => {
                // SAFETY: the caller must ensure that the `new_size` does not overflow.
                // `layout.align()` comes from a `Layout` and is thus guaranteed to be valid.
                let new_layout =
                    std::alloc::Layout::from_size_align_unchecked(new_size, layout.align());
                // SAFETY: the caller must ensure that `new_layout` is greater than zero.
                let new_ptr = match allocator.allocate_first_fit(new_layout) {
                    Ok(ptr) => ptr.as_ptr(),
                    Err(()) => std::ptr::null_mut(),
                };
                if !new_ptr.is_null() {
                    // SAFETY: the previously allocated block cannot overlap the newly allocated
                    // block. The safety contract for `dealloc` must be upheld by the
                    // caller.

                    std::ptr::copy_nonoverlapping(
                        ptr,
                        new_ptr,
                        std::cmp::min(layout.size(), new_size),
                    );
                    self.dealloc(ptr, layout);
                }
                new_ptr
            }
            AnyAllocator::Galloc(allocator) => allocator.realloc(ptr, layout, new_size),
            AnyAllocator::ChunkAllocator(allocator) => {
                match allocator.realloc(NonNull::new_unchecked(ptr), layout, new_size) {
                    Ok(ptr) => ptr.as_ptr() as *mut u8,
                    Err(_) => std::ptr::null_mut(),
                }
            }
        }
    }
}

#[global_allocator]
static mut ALLOCATOR: SpinLockedAnyAllocator = SpinLockedAnyAllocator::system();

struct NamedBenchmark {
    benchmark: fn(f32) -> usize,
    name: &'static str,
}

macro_rules! benchmark_list {
    ($($benchmark_fn: path),+) => {
        &[
            $(
                NamedBenchmark {
                    benchmark: $benchmark_fn,
                    name: stringify!($benchmark_fn),
                }
            ),+
        ]
    }
}

macro_rules! allocator_list {
    ($($switch_fn: path),+) => {
        &[
            $(
                NamedAllocator {
                    switch_fn: $switch_fn,
                    name: stringify!($switch_fn),
                }
            ),+
        ]
    }
}

struct NamedAllocator {
    switch_fn: fn(),
    name: &'static str,
}

// we wanted to also compare linked list allocator, but sadly it didnt work...
#[allow(dead_code)]
fn switch_to_linked_list_allocator() {
    let mut allocator = unsafe { ALLOCATOR.0.lock() };
    *allocator = AnyAllocator::LinkedListAllocator(linked_list_allocator::Heap::empty());
    match allocator.deref_mut() {
        AnyAllocator::LinkedListAllocator(a) => unsafe { a.init(HEAP.as_mut_ptr(), HEAP_SIZE) },
        _ => unreachable!(),
    }
}

fn switch_to_galloc() {
    let mut allocator = unsafe { ALLOCATOR.0.lock() };

    // must first write it to the global variable before initializing, since it
    // cannot be moved after initialization.
    *allocator = AnyAllocator::Galloc(galloc::Allocator::empty());
    match allocator.deref_mut() {
        AnyAllocator::Galloc(galloc_allocator) => unsafe {
            galloc_allocator.init(HEAP.as_ptr() as usize, HEAP_SIZE)
        },
        _ => unreachable!(),
    }
}

fn switch_to_chunk_allocator() {
    let mut allocator = unsafe { ALLOCATOR.0.lock() };

    unsafe {
        *allocator =
            AnyAllocator::ChunkAllocator(simple_chunk_allocator::ChunkAllocator::new_const(
                HEAP.deref_mut_const(),
                HEAP_BITMAP.deref_mut_const(),
            ));
    }
}

fn switch_to_system() {
    let mut allocator = unsafe { ALLOCATOR.0.lock() };
    *allocator = AnyAllocator::System(System);
}

fn benchmark_all() {
    const BENCHMARKS: &[NamedBenchmark] = benchmark_list!(
        benchmarks::push_to_vec,
        benchmarks::push_to_vec_and_alloc_between_each_push,
        benchmarks::alloc_dealloc,
        benchmarks::alloc_until_full_then_dealloc,
        benchmarks::heap_exhaustion,
        benchmarks::random_actions
    );
    const BENCHMARKS_AMOUNT: usize = BENCHMARKS.len();

    const ALLOCATORS: &[NamedAllocator] =
        allocator_list!(switch_to_galloc, switch_to_chunk_allocator);

    const ALLOCATORS_AMOUNT: usize = ALLOCATORS.len();

    const TIME_STEPS_AMOUNT: usize = 10;

    let _ = std::fs::create_dir("./benchmark_results/");

    let mut data: ArrayVec<
        (
            ArrayVec<(ArrayVec<usize, TIME_STEPS_AMOUNT>, &'static str), ALLOCATORS_AMOUNT>,
            &'static str,
        ),
        BENCHMARKS_AMOUNT,
    > = ArrayVec::new();

    let mut benchmark_file_name = ArrayString::<1024>::new();

    for benchmark in BENCHMARKS {
        // get the benchmark file name
        benchmark_file_name.clear();
        benchmark_file_name.push_str("./benchmark_results/");
        benchmark_file_name.push_str(&benchmark.name["benchmarks::".len()..]);
        benchmark_file_name.push_str(".csv");

        if Path::new(benchmark_file_name.as_str()).exists() {
            continue;
        }

        let mut data_for_cur_benchmark = ArrayVec::new();
        for allocator in ALLOCATORS {
            let mut scores_over_time_of_allocator = ArrayVec::new();
            for i in 1..=TIME_STEPS_AMOUNT {
                (allocator.switch_fn)();
                let duration = i as f32 / TIME_STEPS_AMOUNT as f32;
                let score = (benchmark.benchmark)(duration);
                scores_over_time_of_allocator.push(score);
            }
            data_for_cur_benchmark.push((scores_over_time_of_allocator, allocator.name));
        }
        data.push((data_for_cur_benchmark, benchmark.name));
    }

    switch_to_system();

    for (data_for_benchmark, benchmark_name) in data {
        let mut result = String::new();
        for (allocator_scores_over_time, allocator_name) in data_for_benchmark {
            result.push_str(&allocator_name["switch_to_".len()..]);
            result.push(',');
            for score in allocator_scores_over_time {
                result += &score.to_string();
                result.push(',');
            }
            // remove last comma
            result.pop();

            result.push('\n')
        }
        // remove last newline
        result.pop();

        std::fs::write(
            format!(
                "./benchmark_results/{}.csv",
                &benchmark_name["benchmarks::".len()..],
            ),
            &result,
        )
        .unwrap();
    }
}

fn main() {
    benchmark_all();
}
