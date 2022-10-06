use std::{
    alloc::Layout,
    time::{Duration, Instant},
};

use const_random::const_random;
use rand::{rngs::SmallRng, seq::SliceRandom, Rng, SeedableRng};

pub fn push_to_vec(duration: f32) -> usize {
    let start = Instant::now();

    let mut v = Vec::new();
    while start.elapsed().as_secs_f32() < duration {
        v.push(17);
    }

    v.len()
}

pub fn push_to_vec_and_alloc_between_each_push(duration: f32) -> usize {
    let start = Instant::now();

    let mut v = Vec::new();
    while start.elapsed().as_secs_f32() < duration {
        let _x = Box::new(28);

        v.push(17);
    }

    v.len()
}

pub fn alloc_dealloc(duration: f32) -> usize {
    let start = Instant::now();

    let mut score = 0;
    while start.elapsed().as_secs_f32() < duration {
        let _x = Box::new([0u8; 200]);
        score += 1;
    }

    score
}

pub fn alloc_until_full_then_dealloc(duration: f32) -> usize {
    let start = Instant::now();

    let mut score = 0;
    let mut v = Vec::new();
    while start.elapsed().as_secs_f32() < duration {
        score += 1;
        v.push(17);
        if v.len() == 10000 {
            v = Vec::new();
        }
    }

    score
}

pub fn random_actions(duration: f32) -> usize {
    let mut rng = SmallRng::seed_from_u64(const_random!(u64));

    let start = Instant::now();

    let mut score = 0;
    let mut v = Vec::new();

    while start.elapsed().as_secs_f32() < duration {
        let action = rng.gen_range(0..3);

        match action {
            0 => {
                let size = rng.gen_range(100..=1000);
                let alignment = 1 << rng.gen_range(0..=10);
                if let Some(allocation) = AllocationWrapper::new(size, alignment) {
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

pub fn heap_exhaustion(duration: f32) -> usize {
    let start = Instant::now();

    let mut score = 0;
    let mut rng = SmallRng::seed_from_u64(const_random!(u64));

    let mut v = Vec::new();

    while start.elapsed().as_secs_f32() < duration {
        let size = rng.gen_range(20000..=30000);
        match AllocationWrapper::new(size, std::mem::align_of::<usize>()) {
            Some(allocation) => {
                v.push(allocation);
                score += 1
            }
            None => {
                // heap was exhausted, penalize the score
                std::thread::sleep(Duration::from_millis(20));
                v = Vec::new();
            }
        }
    }

    score
}

struct AllocationWrapper {
    ptr: *mut u8,
    layout: Layout,
}
impl AllocationWrapper {
    fn new(size: usize, align: usize) -> Option<Self> {
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            return None;
        }

        Some(Self { ptr, layout })
    }

    fn realloc(&mut self, new_size: usize) {
        let new_ptr = unsafe { std::alloc::realloc(self.ptr, self.layout, new_size) };
        if new_ptr.is_null() {
            return;
        }
        self.ptr = new_ptr;
        self.layout = Layout::from_size_align(new_size, self.layout.align()).unwrap();
    }
}

impl Drop for AllocationWrapper {
    fn drop(&mut self) {
        unsafe { std::alloc::dealloc(self.ptr, self.layout) }
    }
}
