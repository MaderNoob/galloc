use static_assertions::const_assert;

use crate::{
    chunks::FreeChunkPtr, HEADER_SIZE, MIN_ALIGNMENT, MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
};

pub const SMALLBINS_AMOUNT: usize = 20;
pub const ALIGNMENT_SUB_BINS_AMOUNT: usize = 8;

pub const MIN_ALIGNMENT_LOG2: usize = unsafe { log2_of_power_of_2(MIN_ALIGNMENT) };

/// The max alignment index that has a specific sub-bin in which all chunks have
/// that alignment.
pub const MAX_SPECIFIC_ALIGNMENT_INDEX: usize = ALIGNMENT_SUB_BINS_AMOUNT - 1 - 1;

/// The max alignment that has a specific sub-bin in which all chunks have that
/// alignment.
pub const MAX_SPECIFIC_ALIGNMENT: usize = 1 << (MAX_SPECIFIC_ALIGNMENT_INDEX + MIN_ALIGNMENT_LOG2);

pub const MAX_ALIGNMENT_INDEX: usize = ALIGNMENT_SUB_BINS_AMOUNT - 1;

type AlignmentSubBinsBitmapType = u8;

const SMALLEST_SMALLBIN_SIZE: usize = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;
const LARGEST_SMALLBIN_SIZE: usize = SMALLEST_SMALLBIN_SIZE + SMALLBINS_AMOUNT * MIN_ALIGNMENT;

const OPTIMAL_SMALLBIN_LOOKAHEAD: usize = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER / MIN_ALIGNMENT;

// make sure that the alignment sub-bins bitmap type has enough bits to store
// information about each alingment sub-bin.
const_assert!(core::mem::size_of::<AlignmentSubBinsBitmapType>() * 8 >= ALIGNMENT_SUB_BINS_AMOUNT);

// make sure that the alignment sub-bins bitmap type is optimal.
// if this causes an error, use a smaller type for it.
const_assert!(
    core::mem::size_of::<AlignmentSubBinsBitmapType>() == 1
        || (core::mem::size_of::<AlignmentSubBinsBitmapType>() * 8 / 2 < ALIGNMENT_SUB_BINS_AMOUNT)
);

/// Computes log2(x) where x is a power of 2.
///
/// # Safety
///
/// `x` must be a power of 2
pub const unsafe fn log2_of_power_of_2(x: usize) -> usize {
    x.trailing_zeros() as usize
}

/// A collection of small bins, used in the allocator.
pub struct SmallBins {
    small_bins: [SmallBin; SMALLBINS_AMOUNT],
}

impl SmallBins {
    /// Creates a new set of empty smallbins.
    pub const fn new() -> Self {
        Self {
            small_bins: [SmallBin::new(); SMALLBINS_AMOUNT],
        }
    }

    /// Checks if the given size is the size of a smallbin.
    ///
    /// # Safety
    ///
    /// The size must have been prepared.
    pub unsafe fn is_smallbin_size(size: usize) -> bool {
        size < LARGEST_SMALLBIN_SIZE
    }

    /// Returns the index of the smallbin containing chunks of the given size,
    /// if such a small bin exists.
    ///
    /// # Safety
    ///
    /// The size must have been prepared.
    pub unsafe fn smallbin_index(size: usize) -> Option<usize> {
        if size < LARGEST_SMALLBIN_SIZE {
            return None;
        }

        Some((size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT)
    }

    /// Returns the alignment index for the given alignment.
    ///
    /// # Safety
    ///
    /// `alignment` must be a power of 2.
    pub unsafe fn alignment_index(alignment: usize) -> usize {
        if alignment > MAX_SPECIFIC_ALIGNMENT {
            return MAX_ALIGNMENT_INDEX;
        }

        log2_of_power_of_2(alignment)
    }

    /// Returns the alignment index for the chunk content addr.
    ///
    /// # Safety
    ///
    /// `chunk_content_addr` must be aligned to `MIN_ALIGNMENT`.
    pub unsafe fn alignment_index_of_chunk_content_addr(chunk_content_addr: usize) -> usize {
        // find the largest n such that 2^n divides the content address.
        let largest_power_of_2_that_divides_addr = chunk_content_addr.trailing_zeros() as usize;
        let alignment_index = largest_power_of_2_that_divides_addr - MIN_ALIGNMENT_LOG2;

        core::cmp::min(alignment_index, MAX_ALIGNMENT_INDEX)
    }

    /// Returns an iterator over all the smallbins that you need to check for an
    /// allocation request with the given parameters.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub unsafe fn optimal_chunks<'a>(
        &'a self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> impl Iterator<Item = OptimalChunk> + 'a {
        let perfect_size_fit_smallbin_index = (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT;
        let used_smallbins_end_index = core::cmp::min(
            perfect_size_fit_smallbin_index + OPTIMAL_SMALLBIN_LOOKAHEAD,
            SMALLBINS_AMOUNT,
        );
        self.small_bins[perfect_size_fit_smallbin_index..used_smallbins_end_index]
            .iter()
            .enumerate()
            .filter(move |(_, small_bin)| {
                small_bin
                    .contains_alignments_bitmap
                    .contains_aligment_greater_or_equal_to(alignment)
            })
            .map(move |(offset_from_optimal_smallbin, smallbin)| {
                // calculate the size of the current smallbin.
                let end_padding = offset_from_optimal_smallbin * MIN_ALIGNMENT;

                // get all the sub-bins with a valid alignment
                smallbin.alignment_sub_bins[alignment_index..]
                    .iter()
                    .filter_map(|sub_bin| sub_bin.fd)
                    .map(move |sub_bin_first_chunk| OptimalChunk {
                        ptr: sub_bin_first_chunk,
                        end_padding,
                    })
            })
            .flatten()
    }

    /// Returns an iterator over all the smallbins that you need to check for an
    /// allocation request with the given parameters, after failing to allocate
    /// using the other bin.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub fn suboptimal_chunks<'a>(&'a self, size: usize) -> impl Iterator<Item = FreeChunkPtr> + 'a {
        let perfect_size_fit_smallbin_index = (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT;

        // if we failed to allocate from the other bin, we should try to allocate from
        // the smallbins, using chunks that are unaligned.
        //
        // there is no point in trying the perfect size fit smallbin, since that one can
        // fit the allocation only if it is aligned, and we know that it's not
        // aligned because we already tried that.
        //
        // there is also no point on trying the chunks in the range of the smallbin
        // lookahead because, if we know that they don't have aligned chunks,
        // then we know that the allocation will be unaligned, which means that
        // there will be at least `MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER` bytes of start
        // padding, but the lookahead is defined as such that the sizes of the smallbins
        // in is smaller than the optimal size + `MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER`.
        self.small_bins[perfect_size_fit_smallbin_index + 1..SMALLBINS_AMOUNT]
            .iter()
            .map(move |small_bin| small_bin.alignment_sub_bins.iter())
            .flatten()
            .filter_map(move |sub_bin| sub_bin.fd)
    }

    /// Calculates the alignment corresponding to the given alignment index.
    fn alignment_of_alignment_index(alignment_index: usize) -> usize {
        1 << (alignment_index + MIN_ALIGNMENT_LOG2)
    }

    /// Returns fd and bk pointers for inserting a free chunk into the smallbin
    /// with the given index, and in it, into the sub-bin with the given
    /// alignment index.
    ///
    /// This also updates the contains alignment bitmap of the smallbin, such
    /// that it is marked that a chunk with the given alignment is present in
    /// the smallbin.
    ///
    /// # Safety
    ///
    /// After calling this function, the chunk must be inserted into the
    /// smallbin using the returned pointers.
    pub unsafe fn get_fd_and_bk_pointers_for_inserting_to_smallbin(
        &mut self,
        smallbin_index: usize,
        alignment_index: usize,
    ) -> (Option<FreeChunkPtr>, *mut Option<FreeChunkPtr>) {
        // update the contains alignment bitmap that a chunk with the given aligment is
        // now present in the smallbin.
        let smallbin = &mut self.small_bins[smallbin_index];

        smallbin
            .contains_alignments_bitmap
            .set_contains_alignment(alignment_index);

        let mut alignment_sub_bin = smallbin.alignment_sub_bins[alignment_index];

        (alignment_sub_bin.fd, &mut alignment_sub_bin.fd)
    }

    /// Updates the contains alignment bitmap of the smallbin with the given
    /// index, after removing a chunk from the sub-bin with the given alignment.
    pub fn update_smallbin_after_removing_chunk_from_its_sub_bin(
        &mut self,
        smallbin_index: usize,
        alignment_index: usize,
    ) {
        let smallbin = &mut self.small_bins[smallbin_index];

        // if the sub-bin is now empty, update the bitmap
        if smallbin.alignment_sub_bins[alignment_index].fd.is_none() {
            smallbin
                .contains_alignments_bitmap
                .unset_contains_alignment(alignment_index)
        }
    }
}

/// Information about an optimal chunk for some allocation requirements.
pub struct OptimalChunk {
    /// A pointer to the chunk.
    pub ptr: FreeChunkPtr,

    /// The end padding that will be left if this chunk is used for the given
    /// allocation requirements.
    pub end_padding: usize,
}

/// A small bin, which is made up of alignment sub-bins.
#[derive(Clone, Copy)]
pub struct SmallBin {
    alignment_sub_bins: [AlignmentSubBin; ALIGNMENT_SUB_BINS_AMOUNT],
    contains_alignments_bitmap: ContainsAlignmentsBitmap,
}

impl SmallBin {
    /// Creates a new empty smallbin
    pub const fn new() -> Self {
        Self {
            alignment_sub_bins: [AlignmentSubBin::new(); ALIGNMENT_SUB_BINS_AMOUNT],
            contains_alignments_bitmap: ContainsAlignmentsBitmap::new(),
        }
    }
}

impl Default for SmallBin {
    fn default() -> Self {
        Self::new()
    }
}

/// An alignment sub-bin, which is a linked list of chunks with the same size
/// and alignment.
#[derive(Clone, Copy)]
pub struct AlignmentSubBin {
    /// A pointer to the first chunk in the bin, if any.
    fd: Option<FreeChunkPtr>,
}

impl AlignmentSubBin {
    /// Creates a new empty alignment sub-bin.
    pub const fn new() -> Self {
        Self { fd: None }
    }
}

impl Default for AlignmentSubBin {
    fn default() -> Self {
        Self::new()
    }
}

/// A bitmap which tells us whether the bin that this bitmap belongs to contains
/// a chunk with a specific alignment.
#[derive(Clone, Copy)]
pub struct ContainsAlignmentsBitmap {
    bitmap: AlignmentSubBinsBitmapType,
}

impl ContainsAlignmentsBitmap {
    /// Creates a new empty contains alignments bitmap, which indicates that the
    /// smallbin contains no alignments.
    pub const fn new() -> Self {
        Self { bitmap: 0 }
    }

    /// Checks if the smallbin with the given index contains a chunk with an
    /// alignment greater than or equal to the given alignment.
    pub fn contains_aligment_greater_or_equal_to(&self, alignment: usize) -> bool {
        self.bitmap as usize > (alignment >> MIN_ALIGNMENT_LOG2)
    }

    /// Marks the bitmap such that it indicates that a chunk with the given
    /// alignment index is present in the smallbin.
    pub fn set_contains_alignment(&mut self, alignment_index: usize) {
        let alignment = SmallBins::alignment_of_alignment_index(alignment_index);
        self.bitmap |= alignment as AlignmentSubBinsBitmapType;
    }

    /// Marks the bitmap such that it indicates that a chunk with the given
    /// alignment index is not present in the smallbin.
    pub fn unset_contains_alignment(&mut self, alignment_index: usize) {
        let alignment = SmallBins::alignment_of_alignment_index(alignment_index);
        self.bitmap &= !(alignment as AlignmentSubBinsBitmapType);
    }
}
