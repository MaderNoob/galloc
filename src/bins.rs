use static_assertions::const_assert;

use crate::{
    chunks::FreeChunkPtr, HEADER_SIZE, MIN_ALIGNMENT, MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
};

pub const SMALLBINS_AMOUNT: usize = 20;
pub const ALIGNMENT_SUB_BINS_AMOUNT: usize = 8;

/// The max alignment index that has a specific sub-bin in which all chunks have
/// that alignment.
pub const MAX_SPECIFIC_ALIGNMENT_INDEX: usize = ALIGNMENT_SUB_BINS_AMOUNT - 1 - 1;

/// The max alignment that has a specific sub-bin in which all chunks have that
/// alignment.
pub const MAX_SPECIFIC_ALIGNMENT: usize = 1 << (MAX_SPECIFIC_ALIGNMENT_INDEX + 3);

type AlignmentSubBinsBitmapType = u8;

const SMALLEST_SMALLBIN_SIZE: usize = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;
const LARGEST_SMALLBIN_SIZE: usize = SMALLEST_SMALLBIN_SIZE + SMALLBINS_AMOUNT * MIN_ALIGNMENT;

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
pub unsafe fn log2_of_power_of_2(x: usize) -> usize {
    (x - 1).count_ones() as usize
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

    /// Returns the alignment index for the given alignment.
    ///
    /// # Safety
    ///
    /// `alignment` must be a power of 2.
    pub unsafe fn alignment_index(alignment: usize) -> usize {
        if alignment > MAX_SPECIFIC_ALIGNMENT {
            return ALIGNMENT_SUB_BINS_AMOUNT - 1;
        }

        log2_of_power_of_2(alignment)
    }

    /// Returns an iterator over all the smallbins that you need to check for an
    /// allocation request with the given parameters.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub unsafe fn smallbins_to_check<'a>(
        &'a self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> impl Iterator<Item = FreeChunkPtr> + 'a {
        let perfect_fit_smallbin_index = (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT;
        let used_smallbins_end_index =
            core::cmp::min(perfect_fit_smallbin_index + 4, SMALLBINS_AMOUNT);
        self.small_bins[perfect_fit_smallbin_index..used_smallbins_end_index]
            .iter()
            .filter(move |small_bin| {
                small_bin
                    .contains_alignments_bitmap
                    .contains_aligment_greater_or_equal_to(alignment)
            })
            .map(move |smallbin| {
                // get all the sub-bins with a valid alignment
                smallbin.alignment_sub_bins[alignment_index..].iter()
            })
            .flatten()
            .filter_map(move |sub_bin| sub_bin.fd)
    }

    /// Returns an iterator over all the smallbins that you need to check for an
    /// allocation request with the given parameters, after failing to allocate
    /// using the other bin.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub fn smallbins_to_check_after_failing_with_other_bin<'a>(
        &'a self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> impl Iterator<Item = FreeChunkPtr> + 'a {
        let perfect_fit_smallbin_index = (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT;

        let already_used_smallbins_end_index =
            core::cmp::min(perfect_fit_smallbin_index + 4, SMALLBINS_AMOUNT);

        // if we failed to allocate from the other bin, we should try to allocate from
        // the smallbins, using chunks that are unaligned.
        //
        // there is no point in trying the perfect fit smallbin, since that one can fit
        // the allocation only if it is aligned, and we know that it's not aligned
        // because we already tried that.
        //
        // in the chunks that are in the range
        // `perfect_fit_smallbin_index..already_used_smallbins_end_index`, we only need
        // to check the sub-bins with alignment lower than the allocation's
        // requirements, because for these chunks we have already checked the sub-bins
        // with alignments greater than or equal to the allocation requirement.
        self.small_bins[perfect_fit_smallbin_index + 1..SMALLBINS_AMOUNT]
            .iter()
            .enumerate()
            .map(move |(offset_relative_perfect_fit_plus_one, small_bin)| {
                if offset_relative_perfect_fit_plus_one < 3 {
                    // in this case, this chunk's aligned sub-bins were already
                    // checked, so only check the unaligned ones.
                    small_bin.alignment_sub_bins[..alignment_index].iter()
                } else {
                    // in this case, this chunk's sub-bins hasn't been checked
                    // at all yet, so check all of them.
                    small_bin.alignment_sub_bins.iter()
                }
            })
            .flatten()
            .filter_map(move |sub_bin| sub_bin.fd)
    }
}

/// A small bin, which is made up of alignment sub-bins.
#[derive(Clone, Copy)]
pub struct SmallBin {
    alignment_sub_bins: [AlignmentSubBin; ALIGNMENT_SUB_BINS_AMOUNT],
    contains_alignments_bitmap: ContainsAlignmentsBitmap,
    largest_alignment: usize,
}

impl SmallBin {
    /// Creates a new empty smallbin
    pub const fn new() -> Self {
        Self {
            alignment_sub_bins: [AlignmentSubBin::new(); ALIGNMENT_SUB_BINS_AMOUNT],
            contains_alignments_bitmap: ContainsAlignmentsBitmap::new(),
            largest_alignment: 0,
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
}

impl ContainsAlignmentsBitmap {
    /// Checks if the smallbin with the given index contains a chunk with an
    /// alignment greater than or equal to the given alignment.
    pub fn contains_aligment_greater_or_equal_to(&self, alignment: usize) -> bool {
        self.bitmap as usize > (alignment >> 3)
    }
}
