use core::marker::PhantomData;

use either::Either;

use crate::{
    alignment::is_aligned,
    chunks::FreeChunkPtr,
    smallest_type_which_has_at_least_n_bits::{
        ContainsAlignmentsBitmapTrait, SmallestTypeWhichHasAtLeastNBits,
        SmallestTypeWhichHasAtLeastNBitsStruct, SmallestTypeWhichHasAtLeastNBitsTrait,
    },
    HEADER_SIZE, MIN_ALIGNMENT, MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER,
};

/// The default amount of smallbins used by the allocator.
pub const DEFAULT_SMALLBINS_AMOUNT: usize = 20;

/// The default amount of alignemnt sub-bins used by the allocator.
pub const DEFAULT_ALIGNMENT_SUB_BINS_AMOUNT: usize = 8;

pub const MIN_ALIGNMENT_LOG2: usize = unsafe { log2_of_power_of_2(MIN_ALIGNMENT) };

const SMALLEST_SMALLBIN_SIZE: usize = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER - HEADER_SIZE;

const OPTIMAL_SMALLBIN_LOOKAHEAD: usize = MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER / MIN_ALIGNMENT;

/// Computes log2(x) where x is a power of 2.
///
/// # Safety
///
/// `x` must be a power of 2
pub const unsafe fn log2_of_power_of_2(x: usize) -> usize {
    x.trailing_zeros() as usize
}

/// A collection of small bins, used in the allocator.
#[derive(Debug)]
pub struct SmallBins<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    pub(crate) small_bins: [SmallBin<ALIGNMENT_SUB_BINS_AMOUNT>; SMALLBINS_AMOUNT],
}

impl<const SMALLBINS_AMOUNT: usize, const ALIGNMENT_SUB_BINS_AMOUNT: usize>
    SmallBins<SMALLBINS_AMOUNT, ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    const LARGEST_SMALLBIN_SIZE: usize = if SMALLBINS_AMOUNT == 0 {
        0
    } else {
        SMALLEST_SMALLBIN_SIZE + (SMALLBINS_AMOUNT - 1) * MIN_ALIGNMENT
    };
    pub const MAX_ALIGNMENT_INDEX: usize = ALIGNMENT_SUB_BINS_AMOUNT - 1;
    /// The max alignment that has a specific sub-bin in which all chunks have
    /// that alignment.
    pub const MAX_SPECIFIC_ALIGNMENT: usize =
        1 << (Self::MAX_SPECIFIC_ALIGNMENT_INDEX + MIN_ALIGNMENT_LOG2);
    /// The max alignment index that has a specific sub-bin in which all chunks
    /// have that alignment.
    pub const MAX_SPECIFIC_ALIGNMENT_INDEX: usize = ALIGNMENT_SUB_BINS_AMOUNT - 1 - 1;

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
        size <= Self::LARGEST_SMALLBIN_SIZE
    }

    /// Returns the index of the smallbin containing chunks of the given size,
    /// if such a small bin exists.
    ///
    /// # Safety
    ///
    /// The size must have been prepared.
    pub unsafe fn smallbin_index(size: usize) -> Option<usize> {
        if size > Self::LARGEST_SMALLBIN_SIZE {
            return None;
        }

        // SAFETY: we just checked that the size is a smallbin size, and that
        // it's not too large.
        Some(Self::smallbin_index_unchecked(size))
    }

    /// Returns the index of the smallbin containing chunks of the given size,
    /// if such a small bin exists.
    ///
    /// # Safety
    ///
    /// The size must have been prepared, and must be the size of a smallbin.
    pub unsafe fn smallbin_index_unchecked(size: usize) -> usize {
        (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT
    }

    /// Returns the alignment index for the given alignment.
    ///
    /// # Safety
    ///
    /// `alignment` must be a power of 2.
    pub unsafe fn alignment_index(alignment: usize) -> usize {
        if alignment > Self::MAX_SPECIFIC_ALIGNMENT {
            return Self::MAX_ALIGNMENT_INDEX;
        }

        log2_of_power_of_2(alignment) - MIN_ALIGNMENT_LOG2
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

        core::cmp::min(alignment_index, Self::MAX_ALIGNMENT_INDEX)
    }

    /// Returns the smallbin index whose size is a perfect fit for the provided
    /// size.
    ///
    /// # Safety
    ///
    /// The size must have been prepared.
    unsafe fn perfect_size_fit_smallbin_index(size: usize) -> usize {
        (size - SMALLEST_SMALLBIN_SIZE) / MIN_ALIGNMENT
    }

    /// Returns a pointer to an optimal chunk, which will fit the allocation
    /// without splitting any free chunks from it, meaning that the returned
    /// chunk can be used with `alloc_aligned_no_end_padding`.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub unsafe fn optimal_chunk(
        &self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> Option<FreeChunkPtr> {
        let perfect_size_fit_smallbin_index = Self::perfect_size_fit_smallbin_index(size);
        let used_smallbins_end_index = core::cmp::min(
            perfect_size_fit_smallbin_index + OPTIMAL_SMALLBIN_LOOKAHEAD,
            SMALLBINS_AMOUNT,
        );

        Self::get_first_aligned_chunk(
            alignment,
            alignment_index,
            &self.small_bins[perfect_size_fit_smallbin_index..used_smallbins_end_index],
        )
    }

    /// Returns a pointer to an optimal chunk, which will fit the allocation
    /// without splitting any free chunks from it, meaning that the returned
    /// chunk can be used with `alloc_aligned_no_end_padding`.

    /// Returns a pointer to an aligned suboptimal chunk, which is aligned to
    /// the provided alignment, but is large enough that the end padding will be
    /// enough for an entire free chunk.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub unsafe fn aligned_suboptimal_chunk(
        &self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> Option<AlignedSuboptimalChunk> {
        // find the index where the optimal smallbins end.
        // we want to use the suboptimal smallbins, which are right after the optimal
        // ones.
        let perfect_size_fit_smallbin_index = Self::perfect_size_fit_smallbin_index(size);
        let optimal_smallbins_end = perfect_size_fit_smallbin_index + OPTIMAL_SMALLBIN_LOOKAHEAD;

        // if the optimal smallbins reach the end of the smallbins, then there are no
        // suboptimal smallbins
        if optimal_smallbins_end >= SMALLBINS_AMOUNT {
            return None;
        }

        let mut chunk_ptr = Self::get_first_aligned_chunk(
            alignment,
            alignment_index,
            &self.small_bins[optimal_smallbins_end..],
        )?;

        let end_padding = chunk_ptr.as_mut().size() - size;

        Some(AlignedSuboptimalChunk {
            chunk_ptr,
            end_padding,
        })
    }

    /// Returns an iterator over all unaligned suboptimal chunks for the
    /// provided allocation requirements. When allocating this chunks, at least
    /// 1 free chunk of start padding will be created, and optionally another
    /// end padding chunk may need to be created.
    ///
    /// The returned chunks are guaranteed to be unaligned, and may not be large
    /// enough for allocating the given allocation requirements after finding an
    /// aligned address.
    ///
    /// If there are no suboptimal smallbins at all, the function returns
    /// `None`, otherwise it returns an iterator over the unaligned
    /// suboptimal chunks.
    ///
    /// # Safety
    ///
    ///  - The size and alignment must be prepared.
    ///  - The size must be the size of a smallbin.
    pub unsafe fn unaligned_suboptimal_chunks<'a>(
        &'a self,
        size: usize,
        alignment: usize,
        alignment_index: usize,
    ) -> Option<
        // this function returns 2 different iterator types depending on whether the
        // alignment index is specific or not, so we wrap these 2 types in `Either`,
        // which implements the `Iterator` trait for them.
        Either<impl Iterator<Item = FreeChunkPtr> + 'a, impl Iterator<Item = FreeChunkPtr> + 'a>,
    > {
        // find the index where the optimal smallbins end.
        // we want to use the suboptimal smallbins, which are right after the optimal
        // ones.
        let perfect_size_fit_smallbin_index = Self::perfect_size_fit_smallbin_index(size);
        let optimal_smallbins_end = perfect_size_fit_smallbin_index + OPTIMAL_SMALLBIN_LOOKAHEAD;

        // if the optimal smallbins reach the end of the smallbins, then there are no
        // suboptimal smallbins.
        if optimal_smallbins_end >= SMALLBINS_AMOUNT {
            return None;
        }

        // check all the suboptimal smallbins, which start right where the optimal
        // smallbins end.
        let smallbins_to_check = self.small_bins[optimal_smallbins_end..].iter();

        if alignment_index > Self::MAX_SPECIFIC_ALIGNMENT_INDEX {
            // if the alignment index is non-specific, check all the chunks in the non
            // specific alignment sub-bin, and find the ones that are unaligned.
            Some(Either::Left(
                smallbins_to_check
                    .map(move |small_bin| {
                        // take all the chunks from the non-specific alignment sub-bin. we need all
                        // chunks and not only the first because each chunk has a different
                        // alignment, so even if one doesn't work, the other might work.
                        small_bin.alignment_sub_bins[Self::MAX_ALIGNMENT_INDEX].chunks()
                    })
                    .flatten()
                    .filter(move |&(mut chunk_ptr)| {
                        let chunk = chunk_ptr.as_mut();

                        // find all chunks that are unaligned
                        !is_aligned(chunk.content_addr(), alignment)
                    }),
            ))
        } else {
            // if the alignment index is specific, only check alignment sub-bins with
            // alignment index lower than `alignment_index`, because we know for sure that
            // only these chunks will be unaligned.
            Some(Either::Right(
                smallbins_to_check
                    .map(move |small_bin| {
                        // only take alignment sub-bins which are unaligned, which means that their
                        // index is smaller than `alignment_index`.
                        small_bin.alignment_sub_bins[..alignment_index].iter()
                    })
                    .flatten()
                    .filter_map(move |sub_bin| {
                        // take the first chunk in each alignment sub-bin.
                        //
                        // using the first chunk is enough because all chunks in the sub-bin have
                        // the same size and alignment, so it is enough to only check the first one.
                        sub_bin.fd
                    }),
            ))
        }
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

        let alignment_sub_bin = &mut smallbin.alignment_sub_bins[alignment_index];

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

    /// Returns the first chunk which is aligned to the given alignment
    /// from the provided smallbins.
    ///
    /// There is no need to check if the provided smallbins contain chunks with
    /// the provided alignment, this function will do it automatically using
    /// the contains alignment bitmaps.
    fn get_first_aligned_chunk(
        alignment: usize,
        alignment_index: usize,
        smallbins: &[SmallBin<ALIGNMENT_SUB_BINS_AMOUNT>],
    ) -> Option<FreeChunkPtr> {
        if alignment_index > Self::MAX_SPECIFIC_ALIGNMENT_INDEX {
            // if the alignment index is a non specific alignment index, it
            // means that we can't know for sure which chunks in the
            // alignment sub-bins will be well aligned, so we must
            // find one that is aligned.
            smallbins
                .iter()
                .map(move |smallbin| {
                    // the only valid alignment sub-bin is the non specific one
                    // we need to check all chunks in this sub-bin, because each one has a different
                    // alignment and we can't know which ones are aligned.
                    smallbin.alignment_sub_bins[Self::MAX_ALIGNMENT_INDEX].chunks()
                })
                .flatten()
                .filter(|&(mut chunk_ptr)| {
                    let chunk = unsafe { chunk_ptr.as_mut() };

                    // find all chunks that are aligned.
                    // we are checking chunks from the non-specific alignment sub-bin, so we can't
                    // know if they are aligned or not without checking.
                    unsafe { is_aligned(chunk.content_addr(), alignment) }
                })
                .next()
        } else {
            smallbins
                .iter()
                .filter(move |small_bin| {
                    // only take the smallbins which contain chunks with an alignment greater than
                    // or equal to the provided alignment.
                    small_bin
                        .contains_alignments_bitmap
                        .contains_aligment_greater_or_equal_to(alignment)
                })
                .map(move |smallbin| {
                    // get all the sub-bins with a valid alignment
                    smallbin.alignment_sub_bins[alignment_index..]
                        .iter()
                        .filter_map(|sub_bin| {
                            // for each sub-bin, get the first chunk.
                            // it is enough to only check the first chunk because all chunks have
                            // the same size and alignment.
                            sub_bin.fd
                        })
                })
                .flatten()
                .next()
        }
    }
}

/// A small bin, which is made up of alignment sub-bins.
#[derive(Clone, Copy, Debug)]
pub struct SmallBin<const ALIGNMENT_SUB_BINS_AMOUNT: usize>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    pub(crate) alignment_sub_bins: [AlignmentSubBin; ALIGNMENT_SUB_BINS_AMOUNT],
    pub(crate) contains_alignments_bitmap: ContainsAlignmentsBitmap<ALIGNMENT_SUB_BINS_AMOUNT>,
}

impl<const ALIGNMENT_SUB_BINS_AMOUNT: usize> SmallBin<ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    /// Creates a new empty smallbin
    pub const fn new() -> Self {
        Self {
            alignment_sub_bins: [AlignmentSubBin::new(); ALIGNMENT_SUB_BINS_AMOUNT],
            contains_alignments_bitmap: ContainsAlignmentsBitmap::new(),
        }
    }
}

impl<const ALIGNMENT_SUB_BINS_AMOUNT: usize> Default for SmallBin<ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    fn default() -> Self {
        Self::new()
    }
}

/// An alignment sub-bin, which is a linked list of chunks with the same size
/// and alignment.
#[derive(Clone, Copy, Debug)]
pub struct AlignmentSubBin {
    /// A pointer to the first chunk in the bin, if any.
    pub(crate) fd: Option<FreeChunkPtr>,
}

impl AlignmentSubBin {
    /// Creates a new empty alignment sub-bin.
    pub const fn new() -> Self {
        Self { fd: None }
    }

    /// Returns an iterator over the chunks in this alignment sub-bin.
    pub fn chunks(&self) -> AlignmentSubBinChunks {
        AlignmentSubBinChunks {
            cur: self.fd,
            phantom: PhantomData,
        }
    }
}

impl Default for AlignmentSubBin {
    fn default() -> Self {
        Self::new()
    }
}

/// An iterator over the chunks in an alignment sub-bin
pub struct AlignmentSubBinChunks<'a> {
    cur: Option<FreeChunkPtr>,
    phantom: PhantomData<&'a ()>,
}
impl<'a> Iterator for AlignmentSubBinChunks<'a> {
    type Item = FreeChunkPtr;

    fn next(&mut self) -> Option<Self::Item> {
        let mut cur = self.cur?;
        self.cur = unsafe { cur.as_mut() }.fd;
        Some(cur)
    }
}

/// A bitmap which tells us whether the bin that this bitmap belongs to contains
/// a chunk with a specific alignment.
#[derive(Clone, Copy, Debug)]
pub struct ContainsAlignmentsBitmap<const ALIGNMENT_SUB_BINS_AMOUNT: usize>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    bitmap: SmallestTypeWhichHasAtLeastNBits<ALIGNMENT_SUB_BINS_AMOUNT>,
}

impl<const ALIGNMENT_SUB_BINS_AMOUNT: usize> ContainsAlignmentsBitmap<ALIGNMENT_SUB_BINS_AMOUNT>
where
    SmallestTypeWhichHasAtLeastNBitsStruct<ALIGNMENT_SUB_BINS_AMOUNT>:
        SmallestTypeWhichHasAtLeastNBitsTrait,
{
    /// Creates a new empty contains alignments bitmap, which indicates that the
    /// smallbin contains no alignments.
    pub const fn new() -> Self {
        Self {
            bitmap: SmallestTypeWhichHasAtLeastNBits::<ALIGNMENT_SUB_BINS_AMOUNT>::ZERO,
        }
    }

    /// Checks if the smallbin with the given index contains a chunk with an
    /// alignment greater than or equal to the given alignment.
    pub fn contains_aligment_greater_or_equal_to(&self, alignment: usize) -> bool {
        self.bitmap.to_usize() >= (alignment >> MIN_ALIGNMENT_LOG2)
    }

    /// Marks the bitmap such that it indicates that a chunk with the given
    /// alignment index is present in the smallbin.
    pub fn set_contains_alignment(&mut self, alignment_index: usize) {
        let alignment = 1 << alignment_index;
        self.bitmap |=
            SmallestTypeWhichHasAtLeastNBits::<ALIGNMENT_SUB_BINS_AMOUNT>::from_usize(alignment);
    }

    /// Marks the bitmap such that it indicates that a chunk with the given
    /// alignment index is not present in the smallbin.
    pub fn unset_contains_alignment(&mut self, alignment_index: usize) {
        let alignment = 1 << alignment_index;
        self.bitmap &=
            !(SmallestTypeWhichHasAtLeastNBits::<ALIGNMENT_SUB_BINS_AMOUNT>::from_usize(alignment));
    }
}

/// Information about an aligned suboptimal chunk for some allocation
/// requirements.
pub struct AlignedSuboptimalChunk {
    /// A pointer to the chunk
    pub chunk_ptr: FreeChunkPtr,

    /// The amount of end padding that will be left when this chunk will be
    /// allocated for the allocation requirements that were provided.
    ///
    /// This is guaranteed to be greater than or equal to
    /// `MIN_FREE_CHUNK_SIZE_INCLUDING_HEADER`.
    pub end_padding: usize,
}
