/// Align downwards. Returns the greatest x with alignment `align`
/// so that x <= addr.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn align_down(n: usize, align: usize) -> usize {
    if align.is_power_of_two() {
        n & !(align - 1)
    } else if align == 0 {
        n
    } else {
        panic!("`align` must be a power of 2");
    }
}

/// Align upwards. Returns the smallest x with alignment `align`
/// so that x >= addr.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn align_up(n: usize, align: usize) -> usize {
    align_down(n + align - 1, align)
}

/// Checks if the given value is aligned to the given alignment.
///
/// # Safety
///
/// `align` must be a power of 2.
pub unsafe fn is_aligned(n: usize, align: usize) -> bool {
    n & (align - 1) == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_aligned() {
        // test multiple powers of 2
        for i in 1..=20 {
            let power_of_2 = 1 << i;
            let aligned_num = power_of_2 * 2451;
            assert!(unsafe { is_aligned(aligned_num, power_of_2) });
            assert!(unsafe { !is_aligned(aligned_num + power_of_2 / 2, power_of_2) })
        }
    }

    #[test]
    fn test_align_down() {
        // test multiple powers of 2
        for i in 1..=20 {
            let power_of_2 = 1 << i;
            let aligned_num = power_of_2 * 2451;

            // make sure that align down doesn't change a value that's already aligned.
            assert_eq!(unsafe { align_down(aligned_num, power_of_2) }, aligned_num);

            assert_eq!(
                unsafe { align_down(aligned_num + power_of_2 / 2, power_of_2) },
                aligned_num
            )
        }
    }

    #[test]
    fn test_align_up() {
        // test multiple powers of 2
        for i in 1..=20 {
            let power_of_2 = 1 << i;
            let aligned_num = power_of_2 * 2451;

            // make sure that align up doesn't change a value that's already aligned.
            assert_eq!(unsafe { align_up(aligned_num, power_of_2) }, aligned_num);

            assert_eq!(
                unsafe { align_up(aligned_num - power_of_2 / 2, power_of_2) },
                aligned_num
            )
        }
    }
}
