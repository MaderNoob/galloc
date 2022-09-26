/// A usize that is guaranteed to be divisible by 4, which allows storing 2
/// additional bits of information in it.
#[repr(transparent)]
pub struct DivisbleBy4Usize(usize);

impl DivisbleBy4Usize {
    /// Creates divisble by 4 usize if the given value is divisble by 4, and
    /// stores the given additional bits in it.
    pub fn new(n: usize, additional_bit1: bool, additional_bit2: bool) -> Option<Self> {
        if n & 0b11 != 0 {
            return None;
        }
        unsafe {
            // SAFETY: we just checked that this is safe
            Some(Self::new_unchecked(n, additional_bit1, additional_bit2))
        }
    }

    /// Creates a divisible by 4 usize without checking if the given value is
    /// divisible by 4, and stores the given additional bits in it.
    /// This results in undefined behaviour if the value is not divisible by 4.
    pub unsafe fn new_unchecked(n: usize, additional_bit1: bool, additional_bit2: bool) -> Self {
        Self(n | usize::from(additional_bit1) | usize::from(additional_bit2) << 1)
    }

    /// Returns the divisble by 4 value as a `usize`.
    pub fn value(&self) -> usize {
        self.0 & (!0b11)
    }

    /// Returns the first additional bit of information stored within the
    /// number.
    pub fn additional_bit1(&self) -> bool {
        self.0 & 1 != 0
    }

    /// Returns the second additional bit of information stored within the
    /// number.
    pub fn additional_bit2(&self) -> bool {
        (self.0 >> 1) & 1 != 0
    }

    /// Sets the value of this divisble by 4 usize to the given value, without
    /// changing the additional bits stored within the number.
    ///
    /// # Safety
    ///
    /// The new value must be divisble by 4, otherwise the function panics.
    pub fn set_value(&mut self, new_value: usize) {
        if new_value & 0b11 != 0 {
            panic!("the value of a divisible by 4 usize must be divisble by 4");
        }
        self.0 = new_value | self.0 & 0b11;
    }

    /// Sets the first additional bit of information atores within the number.
    pub fn set_additional_bit1(&mut self, new_value: bool) {
        self.0 = (self.0 | 1) ^ usize::from(!new_value)
    }

    /// Sets the second additional bit of information atores within the number.
    pub fn set_additional_bit2(&mut self, new_value: bool) {
        self.0 = (self.0 | 0b10) ^ (usize::from(!new_value) << 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn return_none_if_usize_is_not_divisible_by_4() {
        assert!(DivisbleBy4Usize::new(7, false, false).is_none())
    }

    #[test]
    fn returns_some_if_usize_is_divisible_by_4() {
        assert!(DivisbleBy4Usize::new(8, false, false).is_some())
    }

    #[test]
    fn saves_additional_bits_correctly() {
        let u = DivisbleBy4Usize::new(24, true, false).unwrap();
        assert_eq!(u.additional_bit1(), true);
        assert_eq!(u.additional_bit2(), false);
    }

    #[test]
    fn set_values_updates_values_and_doesnt_change_other_values() {
        let mut u = DivisbleBy4Usize::new(24, false, false).unwrap();

        u.set_additional_bit1(true);
        assert_eq!(u.additional_bit1(), true);
        assert_eq!(u.additional_bit2(), false);
        assert_eq!(u.value(), 24);

        u.set_additional_bit1(false);
        assert_eq!(u.additional_bit1(), false);
        assert_eq!(u.additional_bit2(), false);
        assert_eq!(u.value(), 24);

        u.set_additional_bit2(true);
        assert_eq!(u.additional_bit1(), false);
        assert_eq!(u.additional_bit2(), true);
        assert_eq!(u.value(), 24);

        u.set_additional_bit2(false);
        assert_eq!(u.additional_bit1(), false);
        assert_eq!(u.additional_bit2(), false);
        assert_eq!(u.value(), 24);

        u.set_value(44);
        assert_eq!(u.additional_bit1(), false);
        assert_eq!(u.additional_bit2(), false);
        assert_eq!(u.value(), 44);
    }
}
