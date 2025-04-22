// src/checked_ceil_div.rs

//! Defines performing checked ceiling division for different types

use crate::uint::U256; 

/// Perform a division that rounds up to the nearest integer, returning
/// the (quotient, adjusted_divisor) as a tuple.
///
/// This implementation aims to find the smallest divisor `d'` such that
/// `ceil(dividend / divisor) * d' >= dividend`.
///
/// It first calculates the ceiling of the quotient (`q = ceil(dividend / divisor)`).
/// Then, it calculates a new divisor `d' = ceil(dividend / q)`.
///
/// This method helps in scenarios like proportional distribution where you need
/// to ensure the allocated amount (using the ceiling quotient) can be derived
/// from a potentially adjusted rate (the new divisor).
///
/// Example: 10 / 3
/// - Initial quotient = 10 / 3 = 3 (integer division)
/// - Remainder = 10 % 3 = 1
/// - Since remainder > 0, ceiling quotient = 3 + 1 = 4
/// - Recalculate divisor = 10 / 4 = 2 (integer division)
/// - Remainder of recalc = 10 % 4 = 2
/// - Since recalc remainder > 0, final divisor = 2 + 1 = 3
/// - Result: (4, 3) -> Meaning 4 * 3 >= 10
///
/// Example: 12 / 5
/// - Initial quotient = 12 / 5 = 2
/// - Remainder = 12 % 5 = 2
/// - Since remainder > 0, ceiling quotient = 2 + 1 = 3
/// - Recalculate divisor = 12 / 3 = 4
/// - Remainder of recalc = 12 % 3 = 0
/// - Since recalc remainder == 0, final divisor = 4
/// - Result: (3, 4) -> Meaning 3 * 4 >= 12
///
/// Fails if the divisor is 0, or if the initial division results in a quotient of 0
/// (i.e., dividend < divisor), to avoid nonsensical results like 1 / 1000 = 1.
pub trait CheckedCeilDiv: Sized + Copy + Ord + std::fmt::Debug {
    /// Perform ceiling division.
    /// Returns `None` if `rhs` is zero, or if `self < rhs`, or on overflow.
    /// Otherwise, returns `Some((ceiling_quotient, adjusted_divisor))`.
    fn checked_ceil_div(&self, rhs: Self) -> Option<(Self, Self)>;
}

// --- Implementation for u64 ---
impl CheckedCeilDiv for u64 {
    fn checked_ceil_div(&self, mut rhs: Self) -> Option<(Self, Self)> {
        if rhs == 0 {
            return None; // Explicitly check for division by zero
        }
        // Perform initial checked division
        let mut quotient = self.checked_div(rhs)?; // Returns None on overflow (shouldn't happen for div)

        // If dividend < divisor, quotient is 0. Per trait doc, return None.
        if quotient == 0 && *self > 0 {
             // Handle self=0 case separately if needed, though 0/rhs should yield quotient 0.
             // If self > 0 and quotient is 0, it means self < rhs.
            return None;
        }
        // Handle the edge case 0 / rhs = 0. Ceil(0) is 0.
        // Let's return (0, rhs) or perhaps None depending on desired semantics for 0 dividend?
        // The current logic implicitly handles 0/rhs correctly if we proceed.
        // 0 / 5 -> quotient 0. Remainder 0. Returns Some((0, 5)). Seems reasonable.


        // Ceiling the destination amount if there's any remainder.
        let remainder = self.checked_rem(rhs)?; // Returns None if rhs is 0 (already checked)
        if remainder > 0 {
            quotient = quotient.checked_add(1)?; // Ceil the quotient, return None on overflow

            // Calculate the minimum *integer* divisor needed such that
            // new_divisor * quotient >= self. This is achieved by ceil(self / quotient).
            rhs = self.checked_div(quotient)?; // Recalculate rhs based on the *new* quotient

            // Check if self / quotient had a remainder
            let remainder_after_adjustment = self.checked_rem(quotient)?; // quotient cannot be 0 here
            if remainder_after_adjustment > 0 {
                // If there was a remainder, ceiling the recalculated rhs
                rhs = rhs.checked_add(1)?; // Return None on overflow
            }
        }
        Some((quotient, rhs))
    }
}


// --- Implementation for u128 ---
impl CheckedCeilDiv for u128 {
    fn checked_ceil_div(&self, mut rhs: Self) -> Option<(Self, Self)> {
        if rhs == 0 {
            return None;
        }
        let mut quotient = self.checked_div(rhs)?;
        if quotient == 0 && *self > 0 {
           return None;
        }

        let remainder = self.checked_rem(rhs)?;
        if remainder > 0 {
            quotient = quotient.checked_add(1)?;
            rhs = self.checked_div(quotient)?;
            let remainder_after_adjustment = self.checked_rem(quotient)?;
            if remainder_after_adjustment > 0 {
                rhs = rhs.checked_add(1)?;
            }
        }
        Some((quotient, rhs))
    }
}

// --- Implementation for U256 ---
impl CheckedCeilDiv for U256 {
    fn checked_ceil_div(&self, mut rhs: Self) -> Option<(Self, Self)> {
        let zero = U256::from(0u8); // Use u8 for clarity
        let one = U256::from(1u8);

        if rhs == zero {
            return None;
        }
        let mut quotient = self.checked_div(rhs)?;
        if quotient == zero && *self > zero {
           return None;
        }

        let remainder = self.checked_rem(rhs)?;
        if remainder > zero {
            quotient = quotient.checked_add(one)?;
            rhs = self.checked_div(quotient)?;
            let remainder_after_adjustment = self.checked_rem(quotient)?;
            if remainder_after_adjustment > zero {
                rhs = rhs.checked_add(one)?;
            }
        }
        Some((quotient, rhs))
    }
}


// --- Add Tests ---
#[cfg(test)]
mod tests {
    use super::*; // Import items from parent module (CheckedCeilDiv trait and impls)
    use crate::uint::U256; // Import U256 specifically if needed for tests

    // --- u64 Tests ---
    #[test]
    fn test_checked_ceil_div_u64() {
        // Exact division
        assert_eq!(10u64.checked_ceil_div(5), Some((2, 5)));
        assert_eq!(12u64.checked_ceil_div(4), Some((3, 4)));
        assert_eq!(u64::MAX.checked_ceil_div(1), Some((u64::MAX, 1)));

        // Division with remainder
        assert_eq!(10u64.checked_ceil_div(3), Some((4, 3))); // 10/3 = 3 rem 1 -> ceil 4. 10/4 = 2 rem 2 -> ceil 3. (4, 3)
        assert_eq!(11u64.checked_ceil_div(3), Some((4, 3))); // 11/3 = 3 rem 2 -> ceil 4. 11/4 = 2 rem 3 -> ceil 3. (4, 3)
        assert_eq!(12u64.checked_ceil_div(5), Some((3, 4))); // 12/5 = 2 rem 2 -> ceil 3. 12/3 = 4 rem 0 -> ceil 4. (3, 4)
        assert_eq!(1u64.checked_ceil_div(3), None); // Fails because 1 < 3

        // Edge cases
        assert_eq!(5u64.checked_ceil_div(10), None); // Dividend < Divisor
        assert_eq!(0u64.checked_ceil_div(5), Some((0, 5))); // Zero dividend
        assert_eq!(10u64.checked_ceil_div(0), None); // Division by zero
        assert_eq!(u64::MAX.checked_ceil_div(u64::MAX), Some((1, u64::MAX)));
        assert_eq!((u64::MAX - 1).checked_ceil_div(u64::MAX), None);

        // Overflow case (quotient + 1)
        assert_eq!(u64::MAX.checked_ceil_div(2), Some(((u64::MAX / 2) + 1, 2))); // Quotient = MAX/2. Rem = 1. Ceil = MAX/2 + 1.
                                                                                 // Recalc rhs = MAX / (MAX/2 + 1). Should be 1 rem something.
                                                                                 // Ceil rhs = 1 + 1 = 2. -> (MAX/2 + 1, 2)
        // Overflow case (rhs + 1) - Harder to construct for u64, maybe not possible without MAX dividend/quotient
        // Consider if checked_add on rhs could overflow. If quotient is 1, rhs won't overflow.
        // If quotient is 2, self must be >= 2. rhs = self.checked_div(2). rem = self.checked_rem(2).
        // If rem > 0, rhs_adj = rhs.checked_add(1). This can only overflow if rhs = MAX.
        // rhs = MAX only if self/2 = MAX, which means self = MAX*2 or MAX*2+1 (overflows u64).
        // So, rhs won't overflow u64 in the adjustment step.

         // Check a case where the adjusted divisor becomes smaller
         assert_eq!(99u64.checked_ceil_div(10), Some((10, 10))); // 99/10=9rem9 -> ceil 10. 99/10=9rem9 -> ceil 10. (10,10)
         assert_eq!(91u64.checked_ceil_div(10), Some((10, 10))); // 91/10=9rem1 -> ceil 10. 91/10=9rem1 -> ceil 10. (10,10)
         assert_eq!(100u64.checked_ceil_div(10), Some((10, 10))); // 100/10=10rem0 -> (10,10)


    }

    // You might want to add similar specific test functions for u128 and U256
    // or keep them combined if they were already tested elsewhere.
    #[test]
    fn test_checked_ceil_div_u128() {
        // Add specific u128 tests if needed
        assert_eq!(10u128.checked_ceil_div(3), Some((4, 3)));
        assert_eq!(5u128.checked_ceil_div(10), None);
        assert_eq!(0u128.checked_ceil_div(5), Some((0, 5)));
        assert_eq!(10u128.checked_ceil_div(0), None);
    }

     #[test]
    fn test_checked_ceil_div_u256() {
        // Add specific U256 tests if needed
        let ten = U256::from(10u8);
        let three = U256::from(3u8);
        let five = U256::from(5u8);
        let zero = U256::from(0u8);
        let four = U256::from(4u8);

        assert_eq!(ten.checked_ceil_div(three), Some((four, three)));
        assert_eq!(five.checked_ceil_div(ten), None);
        assert_eq!(zero.checked_ceil_div(five), Some((zero, five)));
        assert_eq!(ten.checked_ceil_div(zero), None);
    }
}