#![allow(clippy::arithmetic_side_effects)]
//! Approximation calculations

use {
    num_traits::{CheckedShl, CheckedShr, PrimInt},
    std::cmp::Ordering,
};

/// Calculate square root of the given number
///
/// Code lovingly adapted from the excellent work at:
///
/// <https://github.com/derekdreery/integer-sqrt-rs>
///
/// The algorithm is based on the implementation in:
///
/// <https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)>
pub fn sqrt<T: PrimInt + CheckedShl + CheckedShr>(radicand: T) -> Option<T> {
    match radicand.cmp(&T::zero()) {
        Ordering::Less => return None,             // fail for less than 0
        Ordering::Equal => return Some(T::zero()), // do nothing for 0
        _ => {}
    }

    // Compute bit, the largest power of 4 <= n
    let max_shift: u32 = T::zero().leading_zeros() - 1;
    let shift: u32 = (max_shift - radicand.leading_zeros()) & !1;
    let mut bit = T::one().checked_shl(shift)?;

    let mut n = radicand;
    let mut result = T::zero();
    while bit != T::zero() {
        let result_with_bit = result.checked_add(&bit)?;
        if n >= result_with_bit {
            n = n.checked_sub(&result_with_bit)?;
            result = result.checked_shr(1)?.checked_add(&bit)?;
        } else {
            result = result.checked_shr(1)?;
        }
        bit = bit.checked_shr(2)?;
    }
    Some(result)
}

/// Calculate the normal cdf of the given number
///
/// The approximation is accurate to 3 digits
///
/// Code lovingly adapted from the excellent work at:
///
/// <https://www.hrpub.org/download/20140305/MS7-13401470.pdf>
///
/// The algorithm is based on the implementation in the paper above.
#[inline(never)]
pub fn f32_normal_cdf(argument: f32) -> f32 {
    const PI: f32 = std::f32::consts::PI;

    let mod_argument = if argument < 0.0 {
        -1.0 * argument
    } else {
        argument
    };
    let tabulation_numerator: f32 =
        (1.0 / (1.0 * (2.0 * PI).sqrt())) * (-1.0 * (mod_argument * mod_argument) / 2.0).exp();
    let tabulation_denominator: f32 =
        0.226 + 0.64 * mod_argument + 0.33 * (mod_argument * mod_argument + 3.0).sqrt();
    let y: f32 = 1.0 - tabulation_numerator / tabulation_denominator;
    if argument < 0.0 {
        1.0 - y
    } else {
        y
    }
}

#[cfg(test)]
mod tests {
    use {super::*, proptest::prelude::*};

    fn check_square_root<T>(radicand: T)
    where
        T: PrimInt + CheckedShl + CheckedShr + std::fmt::Debug + std::ops::Add<Output = T> + std::ops::Sub<Output = T> + Copy + std::ops::Mul<Output=T>,
        // Add bounds needed for checking if not already covered by PrimInt etc.
        // Need checked_pow(2) effectively. Let's do manual multiply for simplicity or add num_traits::pow::CheckedPow
    {
        let one = T::one();
        let root = sqrt(radicand).unwrap();

        // Check: root^2 <= radicand
        let root_squared = root.checked_mul(&root).unwrap();
        assert!(root_squared <= radicand);

        // Check: (root + 1)^2 > radicand
        // Avoid overflow when root is MAX
        if let Some(root_plus_one) = root.checked_add(&one) {
             if let Some(upper_bound_squared) = root_plus_one.checked_mul(&root_plus_one) {
                assert!(radicand < upper_bound_squared);
             }
             // If root_plus_one overflows, then root must be T::max_value(),
             // and root^2 <= radicand must hold, which is sufficient.
        } else {
             // root is T::max_value(), root_squared check is sufficient
             assert_eq!(root, T::max_value());
        }

        // --- Original check logic (might overflow on upper_bound) ---
        // let lower_bound = root.saturating_sub(one);
        // let lower_bound_sq = lower_bound.checked_mul(&lower_bound).unwrap();
        // let upper_bound = root.checked_add(&one); //.unwrap(); // This can overflow!
        // if let Some(ub) = upper_bound {
        //     let upper_bound_sq = ub.checked_mul(&ub).unwrap();
        //     assert!(radicand < upper_bound_sq); // Use < since root is floor(sqrt)
        // } // else: root is MAX, lower bound check is enough
        // assert!(radicand >= lower_bound_sq);

    }

    #[test]
    fn test_square_root_u64() {
        assert_eq!(sqrt(0u64), Some(0u64));
        assert_eq!(sqrt(1u64), Some(1u64));
        assert_eq!(sqrt(3u64), Some(1u64));
        assert_eq!(sqrt(4u64), Some(2u64));
        assert_eq!(sqrt(8u64), Some(2u64));
        assert_eq!(sqrt(9u64), Some(3u64));
        assert_eq!(sqrt(15u64), Some(3u64));
        assert_eq!(sqrt(16u64), Some(4u64));
        assert_eq!(sqrt(25u64), Some(5u64));
        assert_eq!(sqrt(u64::MAX), Some(4294967295u64)); // sqrt(2^64 - 1) is 2^32 - 1
        check_square_root(100u64);
        check_square_root(123456789u64);
        check_square_root(u64::MAX);
    }

    #[test]
    fn test_square_root_u128_min_max() { // Renamed from test_square_root_min_max
        let test_roots = [0u128, u128::MAX]; // Explicitly u128
        for i in test_roots.iter() {
            check_square_root(*i);
        }
         // Added a u64 check here too if 
         check_square_root(0u64);
         check_square_root(u64::MAX);
    }

    proptest! {
        #[test]
        fn test_square_root_prop_u128(a in 0u128..=u128::MAX) { // Use u128 range
            check_square_root(a);
        }

        #[test]
        fn test_square_root_prop_u64(a in 0u64..=u64::MAX) { // Use u64 range
           check_square_root(a);
        }
    }

    // --- f32_normal_cdf tests remain the same ---
    fn check_normal_cdf_f32(argument: f32) {
        let result = f32_normal_cdf(argument);
        let check_result = 0.5 * (1.0 + libm::erff(argument / std::f32::consts::SQRT_2));
        let abs_difference: f32 = (result - check_result).abs();
        assert!(abs_difference <= 0.000_2);
    }

    #[test]
    fn test_normal_cdf_f32_min_max() {
        let test_arguments: [f32; 2] = [f32::MIN, f32::MAX];
        for i in test_arguments.iter() {
            check_normal_cdf_f32(*i)
        }
    }

    proptest! {
        #[test]
        fn test_normal_cdf(a in -1000..1000) {

            check_normal_cdf_f32((a as f32)*0.005);
        }
    }
}
