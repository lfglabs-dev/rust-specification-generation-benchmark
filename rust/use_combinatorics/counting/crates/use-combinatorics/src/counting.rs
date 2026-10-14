use crate::error::CombinatoricsError;

const fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }

    left
}

/// Returns `n!` using checked `u128` arithmetic.
///
/// Overflow begins at `n = 35`.
///
/// # Errors
///
/// Returns [`CombinatoricsError::FactorialOverflow`] when the result no longer
/// fits in `u128`.
///
/// # Examples
///
/// ```rust
/// use use_combinatorics::factorial;
///
/// assert_eq!(factorial(5)?, 120);
/// # Ok::<(), use_combinatorics::CombinatoricsError>(())
/// ```
pub const fn factorial(n: u64) -> Result<u128, CombinatoricsError> {
    let mut result = 1_u128;
    let mut factor = 2_u64;

    while factor <= n {
        result = match result.checked_mul(factor as u128) {
            Some(value) => value,
            None => return Err(CombinatoricsError::FactorialOverflow(n)),
        };

        factor += 1;
    }

    Ok(result)
}

/// Returns the number of ordered selections of size `k` from `n` items.
///
/// # Errors
///
/// Returns [`CombinatoricsError::KExceedsN`] when `k > n`.
///
/// Returns [`CombinatoricsError::PermutationOverflow`] when the result no
/// longer fits in `u128`.
///
/// # Examples
///
/// ```rust
/// use use_combinatorics::permutations;
///
/// assert_eq!(permutations(5, 3)?, 60);
/// # Ok::<(), use_combinatorics::CombinatoricsError>(())
/// ```
pub const fn permutations(n: u64, k: u64) -> Result<u128, CombinatoricsError> {
    if k > n {
        return Err(CombinatoricsError::KExceedsN { n, k });
    }

    if k == 0 {
        return Ok(1);
    }

    let mut result = 1_u128;
    let mut factor = n - k + 1;

    while factor <= n {
        result = match result.checked_mul(factor as u128) {
            Some(value) => value,
            None => return Err(CombinatoricsError::PermutationOverflow { n, k }),
        };

        factor += 1;
    }

    Ok(result)
}

/// Returns the number of unordered selections of size `k` from `n` items.
///
/// # Errors
///
/// Returns [`CombinatoricsError::KExceedsN`] when `k > n`.
///
/// Returns [`CombinatoricsError::CombinationOverflow`] when the result no
/// longer fits in `u128`.
///
/// # Examples
///
/// ```rust
/// use use_combinatorics::combinations;
///
/// assert_eq!(combinations(5, 2)?, 10);
/// # Ok::<(), use_combinatorics::CombinatoricsError>(())
/// ```
pub fn combinations(n: u64, k: u64) -> Result<u128, CombinatoricsError> {
    if k > n {
        return Err(CombinatoricsError::KExceedsN { n, k });
    }

    let choose = k.min(n - k);
    let mut result = 1_u128;
    let mut step = 1_u64;

    while step <= choose {
        let mut numerator = u128::from(n - choose + step);
        let mut denominator = u128::from(step);

        // Cancel common factors before multiplying so more valid inputs fit in
        // `u128` without changing the exact result.
        let numerator_gcd = gcd(numerator, denominator);
        numerator /= numerator_gcd;
        denominator /= numerator_gcd;

        let result_gcd = gcd(result, denominator);
        result /= result_gcd;
        denominator /= result_gcd;

        debug_assert_eq!(denominator, 1);

        result = result
            .checked_mul(numerator)
            .ok_or(CombinatoricsError::CombinationOverflow { n, k })?;

        step += 1;
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::{combinations, factorial, permutations};
    use crate::error::CombinatoricsError;

    #[test]
    fn computes_factorials() {
        assert_eq!(factorial(0), Ok(1));
        assert_eq!(factorial(5), Ok(120));
        assert_eq!(factorial(10), Ok(3_628_800));
    }

    #[test]
    fn reports_factorial_overflow() {
        assert_eq!(
            factorial(35),
            Err(CombinatoricsError::FactorialOverflow(35))
        );
    }

    #[test]
    fn computes_permutations() {
        assert_eq!(permutations(5, 0), Ok(1));
        assert_eq!(permutations(5, 3), Ok(60));
        assert_eq!(permutations(10, 2), Ok(90));
    }

    #[test]
    fn computes_zero_length_permutations_at_u64_max() {
        assert_eq!(permutations(u64::MAX, 0), Ok(1));
    }

    #[test]
    fn rejects_invalid_permutations() {
        assert_eq!(
            permutations(3, 4),
            Err(CombinatoricsError::KExceedsN { n: 3, k: 4 })
        );
    }

    #[test]
    fn reports_permutation_overflow() {
        assert_eq!(
            permutations(40, 30),
            Err(CombinatoricsError::PermutationOverflow { n: 40, k: 30 })
        );
    }

    #[test]
    fn computes_combinations() {
        assert_eq!(combinations(5, 2), Ok(10));
        assert_eq!(combinations(10, 3), Ok(120));
        assert_eq!(combinations(52, 5), Ok(2_598_960));
    }

    #[test]
    fn rejects_invalid_combinations() {
        assert_eq!(
            combinations(3, 4),
            Err(CombinatoricsError::KExceedsN { n: 3, k: 4 })
        );
    }

    #[test]
    fn reports_combination_overflow() {
        assert_eq!(
            combinations(150, 75),
            Err(CombinatoricsError::CombinationOverflow { n: 150, k: 75 })
        );
    }
}
