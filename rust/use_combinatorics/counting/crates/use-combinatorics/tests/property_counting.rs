use proptest::prelude::*;
use use_combinatorics::{CombinatoricsError, combinations, factorial, permutations};

fn factorial_reference(n: u8) -> Option<u128> {
    let mut result = 1_u128;

    for factor in 2..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }

    Some(result)
}

fn permutations_reference(n: u8, k: u8) -> Option<u128> {
    if k > n {
        return None;
    }

    let mut result = 1_u128;
    let start = u64::from(n - k) + 1;

    for factor in start..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }

    Some(result)
}

fn combinations_reference(n: u8, k: u8) -> Option<u128> {
    if k > n {
        return None;
    }

    let target = usize::from(k.min(n - k));
    let mut row = vec![0_u128; target + 1];
    row[0] = 1;

    for current in 1..=usize::from(n) {
        let upper = current.min(target);

        for column in (1..=upper).rev() {
            row[column] = row[column].checked_add(row[column - 1])?;
        }
    }

    Some(row[target])
}

proptest! {
    #[test]
    fn factorial_matches_checked_reference(n in 0_u8..41) {
        let n_u64 = u64::from(n);

        if let Some(expected) = factorial_reference(n) {
            prop_assert_eq!(factorial(n_u64), Ok(expected));
        } else {
            prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
        }
    }

    #[test]
    fn factorial_overflow_boundary_is_exact(n in 0_u8..80) {
        let n_u64 = u64::from(n);

        if n <= 34 {
            prop_assert!(factorial(n_u64).is_ok());
        } else {
            prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
        }
    }

    #[test]
    fn permutations_match_checked_reference(n in 0_u8..81, k in 0_u8..81) {
        let n_u64 = u64::from(n);
        let k_u64 = u64::from(k);

        if k > n {
            prop_assert_eq!(
                permutations(n_u64, k_u64),
                Err(CombinatoricsError::KExceedsN { n: n_u64, k: k_u64 })
            );
        } else if let Some(expected) = permutations_reference(n, k) {
            prop_assert_eq!(permutations(n_u64, k_u64), Ok(expected));
        } else {
            prop_assert_eq!(
                permutations(n_u64, k_u64),
                Err(CombinatoricsError::PermutationOverflow { n: n_u64, k: k_u64 })
            );
        }
    }

    #[test]
    fn combinations_match_pascal_reference(n in 0_u8..201, k in 0_u8..201) {
        let n_u64 = u64::from(n);
        let k_u64 = u64::from(k);

        if k > n {
            prop_assert_eq!(
                combinations(n_u64, k_u64),
                Err(CombinatoricsError::KExceedsN { n: n_u64, k: k_u64 })
            );
        } else if let Some(expected) = combinations_reference(n, k) {
            prop_assert_eq!(combinations(n_u64, k_u64), Ok(expected));
        } else {
            prop_assert_eq!(
                combinations(n_u64, k_u64),
                Err(CombinatoricsError::CombinationOverflow { n: n_u64, k: k_u64 })
            );
        }
    }

    #[test]
    fn combinations_are_symmetric(n in 0_u8..201, k in 0_u8..201) {
        prop_assume!(k <= n);

        let n_u64 = u64::from(n);
        let k_u64 = u64::from(k);
        let reflected_k = u64::from(n - k);
        let left = combinations(n_u64, k_u64);
        let right = combinations(n_u64, reflected_k);

        match (left, right) {
            (Ok(left_value), Ok(right_value)) => prop_assert_eq!(left_value, right_value),
            (
                Err(CombinatoricsError::CombinationOverflow { .. }),
                Err(CombinatoricsError::CombinationOverflow { .. }),
            ) => {}
            (left_result, right_result) => prop_assert_eq!(left_result, right_result),
        }
    }
}
