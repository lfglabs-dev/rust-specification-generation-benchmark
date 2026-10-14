use core::fmt;
use std::error::Error;

/// Errors returned by checked combinatorics helpers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CombinatoricsError {
    /// `k` must not exceed `n` in selection-style helpers.
    KExceedsN {
        /// The size of the source set.
        n: u64,
        /// The requested selection size.
        k: u64,
    },
    /// The factorial result overflowed `u128`.
    FactorialOverflow(u64),
    /// The permutation result overflowed `u128`.
    PermutationOverflow {
        /// The size of the source set.
        n: u64,
        /// The requested ordered selection size.
        k: u64,
    },
    /// The combination result overflowed `u128`.
    CombinationOverflow {
        /// The size of the source set.
        n: u64,
        /// The requested unordered selection size.
        k: u64,
    },
}

impl fmt::Display for CombinatoricsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::KExceedsN { n, k } => {
                write!(
                    formatter,
                    "k must be less than or equal to n, got k={k}, n={n}"
                )
            },
            Self::FactorialOverflow(n) => {
                write!(formatter, "factorial overflowed u128 for n={n}")
            },
            Self::PermutationOverflow { n, k } => {
                write!(formatter, "permutations overflowed u128 for n={n}, k={k}")
            },
            Self::CombinationOverflow { n, k } => {
                write!(formatter, "combinations overflowed u128 for n={n}, k={k}")
            },
        }
    }
}

impl Error for CombinatoricsError {}
