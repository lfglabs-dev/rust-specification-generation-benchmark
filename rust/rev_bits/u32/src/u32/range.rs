use std::ops::RangeBounds;

use super::BITS;

pub fn to_start_end(range: impl RangeBounds<u32>) -> (u32, u32) {
    let start = match range.start_bound() {
        std::ops::Bound::Included(&s) => identity(s),
        std::ops::Bound::Excluded(&s) => increment(s),
        std::ops::Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        std::ops::Bound::Included(&e) => identity(e),
        std::ops::Bound::Excluded(&e) => decrement(e),
        std::ops::Bound::Unbounded => BITS - 1,
    };
    (start, end)
}

fn identity(x: u32) -> u32 {
    if x < BITS {
        x
    } else {
        BITS - 1
    }
}

fn increment(x: u32) -> u32 {
    if x < BITS - 1 {
        x + 1
    } else {
        BITS - 1
    }
}

fn decrement(x: u32) -> u32 {
    if x == 0 {
        0
    } else if x >= BITS {
        BITS - 1
    } else {
        x - 1
    }
}

#[cfg(test)]
mod tests {
    use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

    use quickcheck_macros::quickcheck;

    use super::*;

    // ----- to_start_end -----

    #[quickcheck]
    fn to_start_end_range(range: Range<u32>) -> bool {
        let a = identity(range.start);
        let b = decrement(range.end);
        (a, b) == to_start_end(range)
    }

    #[quickcheck]
    fn to_start_end_range_from(range: RangeFrom<u32>) -> bool {
        let a = identity(range.start);
        (a, BITS - 1) == to_start_end(range)
    }

    #[quickcheck]
    fn to_start_end_range_full(range: RangeFull) -> bool {
        (0, BITS - 1) == to_start_end(range)
    }

    #[quickcheck]
    fn to_start_end_range_inclusive(range: RangeInclusive<u32>) -> bool {
        let a = identity(*range.start());
        let b = identity(*range.end());
        (a, b) == to_start_end(range)
    }

    #[quickcheck]
    fn to_start_end_range_to(range: RangeTo<u32>) -> bool {
        let b = decrement(range.end);
        (0, b) == to_start_end(range)
    }

    #[quickcheck]
    fn to_start_end_range_to_inclusive(range: RangeToInclusive<u32>) -> bool {
        let b = identity(range.end);
        (0, b) == to_start_end(range)
    }

    // ----- decrement -----

    #[quickcheck]
    fn decrement_in_range(x: u32) -> bool {
        decrement(x) < BITS
    }

    #[quickcheck]
    fn decrement_is_correct(x: u32) -> bool {
        let dec = decrement(x);
        if x == 0 {
            dec == 0
        } else {
            dec == std::cmp::min(x - 1, BITS - 1)
        }
    }

    // ----- increment -----

    #[quickcheck]
    fn increment_in_range(x: u32) -> bool {
        increment(x) < BITS
    }

    #[quickcheck]
    fn increment_is_correct(x: u32) -> bool {
        let inc = increment(x);
        if x == std::u32::MAX {
            inc == BITS - 1
        } else {
            inc == std::cmp::min(x + 1, BITS - 1)
        }
    }

    // ----- identity -----

    #[quickcheck]
    fn identity_in_range(x: u32) -> bool {
        identity(x) < BITS
    }

    #[quickcheck]
    fn identity_is_correct(x: u32) -> bool {
        identity(x) == std::cmp::min(x, BITS - 1)
    }
}
