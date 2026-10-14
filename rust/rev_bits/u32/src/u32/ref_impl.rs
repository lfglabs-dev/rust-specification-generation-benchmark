use std::ops::RangeBounds;

use super::to_start_end;

const N: usize = super::BITS as usize;

// This is a reference implementation.
pub fn reverse_u32(input: u32, range: impl RangeBounds<u32>) -> u32 {
    let array = to_array(input);
    let (start, end) = to_start_end(range);
    if end > start {
        let reversed_vec = reverse_array(&array, start, end);
        to_u32(&reversed_vec)
    } else {
        input
    }
}

/// Reverse bits in a specified range.
///
/// For example:
///     ........ABCD................
/// becomes:
///     ........DCBA................
///
/// This is a reference implementation for testing.
fn reverse_array(input: &[bool], min: u32, max: u32) -> Vec<bool> {
    let mut vec = input.to_vec();
    let (a, b) = (min as usize, max as usize);
    vec[a..=b].reverse();
    vec
}

fn to_array(mut input: u32) -> [bool; N] {
    let mut array = [false; N];
    for i in 0..N {
        if input & 1 == 1 {
            array[i] = true;
        }
        input >>= 1;
    }
    array
}

fn to_u32(input: &[bool]) -> u32 {
    let mut out = 0;
    for &bool in input.iter().rev() {
        out = out << 1;
        if bool {
            out |= 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn reverse_u32_ex1() {
        let x = 0xaaaaaaaa;
        let y = 0xaaaaaa5a;
        assert_eq!(reverse_u32(x, 4..8), y);
    }

    #[test]
    fn reverse_u32_ex2() {
        let x = 0xaaaaaaaa;
        let y = 0xaaaaa55a;
        assert_eq!(reverse_u32(x, 4..12), y);
    }

    #[test]
    fn reverse_u32_ex3() {
        let x = 0xaaaaaaaa;
        let y = 0x55555aaa;
        assert_eq!(reverse_u32(x, 12..32), y);
    }

    #[quickcheck]
    fn reverse_u32_reverse_u32(x: u32, range: Range<u32>) -> bool {
        x == reverse_u32(reverse_u32(x, range.clone()), range)
    }

    #[quickcheck]
    fn to_array_to_u32(x: u32) -> bool {
        x == to_u32(&to_array(x))
    }
}
