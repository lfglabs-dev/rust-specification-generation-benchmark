mod range;
mod ref_impl;
mod reverse;

pub use range::*;
pub use ref_impl::*;
pub use reverse::*;

const BITS: u32 = 32;
const ALL_ONES: u32 = 0xFFFFFFFF;
