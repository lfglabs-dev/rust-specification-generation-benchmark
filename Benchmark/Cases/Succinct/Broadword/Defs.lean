import SuccinctBroadword.Extraction

/-!
# succinct (broadword) — specifications

Implementation: `extracted/SuccinctBroadword` (verbatim `cargo hax extract
succinct-broadword` output for tov/succinct-rs@b394d4d1, rooted at the free
functions `broadword::{count_ones, u_nz8, u_le8}`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The byte-wise tests read byte `i` of a word with the crate helper
`BlockType::get_bits(8 * i, 8)` (`(w >> 8i) & low_mask(8)`), for `i < 8`. That
helper is test-side (it is not the code under test) and never panics for these
arguments (`8i + 8 ≤ 64`); its value is the natural number `w / 2^(8i) % 256`,
written `byteAt w i` below.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Succinct.Broadword

open succinct

/-- Byte `i` (little-endian, `i < 8`) of a 64-bit word, i.e. the value of the
test helper `w.get_bits(8 * i, 8)`. -/
def byteAt (w : Std.U64) (i : Nat) : Nat := w.val / 2 ^ (8 * i) % 256

end Benchmark.Cases.Succinct.Broadword
