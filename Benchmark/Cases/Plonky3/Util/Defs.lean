import Plonky3Util.Extraction

/-!
# Plonky3 `p3-util` strict base-3 logarithm — specifications

Implementation: `extracted/Plonky3Util` (verbatim `cargo hax extract
plonky3-util` output for Plonky3/Plonky3@6468485f, crate `util`, rooted at
`p3_util::log3_strict_usize` in `util/src/lib.rs`).

`log3_strict_usize(n)` computes `floor(log2 n)` from `usize::leading_zeros`,
looks the candidate exponent up in the const table `LOG2_TO_EXP : [u8; 64]`, and
checks it against the const table `POWERS_OF_3 : [u64; 41]` (both tables are
built by `while` loops in `const` blocks; the extraction evaluates them with the
`loop` combinator). It panics (`assert!`) on `0` and on non-powers of 3.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`assert!`s panic), which is the configuration `cargo test` runs the original
property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Plonky3.Util

open p3_util

end Benchmark.Cases.Plonky3.Util
