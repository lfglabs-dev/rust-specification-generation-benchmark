import RevBitsU32.Extraction

/-!
# rev_bits (u32) — specifications

Implementation: `extracted/RevBitsU32` (verbatim `cargo hax extract
rev-bits-u32` output for xpe/rev_bits@5fff70bd, library target; see
`cases/rev_bits/u32/case.yaml`, extraction patch `cargo_autobins_false`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

In the upstream crate `BITS = 32` (`src/u32/mod.rs`), so the tests' `BITS - 1`
is the constant `31` (computed at compile time, cannot panic). The tests'
`std::cmp::min` on `u32` values is the minimum of the values, written with
`Nat.min` (`min`) below.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.RevBits.U32

open rev_bits

end Benchmark.Cases.RevBits.U32
