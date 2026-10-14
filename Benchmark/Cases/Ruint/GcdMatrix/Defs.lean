import RuintGcdMatrix.Extraction

/-!
# ruint — Lehmer update matrices (`algorithms::gcd::matrix`) — specifications

Implementation: `extracted/RuintGcdMatrix` (verbatim `cargo hax extract
ruint-gcd-matrix` output for alloy-rs/ruint@2071680b).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`debug_assert!`s panic), which is the configuration `cargo test` runs the
original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Ruint.GcdMatrix

open ruint

end Benchmark.Cases.Ruint.GcdMatrix
