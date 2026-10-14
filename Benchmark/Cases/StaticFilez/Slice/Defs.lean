import StaticFilezSlice.Extraction

/-!
# static-filez — specifications

Implementation: `extracted/StaticFilezSlice` (verbatim `cargo hax extract
static-filez-slice` output for killercup/static-filez@8bafef57, library target;
see `cases/static_filez/slice/case.yaml`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
`usize` keeps Aeneas' abstract platform width (`System.Platform.numBits` is 32
or 64); no assumption on it is made here.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.StaticFilez.Slice

open static_filez

end Benchmark.Cases.StaticFilez.Slice
