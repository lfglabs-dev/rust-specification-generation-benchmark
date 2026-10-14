import JiffCivil.Extraction

/-!
# jiff (jiff-core) civil time — specifications

Implementation: `extracted/JiffCivil` (verbatim `cargo hax extract jiff-civil`
output for BurntSushi/jiff@7bd0c363, crate `crates/jiff-core`, root module
`jiff_core::civil::time`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Jiff.Civil

open jiff_core

end Benchmark.Cases.Jiff.Civil
