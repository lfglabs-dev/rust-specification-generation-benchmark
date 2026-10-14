import QuantilesGreenwaldKhanna.Extraction

/-!
# quantiles (Greenwald-Khanna insertion position) — specifications

Implementation: `extracted/QuantilesGreenwaldKhanna` (verbatim `cargo hax extract
quantiles-greenwald-khanna` output for postmates/quantiles@400abb05).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The Rust functions are generic over `T: Ord`; the PBT instantiates them at
`i32`, whose `Ord` dictionary is the CoreModels instance
`core.I32.Insts.CoreCmpOrd` (comparison of the integer values).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Quantiles.GreenwaldKhanna

open quantiles

end Benchmark.Cases.Quantiles.GreenwaldKhanna
