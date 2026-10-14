import TinysetFits64.Extraction

/-!
# tinyset (Fits64) — specifications

Implementation: `extracted/TinysetFits64` (verbatim `cargo hax extract
tinyset-fits64` output for droundy/tinyset@c21d0dee, rooted at every
`impl Fits64 for _` of src/set64.rs except the `char` one).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Tinyset.Fits64

open tinyset

end Benchmark.Cases.Tinyset.Fits64
