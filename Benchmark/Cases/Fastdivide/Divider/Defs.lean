import FastdivideDivider.Extraction

/-!
# fastdivide — specifications

Implementation: `extracted/FastdivideDivider` (verbatim `cargo hax extract
fastdivide-divider` output for fulmicoton/fastdivide@1e9a5295).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Fastdivide.Divider

open fastdivide

end Benchmark.Cases.Fastdivide.Divider
