import DashuBase.Extraction

/-!
# dashu-base — specifications

Implementation: `extracted/DashuBase` (verbatim `cargo hax extract dashu-base`
output for cmpute/dashu@973f0a8e, crate `dashu-base` 0.6.1, directory `base/`).

The property tests live in the workspace-excluded `fuzz` crate
(`fuzz/tests/base.rs`); they are macro-generated per integer width
(`gen_uint!` / `gen_int!`). Each spec below executes the body of one
instantiation in the extracted semantics.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Dashu.Base

open dashu_base

end Benchmark.Cases.Dashu.Base
