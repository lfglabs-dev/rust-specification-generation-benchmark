import RustCrdtDot.Extraction

/-!
# rust-crdt — `Dot` specifications

Implementation: `extracted/RustCrdtDot` (verbatim `cargo hax extract
rust-crdt-dot` output for rust-crdt/rust-crdt@c92f8d1).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.RustCrdt.Dot

open crdts

end Benchmark.Cases.RustCrdt.Dot
