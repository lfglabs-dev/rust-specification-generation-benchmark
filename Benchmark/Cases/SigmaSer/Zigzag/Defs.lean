import SigmaSerZigzag.Extraction

/-!
# sigma_ser — zigzag specifications

Implementation: `extracted/SigmaSerZigzag` (verbatim `cargo hax extract
sigma-ser-zigzag` output for ergoplatform/sigma-rust@1633e018, crate
`sigma-ser` 0.20.0, module `sigma_ser::zig_zag_encode`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. The extracted
functions are pure integer code; shifts by a constant amount never panic
(amount < bit width), and the negations `-.` act on `0`/`1`, so the only way
the do-blocks below could fail is inside the extracted callee bodies.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.SigmaSer.Zigzag

open sigma_ser

end Benchmark.Cases.SigmaSer.Zigzag
