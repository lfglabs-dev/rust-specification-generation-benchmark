import Bloom2VecBitmap.Extraction

/-!
# bloom2 (VecBitmap) — specifications

Implementation: `extracted/Bloom2VecBitmap` (verbatim `cargo hax extract
bloom2-vec-bitmap` output for domodwyer/bloom2@aa188bd1, rooted at the module
`bloom2::bitmap::vec`; `Bitmap::or` and `Bitmap::byte_size` of `VecBitmap` are
signature-only there and are not used below).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Bloom2.VecBitmap

open bloom2

end Benchmark.Cases.Bloom2.VecBitmap
