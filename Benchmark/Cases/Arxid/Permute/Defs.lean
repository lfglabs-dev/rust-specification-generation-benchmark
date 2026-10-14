import ArxidPermute.Extraction

/-!
# arxid — specifications (module `arxid::permute`)

Implementation: `extracted/ArxidPermute` (verbatim `cargo hax extract
arxid-permute` output for lucasolopes/arxid@35a9a085, crate `impl/rust`,
rooted at `arxid::permute`).

`permute::obfuscate(id, key)` masks `id` to the 40-bit domain
(`id & MAX_ID`, `MAX_ID = (1 << 40) - 1`) and runs a balanced 6-round Feistel
network over two 20-bit halves (`feistel_n`); `permute::deobfuscate` masks and
runs the rounds backwards (`feistel_n_inv`). The round function (`round_fn`,
`subkey`) is ARX arithmetic on `u32`/`u64` with wrapping adds, rotations and a
wrapping multiply.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
Constants: `MAX_ID = 2^40 - 1 = 1099511627775`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Arxid.Permute

open arxid

end Benchmark.Cases.Arxid.Permute
