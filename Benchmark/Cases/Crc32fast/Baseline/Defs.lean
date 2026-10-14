import Crc32fastBaseline.Extraction

/-!
# crc32fast — baseline (table-driven) implementation — specifications

Implementation: `extracted/Crc32fastBaseline` (verbatim `cargo hax extract
crc32fast-baseline` output for srijs/rust-crc32fast@ad14266c): the portable
CRC-32 (IEEE, reflected polynomial `0xEDB88320`) update functions
`crc32fast.baseline.update_slow` (byte-at-a-time, table row 0) and
`crc32fast.baseline.update_fast_16` (slicing-by-16 with the 16×256 table
`crc32fast.table.CRC32_TABLE`, unrolled 4×16 bytes, then 16-byte blocks, then
a byte-wise tail).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic,
indexing and slicing in the extracted code follow Rust debug-build semantics
(out-of-bounds index/slice or overflow panics), which is the configuration
`cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Crc32fast.Baseline

open crc32fast

end Benchmark.Cases.Crc32fast.Baseline
