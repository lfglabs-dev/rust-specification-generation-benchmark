import DltParseStorageHeader.Extraction

/-!
# dlt-parse-rs — specifications

Implementation: `extracted/DltParseStorageHeader` (verbatim `cargo hax extract
dlt-parse-storage-header` output for JulianSchmid/dlt-parse-rs@e84c7ee, module
`src/storage/storage_header.rs` with the `io`-generic `read`/`write`, the
string-returning `ecu_id_str` and the derived `Debug` impl excluded — none of
them is a callee of the properties below).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

Byte arrays: Aeneas models `[u8; N]` as `Std.Array Std.U8 N` (a subtype of
`List Std.U8`), so the specifications compare the returned array against the
expected `List Std.U8` built from `Std.core.num.U32.to_le_bytes` (Aeneas' pure
little-endian encoding; `CoreModels`' monadic `core.num.U32.to_le_bytes` is
proven equal to it by `to_le_bytes_eq` below, following the Byteorder case).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.DltParse.StorageHeader

open dlt_parse

end Benchmark.Cases.DltParse.StorageHeader
