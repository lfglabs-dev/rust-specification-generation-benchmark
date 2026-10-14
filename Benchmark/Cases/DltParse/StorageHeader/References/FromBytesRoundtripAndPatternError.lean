import Benchmark.Cases.DltParse.StorageHeader.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dlt_parse

namespace Benchmark.Cases.DltParse.StorageHeader

/-- For every storage header `header` and 4-byte pattern `bad_pattern` different
from `StorageHeader::PATTERN_AT_START`, decoding `header.to_bytes()` succeeds
with `header` itself, and decoding the same buffer with its first four bytes
overwritten by `bad_pattern` fails with the
`StorageHeaderStartPatternError { actual_pattern: bad_pattern }`. -/
def storage_header_from_bytes_spec (header : storage.storage_header.StorageHeader)
    (bad_pattern : Array Std.U8 4#usize) : Prop :=
  (do
    let bytes ← storage.storage_header.StorageHeader.to_bytes header
    let ok_case ← storage.storage_header.StorageHeader.from_bytes bytes
    let mutated ← ok
      ((((bytes.set 0#usize bad_pattern[0]!).set 1#usize bad_pattern[1]!)
        |>.set 2#usize bad_pattern[2]!).set 3#usize bad_pattern[3]!)
    let bad_case ← storage.storage_header.StorageHeader.from_bytes mutated
    ok (ok_case, bad_case)) ⦃ r =>
    r.1 = core.result.Result.Ok header ∧
    r.2 = core.result.Result.Err
      { actual_pattern := bad_pattern :
        error.storage_header_start_pattern_error.StorageHeaderStartPatternError } ⦄

end Benchmark.Cases.DltParse.StorageHeader
