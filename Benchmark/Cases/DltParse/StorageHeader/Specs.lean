import Benchmark.Cases.DltParse.StorageHeader.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dlt_parse
open Benchmark.Cases.DltParse.StorageHeader

namespace Benchmark.Cases.DltParse.StorageHeader.Oracle

/-- PBT `storage::storage_header::storage_header_tests::from_bytes`
(src/storage/storage_header.rs:132), with the two assertions of the property
test run in sequence on a pair:

* ok case: `Ok(header.clone()) == StorageHeader::from_bytes(header.to_bytes())`
  (`clone` on `StorageHeader` is the identity, so this is
  `from_bytes(to_bytes header) = Ok header`);
* error case: with the first four bytes overwritten by `bad_pattern`
  (filtered by the strategy to differ from `PATTERN_AT_START`),
  `from_bytes` fails with `StorageHeaderStartPatternError` carrying exactly
  `bad_pattern` as the actual pattern. -/
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

axiom from_bytes_roundtrip_and_pattern_error (header : storage.storage_header.StorageHeader)
    (bad_pattern : Array Std.U8 4#usize)
    (h_bad : bad_pattern.val ≠ storage.storage_header.StorageHeader.PATTERN_AT_START.val) :
    storage_header_from_bytes_spec header bad_pattern

end Benchmark.Cases.DltParse.StorageHeader.Oracle
