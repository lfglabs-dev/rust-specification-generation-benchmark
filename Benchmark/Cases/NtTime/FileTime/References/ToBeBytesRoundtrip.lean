import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::to_be_bytes` never panics and returns the big-endian base-256 digits of the
raw tick count (the value of `ft.to_raw().to_be_bytes()`). -/
def to_be_bytes_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  (do
    let bytes ← file_time.FileTime.to_be_bytes ft
    let raw ← file_time.FileTime.to_raw ft
    ok (bytes, raw)) ⦃ r =>
      r.1.val.map (·.val) =
        [r.2.val / 2^56 % 2^8, r.2.val / 2^48 % 2^8, r.2.val / 2^40 % 2^8,
         r.2.val / 2^32 % 2^8, r.2.val / 2^24 % 2^8, r.2.val / 2^16 % 2^8,
         r.2.val / 2^8 % 2^8, r.2.val % 2^8] ⦄

end Benchmark.Cases.NtTime.FileTime
