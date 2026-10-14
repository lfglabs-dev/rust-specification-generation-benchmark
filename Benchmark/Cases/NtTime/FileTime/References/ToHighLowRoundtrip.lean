import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::to_high_low` never panics and returns `(raw / 2^32, raw % 2^32)`, the
value of `((raw >> u32::BITS) as u32, raw as u32)`. -/
def to_high_low_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  (do
    let raw ← file_time.FileTime.to_raw ft
    let hl ← file_time.FileTime.to_high_low ft
    ok (raw, hl)) ⦃ r =>
      r.2.1.val = r.1.val / 2^32 ∧ r.2.2.val = r.1.val % 2^32 ⦄

end Benchmark.Cases.NtTime.FileTime
