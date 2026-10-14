import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::to_high_low` never panics and returns `(raw / 2^32, raw % 2^32)`, the
value of `((raw >> u32::BITS) as u32, raw as u32)`. -/
def to_high_low_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.NtTime.FileTime
