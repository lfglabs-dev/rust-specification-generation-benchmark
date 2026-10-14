import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::to_be_bytes` never panics and returns the big-endian base-256 digits of the
raw tick count (the value of `ft.to_raw().to_be_bytes()`). -/
def to_be_bytes_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.NtTime.FileTime
