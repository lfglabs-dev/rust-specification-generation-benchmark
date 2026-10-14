import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::to_unix_time_nanos` never panics (no i128 overflow) and its result lies in
`-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500`. -/
def to_unix_time_nanos_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.NtTime.FileTime
