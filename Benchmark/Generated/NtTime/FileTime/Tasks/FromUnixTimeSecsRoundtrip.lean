import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- For every Unix time in `-11_644_473_600..=1_833_029_933_770` seconds,
`FileTime::from_unix_time_secs(ts)` succeeds (`is_ok()`): in particular the
`duration * FILE_TIMES_PER_SEC` multiplication never overflows `u64`. -/
def from_unix_time_secs_roundtrip_spec (ts : Std.I64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.NtTime.FileTime
