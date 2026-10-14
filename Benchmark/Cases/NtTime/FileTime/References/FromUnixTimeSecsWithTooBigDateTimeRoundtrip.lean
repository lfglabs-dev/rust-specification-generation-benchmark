import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- For Unix times after `+60056-05-28 05:36:10 UTC` (`ts ≥ 1_833_029_933_771`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Overflow.into())`. -/
def from_unix_time_secs_with_too_big_date_time_roundtrip_spec (ts : Std.I64) : Prop :=
  (do
    let r ← file_time.unix_time.FileTime.from_unix_time_secs ts
    let expected ← core.convert.Into.Blanket.into
      error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind
      error.FileTimeRangeErrorKind.Overflow
    ok (r, expected)) ⦃ p => p.1 = core.result.Result.Err p.2 ⦄

end Benchmark.Cases.NtTime.FileTime
