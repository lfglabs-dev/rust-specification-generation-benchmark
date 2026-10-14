import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- For Unix times before the NT epoch (`ts ≤ -11_644_473_601`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Negative.into())`. -/
def from_unix_time_secs_before_nt_time_epoch_roundtrip_spec (ts : Std.I64) : Prop :=
  (do
    let r ← file_time.unix_time.FileTime.from_unix_time_secs ts
    let expected ← core.convert.Into.Blanket.into
      error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind
      error.FileTimeRangeErrorKind.Negative
    ok (r, expected)) ⦃ p => p.1 = core.result.Result.Err p.2 ⦄

end Benchmark.Cases.NtTime.FileTime
