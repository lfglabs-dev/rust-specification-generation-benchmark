import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::from_high_low(high, low)` never panics and returns the file time
`high * 2^32 + low`, the value of `(u64::from(high) << u32::BITS) | u64::from(low)`. -/
def from_high_low_roundtrip_spec (high low : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.NtTime.FileTime
