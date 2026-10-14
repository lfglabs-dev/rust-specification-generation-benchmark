import Benchmark.Cases.Jiff.Civil.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open jiff_core

namespace Benchmark.Cases.Jiff.Civil

/-- Converting a valid civil `Time` to its nanosecond of the day
(`Time::to_nanosecond`) and back (`TimeNanosecond::to_time`, a chain of
unsigned divisions/remainders with early exits on zero remainders) never
panics and returns a time equal to the original one. -/
def time_to_nanosecond_roundtrip_spec (t : civil.time.Time) : Prop :=
  (do
    let n ← civil.time.Time.to_nanosecond t
    let t' ← civil.time.TimeNanosecond.to_time n
    civil.time.Time.Insts.CoreCmpPartialEqTime.eq t t') ⦃ b => b = true ⦄

end Benchmark.Cases.Jiff.Civil
