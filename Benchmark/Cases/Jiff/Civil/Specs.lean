import Benchmark.Cases.Jiff.Civil.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open jiff_core
open Benchmark.Cases.Jiff.Civil

namespace Benchmark.Cases.Jiff.Civil.Oracle

/-- PBT `civil::time::tests::prop_time_to_nanosecond_roundtrip`
(crates/jiff-core/src/civil/time.rs:672):
`t == t.to_nanosecond().to_time()` — converting a civil time to its
nanosecond-of-day and back yields the same `Time` (derived `PartialEq`). -/
def time_to_nanosecond_roundtrip_spec (t : civil.time.Time) : Prop :=
  (do
    let n ← civil.time.Time.to_nanosecond t
    let t' ← civil.time.TimeNanosecond.to_time n
    civil.time.Time.Insts.CoreCmpPartialEqTime.eq t t') ⦃ b => b = true ⦄

axiom time_to_nanosecond_roundtrip (t : civil.time.Time)
    (h_hour : 0 ≤ t.hour.val ∧ t.hour.val ≤ 23)
    (h_minute : 0 ≤ t.minute.val ∧ t.minute.val ≤ 59)
    (h_second : 0 ≤ t.second.val ∧ t.second.val ≤ 59)
    (h_subsec : 0 ≤ t.subsec_nanosecond.val ∧ t.subsec_nanosecond.val ≤ 999999999) :
    time_to_nanosecond_roundtrip_spec t

end Benchmark.Cases.Jiff.Civil.Oracle
