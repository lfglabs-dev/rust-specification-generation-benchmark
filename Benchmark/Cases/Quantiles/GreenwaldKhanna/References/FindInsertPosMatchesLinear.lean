import Benchmark.Cases.Quantiles.GreenwaldKhanna.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open quantiles

namespace Benchmark.Cases.Quantiles.GreenwaldKhanna

/-- On a sorted `i32` slice, the recursive binary search `find_insert_pos`
(linear scan below 11 elements, otherwise split at `len / 2` on `v < vs[len/2]`)
never panics and returns the same insertion position as the linear scan
`find_insert_pos_linear` (index of the first element greater than `v`, or `len`). -/
def find_insert_pos_matches_linear_spec (vs : Slice Std.I32) (v : Std.I32) : Prop :=
  (do
    let log ← greenwald_khanna.find_insert_pos core.I32.Insts.CoreCmpOrd vs v
    let lin ← greenwald_khanna.find_insert_pos_linear core.I32.Insts.CoreCmpOrd vs v
    ok (log, lin)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Quantiles.GreenwaldKhanna
