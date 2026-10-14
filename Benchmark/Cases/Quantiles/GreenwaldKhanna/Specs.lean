import Benchmark.Cases.Quantiles.GreenwaldKhanna.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open quantiles
open Benchmark.Cases.Quantiles.GreenwaldKhanna

namespace Benchmark.Cases.Quantiles.GreenwaldKhanna.Oracle

/-- PBT `greenwald_khanna::test::find_insert_pos_log_equals_find_insert_pos_linear`
(src/greenwald_khanna.rs:484), one iteration `v` of its `for v in -100..100` loop
over the sorted vector `vs`:
`find_insert_pos(&vs, &v) == find_insert_pos_linear(&vs, &v)` (the test returns
`false` otherwise). Both calls are evaluated in the Rust order; a panic in either
falsifies the spec. -/
def find_insert_pos_matches_linear_spec (vs : Slice Std.I32) (v : Std.I32) : Prop :=
  (do
    let log ← greenwald_khanna.find_insert_pos core.I32.Insts.CoreCmpOrd vs v
    let lin ← greenwald_khanna.find_insert_pos_linear core.I32.Insts.CoreCmpOrd vs v
    ok (log, lin)) ⦃ r => r.1 = r.2 ⦄

axiom find_insert_pos_matches_linear (vs : Slice Std.I32) (v : Std.I32)
    (h_sorted : vs.val.Pairwise (fun a b => a.val ≤ b.val))
    (h_v_lo : -100 ≤ v.val) (h_v_hi : v.val < 100) :
    find_insert_pos_matches_linear_spec vs v

end Benchmark.Cases.Quantiles.GreenwaldKhanna.Oracle
