import Benchmark.Cases.OrderStat.Quickselect.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open order_stat

namespace Benchmark.Cases.OrderStat.Quickselect

/-- For every `i32` slice `x` and index `k < x.len()`, quickselect's
`select(&mut x, k)` never panics and leaves at position `k` exactly the
`k`-th smallest element of the slice, i.e. the element that sorting the
resulting slice would put at position `k`. -/
def select_kth_is_kth_smallest_spec (x : Slice Std.I32) (k : Std.Usize) : Prop :=
  (do
    let x1 ← quickselect.select core.I32.Insts.CoreCmpOrd x k
    let element ← Slice.index_usize x1 k
    ok (x1, element)) ⦃ r => (sortI32 r.1.val)[k.val]? = some r.2 ⦄

end Benchmark.Cases.OrderStat.Quickselect
