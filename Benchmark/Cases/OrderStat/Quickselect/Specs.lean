import Benchmark.Cases.OrderStat.Quickselect.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open order_stat
open Benchmark.Cases.OrderStat.Quickselect

namespace Benchmark.Cases.OrderStat.Quickselect.Oracle

/-- PBT `quickselect::tests::qc` (src/quickselect.rs:53-66):
```
fn run(mut x: Vec<i32>, k: usize) -> TestResult {
    if k >= x.len() { return TestResult::discard(); }
    select(&mut x, k);
    let element = x[k];
    x.sort();
    TestResult::from_bool(element == x[k])
}
```
`select` runs without panicking, reading `x[k]` afterwards succeeds, and the
element read is the `k`-th element of the sorted final contents of `x`
(`(sortI32 x1)[k]? = some element` also states that the test's second `x[k]`
is in bounds). -/
def select_kth_is_kth_smallest_spec (x : Slice Std.I32) (k : Std.Usize) : Prop :=
  (do
    let x1 ← quickselect.select core.I32.Insts.CoreCmpOrd x k
    let element ← Slice.index_usize x1 k
    ok (x1, element)) ⦃ r => (sortI32 r.1.val)[k.val]? = some r.2 ⦄

axiom select_kth_is_kth_smallest (x : Slice Std.I32) (k : Std.Usize)
    (h_assume_k : k.val < x.length) :
    select_kth_is_kth_smallest_spec x k

end Benchmark.Cases.OrderStat.Quickselect.Oracle
