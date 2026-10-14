import OrderStatQuickselect.Extraction

/-!
# order-stat (quickselect) — specifications

Implementation: `extracted/OrderStatQuickselect` (verbatim `cargo hax extract
order-stat-quickselect` output for huonw/order-stat@2a2b5cf2, rooted at the
private module `order_stat::quickselect`).

`quickselect::select<T: Ord>(x: &mut [T], k: usize)` is generic; the property
test instantiates it at `T = i32`, so the spec passes CoreModels' `Ord for i32`
instance `core.I32.Insts.CoreCmpOrd` (whose `<` compares the integer values).
The `&mut [T]` argument is threaded functionally: `select` returns the final
contents of the slice.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic and
indexing follow Rust debug-build semantics (overflow and out-of-bounds panic),
the configuration `cargo test` runs the original property test under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.OrderStat.Quickselect

open order_stat

/-- The test's `x.sort()` on a `Vec<i32>`: the list of `i32` values sorted in
ascending order (`List.mergeSort` with `≤` on the integer values; a sorted
permutation of a list of integers is unique, so this is exactly the contents
of `x` after Rust's stable `sort`). -/
def sortI32 (l : List Std.I32) : List Std.I32 :=
  l.mergeSort (fun a b => decide (a.val ≤ b.val))

end Benchmark.Cases.OrderStat.Quickselect
