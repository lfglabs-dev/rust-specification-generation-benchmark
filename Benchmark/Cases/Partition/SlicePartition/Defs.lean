import PartitionSlicePartition.Extraction

/-!
# partition — specifications

Implementation: `extracted/PartitionSlicePartition` (verbatim `cargo hax
extract partition-slice-partition` output for llogiq/partition@628b0a4c).

`partition_index<T, P: Fn(&T) -> bool>(data: &mut [T], predicate: P)` and
`partition` (which additionally splits the slice at that index with
`split_at_mut`) are generic. The property tests instantiate them at `T = u32`
with the test closure `|&e| e % 2 == 0`. In the extraction a closure argument
is a value `pred : P` together with an `Fn P u32 Bool` instance record; the
test's closure is not part of the library, so every theorem quantifies over
*any* instance satisfying `IsEvenPredicate` below, which states exactly what the
test closure computes (in particular the closure itself satisfies it; see
`cases/partition/slice_partition/review/NonVacuity.lean`). The `&mut [T]`
argument is threaded functionally: `partition_index` returns the index and the
final contents of the slice; `partition` returns the two sub-slices (and a
write-back function that the tests never use).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic and
indexing follow Rust debug-build semantics (overflow and out-of-bounds panic),
the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Partition.SlicePartition

open partition

/-- The test closure `|&e| e % 2 == 0` (src/lib.rs:97 and 109) passed as
`predicate`: calling it on `e : u32` never panics (`e % 2` has a non-zero
divisor) and returns whether `e` is even. -/
def IsEvenPredicate {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P) : Prop :=
  ∀ e : Std.U32, inst.call pred e = ok (decide (e.val % 2 = 0))

/-- The tests' `v.sort()` on a `Vec<u32>`: the list sorted in ascending order
(`List.mergeSort` with `≤` on the values; a sorted permutation of a list of
integers is unique, so this is exactly the contents after Rust's `sort`). -/
def sortU32 (l : List Std.U32) : List Std.U32 :=
  l.mergeSort (fun a b => decide (a.val ≤ b.val))

/-- The tests' reference side
`data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>()`. -/
def evens (l : List Std.U32) : List Std.U32 :=
  l.filter (fun e => decide (e.val % 2 = 0))

/-- The tests' reference side
`data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>()`. -/
def odds (l : List Std.U32) : List Std.U32 :=
  l.filter (fun e => decide (e.val % 2 ≠ 0))

end Benchmark.Cases.Partition.SlicePartition
