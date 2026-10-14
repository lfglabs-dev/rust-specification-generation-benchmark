import Benchmark.Cases.Partition.SlicePartition.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open partition
open Benchmark.Cases.Partition.SlicePartition

namespace Benchmark.Cases.Partition.SlicePartition.Oracle

/-- PBT `tests::quickcheck` / `prop_partition_index` (src/lib.rs:105-119):
```
let mut trues = data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>();
let mut falses = data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>();
let first_false = partition_index(&mut data, |&e| e % 2 == 0);
let (mut left, mut right) = (
    data[0..first_false].iter().cloned().collect::<Vec<u32>>(),
    data[first_false..].iter().cloned().collect::<Vec<u32>>());
trues.sort(); falses.sort(); left.sort(); right.sort();
trues == left && falses == right
```
`trues`/`falses` are computed from the original `data`; `left`/`right` from the
contents of `data` after the call (`r.2`). The conjunct
`first_false ≤ len` states that the test's range indexing
`data[0..first_false]` / `data[first_false..]` does not panic. -/
def partition_index_separates_even_odd_spec {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) : Prop :=
  partition_index inst data pred ⦃ r =>
    r.1.val ≤ r.2.length ∧
    sortU32 (evens data.val) = sortU32 (r.2.val.take r.1.val) ∧
    sortU32 (odds data.val) = sortU32 (r.2.val.drop r.1.val) ⦄

/-- PBT `tests::quickcheck` / `prop_partition` (src/lib.rs:93-103):
```
let mut trues = data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>();
let mut falses = data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>();
let (left, right) = partition(&mut data, |&e| e % 2 == 0);
trues.sort(); falses.sort(); left.sort(); right.sort();
trues == left && falses == right
```
`r.1.1` / `r.1.2` are the two sub-slices returned by `partition` (the
write-back function `r.2` is not used by the test). -/
def partition_separates_even_odd_spec {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) : Prop :=
  partition.partition inst data pred ⦃ r =>
    sortU32 (evens data.val) = sortU32 r.1.1.val ∧
    sortU32 (odds data.val) = sortU32 r.1.2.val ⦄

axiom partition_index_separates_even_odd {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data : Slice Std.U32) :
    partition_index_separates_even_odd_spec inst pred data

end Benchmark.Cases.Partition.SlicePartition.Oracle
