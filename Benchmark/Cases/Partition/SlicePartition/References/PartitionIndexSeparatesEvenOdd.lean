import Benchmark.Cases.Partition.SlicePartition.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open partition

namespace Benchmark.Cases.Partition.SlicePartition

/-- Partitioning any `u32` slice in place with the predicate "is even" never
panics and returns an index `first_false ≤ len` such that the prefix
`data[..first_false]` of the rearranged slice holds exactly the even
elements of the original slice and the suffix `data[first_false..]` exactly
the odd ones (compared as sorted vectors, as the property test does). -/
def partition_index_separates_even_odd_spec {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) : Prop :=
  partition_index inst data pred ⦃ r =>
    r.1.val ≤ r.2.length ∧
    sortU32 (evens data.val) = sortU32 (r.2.val.take r.1.val) ∧
    sortU32 (odds data.val) = sortU32 (r.2.val.drop r.1.val) ⦄

end Benchmark.Cases.Partition.SlicePartition
