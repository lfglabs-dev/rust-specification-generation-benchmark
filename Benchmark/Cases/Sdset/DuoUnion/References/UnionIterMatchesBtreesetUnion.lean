import Benchmark.Cases.Sdset.DuoUnion.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sdset

namespace Benchmark.Cases.Sdset.DuoUnion

/-- For any two sorted, deduplicated `i32` slices `a` and `b`, iterating
`Union { a, b }` (`into_iter`, then `next` until `None`, i.e. `collect`) never
panics and yields exactly the elements of the `BTreeSet` union of `a` and `b`,
in increasing order. -/
def union_iter_matches_btreeset_union_spec (a b : Slice Std.I32) : Prop :=
  (duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
      core.I32.Insts.CoreCmpOrd ({ a := a, b := b } : duo.union.Union Std.I32)) ⦃ it =>
    ∃ x : List Std.I32,
      CollectsTo
        (duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
          core.I32.Insts.CoreCmpOrd) it x ∧
      x.map (·.val) = btreeset_union_vec a.val b.val ⦄

end Benchmark.Cases.Sdset.DuoUnion
