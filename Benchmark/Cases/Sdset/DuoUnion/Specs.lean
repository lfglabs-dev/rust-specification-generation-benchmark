import Benchmark.Cases.Sdset.DuoUnion.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sdset
open Benchmark.Cases.Sdset.DuoUnion

namespace Benchmark.Cases.Sdset.DuoUnion.Oracle

/-- PBT `duo::union::tests::set_to_iter::qc_union` (src/duo/union.rs:280):
```
let x: Vec<i32> = Union { a: &a, b: &b }.into_iter().cloned().collect();
let y: Vec<_> = BTreeSet::from_iter(a).union(&BTreeSet::from_iter(b)).cloned().collect();
x.as_slice() == y.as_slice()
```
`a`, `b` are the slices of the (sorted, deduplicated) test vectors. The Rust
side runs `IntoIterator::into_iter` of `Union<'_, i32>` (the by-value impl) and
collects the resulting `UnionIter` (`CollectsTo`); the collected vector must be
the BTreeSet union (compared through the injective `.val`, i.e. as `i32`
values). -/
def union_iter_matches_btreeset_union_spec (a b : Slice Std.I32) : Prop :=
  (duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
      core.I32.Insts.CoreCmpOrd ({ a := a, b := b } : duo.union.Union Std.I32)) ⦃ it =>
    ∃ x : List Std.I32,
      CollectsTo
        (duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
          core.I32.Insts.CoreCmpOrd) it x ∧
      x.map (·.val) = btreeset_union_vec a.val b.val ⦄

axiom union_iter_matches_btreeset_union (a b : Slice Std.I32)
    (h_a : a.val.Pairwise (fun x y => x.val < y.val))
    (h_b : b.val.Pairwise (fun x y => x.val < y.val)) :
    union_iter_matches_btreeset_union_spec a b

end Benchmark.Cases.Sdset.DuoUnion.Oracle
