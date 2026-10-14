import Benchmark.Cases.Blue.ScrunchBinarySearch.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open scrunch
open Benchmark.Cases.Blue.ScrunchBinarySearch

namespace Benchmark.Cases.Blue.ScrunchBinarySearch.Oracle

/-- PBT `binary_search::tests::binary_search` (scrunch/src/binary_search.rs:95-105),
one iteration `i` of its loop `for i in 0..elements.len()`:
```
let expected = elements.partition_point(|x| *x < elements[i]);
assert_eq!(expected, i);
let returned = binary_search_by(0, elements.len() - 1, |x| elements[x].cmp(&elements[i]));
assert_eq!(expected, returned, ...);
```
`elements.len() - 1` is computed with checked `usize` subtraction. -/
def binary_search_finds_index_spec (elements : Slice Std.Usize) (i : Std.Usize) : Prop :=
  (do
    let n ← core.slice.Slice.len elements
    let last ← n - 1#usize
    binary_search.binary_search_by ProbeClosure.Insts.FnMut 0#usize last
      { elements := elements, i := i }) ⦃ returned =>
    partitionPointLt elements (elements.val[i.val]!) = i.val ∧
      partitionPointLt elements (elements.val[i.val]!) = returned.val ⦄

axiom binary_search_finds_index (elements : Slice Std.Usize)
    (h_len : elements.length < 64)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize)
    (h_i : i.val < elements.length) :
    binary_search_finds_index_spec elements i

end Benchmark.Cases.Blue.ScrunchBinarySearch.Oracle
