import Benchmark.Cases.Blue.ScrunchBinarySearch.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open scrunch

namespace Benchmark.Cases.Blue.ScrunchBinarySearch

/-- For a strictly increasing `usize` vector `elements` and any position `i`,
`binary_search_by(0, elements.len() - 1, |x| elements[x].cmp(&elements[i]))`
never panics and returns `i`, which is also the partition point of
`|x| *x < elements[i]`. -/
def binary_search_finds_index_spec (elements : Slice Std.Usize) (i : Std.Usize) : Prop :=
  (do
    let n ← core.slice.Slice.len elements
    let last ← n - 1#usize
    binary_search.binary_search_by ProbeClosure.Insts.FnMut 0#usize last
      { elements := elements, i := i }) ⦃ returned =>
    partitionPointLt elements (elements.val[i.val]!) = i.val ∧
      partitionPointLt elements (elements.val[i.val]!) = returned.val ⦄

end Benchmark.Cases.Blue.ScrunchBinarySearch
