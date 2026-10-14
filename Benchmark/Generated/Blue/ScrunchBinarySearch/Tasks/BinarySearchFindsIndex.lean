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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Blue.ScrunchBinarySearch
