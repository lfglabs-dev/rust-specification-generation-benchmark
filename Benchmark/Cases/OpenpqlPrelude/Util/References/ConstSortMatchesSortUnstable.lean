import Benchmark.Cases.OpenpqlPrelude.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- `const_sort` (insertion sort on a `[u64; 10]`) never panics and returns exactly
`sort_unstable`'s result: the non-decreasing permutation of the input. -/
def const_sort_spec (numbers : Std.Array Std.U64 10#usize) : Prop :=
  waugh_indexer.util.const_sort numbers ⦃ sorted =>
    sorted.val.map (·.val) = (numbers.val.map (·.val)).mergeSort ⦄

end Benchmark.Cases.OpenpqlPrelude.Util
