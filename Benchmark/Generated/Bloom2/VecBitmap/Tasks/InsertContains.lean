import Benchmark.Cases.Bloom2.VecBitmap.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open bloom2

namespace Benchmark.Cases.Bloom2.VecBitmap

/-- Setting the bits of a set of fewer than 20 distinct keys below 1028 in a fresh
`VecBitmap::new_with_capacity(1028)` never panics, and afterwards `get(i)`
answers exactly the membership of `i` in the set, for every `i < 1028`. -/
def insert_contains_spec (values : List Std.Usize) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Bloom2.VecBitmap
