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
  (do
    let b ← bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.new_with_capacity 1028#usize
    values.foldlM (fun b v => bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.set b v true) b)
  ⦃ b => ∀ i : Std.Usize, i.val < 1028 →
      bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.get b i ⦃ r => r = decide (i ∈ values) ⦄ ⦄

end Benchmark.Cases.Bloom2.VecBitmap
