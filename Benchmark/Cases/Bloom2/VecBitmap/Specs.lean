import Benchmark.Cases.Bloom2.VecBitmap.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open bloom2
open Benchmark.Cases.Bloom2.VecBitmap

namespace Benchmark.Cases.Bloom2.VecBitmap.Oracle

/-- PBT `bitmap::vec::tests::prop_insert_contains` (src/bitmap/vec.rs:78-92),
with `MAX_KEY = 1028`:
```
let mut b = VecBitmap::new_with_capacity(MAX_KEY);
for v in &values { b.set(*v, true); }
for i in 0..MAX_KEY { assert_eq!(b.get(i), values.contains(&i)); }
```
`values` is the generated `HashSet<usize>`, given as the list of its elements
in iteration order (each element once; any order). The insertion loop is the
left fold of the extracted `Bitmap::set` over that list. The checking loop only
reads the bitmap, so it succeeds iff every single `get(i)`, `i < MAX_KEY`,
returns `values.contains(&i)` without panicking. -/
def insert_contains_spec (values : List Std.Usize) : Prop :=
  (do
    let b ← bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.new_with_capacity 1028#usize
    values.foldlM (fun b v => bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.set b v true) b)
  ⦃ b => ∀ i : Std.Usize, i.val < 1028 →
      bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.get b i ⦃ r => r = decide (i ∈ values) ⦄ ⦄

axiom insert_contains (values : List Std.Usize)
    (h_nodup : values.Nodup)
    (h_len : values.length < 20)
    (h_range : ∀ v ∈ values, v.val < 1028)
    (h_platform : System.Platform.numBits = 64) :
    insert_contains_spec values

end Benchmark.Cases.Bloom2.VecBitmap.Oracle
