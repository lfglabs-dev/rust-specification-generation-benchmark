import Benchmark.Cases.IndexedBitvec.Word.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

/-- For every word `x` and all bit indices `i, j < 64`, `Word::set(i, true)` and
`Word::set(i, false)` succeed (return `Some(())`), after which `get(i)` reports
the written bit and `get(j)` for `j ≠ i` reports the original bit of `x`. -/
def set_updates_only_target_bit_spec (x : word.Word) : Prop :=
  ∀ i j : Std.Usize, i.val < 64 → j.val < 64 →
    (do
      let (rt, set_true) ← word.Word.set x i true
      let (rf, set_false) ← word.Word.set x i false
      let gt ← word.Word.get set_true j
      let gf ← word.Word.get set_false j
      let g ← word.Word.get x j
      ok (rt, rf, gt, gf, g)) ⦃ (rt, rf, gt, gf, g) =>
        rt = core.option.Option.Some () ∧ rf = core.option.Option.Some () ∧
        (if i = j then
          gt = core.option.Option.Some true ∧ gf = core.option.Option.Some false
        else gt = g ∧ gf = g) ⦄

end Benchmark.Cases.IndexedBitvec.Word
