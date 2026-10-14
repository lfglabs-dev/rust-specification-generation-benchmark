import Benchmark.Cases.IndexedBitvec.Word.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

/-- For every word `x` and every `i` below `x.count_ones()`, `x.select_ones(i)`
returns `Some(r)` with `x.rank_ones(r) == Some(i)` and `x.get(r) == Some(true)`;
`x.select_ones(x.count_ones())` returns `None`. -/
def select_ones_inverts_rank_spec (x : word.Word) : Prop :=
  word.Word.count_ones x ⦃ total =>
    (∀ i : Std.U32, i.val < total.val →
      (do
        let o ← word.Word.select_ones x i
        let r ← core.option.Option.unwrap o
        let r ← lift (UScalar.cast .Usize r)
        let rank ← word.Word.rank_ones x r
        let g ← word.Word.get x r
        ok (rank, g)) ⦃ (rank, g) =>
          rank = core.option.Option.Some i ∧ g = core.option.Option.Some true ⦄) ∧
    word.Word.select_ones x total ⦃ o => o = core.option.Option.None ⦄ ⦄

end Benchmark.Cases.IndexedBitvec.Word
