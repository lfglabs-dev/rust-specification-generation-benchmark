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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.IndexedBitvec.Word
