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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.IndexedBitvec.Word
