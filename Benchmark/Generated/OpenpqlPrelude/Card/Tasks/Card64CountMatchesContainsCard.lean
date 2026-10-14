import Benchmark.Cases.OpenpqlPrelude.Card.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Card

/-- For every `Card64` produced by the property-test generator (a `u64` masked with
`Card64::ALL`), `count()` (a popcount) never panics and equals the number of the 52 cards
for which `contains_card` holds. -/
def card64_count_spec (c64 : card.card64.Card64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.OpenpqlPrelude.Card
