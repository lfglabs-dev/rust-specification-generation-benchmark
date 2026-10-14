import Benchmark.Cases.OpenpqlPrelude.Card.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude
open Benchmark.Cases.OpenpqlPrelude.Card

namespace Benchmark.Cases.OpenpqlPrelude.Card.Oracle

/-- quickcheck `card::card64::tests::test_count` (openpql-prelude/src/card/card64.rs:434-444):

```rust
assert_eq!(
    c64.count(),
    Card::all::<false>().iter().filter(|&c| c64.contains_card(*c)).count() as CardCount
);
```

Both sides are computed in the extracted semantics; the `usize` count (at most
52) cast `as u8` is its value. -/
def card64_count_spec (c64 : card.card64.Card64) : Prop :=
  (do
    let n ← card.card64.Card64.count c64
    let cards ← allCards.filterM (fun c => card.card64.Card64.contains_card c64 c)
    ok (n, cards.length)) ⦃ p => p.1.val = p.2 ⦄

axiom card64_count_matches_contains_card (c64 : card.card64.Card64)
    (h_c64 : c64.val &&& 0x1FFF1FFF1FFF1FFF = c64.val) :
    card64_count_spec c64

end Benchmark.Cases.OpenpqlPrelude.Card.Oracle
