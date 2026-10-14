import OpenpqlPreludeCard.Extraction

/-!
# openpql-prelude — specifications (card bitsets)

Implementation: `extracted/OpenpqlPreludeCard` (verbatim `cargo hax extract
openpql-prelude-card` output for solve-poker/Poker-Query-Language@157235d6,
crate `openpql-prelude`, modules `card::card64`, `card::rank16`, `card::suit4`).
`Card64` is a `u64` bitset (`Std.U64`): suit `s` (`S, H, D, C` = 0..3) occupies
bits `16 s .. 16 s + 15`, rank `r` (`R2 .. RA` = 0..12) is bit `16 s + r` of
that block; bits `13..15` of each block are unused. `Rank16` is a `u16` bitset
of ranks (`Std.U16`).

The property tests compare the bitset operations with a reference computed by
iterating over `Card::all::<false>()` (the 52 cards `Card::ARR_ALL`, rank-major:
`2s 2h 2d 2c 3s .. Ac`). That constant array sits behind an inline
`const { }` block which the extraction cannot translate, so it is written out
here (`allCards`); the per-card predicate the test evaluates
(`c64.contains_card(c)`) is the extracted function, run for every card in the
`RustM` monad (`List.filterM`), exactly as the test's `filter` does.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (shifts and `+`/`*`
panic on overflow), the configuration `cargo test` runs the properties under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.OpenpqlPrelude.Card

open openpql_prelude

/-- `Rank::ARR_ALL` (`Rank::all::<false>()`): the 13 ranks in increasing order. -/
def allRanks : List card.rank.Rank :=
  [.R2, .R3, .R4, .R5, .R6, .R7, .R8, .R9, .RT, .RJ, .RQ, .RK, .RA]

/-- `Suit::ARR_ALL`: the 4 suits `S, H, D, C`. -/
def allSuits : List card.suit.Suit := [.S, .H, .D, .C]

/-- `Card::ARR_ALL` (`Card::all::<false>()`): the 52 cards, rank-major
(`Card::new(R2, S), Card::new(R2, H), .., Card::new(RA, C)`). -/
def allCards : List card.card.Card :=
  allRanks.flatMap (fun r => allSuits.map (fun s => { rank := r, suit := s }))

end Benchmark.Cases.OpenpqlPrelude.Card
