import IndexedBitvecWord.Extraction

/-!
# indexed_bitvec (core `word` module) — specifications

Implementation: `extracted/IndexedBitvecWord` (verbatim `cargo hax extract
indexed-bitvec-word` output for DarkOtter/indexed-bitvec-rs@cbf32fff, crate
`indexed_bitvec_core` in `core/`, rooted at the module `word` and the free
functions `ceil_div`, `ceil_div_slow`, `ceil_div_u64`, `ceil_div_u64_slow`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

`Word` is the newtype `struct Word(u64)`; Aeneas represents it by its `u64`
payload (`word.Word := Std.U64`). Bits of a `Word` are indexed MSB-first:
`Word::get(i)` reads bit `63 - i` of the integer. `Word::len` is the constant
`64` (extracted `word.Word.len`: `ok 64#usize`), so the tests' `0..x.len()`
loops range over `0..64`.

The quickcheck generators (`impl Arbitrary for Word` = `u64::arbitrary(g).into()`,
`u16`/`usize`/`u64` arbitrary) produce every value of the type, so the only
theorem hypotheses are the explicit proptest ranges.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.IndexedBitvec.Word

open indexed_bitvec_core

/-- `bit` lists what `Word::get` reports for `x`: for every index `j < 64`,
`x.get(j)` terminates without panicking and returns `Some(bit j)`. (Since `get`
is a deterministic function, `bit` is uniquely determined on `0..64`; the
tests call `x.get(j).unwrap()` and use the resulting booleans as their naive
reference.) -/
def GetBits (x : word.Word) (bit : Nat → Bool) : Prop :=
  ∀ j : Std.Usize, j.val < 64 →
    word.Word.get x j ⦃ r => r = core.option.Option.Some (bit j.val) ⦄

/-- Naive counting: the number of indices `j < n` with `bit j = b` (what the
tests compute with `(0..n).filter(..).count()` or with running counters). -/
def countBits (bit : Nat → Bool) (b : Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun j => bit j == b)).length

end Benchmark.Cases.IndexedBitvec.Word
