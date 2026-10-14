import RuintUintAdd.Extraction

/-!
# ruint — `Uint<BITS, LIMBS>` addition, subtraction and negation — specifications

Implementation: `extracted/RuintUintAdd` (verbatim `cargo hax extract
ruint-uint-add` output for alloy-rs/ruint@2071680b).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`debug_assert!`s panic), which is the configuration `cargo test` runs the
original property tests under.

Common translation of the test scaffolding (see `review/translation-notes.md`):
* `const_for!(BITS in SIZES { const LIMBS: usize = nlimbs(BITS); type U =
  Uint<BITS, LIMBS>; ... })` runs the property for every `BITS` of
  `SIZES = [0, 1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096]`: the
  theorems quantify over the const generics `BITS LIMBS : Usize` with
  `BITS.val ∈ SIZES` and `nlimbs BITS = ok LIMBS` (the extracted `ruint::nlimbs`).
* A value `a: U` drawn by proptest comes from `Uint`'s `Arbitrary` impl
  (src/support/proptest.rs): `any::<[u64; LIMBS]>().prop_map(Uint::from_limbs_unmasked)`.
  The specs therefore take an arbitrary limb array `la : Array U64 LIMBS` and run
  the extracted `Uint.from_limbs_unmasked BITS la` first.
* `a + b`, `a - b`, `-a` are the `Add`/`Sub`/`Neg` operator impls for
  `Uint<BITS, LIMBS>` (by value); `U::ZERO` is the associated constant
  `Uint.ZERO BITS LIMBS`; `assert_eq!` compares with the derived `PartialEq`
  (structural equality of the limb arrays), i.e. Lean `=` on `Uint BITS LIMBS`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Ruint.UintAdd

open ruint

end Benchmark.Cases.Ruint.UintAdd
