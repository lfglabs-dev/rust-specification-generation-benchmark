import GoldilocksField.Extraction

/-!
# goldilocks (`goldilocks-ntt` field arithmetic) — specifications

Implementation: `extracted/GoldilocksField` (verbatim `cargo hax extract
goldilocks-field` output for recmo/goldilocks@e7588712, crate `goldilocks-ntt`).

The Goldilocks prime is `MODULUS = 2^64 - 2^32 + 1` (`0xffff_ffff_0000_0001`).
`algo::generic::{add, sub}` implement modular addition/subtraction on reduced
`u64`s; `mont_mul(a, b) = mont_reduce_128(a * b)` is Montgomery multiplication
(`R = 2^64`), and `mont_pow` is square-and-multiply over `mont_mul`.
`Field` is `#[repr(transparent)] struct Field(u64)` holding the Montgomery form
of the element; the extraction flattens the newtype, so `field.Field` is
(reducibly) `Std.U64` and `a.val` is the stored representative. The derived
`PartialEq` is extracted as `ok (self = other)`, so `assert_eq!` on `Field` or
`u64` values is stated as Lean equality of the extracted values.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, and the
`debug_assert!`s of `add`/`sub`/`mont_reduce_128`/`mont_pow` are `massert`s),
which is the configuration `cargo test` runs the original property tests under.

Strategies: `a: Field` uses the test module's `Arbitrary for Field`
(`(0..algo::MODULUS).prop_map(Self)`), i.e. any representative `< MODULUS`;
`a: u64` with `prop_assume!(a < MODULUS)` gives the same bound as a hypothesis.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Goldilocks.Field

open goldilocks_ntt

/-! ## `Field` arithmetic laws (`ntt/src/field/mod.rs`, module `tests`) -/

end Benchmark.Cases.Goldilocks.Field
