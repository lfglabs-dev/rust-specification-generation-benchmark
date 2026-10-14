import UintU64.Extraction

/-!
# uint (parity-common) — specifications for `construct_uint!`-generated `U64`

Implementation: `extracted/UintU64` (verbatim `cargo hax extract uint-u64`
output for paritytech/parity-common@2b887751, crate `ethereum-types`, module
`ethereum_types::uint`). That module is the single macro invocation
`construct_uint! { pub struct U64(1); }` of the workspace's `uint` crate (0.10.1),
the same invocation the property tests make in `uint/tests/uint_tests.rs`
(`mod laws`, `construct_uint! { pub struct U64(1); }`, then
`uint_laws!(u64, U64)`); the generated code is identical. `U64` is a
little-endian array of one `u64` limb (`Array Std.U64 1#usize`).

The quickcheck laws use the operators of the generated type:
* `x + y` is `impl<T: Into<U64>> Add<T> for U64` at `T = U64` (the `Into` is
  core's blanket `impl<T, U: From<T>> Into<U> for T` with the reflexive
  `impl<T> From<T> for T`): `overflowing_add` followed by
  `panic_on_overflow!` (extracted as `massert (¬ overflow)`);
* `x - y` likewise with `overflowing_sub`;
* `a == b` is the derived `PartialEq` (CoreModels array equality on the limbs).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. The laws are
`TestResult` / `bool` quickcheck properties: `TestResult::discard()` branches
become the theorems' `h_assume_*` hypotheses (stated with the extracted
`overflowing_add`, exactly as the test computes them), and the returned boolean
must be `true`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Uint.U64

open ethereum_types

/-- `x + y` for the generated `U64` (the `Add<U64>` instance of `impl<T: Into<U64>> Add<T> for U64`). -/
abbrev add (x y : uint.U64) : RustM uint.U64 :=
  uint.U64.Insts.CoreOpsArithAddTU64.add (core.convert.Into.Blanket (core.convert.From.Blanket uint.U64)) x y

/-- `x - y` for the generated `U64` (the `Sub<U64>` instance of `impl<T: Into<U64>> Sub<T> for U64`). -/
abbrev sub (x y : uint.U64) : RustM uint.U64 :=
  uint.U64.Insts.CoreOpsArithSubTU64.sub (core.convert.Into.Blanket (core.convert.From.Blanket uint.U64)) x y

end Benchmark.Cases.Uint.U64
