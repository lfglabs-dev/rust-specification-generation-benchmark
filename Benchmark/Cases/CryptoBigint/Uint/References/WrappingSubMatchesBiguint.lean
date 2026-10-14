import Benchmark.Cases.CryptoBigint.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

/-- For all `U256` values `a`, `b`, after swapping them so that `a >= b`, `a.wrapping_sub(&b)` never panics and its value is `a - b`, the value of `to_uint(a_bi - b_bi)`. -/
def wrapping_sub_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  let hi := if uintVal b > uintVal a then b else a -- `a` after the swap
  let lo := if uintVal b > uintVal a then a else b -- `b` after the swap
  (uint.sub.Uint.wrapping_sub hi lo) ⦃ r => uintVal r = (uintVal hi - uintVal lo) % 2^256 ⦄

end Benchmark.Cases.CryptoBigint.Uint
