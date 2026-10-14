import Benchmark.Cases.CryptoBigint.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

/-- For all `U256` values `a`, `b`, `a.wrapping_and(&b)` never panics and its value is the bitwise AND of the values, the value of `to_uint(a_bi & b_bi)`. -/
def wrapping_and_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_and.Uint.wrapping_and a b) ⦃ r => uintVal r = (uintVal a &&& uintVal b) % 2^256 ⦄

end Benchmark.Cases.CryptoBigint.Uint
