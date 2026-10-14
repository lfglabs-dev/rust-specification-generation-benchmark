import Benchmark.Cases.CryptoBigint.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

/-- For all `U256` values `a`, `b`, after swapping them so that `a >= b`, `a.wrapping_sub(&b)` never panics and its value is `a - b`, the value of `to_uint(a_bi - b_bi)`. -/
def wrapping_sub_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.CryptoBigint.Uint
