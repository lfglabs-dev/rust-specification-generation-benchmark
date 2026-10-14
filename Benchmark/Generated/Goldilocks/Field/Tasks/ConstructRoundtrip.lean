import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- `Field::new(n)` (u128 `n * MONT_R1 % MODULUS`) and `Field::from(n)` (`mont_mul(reduce_64(n), MONT_R2)`)
produce the same Montgomery representative, and `u64::from` of it gives back `n`. -/
def construct_roundtrip_spec (n : Std.U64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Goldilocks.Field
