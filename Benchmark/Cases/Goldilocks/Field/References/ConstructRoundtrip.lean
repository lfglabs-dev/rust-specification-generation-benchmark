import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- `Field::new(n)` (u128 `n * MONT_R1 % MODULUS`) and `Field::from(n)` (`mont_mul(reduce_64(n), MONT_R2)`)
produce the same Montgomery representative, and `u64::from` of it gives back `n`. -/
def construct_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let a ← field.Field.new n
    let b ← field.Field.Insts.CoreConvertFromU64.from n
    let m ← goldilocks_ntt.U64.Insts.CoreConvertFromField.from a
    ok (a, b, m)) ⦃ r => r.1 = r.2.1 ∧ r.2.2 = n ⦄

end Benchmark.Cases.Goldilocks.Field
