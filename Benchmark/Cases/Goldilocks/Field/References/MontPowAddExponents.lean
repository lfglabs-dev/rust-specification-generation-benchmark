import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- Montgomery square-and-multiply exponentiation satisfies `a^(b+c) = a^b * a^c` (in the Montgomery domain). -/
def mont_pow_add_exponents_spec (a b c : Std.U64) : Prop :=
  (do
    let ab ← field.algo.generic.mont_pow a b
    let ac ← field.algo.generic.mont_pow a c
    let bc ← b + c
    let a_bc ← field.algo.generic.mont_pow a bc
    let ab_ac ← field.algo.generic.mont_mul ab ac
    ok (a_bc, ab_ac)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Goldilocks.Field
