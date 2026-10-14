import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- Montgomery multiplication of reduced elements never panics and is commutative. -/
def mul_commutative_spec (a b : field.Field) : Prop :=
  (do
    let ab ← field.Field.Insts.CoreOpsArithMulFieldField.mul a b
    let ba ← field.Field.Insts.CoreOpsArithMulFieldField.mul b a
    ok (ab, ba)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Goldilocks.Field
