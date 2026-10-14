import Benchmark.Cases.Lilliput.IntValue.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/-- `SignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `i8` values `lhs`, `rhs` and every pair of width
variants (`I8`, `I16`, `I32`, `I64` holding the sign-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`. -/
def signed_int_value_cmp_across_widths_spec (lhs rhs : Std.I8) : Prop :=
  ∀ lhs_value ∈ signedValues lhs, ∀ rhs_value ∈ signedValues rhs,
    (do
      let int_ordering ← core.I8.Insts.CoreCmpOrd.cmp lhs rhs
      let a ← value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp lhs_value rhs_value
      let b ← value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp rhs_value lhs_value
      let reversed ← core.cmp.Ordering.reverse int_ordering
      ok (int_ordering, reversed, a, b)) ⦃ r => r.2.2.1 = r.1 ∧ r.2.2.2 = r.2.1 ⦄

end Benchmark.Cases.Lilliput.IntValue
