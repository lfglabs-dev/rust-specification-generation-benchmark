import Benchmark.Cases.Lilliput.IntValue.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/-- `UnsignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `u8` values `lhs`, `rhs` and every pair of width
variants (`U8`, `U16`, `U32`, `U64` holding the zero-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`. -/
def unsigned_int_value_cmp_across_widths_spec (lhs rhs : Std.U8) : Prop :=
  ∀ lhs_value ∈ unsignedValues lhs, ∀ rhs_value ∈ unsignedValues rhs,
    (do
      let int_ordering ← core.U8.Insts.CoreCmpOrd.cmp lhs rhs
      let a ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp lhs_value rhs_value
      let b ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp rhs_value lhs_value
      let reversed ← core.cmp.Ordering.reverse int_ordering
      ok (int_ordering, reversed, a, b)) ⦃ r => r.2.2.1 = r.1 ∧ r.2.2.2 = r.2.1 ⦄

end Benchmark.Cases.Lilliput.IntValue
