import Benchmark.Cases.Lilliput.IntValue.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/-- `UnsignedIntValue`'s `PartialEq` ignores the storage width: for all `u8`
values `lhs`, `rhs` and every pair of width variants (`U8`, `U16`, `U32`, `U64`
holding the zero-extended values), `lhs_value.eq(rhs_value)` and
`rhs_value.eq(lhs_value)` never panic and both equal `lhs == rhs`. -/
def unsigned_int_value_eq_across_widths_spec (lhs rhs : Std.U8) : Prop :=
  ∀ lhs_value ∈ unsignedValues lhs, ∀ rhs_value ∈ unsignedValues rhs,
    (do
      let int_is_equal ← core.U8.Insts.CoreCmpPartialEqU8.eq lhs rhs
      let a ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq
        lhs_value rhs_value
      let b ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq
        rhs_value lhs_value
      ok (int_is_equal, a, b)) ⦃ r => r.2.1 = r.1 ∧ r.2.2 = r.1 ⦄

end Benchmark.Cases.Lilliput.IntValue
