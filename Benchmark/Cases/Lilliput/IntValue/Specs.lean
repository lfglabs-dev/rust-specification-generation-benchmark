import Benchmark.Cases.Lilliput.IntValue.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core
open Benchmark.Cases.Lilliput.IntValue

namespace Benchmark.Cases.Lilliput.IntValue.Oracle

/-- PBT `value::int::unsigned::tests::eq` (lilliput-core/src/value/int/unsigned.rs:254-278):
for every `lhs_value` of `lhs_values` and `rhs_value` of `rhs_values`,
`let int_is_equal = lhs.eq(&rhs);`
`prop_assert_eq!(lhs_value.eq(rhs_value), int_is_equal);`
`prop_assert_eq!(rhs_value.eq(lhs_value), int_is_equal);` -/
def unsigned_int_value_eq_across_widths_spec (lhs rhs : Std.U8) : Prop :=
  ∀ lhs_value ∈ unsignedValues lhs, ∀ rhs_value ∈ unsignedValues rhs,
    (do
      let int_is_equal ← core.U8.Insts.CoreCmpPartialEqU8.eq lhs rhs
      let a ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq
        lhs_value rhs_value
      let b ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq
        rhs_value lhs_value
      ok (int_is_equal, a, b)) ⦃ r => r.2.1 = r.1 ∧ r.2.2 = r.1 ⦄

/-- PBT `value::int::unsigned::tests::ord` (lilliput-core/src/value/int/unsigned.rs:280-303):
for every `lhs_value` of `lhs_values` and `rhs_value` of `rhs_values`,
`let int_ordering = lhs.cmp(&rhs);`
`prop_assert_eq!(lhs_value.cmp(rhs_value), int_ordering);`
`prop_assert_eq!(rhs_value.cmp(lhs_value), int_ordering.reverse());` -/
def unsigned_int_value_cmp_across_widths_spec (lhs rhs : Std.U8) : Prop :=
  ∀ lhs_value ∈ unsignedValues lhs, ∀ rhs_value ∈ unsignedValues rhs,
    (do
      let int_ordering ← core.U8.Insts.CoreCmpOrd.cmp lhs rhs
      let a ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp lhs_value rhs_value
      let b ← value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp rhs_value lhs_value
      let reversed ← core.cmp.Ordering.reverse int_ordering
      ok (int_ordering, reversed, a, b)) ⦃ r => r.2.2.1 = r.1 ∧ r.2.2.2 = r.2.1 ⦄

/-- PBT `value::int::signed::tests::eq` (lilliput-core/src/value/int/signed.rs:236-260):
for every `lhs_value` of `lhs_values` and `rhs_value` of `rhs_values`,
`let int_is_equal = lhs.eq(&rhs);`
`prop_assert_eq!(lhs_value.eq(rhs_value), int_is_equal);`
`prop_assert_eq!(rhs_value.eq(lhs_value), int_is_equal);` -/
def signed_int_value_eq_across_widths_spec (lhs rhs : Std.I8) : Prop :=
  ∀ lhs_value ∈ signedValues lhs, ∀ rhs_value ∈ signedValues rhs,
    (do
      let int_is_equal ← core.I8.Insts.CoreCmpPartialEqI8.eq lhs rhs
      let a ← value.int.signed.SignedIntValue.Insts.CoreCmpPartialEqSignedIntValue.eq
        lhs_value rhs_value
      let b ← value.int.signed.SignedIntValue.Insts.CoreCmpPartialEqSignedIntValue.eq
        rhs_value lhs_value
      ok (int_is_equal, a, b)) ⦃ r => r.2.1 = r.1 ∧ r.2.2 = r.1 ⦄

/-- PBT `value::int::signed::tests::ord` (lilliput-core/src/value/int/signed.rs:262-285):
for every `lhs_value` of `lhs_values` and `rhs_value` of `rhs_values`,
`let int_ordering = lhs.cmp(&rhs);`
`prop_assert_eq!(lhs_value.cmp(rhs_value), int_ordering);`
`prop_assert_eq!(rhs_value.cmp(lhs_value), int_ordering.reverse());` -/
def signed_int_value_cmp_across_widths_spec (lhs rhs : Std.I8) : Prop :=
  ∀ lhs_value ∈ signedValues lhs, ∀ rhs_value ∈ signedValues rhs,
    (do
      let int_ordering ← core.I8.Insts.CoreCmpOrd.cmp lhs rhs
      let a ← value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp lhs_value rhs_value
      let b ← value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp rhs_value lhs_value
      let reversed ← core.cmp.Ordering.reverse int_ordering
      ok (int_ordering, reversed, a, b)) ⦃ r => r.2.2.1 = r.1 ∧ r.2.2.2 = r.2.1 ⦄

axiom signed_int_value_cmp_across_widths (lhs rhs : Std.I8) :
    signed_int_value_cmp_across_widths_spec lhs rhs

axiom unsigned_int_value_cmp_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_cmp_across_widths_spec lhs rhs

axiom unsigned_int_value_eq_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_eq_across_widths_spec lhs rhs

end Benchmark.Cases.Lilliput.IntValue.Oracle
