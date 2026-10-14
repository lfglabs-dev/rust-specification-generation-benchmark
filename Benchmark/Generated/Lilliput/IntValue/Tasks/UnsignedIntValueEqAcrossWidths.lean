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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Lilliput.IntValue
