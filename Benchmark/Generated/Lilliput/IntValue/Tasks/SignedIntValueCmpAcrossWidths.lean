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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Lilliput.IntValue
