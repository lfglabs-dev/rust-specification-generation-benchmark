import Benchmark.Cases.Ruint.UintAdd.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.UintAdd

/-- For every supported width `BITS` (with `LIMBS = nlimbs(BITS)`) and every
`a : Uint<BITS, LIMBS>` produced by the proptest strategy, wrapping negation is
an additive inverse and an involution: `a + (-a) == U::ZERO`,
`a - a == U::ZERO` and `-(-a) == a`. -/
def inverse_spec (BITS LIMBS : Std.Usize) (la : Array Std.U64 LIMBS) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Ruint.UintAdd
