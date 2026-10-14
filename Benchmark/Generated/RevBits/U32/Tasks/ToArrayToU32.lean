import Benchmark.Cases.RevBits.U32.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open rev_bits

namespace Benchmark.Cases.RevBits.U32

/-- For every `u32` value `x`, expanding it into a `[bool; 32]` bit array with
the reference implementation's `to_array` (bit `i` at index `i`) and
packing the array back with `to_u32` (which folds the bits from the last
index down with `out = out << 1 | bit`) never panics and returns `x`. -/
def to_array_to_u32_spec (x : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.RevBits.U32
