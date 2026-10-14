import Benchmark.Cases.RevBits.U32.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open rev_bits

namespace Benchmark.Cases.RevBits.U32

/-- For every `u32` bound `x`, the range helper `decrement` (used by
`to_start_end` for excluded end bounds) never panics and returns `0` for
`x == 0` and `min(x - 1, BITS - 1)` otherwise (`BITS - 1 = 31`). -/
def decrement_is_correct_spec (x : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.RevBits.U32
