import Benchmark.Cases.UseCombinatorics.Counting.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/-- For every `n` drawn from `0_u8..80`, `factorial(u64::from(n))` never panics; it
succeeds (`is_ok()`) exactly for `n ≤ 34` and returns
`Err(FactorialOverflow(n))` for `35 ≤ n < 80`. -/
def factorial_overflow_boundary_is_exact_spec (n : Std.U8) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.UseCombinatorics.Counting
