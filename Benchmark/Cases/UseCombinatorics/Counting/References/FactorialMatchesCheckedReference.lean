import Benchmark.Cases.UseCombinatorics.Counting.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/-- For every `n` drawn from `0_u8..41`, `factorial(u64::from(n))` never panics and
agrees with the test's checked `u128` reference: it returns `Ok(expected)` when
`factorial_reference(n)` is `Some(expected)` and `Err(FactorialOverflow(n))`
when the reference overflows (`None`). -/
def factorial_matches_checked_reference_spec (n : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let result ← counting.factorial n_u64
    ok (n_u64, result)) ⦃ out =>
      match out with
      | (n_u64, result) =>
        match factorial_reference n.val with
        | some expected =>
          ∃ v : Std.U128, result = core.result.Result.Ok v ∧ v.val = expected
        | none =>
          result = core.result.Result.Err (error.CombinatoricsError.FactorialOverflow n_u64) ⦄

end Benchmark.Cases.UseCombinatorics.Counting
