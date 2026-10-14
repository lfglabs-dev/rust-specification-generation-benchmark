import Benchmark.Cases.UseCombinatorics.Counting.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/-- For every `n, k` drawn from `0_u8..81`, `permutations(u64::from(n), u64::from(k))`
never panics and returns `Err(KExceedsN { n, k })` when `k > n`, otherwise
`Ok(expected)` when the checked `u128` reference `permutations_reference(n, k)`
is `Some(expected)`, and `Err(PermutationOverflow { n, k })` when it overflows. -/
def permutations_match_checked_reference_spec (n k : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let k_u64 ← core.U64.Insts.CoreConvertFromU8.from k
    let result ← counting.permutations n_u64 k_u64
    ok (n_u64, k_u64, result)) ⦃ out =>
      match out with
      | (n_u64, k_u64, result) =>
        if k.val > n.val then
          result = core.result.Result.Err (error.CombinatoricsError.KExceedsN n_u64 k_u64)
        else
          match permutations_reference n.val k.val with
          | some expected =>
            ∃ v : Std.U128, result = core.result.Result.Ok v ∧ v.val = expected
          | none =>
            result = core.result.Result.Err
              (error.CombinatoricsError.PermutationOverflow n_u64 k_u64) ⦄

end Benchmark.Cases.UseCombinatorics.Counting
