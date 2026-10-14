import Benchmark.Cases.UseCombinatorics.Counting.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics
open Benchmark.Cases.UseCombinatorics.Counting

namespace Benchmark.Cases.UseCombinatorics.Counting.Oracle

/-- PBT `factorial_matches_checked_reference` (tests/property_counting.rs:50-59):
```rust
let n_u64 = u64::from(n);
if let Some(expected) = factorial_reference(n) {
    prop_assert_eq!(factorial(n_u64), Ok(expected));
} else {
    prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
}
```
The do-block performs the conversion `u64::from(n)` and the call; the
postcondition is the branch selected by the reference. -/
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

/-- PBT `factorial_overflow_boundary_is_exact` (tests/property_counting.rs:61-70):
```rust
let n_u64 = u64::from(n);
if n <= 34 {
    prop_assert!(factorial(n_u64).is_ok());
} else {
    prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
}
```
`is_ok()` holds exactly when the result is an `Ok _`. -/
def factorial_overflow_boundary_is_exact_spec (n : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let result ← counting.factorial n_u64
    ok (n_u64, result)) ⦃ out =>
      match out with
      | (n_u64, result) =>
        if n.val ≤ 34 then
          ∃ v : Std.U128, result = core.result.Result.Ok v
        else
          result = core.result.Result.Err (error.CombinatoricsError.FactorialOverflow n_u64) ⦄

/-- PBT `permutations_match_checked_reference` (tests/property_counting.rs:72-90):
```rust
let n_u64 = u64::from(n);
let k_u64 = u64::from(k);
if k > n {
    prop_assert_eq!(permutations(n_u64, k_u64),
        Err(CombinatoricsError::KExceedsN { n: n_u64, k: k_u64 }));
} else if let Some(expected) = permutations_reference(n, k) {
    prop_assert_eq!(permutations(n_u64, k_u64), Ok(expected));
} else {
    prop_assert_eq!(permutations(n_u64, k_u64),
        Err(CombinatoricsError::PermutationOverflow { n: n_u64, k: k_u64 }));
}
``` -/
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

axiom factorial_matches_checked_reference (n : Std.U8)
    (h_n : n.val < 41) :
    factorial_matches_checked_reference_spec n

axiom factorial_overflow_boundary_is_exact (n : Std.U8)
    (h_n : n.val < 80) :
    factorial_overflow_boundary_is_exact_spec n

axiom permutations_match_checked_reference (n k : Std.U8)
    (h_n : n.val < 81) (h_k : k.val < 81) :
    permutations_match_checked_reference_spec n k

end Benchmark.Cases.UseCombinatorics.Counting.Oracle
