import Benchmark.V2.Prelude
import UseCombinatoricsCounting.Extraction

/-! Hidden gold specification for target `use_combinatorics/counting`.

Model: `factorial n = Ok n!` when `n!` fits in `u128`, else
`Err(FactorialOverflow(n))`; `permutations n k = Err(KExceedsN{n,k})` when
`k > n`, else `Ok(n·(n-1)·…·(n-k+1))` when that fits in `u128`, else
`Err(PermutationOverflow{n,k})`.

Implementation discrepancy (recorded): the loop in `permutations` increments
`factor` after multiplying by `factor = n`, so for `n = u64::MAX` and `k ∈ {1, 2}`
(where the result still fits in `u128`) the `factor += 1` overflows and the
function panics in debug builds instead of returning `Ok(n)` / `Ok(n·(n-1))` as
documented. The gold spec accepts either outcome there (a fixed sibling
implementation is registered). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM use_combinatorics RSGB

/-! Data-valued helpers live outside the `Benchmark.` namespace so that the
test driver does not delta-expand their `match`es (which breaks instance
elaboration). -/
namespace RSGBGold.UseCombinatoricsCounting

/-- Observable encoding of a result: `(tag, a, b)` with
`Ok v ↦ (0, v, 0)`, `KExceedsN n k ↦ (1, n, k)`, `FactorialOverflow n ↦ (2, n, 0)`,
`PermutationOverflow n k ↦ (3, n, k)`, `CombinationOverflow n k ↦ (4, n, k)`. -/
def enc : core.result.Result Std.U128 error.CombinatoricsError → Nat × Nat × Nat
  | .Ok v => (0, v.val, 0)
  | .Err (.KExceedsN n k) => (1, n.val, k.val)
  | .Err (.FactorialOverflow n) => (2, n.val, 0)
  | .Err (.PermutationOverflow n k) => (3, n.val, k.val)
  | .Err (.CombinationOverflow n k) => (4, n.val, k.val)

def obs (r : RustM (core.result.Result Std.U128 error.CombinatoricsError)) : RustM (Nat × Nat × Nat) := do
  let x ← r
  ok (enc x)

def U64MAX : Nat := 2^64 - 1

/-- Mathematical model of `factorial` (for `n ≥ 40`, `n! ≥ 40! > 2^128`). -/
def factModel (n : Nat) : Nat × Nat × Nat :=
  if n < 40 then
    if Nat.factorial n < 2^128 then (0, Nat.factorial n, 0) else (2, n, 0)
  else (2, n, 0)

/-- Mathematical model of `permutations` (falling factorial `n^{(k)}`; for
`k ≥ 40 ≤ n`, `n^{(k)} ≥ k! > 2^128`). -/
def permModel (n k : Nat) : Nat × Nat × Nat :=
  if n < k then (1, n, k)
  else if k < 40 then
    if Nat.descFactorial n k < 2^128 then (0, Nat.descFactorial n k, 0) else (3, n, k)
  else (3, n, k)

/-- Acceptable outcomes of `permutations n k`: the model value; additionally, for
`n = u64::MAX`, `k ∈ {1, 2}` the implementation panics (debug overflow of the loop
counter `factor += 1` after the last factor) — a panic or the correct value are both
accepted there. -/
def permOk (n k : Nat) : RustM (Nat × Nat × Nat) → Bool
  | .ok v => v == permModel n k
  | .fail .panic => n == U64MAX && (k == 1 || k == 2)
  | _ => false

end RSGBGold.UseCombinatoricsCounting

namespace Benchmark.V2.UseCombinatorics.Counting.Gold
open RSGBGold.UseCombinatoricsCounting

/-! ## factorial -/

/-- Exact result of `factorial` for every `u64`. -/
def gold_factorial_exact (n : Std.U64) : Prop :=
  obs (counting.factorial n) = ok (factModel n.val)

/-- Same, densely on small inputs (around the overflow boundary 34/35). -/
def gold_factorial_exact_small (n : Std.U8) : Prop :=
  obs (counting.factorial (mkU .U64 n.val)) = ok (factModel n.val)

/-- Overflow boundary: `Ok` exactly for `n ≤ 34`; otherwise the error carries `n`. -/
def gold_factorial_boundary (n : Std.U8) : Prop :=
  (obs (counting.factorial (mkU .U64 n.val))) ⦃ r =>
    (r.1 = 0 ↔ n.val ≤ 34) ∧ (r.1 ≠ 0 → r = (2, n.val, 0)) ⦄

/-- Recurrence `(n+1)! = (n+1) · n!` whenever both succeed. -/
def gold_factorial_recurrence (n : Std.U8) : Prop :=
  (do
    let a ← obs (counting.factorial (mkU .U64 n.val))
    let b ← obs (counting.factorial (mkU .U64 (n.val + 1)))
    ok (a, b)) ⦃ (a, b) => a.1 = 0 → b.1 = 0 → b.2.1 = (n.val + 1) * a.2.1 ⦄

/-! ## permutations -/

/-- Exact result (including the panic cases) for arbitrary `u64` arguments. -/
def gold_perm_exact (n k : Std.U64) : Prop :=
  permOk n.val k.val (obs (counting.permutations n k)) = true

/-- Exact result, dense small domain. -/
def gold_perm_exact_small (n k : Std.U8) : Prop :=
  permOk n.val k.val (obs (counting.permutations (mkU .U64 n.val) (mkU .U64 k.val))) = true

/-- Exact result for large `n` and small `k`. -/
def gold_perm_exact_large_n (n : Std.U64) (k : Std.U8) : Prop :=
  permOk n.val (k.val % 40) (obs (counting.permutations n (mkU .U64 (k.val % 40)))) = true

/-- Exact result near `u64::MAX` (both arguments). -/
def gold_perm_exact_near_max (d e : Std.U8) : Prop :=
  let n := U64MAX - d.val % 4
  let k := if e.val < 128 then e.val % 6 else n - e.val % 6
  permOk n k (obs (counting.permutations (mkU .U64 n) (mkU .U64 k))) = true

/-- `permutations n 0 = Ok 1` for every `n` (including `u64::MAX`). -/
def gold_perm_zero (n : Std.U64) : Prop :=
  obs (counting.permutations n (mkU .U64 0)) = ok (0, 1, 0)

/-- `permutations n 1 = Ok n` for every `1 ≤ n < u64::MAX`. -/
def gold_perm_one (n : Std.U64) : Prop :=
  1 ≤ n.val → n.val < U64MAX → obs (counting.permutations n (mkU .U64 1)) = ok (0, n.val, 0)

/-- `k > n` is rejected with `KExceedsN { n, k }` (never panics). -/
def gold_perm_k_exceeds (n k : Std.U64) : Prop :=
  n.val < k.val → obs (counting.permutations n k) = ok (1, n.val, k.val)

/-- Never panics outside `n = u64::MAX, k ∈ {1,2}`; on overflow the error
carries `{n, k}`; a success value is never zero. -/
def gold_perm_shape (n k : Std.U64) : Prop :=
  ¬ (n.val = U64MAX ∧ (k.val = 1 ∨ k.val = 2)) →
    (obs (counting.permutations n k)) ⦃ r =>
      (r.1 = 0 ∧ 0 < r.2.1 ∧ r.2.2 = 0) ∨ r = (1, n.val, k.val) ∨ r = (3, n.val, k.val) ⦄

/-- `permutations n n = factorial n` (same value, or the corresponding overflow). -/
def gold_perm_full_is_factorial (n : Std.U8) : Prop :=
  (do
    let p ← obs (counting.permutations (mkU .U64 n.val) (mkU .U64 n.val))
    let f ← obs (counting.factorial (mkU .U64 n.val))
    ok (p, f)) ⦃ (p, f) =>
      (f.1 = 0 → p = f) ∧ (f.1 ≠ 0 → p = (3, n.val, n.val)) ⦄

/-- `P(n, k) · (n-k)! = n!` whenever all three succeed. -/
def gold_perm_factorial_identity (n k : Std.U8) : Prop :=
  k.val ≤ n.val →
  (do
    let p ← obs (counting.permutations (mkU .U64 n.val) (mkU .U64 k.val))
    let a ← obs (counting.factorial (mkU .U64 (n.val - k.val)))
    let b ← obs (counting.factorial (mkU .U64 n.val))
    ok (p, a, b)) ⦃ (p, a, b) =>
      p.1 = 0 → a.1 = 0 → b.1 = 0 → p.2.1 * a.2.1 = b.2.1 ⦄

/-- Recurrence `P(n, k+1) = (n-k) · P(n, k)` whenever both succeed. -/
def gold_perm_recurrence (n : Std.U64) (k : Std.U8) : Prop :=
  let k' := k.val % 40
  k' < n.val → n.val < U64MAX →
  (do
    let a ← obs (counting.permutations n (mkU .U64 k'))
    let b ← obs (counting.permutations n (mkU .U64 (k' + 1)))
    ok (a, b)) ⦃ (a, b) => a.1 = 0 → b.1 = 0 → b.2.1 = (n.val - k') * a.2.1 ⦄

/-! Differential-testing probes. -/

def diff_factorial (n : Std.U64) := obs (counting.factorial n)
def diff_factorial_small (n : Std.U8) := obs (counting.factorial (mkU .U64 (n.val % 64)))
def diff_perm (n k : Std.U64) := obs (counting.permutations n k)
def diff_perm_small (n k : Std.U8) :=
  obs (counting.permutations (mkU .U64 (n.val % 64)) (mkU .U64 (k.val % 64)))
def diff_perm_large_n (n : Std.U64) (k : Std.U8) :=
  obs (counting.permutations n (mkU .U64 (k.val % 40)))
def diff_perm_near_max (d e : Std.U8) :=
  obs (counting.permutations (mkU .U64 (U64MAX - d.val % 4)) (mkU .U64 (e.val % 6)))

end Benchmark.V2.UseCombinatorics.Counting.Gold
