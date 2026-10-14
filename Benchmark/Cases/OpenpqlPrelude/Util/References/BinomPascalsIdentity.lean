import Benchmark.Cases.OpenpqlPrelude.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- For every `1 ≤ r ≤ n ≤ 52`, the multiplicative binomial-coefficient routine `binom` never panics (on a 64-bit target) and satisfies Pascal's rule `binom(n, r) = binom(n - 1, r - 1) + binom(n - 1, r)`. -/
def binom_pascals_identity_spec (n r : Std.Usize) : Prop :=
  (do
    let lhs ← iterator.binomial.coefficient.binom n r
    let n1 ← n - 1#usize
    let r1 ← r - 1#usize
    let rhs1 ← iterator.binomial.coefficient.binom n1 r1
    let rhs2 ← iterator.binomial.coefficient.binom n1 r
    let rhs ← rhs1 + rhs2
    ok (lhs, rhs)) ⦃ p => p.1 = p.2 ⦄

end Benchmark.Cases.OpenpqlPrelude.Util
