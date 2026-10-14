import Benchmark.Cases.Dashu.Base.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/-- For `i64` operands with a nonzero divisor (excluding `i64::MIN / -1`),
dashu's `DivRemEuclid::div_rem_euclid` never panics, its result reconstructs
the dividend with wrapping `i64` arithmetic, its remainder lies in
`[0, |b|)`, and quotient and remainder agree with the Euclidean division
`div_euclid` / `rem_euclid`. -/
def i64_div_rem_euclid_matches_std_spec (a b : Std.I64) : Prop :=
  (do
    let (q, r) ← I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b
    let qb ← core.num.I64.wrapping_mul q b
    let recon ← core.num.I64.wrapping_add qb r
    ok (q, r, recon)) ⦃ res =>
      res.2.2 = a ∧
      (0 ≤ res.2.1.val ∧ res.2.1.val < |b.val|) ∧
      res.1.val = Int.ediv a.val b.val ∧
      res.2.1.val = Int.emod a.val b.val ⦄

end Benchmark.Cases.Dashu.Base
