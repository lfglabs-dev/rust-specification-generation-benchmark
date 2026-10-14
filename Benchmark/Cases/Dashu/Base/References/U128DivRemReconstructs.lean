import Benchmark.Cases.Dashu.Base.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/-- For `u128` operands with a nonzero divisor, dashu's `DivRem::div_rem` never
panics, and its quotient and remainder reconstruct the dividend with checked
`u128` arithmetic (`q * b + r == a`, no overflow) with `r < b`. -/
def u128_div_rem_reconstructs_spec (a b : Std.U128) : Prop :=
  (do
    let (q, r) ← U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem a b
    let qb ← q * b
    let recon ← qb + r
    ok (recon, r)) ⦃ res => res.1.val = a.val ∧ res.2.val < b.val ⦄

end Benchmark.Cases.Dashu.Base
