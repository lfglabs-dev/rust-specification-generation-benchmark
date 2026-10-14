import Benchmark.Cases.Dashu.Base.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/-- For every `u64`, dashu's `PowerOfTwo::is_power_of_two` never panics and
returns `true` exactly when the population count `x.count_ones()` is 1. -/
def u64_is_power_of_two_iff_one_bit_spec (x : Std.U64) : Prop :=
  (do
    let p ← U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
    let c ← core.num.U64.count_ones x
    ok (p, c)) ⦃ res => (res.1 = true ↔ res.2.val = 1) ⦄

end Benchmark.Cases.Dashu.Base
