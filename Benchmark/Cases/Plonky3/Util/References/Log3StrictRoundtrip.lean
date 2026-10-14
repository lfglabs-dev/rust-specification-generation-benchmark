import Benchmark.Cases.Plonky3.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_util

namespace Benchmark.Cases.Plonky3.Util

/-- `log3_strict_usize(3^k) = k` for every exponent `k < 25`: neither `3usize.pow(k)` nor the
table-driven strict base-3 logarithm (leading-zeros bucket lookup in `LOG2_TO_EXP`, verified
against `POWERS_OF_3`) panics, and the exponent is recovered. -/
def log3_strict_roundtrip_spec (k : Std.U32) : Prop :=
  (do
    let n ← core.num.Usize.pow 3#usize k
    log3_strict_usize n) ⦃ r => r.val = k.val ⦄

end Benchmark.Cases.Plonky3.Util
