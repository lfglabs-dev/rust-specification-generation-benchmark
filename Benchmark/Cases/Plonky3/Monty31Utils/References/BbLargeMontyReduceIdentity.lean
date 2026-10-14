import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- `large_monty_reduce(x) * 2^32 ≡ x (mod P)` on its whole domain `[0, 2 * P * 2^32)` (BabyBear),
without panicking. -/
def bb_large_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val * 2^32 % 2013265921 = x.val % 2013265921 ⦄

/-! ## 128-bit Montgomery reduction -/

end Benchmark.Cases.Plonky3.Monty31Utils
