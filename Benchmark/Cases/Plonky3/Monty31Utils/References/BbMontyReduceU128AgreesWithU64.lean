import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- On `[0, P * 2^32)` the 128-bit reduction `monty_reduce_u128` agrees with the 64-bit
`monty_reduce` (BabyBear), and neither panics. -/
def bb_monty_reduce_u128_agrees_with_u64_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  (do
    let wide ← utils.monty_reduce_u128 inst (UScalar.cast .U128 x)
    let narrow ← utils.monty_reduce inst x
    ok (wide, narrow)) ⦃ p => p.1.val = p.2.val ⦄

/-! ## Montgomery multiplication -/

end Benchmark.Cases.Plonky3.Monty31Utils
