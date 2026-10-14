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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
