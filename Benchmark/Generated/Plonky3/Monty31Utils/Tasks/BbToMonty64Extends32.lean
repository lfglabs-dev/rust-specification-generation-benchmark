import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- The 64-bit Montgomery conversion `to_monty_64` (computing in `u128`) agrees with the 32-bit
`to_monty` (computing in `u64`) on every `u32` input, for the BabyBear parameters. -/
def bb_to_monty_64_extends_32_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
