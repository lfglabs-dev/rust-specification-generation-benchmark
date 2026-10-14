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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
