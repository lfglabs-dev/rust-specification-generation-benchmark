import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- Decoding a canonical BabyBear Montgomery-form value (`from_monty`, i.e. Montgomery reduction) and
re-encoding it with `to_monty` never panics and gives back the original value. -/
def bb_from_to_monty_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (m : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
