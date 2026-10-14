import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- Modular subtraction undoes modular addition: `sub(add(a, b), b) = a` for canonical BabyBear
inputs, without panicking. -/
def bb_add_sub_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let s ← utils.add inst a b
    utils.sub inst s b) ⦃ r => r.val = a.val ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
