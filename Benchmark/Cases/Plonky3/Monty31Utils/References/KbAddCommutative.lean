import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- Modular addition `add` (checked `u32` sum followed by a conditional subtraction of `P` via
`overflowing_sub`) never panics on canonical KoalaBear inputs and is commutative. -/
def kb_add_commutative_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let ab ← utils.add inst a b
    let ba ← utils.add inst b a
    ok (ab, ba)) ⦃ p => p.1.val = p.2.val ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
