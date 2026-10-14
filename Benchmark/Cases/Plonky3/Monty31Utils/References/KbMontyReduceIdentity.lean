import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- The defining Montgomery identity: `monty_reduce(x) * 2^32 ≡ x (mod P)` for every input below
`P * 2^32` (KoalaBear), and the reduction never panics. -/
def kb_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
