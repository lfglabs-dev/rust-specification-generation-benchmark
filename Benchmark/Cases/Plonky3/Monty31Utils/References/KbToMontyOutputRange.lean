import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- For every `u32`, `to_monty` (computing `((x as u64) << 32) % P`) never panics and lands in
`[0, P)` for the KoalaBear prime. -/
def kb_to_monty_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  utils.to_monty inst x ⦃ r => r.val < 2130706433 ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
