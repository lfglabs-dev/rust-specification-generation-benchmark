import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- `large_monty_reduce` never panics on inputs below `2 * P * 2^32` and returns a canonical
KoalaBear value (`< P`). -/
def kb_large_monty_reduce_output_range_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val < 2130706433 ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
