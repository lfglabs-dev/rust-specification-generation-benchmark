import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- Montgomery reduction `monty_reduce` never panics on inputs below `P * 2^32` and returns a
canonical BabyBear value (`< P`). -/
def bb_monty_reduce_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val < 2013265921 ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
