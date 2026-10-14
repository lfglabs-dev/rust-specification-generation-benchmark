import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- On the common input range `[0, P * 2^32)` the wide-range Montgomery reduction
`large_monty_reduce` agrees with `monty_reduce` (KoalaBear), and neither panics. -/
def kb_large_agrees_with_standard_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
