import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- Montgomery multiplication is correct: reducing the product of the Montgomery forms of `a` and `b`
gives the Montgomery form of `a * b mod P` (KoalaBear), and nothing panics. -/
def kb_monty_mul_correct_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
