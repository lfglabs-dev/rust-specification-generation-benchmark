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
  (do
    let ma ← utils.to_monty inst a
    let mb ← utils.to_monty inst b
    let product ← UScalar.cast .U64 ma * UScalar.cast .U64 mb
    let ab ← UScalar.cast .U64 a * UScalar.cast .U64 b
    let ab_mod ← ab % 2130706433#u64
    let expected ← utils.to_monty inst (UScalar.cast .U32 ab_mod)
    let reduced ← utils.monty_reduce inst product
    ok (reduced, expected)) ⦃ p => p.1.val = p.2.val ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
