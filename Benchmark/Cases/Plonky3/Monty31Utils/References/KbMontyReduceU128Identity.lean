import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/-- `monty_reduce_u128(x) * 2^32 ≡ x (mod P)` for every `x = hi * 2^64 + lo` (`hi: u32`, `lo: u64`),
KoalaBear parameters, without panicking. -/
def kb_monty_reduce_u128_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (lo : Std.U64) (hi : Std.U32) : Prop :=
  (do
    let hi_shifted ← UScalar.cast .U128 hi <<< 64#i32
    let x := hi_shifted ||| UScalar.cast .U128 lo
    let result ← utils.monty_reduce_u128 inst x
    ok (x, result)) ⦃ p => p.2.val * 2^32 % 2130706433 = p.1.val % 2130706433 ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
