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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Plonky3.Monty31Utils
