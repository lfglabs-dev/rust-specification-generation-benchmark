import Benchmark.Cases.Varing.Packable.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

/-- Packing two `u64` values into a `u128` with `<u64 as Packable<u64, u128>>::pack` and unpacking the result never panics and returns the original pair. -/
def roundtrip_u64_spec (a b : Std.U64) : Prop :=
  (do
    let packed ← U64.Insts.VaringPackablePackableU64U128.pack a b
    U64.Insts.VaringPackablePackableU64U128.unpack packed)
  ⦃ r => a = r.1 ∧ b = r.2 ⦄

end Benchmark.Cases.Varing.Packable
