import Benchmark.Cases.Varing.Packable.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

/-- Packing a `u32` and a `u64` into a `u128` in either order (`a.pack(&b)` and `b.pack(&a)`) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions. -/
def mix_roundtrip_u32_u64_spec (a : Std.U32) (b : Std.U64) : Prop :=
  (do
    let packed ← U32.Insts.VaringPackablePackableU64U128.pack a b
    let r1 ← U32.Insts.VaringPackablePackableU64U128.unpack packed
    let packed' ← U64.Insts.VaringPackablePackableU32U128.pack b a
    let r2 ← U64.Insts.VaringPackablePackableU32U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

end Benchmark.Cases.Varing.Packable
