import Benchmark.Cases.Varing.Packable.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

/-- Packing an `i16` and an `i64` into a `u128` in either order (zigzag-encoding both halves) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions. -/
def mix_roundtrip_i16_i64_spec (a : Std.I16) (b : Std.I64) : Prop :=
  (do
    let packed ← I16.Insts.VaringPackablePackableI64U128.pack a b
    let r1 ← I16.Insts.VaringPackablePackableI64U128.unpack packed
    let packed' ← I64.Insts.VaringPackablePackableI16U128.pack b a
    let r2 ← I64.Insts.VaringPackablePackableI16U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

end Benchmark.Cases.Varing.Packable
