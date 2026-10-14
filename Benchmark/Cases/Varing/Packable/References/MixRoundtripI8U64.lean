import Benchmark.Cases.Varing.Packable.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

/-- Packing an `i8` and a `u64` into a `u128` in either order (zigzag-encoding the `i8` into the low byte) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions. -/
def mix_roundtrip_i8_u64_spec (a : Std.I8) (b : Std.U64) : Prop :=
  (do
    let packed ← I8.Insts.VaringPackablePackableU64U128.pack a b
    let r1 ← I8.Insts.VaringPackablePackableU64U128.unpack packed
    let packed' ← U64.Insts.VaringPackablePackableI8U128.pack b a
    let r2 ← U64.Insts.VaringPackablePackableI8U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

end Benchmark.Cases.Varing.Packable
