import Benchmark.V2.Prelude
import StaticFilezSlice.Extraction

/-! Hidden gold specification for target `static_filez/slice`.

`pack_in_u64(offset, length)` stores a slice descriptor in one `u64`: the
offset in the high 32 bits and the length in the low 32 bits;
`unpack_from_u64` splits a `u64` back into `(offset, length)`.

Implementation note (recorded discrepancy): `pack_in_u64` does not mask the
length, so a `length ≥ 2^32` (possible with a 64-bit `usize`) silently ORs its
high bits into the offset field, and an `offset ≥ 2^32` is truncated. The gold
specification does not fix the value in the `length ≥ 2^32` case (only that the
call does not panic and keeps the low 32 bits of the length).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM static_filez RSGB

namespace Benchmark.V2.StaticFilez.Slice.Gold

/-- 32-bit offset / length packed as `offset * 2^32 + length`. -/
def gold_pack_exact (o l : Std.U32) : Prop :=
  slice.pack_in_u64 (mkU .Usize o.val) (mkU .Usize l.val) ⦃ r => r.val = o.val * 2^32 + l.val ⦄

/-- Offsets are truncated to their low 32 bits (32-bit length). -/
def gold_pack_offset_truncated (o : Std.Usize) (l : Std.U32) : Prop :=
  slice.pack_in_u64 o (mkU .Usize l.val) ⦃ r => r.val = (o.val % 2^32) * 2^32 + l.val ⦄

/-- `pack_in_u64` never panics and the low 32 bits always hold the length's low 32 bits. -/
def gold_pack_total_low_bits (o l : Std.Usize) : Prop :=
  slice.pack_in_u64 o l ⦃ r => r.val % 2^32 = l.val % 2^32 ⦄

/-- `unpack_from_u64` never panics and splits into (high 32 bits, low 32 bits). -/
def gold_unpack_exact (n : Std.U64) : Prop :=
  slice.unpack_from_u64 n ⦃ r => r.1.val = n.val / 2^32 ∧ r.2.val = n.val % 2^32 ⦄

/-- Both components of `unpack_from_u64` fit in 32 bits. -/
def gold_unpack_range (n : Std.U64) : Prop :=
  slice.unpack_from_u64 n ⦃ r => r.1.val < 2^32 ∧ r.2.val < 2^32 ⦄

/-- `unpack ∘ pack = id` for 32-bit offsets and lengths (upstream property). -/
def gold_roundtrip (o l : Std.U32) : Prop :=
  (do
    let p ← slice.pack_in_u64 (mkU .Usize o.val) (mkU .Usize l.val)
    slice.unpack_from_u64 p) ⦃ r => r.1.val = o.val ∧ r.2.val = l.val ⦄

/-- `unpack ∘ pack` keeps the low 32 bits of the offset. -/
def gold_roundtrip_trunc (o : Std.Usize) (l : Std.U32) : Prop :=
  (do
    let p ← slice.pack_in_u64 o (mkU .Usize l.val)
    slice.unpack_from_u64 p) ⦃ r => r.1.val = o.val % 2^32 ∧ r.2.val = l.val ⦄

/-- `pack ∘ unpack = id` on all of `u64`: every packed value is a valid descriptor. -/
def gold_pack_unpack (n : Std.U64) : Prop :=
  (do
    let (o, l) ← slice.unpack_from_u64 n
    slice.pack_in_u64 o l) ⦃ r => r = n ⦄

/-! Differential-testing probes. -/

def diff_pack (o l : Std.Usize) := slice.pack_in_u64 o l
def diff_pack32 (o l : Std.U32) := slice.pack_in_u64 (mkU .Usize o.val) (mkU .Usize l.val)
def diff_unpack (n : Std.U64) := slice.unpack_from_u64 n

end Benchmark.V2.StaticFilez.Slice.Gold
