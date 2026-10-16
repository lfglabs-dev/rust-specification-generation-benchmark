import Benchmark.V2.Prelude
import VaringPackable.Extraction

/-! Hidden gold specification for target `varing/packable`.

API: the builtin-integer `Packable<Rhs, Packed>` impls exercised by the v1 case
(`pack(&self, &rhs) -> Packed`, `unpack(Packed) -> (Self, Rhs)`), for
`u64/u64 → u128`, `i64/i64 → u128`, `u32/i32 ↔ i32/u32 → u64`,
`u32/u64 ↔ u64/u32 → u128`, `i16/i64 ↔ i64/i16 → u128`,
`u16/i32 ↔ i32/u16 → u64`, `i8/u64 ↔ u64/i8 → u128`.

Reference model: signed values are ZigZag-encoded (`v ↦ 2v` / `-2v-1`, so that
small magnitudes give small packed values, "suitable for LEB128"), unsigned
values are kept as is, and the two codes are concatenated
`packed = lo + 2^w(lo) * hi` where the low field is `self` for same-type pairs,
the narrower operand for mixed widths, and the unsigned operand for
`i32/u32` (the exchanged impl `Y: Packable<X>` produces the same packed value
as `X: Packable<Y>`). `unpack` is total: it reads the low field and the next
`w(hi)` bits and ignores any bits above (truncating `as` casts).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM varing RSGB

namespace Benchmark.V2.Varing.Packable.Gold

/-- ZigZag code of an integer. -/
def zz (v : Int) : Nat := if 0 ≤ v then 2 * v.toNat else 2 * (-v).toNat - 1

/-- Inverse of `zz`. -/
def unzz (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -(((n + 1) / 2 : Nat) : Int)

/-! ## `u64: Packable<u64, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (u64 in the low 64 bits). -/
def gold_u64_u64_pack_exact (a : Std.U64) (b : Std.U64) : Prop :=
  U64.Insts.VaringPackablePackableU64U128.pack a b ⦃ p => p.val = a.val + 2^64 * b.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_u64_u64_unpack_exact (p : Std.U128) : Prop :=
  U64.Insts.VaringPackablePackableU64U128.unpack p ⦃ r => r.1.val = p.val % 2^64 ∧ r.2.val = p.val / 2^64 % 2^64 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u64_u64_roundtrip (a : Std.U64) (b : Std.U64) : Prop :=
  (do let p ← U64.Insts.VaringPackablePackableU64U128.pack a b; U64.Insts.VaringPackablePackableU64U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 128 bits. -/
def gold_u64_u64_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← U64.Insts.VaringPackablePackableU64U128.unpack p; U64.Insts.VaringPackablePackableU64U128.pack a b) ⦃ q => q.val = p.val % 2^128 ⦄

/-! ## `i64: Packable<i64, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (i64 in the low 64 bits). -/
def gold_i64_i64_pack_exact (a : Std.I64) (b : Std.I64) : Prop :=
  I64.Insts.VaringPackablePackableI64U128.pack a b ⦃ p => p.val = zz a.val + 2^64 * zz b.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_i64_i64_unpack_exact (p : Std.U128) : Prop :=
  I64.Insts.VaringPackablePackableI64U128.unpack p ⦃ r => r.1.val = unzz (p.val % 2^64) ∧ r.2.val = unzz (p.val / 2^64 % 2^64) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i64_i64_roundtrip (a : Std.I64) (b : Std.I64) : Prop :=
  (do let p ← I64.Insts.VaringPackablePackableI64U128.pack a b; I64.Insts.VaringPackablePackableI64U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 128 bits. -/
def gold_i64_i64_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← I64.Insts.VaringPackablePackableI64U128.unpack p; I64.Insts.VaringPackablePackableI64U128.pack a b) ⦃ q => q.val = p.val % 2^128 ⦄

/-! ## `u32: Packable<i32, u64>` -/

/-- `pack` is total and equals the concatenation of the codes (u32 in the low 32 bits). -/
def gold_u32_i32_pack_exact (a : Std.U32) (b : Std.I32) : Prop :=
  U32.Insts.VaringPackablePackableI32U64.pack a b ⦃ p => p.val = a.val + 2^32 * zz b.val ⦄

/-- `unpack` is total and decodes the low field and the next 32 bits (higher bits ignored). -/
def gold_u32_i32_unpack_exact (p : Std.U64) : Prop :=
  U32.Insts.VaringPackablePackableI32U64.unpack p ⦃ r => r.1.val = p.val % 2^32 ∧ r.2.val = unzz (p.val / 2^32 % 2^32) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u32_i32_roundtrip (a : Std.U32) (b : Std.I32) : Prop :=
  (do let p ← U32.Insts.VaringPackablePackableI32U64.pack a b; U32.Insts.VaringPackablePackableI32U64.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 64 bits. -/
def gold_u32_i32_pack_unpack (p : Std.U64) : Prop :=
  (do let (a, b) ← U32.Insts.VaringPackablePackableI32U64.unpack p; U32.Insts.VaringPackablePackableI32U64.pack a b) ⦃ q => q.val = p.val % 2^64 ⦄

/-- The exchanged impl packs to the same value and unpacks to the swapped pair. -/
def gold_u32_i32_exchange (a : Std.U32) (b : Std.I32) (p : Std.U64) : Prop :=
  U32.Insts.VaringPackablePackableI32U64.pack a b = I32.Insts.VaringPackablePackableU32U64.pack b a ∧
  ((fun r => (r.2, r.1)) <$> U32.Insts.VaringPackablePackableI32U64.unpack p) = I32.Insts.VaringPackablePackableU32U64.unpack p

/-! ## `i32: Packable<u32, u64>` -/

/-- `pack` is total and equals the concatenation of the codes (u32 in the low 32 bits). -/
def gold_i32_u32_pack_exact (a : Std.I32) (b : Std.U32) : Prop :=
  I32.Insts.VaringPackablePackableU32U64.pack a b ⦃ p => p.val = b.val + 2^32 * zz a.val ⦄

/-- `unpack` is total and decodes the low field and the next 32 bits (higher bits ignored). -/
def gold_i32_u32_unpack_exact (p : Std.U64) : Prop :=
  I32.Insts.VaringPackablePackableU32U64.unpack p ⦃ r => r.1.val = unzz (p.val / 2^32 % 2^32) ∧ r.2.val = p.val % 2^32 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i32_u32_roundtrip (a : Std.I32) (b : Std.U32) : Prop :=
  (do let p ← I32.Insts.VaringPackablePackableU32U64.pack a b; I32.Insts.VaringPackablePackableU32U64.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 64 bits. -/
def gold_i32_u32_pack_unpack (p : Std.U64) : Prop :=
  (do let (a, b) ← I32.Insts.VaringPackablePackableU32U64.unpack p; I32.Insts.VaringPackablePackableU32U64.pack a b) ⦃ q => q.val = p.val % 2^64 ⦄

/-! ## `u32: Packable<u64, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (u32 in the low 32 bits). -/
def gold_u32_u64_pack_exact (a : Std.U32) (b : Std.U64) : Prop :=
  U32.Insts.VaringPackablePackableU64U128.pack a b ⦃ p => p.val = a.val + 2^32 * b.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_u32_u64_unpack_exact (p : Std.U128) : Prop :=
  U32.Insts.VaringPackablePackableU64U128.unpack p ⦃ r => r.1.val = p.val % 2^32 ∧ r.2.val = p.val / 2^32 % 2^64 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u32_u64_roundtrip (a : Std.U32) (b : Std.U64) : Prop :=
  (do let p ← U32.Insts.VaringPackablePackableU64U128.pack a b; U32.Insts.VaringPackablePackableU64U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 96 bits. -/
def gold_u32_u64_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← U32.Insts.VaringPackablePackableU64U128.unpack p; U32.Insts.VaringPackablePackableU64U128.pack a b) ⦃ q => q.val = p.val % 2^96 ⦄

/-- The exchanged impl packs to the same value and unpacks to the swapped pair. -/
def gold_u32_u64_exchange (a : Std.U32) (b : Std.U64) (p : Std.U128) : Prop :=
  U32.Insts.VaringPackablePackableU64U128.pack a b = U64.Insts.VaringPackablePackableU32U128.pack b a ∧
  ((fun r => (r.2, r.1)) <$> U32.Insts.VaringPackablePackableU64U128.unpack p) = U64.Insts.VaringPackablePackableU32U128.unpack p

/-! ## `u64: Packable<u32, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (u32 in the low 32 bits). -/
def gold_u64_u32_pack_exact (a : Std.U64) (b : Std.U32) : Prop :=
  U64.Insts.VaringPackablePackableU32U128.pack a b ⦃ p => p.val = b.val + 2^32 * a.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_u64_u32_unpack_exact (p : Std.U128) : Prop :=
  U64.Insts.VaringPackablePackableU32U128.unpack p ⦃ r => r.1.val = p.val / 2^32 % 2^64 ∧ r.2.val = p.val % 2^32 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u64_u32_roundtrip (a : Std.U64) (b : Std.U32) : Prop :=
  (do let p ← U64.Insts.VaringPackablePackableU32U128.pack a b; U64.Insts.VaringPackablePackableU32U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 96 bits. -/
def gold_u64_u32_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← U64.Insts.VaringPackablePackableU32U128.unpack p; U64.Insts.VaringPackablePackableU32U128.pack a b) ⦃ q => q.val = p.val % 2^96 ⦄

/-! ## `i16: Packable<i64, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (i16 in the low 16 bits). -/
def gold_i16_i64_pack_exact (a : Std.I16) (b : Std.I64) : Prop :=
  I16.Insts.VaringPackablePackableI64U128.pack a b ⦃ p => p.val = zz a.val + 2^16 * zz b.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_i16_i64_unpack_exact (p : Std.U128) : Prop :=
  I16.Insts.VaringPackablePackableI64U128.unpack p ⦃ r => r.1.val = unzz (p.val % 2^16) ∧ r.2.val = unzz (p.val / 2^16 % 2^64) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i16_i64_roundtrip (a : Std.I16) (b : Std.I64) : Prop :=
  (do let p ← I16.Insts.VaringPackablePackableI64U128.pack a b; I16.Insts.VaringPackablePackableI64U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 80 bits. -/
def gold_i16_i64_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← I16.Insts.VaringPackablePackableI64U128.unpack p; I16.Insts.VaringPackablePackableI64U128.pack a b) ⦃ q => q.val = p.val % 2^80 ⦄

/-- The exchanged impl packs to the same value and unpacks to the swapped pair. -/
def gold_i16_i64_exchange (a : Std.I16) (b : Std.I64) (p : Std.U128) : Prop :=
  I16.Insts.VaringPackablePackableI64U128.pack a b = I64.Insts.VaringPackablePackableI16U128.pack b a ∧
  ((fun r => (r.2, r.1)) <$> I16.Insts.VaringPackablePackableI64U128.unpack p) = I64.Insts.VaringPackablePackableI16U128.unpack p

/-! ## `i64: Packable<i16, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (i16 in the low 16 bits). -/
def gold_i64_i16_pack_exact (a : Std.I64) (b : Std.I16) : Prop :=
  I64.Insts.VaringPackablePackableI16U128.pack a b ⦃ p => p.val = zz b.val + 2^16 * zz a.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_i64_i16_unpack_exact (p : Std.U128) : Prop :=
  I64.Insts.VaringPackablePackableI16U128.unpack p ⦃ r => r.1.val = unzz (p.val / 2^16 % 2^64) ∧ r.2.val = unzz (p.val % 2^16) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i64_i16_roundtrip (a : Std.I64) (b : Std.I16) : Prop :=
  (do let p ← I64.Insts.VaringPackablePackableI16U128.pack a b; I64.Insts.VaringPackablePackableI16U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 80 bits. -/
def gold_i64_i16_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← I64.Insts.VaringPackablePackableI16U128.unpack p; I64.Insts.VaringPackablePackableI16U128.pack a b) ⦃ q => q.val = p.val % 2^80 ⦄

/-! ## `u16: Packable<i32, u64>` -/

/-- `pack` is total and equals the concatenation of the codes (u16 in the low 16 bits). -/
def gold_u16_i32_pack_exact (a : Std.U16) (b : Std.I32) : Prop :=
  U16.Insts.VaringPackablePackableI32U64.pack a b ⦃ p => p.val = a.val + 2^16 * zz b.val ⦄

/-- `unpack` is total and decodes the low field and the next 32 bits (higher bits ignored). -/
def gold_u16_i32_unpack_exact (p : Std.U64) : Prop :=
  U16.Insts.VaringPackablePackableI32U64.unpack p ⦃ r => r.1.val = p.val % 2^16 ∧ r.2.val = unzz (p.val / 2^16 % 2^32) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u16_i32_roundtrip (a : Std.U16) (b : Std.I32) : Prop :=
  (do let p ← U16.Insts.VaringPackablePackableI32U64.pack a b; U16.Insts.VaringPackablePackableI32U64.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 48 bits. -/
def gold_u16_i32_pack_unpack (p : Std.U64) : Prop :=
  (do let (a, b) ← U16.Insts.VaringPackablePackableI32U64.unpack p; U16.Insts.VaringPackablePackableI32U64.pack a b) ⦃ q => q.val = p.val % 2^48 ⦄

/-- The exchanged impl packs to the same value and unpacks to the swapped pair. -/
def gold_u16_i32_exchange (a : Std.U16) (b : Std.I32) (p : Std.U64) : Prop :=
  U16.Insts.VaringPackablePackableI32U64.pack a b = I32.Insts.VaringPackablePackableU16U64.pack b a ∧
  ((fun r => (r.2, r.1)) <$> U16.Insts.VaringPackablePackableI32U64.unpack p) = I32.Insts.VaringPackablePackableU16U64.unpack p

/-! ## `i32: Packable<u16, u64>` -/

/-- `pack` is total and equals the concatenation of the codes (u16 in the low 16 bits). -/
def gold_i32_u16_pack_exact (a : Std.I32) (b : Std.U16) : Prop :=
  I32.Insts.VaringPackablePackableU16U64.pack a b ⦃ p => p.val = b.val + 2^16 * zz a.val ⦄

/-- `unpack` is total and decodes the low field and the next 32 bits (higher bits ignored). -/
def gold_i32_u16_unpack_exact (p : Std.U64) : Prop :=
  I32.Insts.VaringPackablePackableU16U64.unpack p ⦃ r => r.1.val = unzz (p.val / 2^16 % 2^32) ∧ r.2.val = p.val % 2^16 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i32_u16_roundtrip (a : Std.I32) (b : Std.U16) : Prop :=
  (do let p ← I32.Insts.VaringPackablePackableU16U64.pack a b; I32.Insts.VaringPackablePackableU16U64.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 48 bits. -/
def gold_i32_u16_pack_unpack (p : Std.U64) : Prop :=
  (do let (a, b) ← I32.Insts.VaringPackablePackableU16U64.unpack p; I32.Insts.VaringPackablePackableU16U64.pack a b) ⦃ q => q.val = p.val % 2^48 ⦄

/-! ## `i8: Packable<u64, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (i8 in the low 8 bits). -/
def gold_i8_u64_pack_exact (a : Std.I8) (b : Std.U64) : Prop :=
  I8.Insts.VaringPackablePackableU64U128.pack a b ⦃ p => p.val = zz a.val + 2^8 * b.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_i8_u64_unpack_exact (p : Std.U128) : Prop :=
  I8.Insts.VaringPackablePackableU64U128.unpack p ⦃ r => r.1.val = unzz (p.val % 2^8) ∧ r.2.val = p.val / 2^8 % 2^64 ⦄

/-- `unpack ∘ pack = id`. -/
def gold_i8_u64_roundtrip (a : Std.I8) (b : Std.U64) : Prop :=
  (do let p ← I8.Insts.VaringPackablePackableU64U128.pack a b; I8.Insts.VaringPackablePackableU64U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 72 bits. -/
def gold_i8_u64_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← I8.Insts.VaringPackablePackableU64U128.unpack p; I8.Insts.VaringPackablePackableU64U128.pack a b) ⦃ q => q.val = p.val % 2^72 ⦄

/-- The exchanged impl packs to the same value and unpacks to the swapped pair. -/
def gold_i8_u64_exchange (a : Std.I8) (b : Std.U64) (p : Std.U128) : Prop :=
  I8.Insts.VaringPackablePackableU64U128.pack a b = U64.Insts.VaringPackablePackableI8U128.pack b a ∧
  ((fun r => (r.2, r.1)) <$> I8.Insts.VaringPackablePackableU64U128.unpack p) = U64.Insts.VaringPackablePackableI8U128.unpack p

/-! ## `u64: Packable<i8, u128>` -/

/-- `pack` is total and equals the concatenation of the codes (i8 in the low 8 bits). -/
def gold_u64_i8_pack_exact (a : Std.U64) (b : Std.I8) : Prop :=
  U64.Insts.VaringPackablePackableI8U128.pack a b ⦃ p => p.val = zz b.val + 2^8 * a.val ⦄

/-- `unpack` is total and decodes the low field and the next 64 bits (higher bits ignored). -/
def gold_u64_i8_unpack_exact (p : Std.U128) : Prop :=
  U64.Insts.VaringPackablePackableI8U128.unpack p ⦃ r => r.1.val = p.val / 2^8 % 2^64 ∧ r.2.val = unzz (p.val % 2^8) ⦄

/-- `unpack ∘ pack = id`. -/
def gold_u64_i8_roundtrip (a : Std.U64) (b : Std.I8) : Prop :=
  (do let p ← U64.Insts.VaringPackablePackableI8U128.pack a b; U64.Insts.VaringPackablePackableI8U128.unpack p) ⦃ r => r = (a, b) ⦄

/-- `pack ∘ unpack` keeps exactly the low 72 bits. -/
def gold_u64_i8_pack_unpack (p : Std.U128) : Prop :=
  (do let (a, b) ← U64.Insts.VaringPackablePackableI8U128.unpack p; U64.Insts.VaringPackablePackableI8U128.pack a b) ⦃ q => q.val = p.val % 2^72 ⦄

/-! Differential-testing probes. -/

def diff_u64_u64_pack (a : Std.U64) (b : Std.U64) := U64.Insts.VaringPackablePackableU64U128.pack a b
def diff_u64_u64_unpack (p : Std.U128) := U64.Insts.VaringPackablePackableU64U128.unpack p
def diff_i64_i64_pack (a : Std.I64) (b : Std.I64) := I64.Insts.VaringPackablePackableI64U128.pack a b
def diff_i64_i64_unpack (p : Std.U128) := I64.Insts.VaringPackablePackableI64U128.unpack p
def diff_u32_i32_pack (a : Std.U32) (b : Std.I32) := U32.Insts.VaringPackablePackableI32U64.pack a b
def diff_u32_i32_unpack (p : Std.U64) := U32.Insts.VaringPackablePackableI32U64.unpack p
def diff_i32_u32_pack (a : Std.I32) (b : Std.U32) := I32.Insts.VaringPackablePackableU32U64.pack a b
def diff_i32_u32_unpack (p : Std.U64) := I32.Insts.VaringPackablePackableU32U64.unpack p
def diff_u32_u64_pack (a : Std.U32) (b : Std.U64) := U32.Insts.VaringPackablePackableU64U128.pack a b
def diff_u32_u64_unpack (p : Std.U128) := U32.Insts.VaringPackablePackableU64U128.unpack p
def diff_u64_u32_pack (a : Std.U64) (b : Std.U32) := U64.Insts.VaringPackablePackableU32U128.pack a b
def diff_u64_u32_unpack (p : Std.U128) := U64.Insts.VaringPackablePackableU32U128.unpack p
def diff_i16_i64_pack (a : Std.I16) (b : Std.I64) := I16.Insts.VaringPackablePackableI64U128.pack a b
def diff_i16_i64_unpack (p : Std.U128) := I16.Insts.VaringPackablePackableI64U128.unpack p
def diff_i64_i16_pack (a : Std.I64) (b : Std.I16) := I64.Insts.VaringPackablePackableI16U128.pack a b
def diff_i64_i16_unpack (p : Std.U128) := I64.Insts.VaringPackablePackableI16U128.unpack p
def diff_u16_i32_pack (a : Std.U16) (b : Std.I32) := U16.Insts.VaringPackablePackableI32U64.pack a b
def diff_u16_i32_unpack (p : Std.U64) := U16.Insts.VaringPackablePackableI32U64.unpack p
def diff_i32_u16_pack (a : Std.I32) (b : Std.U16) := I32.Insts.VaringPackablePackableU16U64.pack a b
def diff_i32_u16_unpack (p : Std.U64) := I32.Insts.VaringPackablePackableU16U64.unpack p
def diff_i8_u64_pack (a : Std.I8) (b : Std.U64) := I8.Insts.VaringPackablePackableU64U128.pack a b
def diff_i8_u64_unpack (p : Std.U128) := I8.Insts.VaringPackablePackableU64U128.unpack p
def diff_u64_i8_pack (a : Std.U64) (b : Std.I8) := U64.Insts.VaringPackablePackableI8U128.pack a b
def diff_u64_i8_unpack (p : Std.U128) := U64.Insts.VaringPackablePackableI8U128.unpack p

end Benchmark.V2.Varing.Packable.Gold
