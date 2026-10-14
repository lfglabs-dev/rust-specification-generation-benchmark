import Benchmark.Cases.Varing.Packable.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing
open Benchmark.Cases.Varing.Packable

namespace Benchmark.Cases.Varing.Packable.Oracle

/-- PBT `packable::builtin::fuzzy_roundtrip_u64` (src/packable/builtin.rs:120-124,
`@self_packable` arm, instance `64 => 128`):
`let packed = a.pack(&b); let (a2, b2) = <u64 as Packable<u64, _>>::unpack(packed);
a == a2 && b == b2`. -/
def roundtrip_u64_spec (a b : Std.U64) : Prop :=
  (do
    let packed ← U64.Insts.VaringPackablePackableU64U128.pack a b
    U64.Insts.VaringPackablePackableU64U128.unpack packed)
  ⦃ r => a = r.1 ∧ b = r.2 ⦄

/-- PBT `packable::builtin::fuzzy_roundtrip_i64` (src/packable/builtin.rs:126-130,
`@self_packable` arm, instance `64 => 128`):
`let packed = a.pack(&b); let (a2, b2) = <i64 as Packable<i64, _>>::unpack(packed);
a == a2 && b == b2`. -/
def roundtrip_i64_spec (a b : Std.I64) : Prop :=
  (do
    let packed ← I64.Insts.VaringPackablePackableI64U128.pack a b
    I64.Insts.VaringPackablePackableI64U128.unpack packed)
  ⦃ r => a = r.1 ∧ b = r.2 ⦄

/-- PBT `packable::builtin::fuzzy_roundtrip_i32_u32` (src/packable/builtin.rs:138-142,
`@self_packable` arm, instance `32 => 64`):
`let packed = a.pack(&b); let (a2, b2) = <i32 as Packable<u32, _>>::unpack(packed);
a == a2 && b == b2`. -/
def roundtrip_i32_u32_spec (a : Std.I32) (b : Std.U32) : Prop :=
  (do
    let packed ← I32.Insts.VaringPackablePackableU32U64.pack a b
    I32.Insts.VaringPackablePackableU32U64.unpack packed)
  ⦃ r => a = r.1 ∧ b = r.2 ⦄

/-- PBT `packable::builtin::fuzzy_mix_roundtrip_u32_u64` (src/packable/builtin.rs:204-214,
`@exchange` arm, instance `(32, 64) => 128`):
`let packed = a.pack(&b); let (a2, b2) = <u32 as Packable<u64, _>>::unpack(packed);
let cond1 = a == a2 && b == b2; let packed = b.pack(&a);
let (a2, b2) = <u64 as Packable<u32, _>>::unpack(packed); let cond2 = a == b2 && b == a2;
cond1 && cond2`. -/
def mix_roundtrip_u32_u64_spec (a : Std.U32) (b : Std.U64) : Prop :=
  (do
    let packed ← U32.Insts.VaringPackablePackableU64U128.pack a b
    let r1 ← U32.Insts.VaringPackablePackableU64U128.unpack packed
    let packed' ← U64.Insts.VaringPackablePackableU32U128.pack b a
    let r2 ← U64.Insts.VaringPackablePackableU32U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

/-- PBT `packable::builtin::fuzzy_mix_roundtrip_i16_i64` (src/packable/builtin.rs:216-225,
`@exchange` arm, instance `(16, 64) => 128`):
`let packed = a.pack(&b); let (a2, b2) = <i16 as Packable<i64, _>>::unpack(packed);
let cond1 = a == a2 && b == b2; let packed = b.pack(&a);
let (a2, b2) = <i64 as Packable<i16, _>>::unpack(packed); let cond2 = a == b2 && b == a2;
cond1 && cond2`. -/
def mix_roundtrip_i16_i64_spec (a : Std.I16) (b : Std.I64) : Prop :=
  (do
    let packed ← I16.Insts.VaringPackablePackableI64U128.pack a b
    let r1 ← I16.Insts.VaringPackablePackableI64U128.unpack packed
    let packed' ← I64.Insts.VaringPackablePackableI16U128.pack b a
    let r2 ← I64.Insts.VaringPackablePackableI16U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

/-- PBT `packable::builtin::fuzzy_mix_roundtrip_u16_i32` (src/packable/builtin.rs:227-236,
`@exchange` arm, instance `(16, 32) => 64`):
`let packed = a.pack(&b); let (a2, b2) = <u16 as Packable<i32, _>>::unpack(packed);
let cond1 = a == a2 && b == b2; let packed = b.pack(&a);
let (a2, b2) = <i32 as Packable<u16, _>>::unpack(packed); let cond2 = a == b2 && b == a2;
cond1 && cond2`. -/
def mix_roundtrip_u16_i32_spec (a : Std.U16) (b : Std.I32) : Prop :=
  (do
    let packed ← U16.Insts.VaringPackablePackableI32U64.pack a b
    let r1 ← U16.Insts.VaringPackablePackableI32U64.unpack packed
    let packed' ← I32.Insts.VaringPackablePackableU16U64.pack b a
    let r2 ← I32.Insts.VaringPackablePackableU16U64.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

/-- PBT `packable::builtin::fuzzy_mix_roundtrip_i8_u64` (src/packable/builtin.rs:238-247,
`@exchange` arm, instance `(8, 64) => 128`):
`let packed = a.pack(&b); let (a2, b2) = <i8 as Packable<u64, _>>::unpack(packed);
let cond1 = a == a2 && b == b2; let packed = b.pack(&a);
let (a2, b2) = <u64 as Packable<i8, _>>::unpack(packed); let cond2 = a == b2 && b == a2;
cond1 && cond2`. -/
def mix_roundtrip_i8_u64_spec (a : Std.I8) (b : Std.U64) : Prop :=
  (do
    let packed ← I8.Insts.VaringPackablePackableU64U128.pack a b
    let r1 ← I8.Insts.VaringPackablePackableU64U128.unpack packed
    let packed' ← U64.Insts.VaringPackablePackableI8U128.pack b a
    let r2 ← U64.Insts.VaringPackablePackableI8U128.unpack packed'
    ok (r1, r2))
  ⦃ r => (a = r.1.1 ∧ b = r.1.2) ∧ (a = r.2.2 ∧ b = r.2.1) ⦄

axiom mix_roundtrip_i16_i64 (a : Std.I16) (b : Std.I64) :
    mix_roundtrip_i16_i64_spec a b

axiom mix_roundtrip_i8_u64 (a : Std.I8) (b : Std.U64) :
    mix_roundtrip_i8_u64_spec a b

axiom mix_roundtrip_u32_u64 (a : Std.U32) (b : Std.U64) :
    mix_roundtrip_u32_u64_spec a b

axiom roundtrip_u64 (a : Std.U64) (b : Std.U64) :
    roundtrip_u64_spec a b

end Benchmark.Cases.Varing.Packable.Oracle
