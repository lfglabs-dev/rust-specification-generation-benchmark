import Benchmark.V2.Prelude
import LilliputIntValue.Extraction

/-! Hidden gold specification for target `lilliput/int_value`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM lilliput_core RSGB


namespace Benchmark.V2.Lilliput.IntValue.Gold

open value.int.signed value.int.unsigned value.int

/-! ## Reference model -/

/-- Zig-zag encoding of an integer: `0, -1, 1, -2, 2, … ↦ 0, 1, 2, 3, 4, …`. -/
def zz (v : Int) : Nat := if 0 ≤ v then (2 * v).toNat else (-2 * v - 1).toNat

/-- Zig-zag decoding. -/
def unzz (z : Nat) : Int := if z % 2 = 0 then (z / 2 : Nat) else -(((z + 1) / 2 : Nat) : Int)

/-- The mathematical value of a signed integer value. -/
def sint : SignedIntValue → Int
  | .I8 x => x.val | .I16 x => x.val | .I32 x => x.val | .I64 x => x.val

/-- The mathematical value of an unsigned integer value. -/
def uint : UnsignedIntValue → Nat
  | .U8 x => x.val | .U16 x => x.val | .U32 x => x.val | .U64 x => x.val

/-- Width index of a variant (0 = 8 bit … 3 = 64 bit). -/
def swidth : SignedIntValue → Nat
  | .I8 _ => 0 | .I16 _ => 1 | .I32 _ => 2 | .I64 _ => 3

def uwidth : UnsignedIntValue → Nat
  | .U8 _ => 0 | .U16 _ => 1 | .U32 _ => 2 | .U64 _ => 3

/-- A signed value of width `w % 4` holding `x` truncated to that width. -/
def sval (w : Std.U8) (x : Std.I64) : SignedIntValue :=
  if w.val % 4 = 0 then .I8 (mkI .I8 x.val)
  else if w.val % 4 = 1 then .I16 (mkI .I16 x.val)
  else if w.val % 4 = 2 then .I32 (mkI .I32 x.val)
  else .I64 x

/-- An unsigned value of width `w % 4` holding `x` truncated to that width. -/
def uval (w : Std.U8) (x : Std.U64) : UnsignedIntValue :=
  if w.val % 4 = 0 then .U8 (mkU .U8 x.val)
  else if w.val % 4 = 1 then .U16 (mkU .U16 x.val)
  else if w.val % 4 = 2 then .U32 (mkU .U32 x.val)
  else .U64 x

def ordOf {α} [LT α] [DecidableRel (α := α) (· < ·)] [DecidableEq α] (a b : α) : core.cmp.Ordering :=
  if a < b then .Less else if a = b then .Equal else .Greater

/-! ## Scalar zig-zag coding -/

def gold_zz_i8 (x : Std.I8) : Prop :=
  I8.Insts.Lilliput_coreNumZigzagToZigZagU8.to_zig_zag x ⦃ z => z.val = zz x.val ⦄
def gold_zz_i16 (x : Std.I16) : Prop :=
  I16.Insts.Lilliput_coreNumZigzagToZigZagU16.to_zig_zag x ⦃ z => z.val = zz x.val ⦄
def gold_zz_i32 (x : Std.I32) : Prop :=
  I32.Insts.Lilliput_coreNumZigzagToZigZagU32.to_zig_zag x ⦃ z => z.val = zz x.val ⦄
def gold_zz_i64 (x : Std.I64) : Prop :=
  I64.Insts.Lilliput_coreNumZigzagToZigZagU64.to_zig_zag x ⦃ z => z.val = zz x.val ⦄

def gold_unzz_i8 (z : Std.U8) : Prop :=
  I8.Insts.Lilliput_coreNumZigzagFromZigZagU8.from_zig_zag z ⦃ x => x.val = unzz z.val ⦄
def gold_unzz_i16 (z : Std.U16) : Prop :=
  I16.Insts.Lilliput_coreNumZigzagFromZigZagU16.from_zig_zag z ⦃ x => x.val = unzz z.val ⦄
def gold_unzz_i32 (z : Std.U32) : Prop :=
  I32.Insts.Lilliput_coreNumZigzagFromZigZagU32.from_zig_zag z ⦃ x => x.val = unzz z.val ⦄
def gold_unzz_i64 (z : Std.U64) : Prop :=
  I64.Insts.Lilliput_coreNumZigzagFromZigZagU64.from_zig_zag z ⦃ x => x.val = unzz z.val ⦄

/-- Round trips (both directions) at every width. -/
def gold_zz_roundtrip (a : Std.I8) (b : Std.I16) (c : Std.I32) (d : Std.I64) : Prop :=
  (do let z ← I8.Insts.Lilliput_coreNumZigzagToZigZagU8.to_zig_zag a
      I8.Insts.Lilliput_coreNumZigzagFromZigZagU8.from_zig_zag z) = ok a ∧
  (do let z ← I16.Insts.Lilliput_coreNumZigzagToZigZagU16.to_zig_zag b
      I16.Insts.Lilliput_coreNumZigzagFromZigZagU16.from_zig_zag z) = ok b ∧
  (do let z ← I32.Insts.Lilliput_coreNumZigzagToZigZagU32.to_zig_zag c
      I32.Insts.Lilliput_coreNumZigzagFromZigZagU32.from_zig_zag z) = ok c ∧
  (do let z ← I64.Insts.Lilliput_coreNumZigzagToZigZagU64.to_zig_zag d
      I64.Insts.Lilliput_coreNumZigzagFromZigZagU64.from_zig_zag z) = ok d

def gold_unzz_roundtrip (a : Std.U8) (b : Std.U16) (c : Std.U32) (d : Std.U64) : Prop :=
  (do let x ← I8.Insts.Lilliput_coreNumZigzagFromZigZagU8.from_zig_zag a
      I8.Insts.Lilliput_coreNumZigzagToZigZagU8.to_zig_zag x) = ok a ∧
  (do let x ← I16.Insts.Lilliput_coreNumZigzagFromZigZagU16.from_zig_zag b
      I16.Insts.Lilliput_coreNumZigzagToZigZagU16.to_zig_zag x) = ok b ∧
  (do let x ← I32.Insts.Lilliput_coreNumZigzagFromZigZagU32.from_zig_zag c
      I32.Insts.Lilliput_coreNumZigzagToZigZagU32.to_zig_zag x) = ok c ∧
  (do let x ← I64.Insts.Lilliput_coreNumZigzagFromZigZagU64.from_zig_zag d
      I64.Insts.Lilliput_coreNumZigzagToZigZagU64.to_zig_zag x) = ok d

/-! ## Zig-zag coding of `SignedIntValue` / `UnsignedIntValue` -/

/-- `to_zig_zag` keeps the width and zig-zag encodes the value. -/
def gold_value_zz (w : Std.U8) (x : Std.I64) : Prop :=
  SignedIntValue.Insts.Lilliput_coreNumZigzagToZigZagUnsignedIntValue.to_zig_zag (sval w x)
    ⦃ u => uwidth u = swidth (sval w x) ∧ uint u = zz (sint (sval w x)) ⦄

/-- `from_zig_zag` keeps the width and zig-zag decodes the value. -/
def gold_value_unzz (w : Std.U8) (z : Std.U64) : Prop :=
  SignedIntValue.Insts.Lilliput_coreNumZigzagFromZigZagUnsignedIntValue.from_zig_zag (uval w z)
    ⦃ s => swidth s = uwidth (uval w z) ∧ sint s = unzz (uint (uval w z)) ⦄

def gold_value_zz_roundtrip (w : Std.U8) (x : Std.I64) (z : Std.U64) : Prop :=
  (do let u ← SignedIntValue.Insts.Lilliput_coreNumZigzagToZigZagUnsignedIntValue.to_zig_zag (sval w x)
      SignedIntValue.Insts.Lilliput_coreNumZigzagFromZigZagUnsignedIntValue.from_zig_zag u) = ok (sval w x) ∧
  (do let s ← SignedIntValue.Insts.Lilliput_coreNumZigzagFromZigZagUnsignedIntValue.from_zig_zag (uval w z)
      SignedIntValue.Insts.Lilliput_coreNumZigzagToZigZagUnsignedIntValue.to_zig_zag s) = ok (uval w z)

/-! ## Equality and ordering (by numeric value, independent of width) -/

def gold_signed_eq (w1 w2 : Std.U8) (x y : Std.I64) (same : Bool) : Prop :=
  let a := sval w1 x
  let b := sval w2 (if same then x else y)
  SignedIntValue.Insts.CoreCmpPartialEqSignedIntValue.eq a b = ok (decide (sint a = sint b))

def gold_signed_cmp (w1 w2 : Std.U8) (x y : Std.I64) (same : Bool) : Prop :=
  let a := sval w1 x
  let b := sval w2 (if same then x else y)
  SignedIntValue.Insts.CoreCmpOrd.cmp a b = ok (ordOf (sint a) (sint b)) ∧
  SignedIntValue.Insts.CoreCmpPartialOrdSignedIntValue.partial_cmp a b = ok (some (ordOf (sint a) (sint b)))

def gold_unsigned_eq (w1 w2 : Std.U8) (x y : Std.U64) (same : Bool) : Prop :=
  let a := uval w1 x
  let b := uval w2 (if same then x else y)
  UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq a b = ok (decide (uint a = uint b))

def gold_unsigned_cmp (w1 w2 : Std.U8) (x y : Std.U64) (same : Bool) : Prop :=
  let a := uval w1 x
  let b := uval w2 (if same then x else y)
  UnsignedIntValue.Insts.CoreCmpOrd.cmp a b = ok (ordOf (uint a) (uint b)) ∧
  UnsignedIntValue.Insts.CoreCmpPartialOrdUnsignedIntValue.partial_cmp a b = ok (some (ordOf (uint a) (uint b)))

/-- The same small value stored at any two widths compares equal (upstream eq/ord tests). -/
def gold_widening_equal (w1 w2 : Std.U8) (x : Std.I8) (y : Std.U8) : Prop :=
  SignedIntValue.Insts.CoreCmpPartialEqSignedIntValue.eq (sval w1 (mkI .I64 x.val)) (sval w2 (mkI .I64 x.val)) = ok true ∧
  SignedIntValue.Insts.CoreCmpOrd.cmp (sval w1 (mkI .I64 x.val)) (sval w2 (mkI .I64 x.val)) = ok .Equal ∧
  UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq (uval w1 (mkU .U64 y.val)) (uval w2 (mkU .U64 y.val)) = ok true ∧
  UnsignedIntValue.Insts.CoreCmpOrd.cmp (uval w1 (mkU .U64 y.val)) (uval w2 (mkU .U64 y.val)) = ok .Equal

/-! ## Constructors, defaults, `IntValue` -/

def gold_signed_from (a : Std.I8) (b : Std.I16) (c : Std.I32) (d : Std.I64) : Prop :=
  SignedIntValue.Insts.CoreConvertFromI8.from a = ok (.I8 a) ∧
  SignedIntValue.Insts.CoreConvertFromI16.from b = ok (.I16 b) ∧
  SignedIntValue.Insts.CoreConvertFromI32.from c = ok (.I32 c) ∧
  SignedIntValue.Insts.CoreConvertFromI64.from d = ok (.I64 d)

def gold_unsigned_from (a : Std.U8) (b : Std.U16) (c : Std.U32) (d : Std.U64) : Prop :=
  UnsignedIntValue.Insts.CoreConvertFromU8.from a = ok (.U8 a) ∧
  UnsignedIntValue.Insts.CoreConvertFromU16.from b = ok (.U16 b) ∧
  UnsignedIntValue.Insts.CoreConvertFromU32.from c = ok (.U32 c) ∧
  UnsignedIntValue.Insts.CoreConvertFromU64.from d = ok (.U64 d)

def gold_int_from_signed (a : Std.I8) (b : Std.I16) (c : Std.I32) (d : Std.I64) : Prop :=
  IntValue.Insts.CoreConvertFromI8.from a = ok (.Signed (.I8 a)) ∧
  IntValue.Insts.CoreConvertFromI16.from b = ok (.Signed (.I16 b)) ∧
  IntValue.Insts.CoreConvertFromI32.from c = ok (.Signed (.I32 c)) ∧
  IntValue.Insts.CoreConvertFromI64.from d = ok (.Signed (.I64 d))

def gold_int_from_unsigned (a : Std.U8) (b : Std.U16) (c : Std.U32) (d : Std.U64) (e : Std.Usize) : Prop :=
  IntValue.Insts.CoreConvertFromU8.from a = ok (.Unsigned (.U8 a)) ∧
  IntValue.Insts.CoreConvertFromU16.from b = ok (.Unsigned (.U16 b)) ∧
  IntValue.Insts.CoreConvertFromU32.from c = ok (.Unsigned (.U32 c)) ∧
  IntValue.Insts.CoreConvertFromU64.from d = ok (.Unsigned (.U64 d)) ∧
  IntValue.Insts.CoreConvertFromUsize.from e ⦃ v => v = .Unsigned (.U64 (mkU .U64 e.val)) ⦄

/-- `is_signed` tells the two families apart. -/
def gold_is_signed (w : Std.U8) (x : Std.I64) (y : Std.U64) : Prop :=
  IntValue.is_signed (.Signed (sval w x)) = ok true ∧
  IntValue.is_signed (.Unsigned (uval w y)) = ok false

/-- The mathematical value of an `IntValue`. -/
def ival : IntValue → Int
  | .Signed v => sint v | .Unsigned v => (uint v : Int)

/-- Defaults are zero (the storage width / signedness of the zero is not promised). -/
def gold_defaults (_u : Std.U8) : Prop :=
  SignedIntValue.Insts.CoreDefaultDefault.default ⦃ v => sint v = 0 ⦄ ∧
  UnsignedIntValue.Insts.CoreDefaultDefault.default ⦃ v => uint v = 0 ⦄ ∧
  IntValue.Insts.CoreDefaultDefault.default ⦃ v => ival v = 0 ⦄

/-! Differential-testing probes. -/

def diff_zz8 (x : Std.I8) := I8.Insts.Lilliput_coreNumZigzagToZigZagU8.to_zig_zag x
def diff_zz16 (x : Std.I16) := I16.Insts.Lilliput_coreNumZigzagToZigZagU16.to_zig_zag x
def diff_zz32 (x : Std.I32) := I32.Insts.Lilliput_coreNumZigzagToZigZagU32.to_zig_zag x
def diff_zz64 (x : Std.I64) := I64.Insts.Lilliput_coreNumZigzagToZigZagU64.to_zig_zag x
def diff_unzz8 (x : Std.U8) := I8.Insts.Lilliput_coreNumZigzagFromZigZagU8.from_zig_zag x
def diff_unzz16 (x : Std.U16) := I16.Insts.Lilliput_coreNumZigzagFromZigZagU16.from_zig_zag x
def diff_unzz32 (x : Std.U32) := I32.Insts.Lilliput_coreNumZigzagFromZigZagU32.from_zig_zag x
def diff_unzz64 (x : Std.U64) := I64.Insts.Lilliput_coreNumZigzagFromZigZagU64.from_zig_zag x
def diff_vzz (w : Std.U8) (x : Std.I64) :=
  SignedIntValue.Insts.Lilliput_coreNumZigzagToZigZagUnsignedIntValue.to_zig_zag (sval w x)
def diff_vunzz (w : Std.U8) (z : Std.U64) :=
  SignedIntValue.Insts.Lilliput_coreNumZigzagFromZigZagUnsignedIntValue.from_zig_zag (uval w z)
def diff_seq (w1 w2 : Std.U8) (x y : Std.I64) (same : Bool) :=
  SignedIntValue.Insts.CoreCmpPartialEqSignedIntValue.eq (sval w1 x) (sval w2 (if same then x else y))
def diff_scmp (w1 w2 : Std.U8) (x y : Std.I64) (same : Bool) :=
  SignedIntValue.Insts.CoreCmpPartialOrdSignedIntValue.partial_cmp (sval w1 x) (sval w2 (if same then x else y))
def diff_ueq (w1 w2 : Std.U8) (x y : Std.U64) (same : Bool) :=
  UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq (uval w1 x) (uval w2 (if same then x else y))
def diff_ucmp (w1 w2 : Std.U8) (x y : Std.U64) (same : Bool) :=
  UnsignedIntValue.Insts.CoreCmpPartialOrdUnsignedIntValue.partial_cmp (uval w1 x) (uval w2 (if same then x else y))
def diff_usize (e : Std.Usize) := IntValue.Insts.CoreConvertFromUsize.from e
def diff_is_signed (b : Bool) (w : Std.U8) (x : Std.I64) (y : Std.U64) :=
  IntValue.is_signed (if b then .Signed (sval w x) else .Unsigned (uval w y))
def diff_defaults (_u : Std.U8) :=
  (SignedIntValue.Insts.CoreDefaultDefault.default, UnsignedIntValue.Insts.CoreDefaultDefault.default,
   IntValue.Insts.CoreDefaultDefault.default)

end Benchmark.V2.Lilliput.IntValue.Gold
