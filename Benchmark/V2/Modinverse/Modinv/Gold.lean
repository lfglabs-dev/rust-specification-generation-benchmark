import Benchmark.V2.Prelude
import ModinverseModinv.Extraction

/-! Hidden gold specification for target `modinverse/modinv`.

API: `ModInverse::modinverse` for every primitive integer type (Lean:
`modinverse.<T>.Insts.ModinverseModInverse.modinverse`), the free function
`modinverse::modinverse` and `modinverse::egcd_u64`.

Contract (docs): `x = a.modinverse(m)` is the inverse of `a` modulo `m`, i.e.
`a * x ≡ 1 (mod m)`, in the canonical range `[0, |m|)`; `None` iff no inverse
exists (`gcd(a, m) ≠ 1`) or `m == 0`; `modinverse(_, 1) == Some(0)`; no panics
for any input (incl. `T::MIN`). `egcd_u64(a, b) = (g, x, y)` with `g = gcd(a, b)`,
`a*x + b*y = g` exactly, `0 ≤ x < b` when `b > 0` (Bezout coefficients are not
unique: which `x` in `[0, b)` is returned is not part of the contract), `y` in
`(-2^64, 1]`, never panics. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM modinverse RSGB

namespace RSGBGold.Modinverse.Modinv

def optU {ty : UScalarTy} : core.option.Option (UScalar ty) → Option Nat
  | .None => none
  | .Some x => some x.val

def optI {ty : IScalarTy} : core.option.Option (IScalar ty) → Option Int
  | .None => none
  | .Some x => some x.val

/-- An inverse of `a` modulo `M > 0` in canonical range. -/
def isInv (a : Int) (M : Nat) (x : Int) : Bool :=
  decide (0 ≤ x) && decide (x < M) && decide ((a * x - 1) % (M : Int) = 0)

/-- An inverse exists. -/
def hasInv (a : Int) (M : Nat) : Bool := M != 0 && Int.gcd a M == 1

/-- Full contract for one call (unsigned or signed, values as integers). -/
def invOk (a m : Int) (r : Option Int) : Bool :=
  match r with
  | none => !hasInv a m.natAbs
  | some x => m != 0 && isInv a m.natAbs x

/-- `Some` results are valid inverses in `[0, |m|)`. -/
def someValid (a m : Int) (r : Option Int) : Bool :=
  match r with
  | none => true
  | some x => m != 0 && isInv a m.natAbs x

/-- `None` exactly when no inverse exists. -/
def noneIff (a m : Int) (r : Option Int) : Bool := r.isNone == !hasInv a m.natAbs

def oU (r : Option Nat) : Option Int := r.map (fun n => (n : Int))

def egcdOk (a b : Nat) (r : Std.U64 × Std.I128 × Std.I128) : Bool :=
  let (g, x, y) := r
  g.val == Nat.gcd a b && (a : Int) * x.val + (b : Int) * y.val == (g.val : Int)

end RSGBGold.Modinverse.Modinv

namespace Benchmark.V2.Modinverse.Modinv.Gold
open RSGBGold.Modinverse.Modinv


/-! ### `u8` -/

def gold_u8_some_valid (a m : Std.U8) : Prop :=
  modinverse.U8.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_u8_none_iff (a m : Std.U8) : Prop :=
  modinverse.U8.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_u8_small (a m : Std.U8) : Prop :=
  modinverse.U8.Insts.ModinverseModInverse.modinverse (mkU .U8 (a.val % 64)) (mkU .U8 (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_u8_mod_one (a : Std.U8) : Prop :=
  modinverse.U8.Insts.ModinverseModInverse.modinverse a (mkU .U8 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.U8.Insts.ModinverseModInverse.modinverse a (mkU .U8 0) ⦃ r => optU r = none ⦄


/-! ### `u16` -/

def gold_u16_some_valid (a m : Std.U16) : Prop :=
  modinverse.U16.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_u16_none_iff (a m : Std.U16) : Prop :=
  modinverse.U16.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_u16_small (a m : Std.U8) : Prop :=
  modinverse.U16.Insts.ModinverseModInverse.modinverse (mkU .U16 (a.val % 64)) (mkU .U16 (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_u16_mod_one (a : Std.U16) : Prop :=
  modinverse.U16.Insts.ModinverseModInverse.modinverse a (mkU .U16 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.U16.Insts.ModinverseModInverse.modinverse a (mkU .U16 0) ⦃ r => optU r = none ⦄


/-! ### `u32` -/

def gold_u32_some_valid (a m : Std.U32) : Prop :=
  modinverse.U32.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_u32_none_iff (a m : Std.U32) : Prop :=
  modinverse.U32.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_u32_small (a m : Std.U8) : Prop :=
  modinverse.U32.Insts.ModinverseModInverse.modinverse (mkU .U32 (a.val % 64)) (mkU .U32 (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_u32_mod_one (a : Std.U32) : Prop :=
  modinverse.U32.Insts.ModinverseModInverse.modinverse a (mkU .U32 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.U32.Insts.ModinverseModInverse.modinverse a (mkU .U32 0) ⦃ r => optU r = none ⦄


/-! ### `u64` -/

def gold_u64_some_valid (a m : Std.U64) : Prop :=
  modinverse.U64.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_u64_none_iff (a m : Std.U64) : Prop :=
  modinverse.U64.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_u64_small (a m : Std.U8) : Prop :=
  modinverse.U64.Insts.ModinverseModInverse.modinverse (mkU .U64 (a.val % 64)) (mkU .U64 (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_u64_mod_one (a : Std.U64) : Prop :=
  modinverse.U64.Insts.ModinverseModInverse.modinverse a (mkU .U64 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.U64.Insts.ModinverseModInverse.modinverse a (mkU .U64 0) ⦃ r => optU r = none ⦄


/-! ### `u128` -/

def gold_u128_some_valid (a m : Std.U128) (g : Std.U8) : Prop :=
  g.val % 5 = 0 → modinverse.U128.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_u128_none_iff (a m : Std.U128) (g : Std.U8) : Prop :=
  g.val % 5 = 0 → modinverse.U128.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_u128_small (a m : Std.U8) : Prop :=
  modinverse.U128.Insts.ModinverseModInverse.modinverse (mkU .U128 (a.val % 64)) (mkU .U128 (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_u128_mod_one (a : Std.U128) : Prop :=
  modinverse.U128.Insts.ModinverseModInverse.modinverse a (mkU .U128 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.U128.Insts.ModinverseModInverse.modinverse a (mkU .U128 0) ⦃ r => optU r = none ⦄


/-! ### `usize` -/

def gold_usize_some_valid (a m : Std.Usize) : Prop :=
  modinverse.Usize.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (oU (optU r)) = true ⦄

def gold_usize_none_iff (a m : Std.Usize) : Prop :=
  modinverse.Usize.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (oU (optU r)) = true ⦄

/-- Small moduli (incl. `0`, `1`) and small values. -/
def gold_usize_small (a m : Std.U8) : Prop :=
  modinverse.Usize.Insts.ModinverseModInverse.modinverse (mkU .Usize (a.val % 64)) (mkU .Usize (m.val % 41)) ⦃ r =>
    invOk (a.val % 64) (m.val % 41) (oU (optU r)) = true ⦄

/-- Values reduced modulo the modulus behave like the residue (`a` may exceed `m`). -/
def gold_usize_mod_one (a : Std.Usize) : Prop :=
  modinverse.Usize.Insts.ModinverseModInverse.modinverse a (mkU .Usize 1) ⦃ r => optU r = some 0 ⦄ ∧
  modinverse.Usize.Insts.ModinverseModInverse.modinverse a (mkU .Usize 0) ⦃ r => optU r = none ⦄


/-! ### `i8` -/

def gold_i8_some_valid (a m : Std.I8) : Prop :=
  modinverse.I8.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_i8_none_iff (a m : Std.I8) : Prop :=
  modinverse.I8.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_i8_small (a m : Std.U8) : Prop :=
  modinverse.I8.Insts.ModinverseModInverse.modinverse (mkI .I8 ((a.val : Int) - 128)) (mkI .I8 ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_i8_min (a : Std.I8) : Prop :=
  modinverse.I8.Insts.ModinverseModInverse.modinverse a (mkI .I8 (-128)) ⦃ r => invOk a.val (-128) (optI r) = true ⦄ ∧
  modinverse.I8.Insts.ModinverseModInverse.modinverse (mkI .I8 (-128)) a ⦃ r => invOk (-128) a.val (optI r) = true ⦄

def gold_i8_mod_one (a : Std.I8) : Prop :=
  modinverse.I8.Insts.ModinverseModInverse.modinverse a (mkI .I8 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I8.Insts.ModinverseModInverse.modinverse a (mkI .I8 (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I8.Insts.ModinverseModInverse.modinverse a (mkI .I8 0) ⦃ r => optI r = none ⦄


/-! ### `i16` -/

def gold_i16_some_valid (a m : Std.I16) : Prop :=
  modinverse.I16.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_i16_none_iff (a m : Std.I16) : Prop :=
  modinverse.I16.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_i16_small (a m : Std.U8) : Prop :=
  modinverse.I16.Insts.ModinverseModInverse.modinverse (mkI .I16 ((a.val : Int) - 128)) (mkI .I16 ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_i16_min (a : Std.I16) : Prop :=
  modinverse.I16.Insts.ModinverseModInverse.modinverse a (mkI .I16 (-32768)) ⦃ r => invOk a.val (-32768) (optI r) = true ⦄ ∧
  modinverse.I16.Insts.ModinverseModInverse.modinverse (mkI .I16 (-32768)) a ⦃ r => invOk (-32768) a.val (optI r) = true ⦄

def gold_i16_mod_one (a : Std.I16) : Prop :=
  modinverse.I16.Insts.ModinverseModInverse.modinverse a (mkI .I16 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I16.Insts.ModinverseModInverse.modinverse a (mkI .I16 (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I16.Insts.ModinverseModInverse.modinverse a (mkI .I16 0) ⦃ r => optI r = none ⦄


/-! ### `i32` -/

def gold_i32_some_valid (a m : Std.I32) : Prop :=
  modinverse.I32.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_i32_none_iff (a m : Std.I32) : Prop :=
  modinverse.I32.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_i32_small (a m : Std.U8) : Prop :=
  modinverse.I32.Insts.ModinverseModInverse.modinverse (mkI .I32 ((a.val : Int) - 128)) (mkI .I32 ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_i32_min (a : Std.I32) : Prop :=
  modinverse.I32.Insts.ModinverseModInverse.modinverse a (mkI .I32 (-2147483648)) ⦃ r => invOk a.val (-2147483648) (optI r) = true ⦄ ∧
  modinverse.I32.Insts.ModinverseModInverse.modinverse (mkI .I32 (-2147483648)) a ⦃ r => invOk (-2147483648) a.val (optI r) = true ⦄

def gold_i32_mod_one (a : Std.I32) : Prop :=
  modinverse.I32.Insts.ModinverseModInverse.modinverse a (mkI .I32 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I32.Insts.ModinverseModInverse.modinverse a (mkI .I32 (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I32.Insts.ModinverseModInverse.modinverse a (mkI .I32 0) ⦃ r => optI r = none ⦄


/-! ### `i64` -/

def gold_i64_some_valid (a m : Std.I64) : Prop :=
  modinverse.I64.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_i64_none_iff (a m : Std.I64) : Prop :=
  modinverse.I64.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_i64_small (a m : Std.U8) : Prop :=
  modinverse.I64.Insts.ModinverseModInverse.modinverse (mkI .I64 ((a.val : Int) - 128)) (mkI .I64 ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_i64_min (a : Std.I64) : Prop :=
  modinverse.I64.Insts.ModinverseModInverse.modinverse a (mkI .I64 (-9223372036854775808)) ⦃ r => invOk a.val (-9223372036854775808) (optI r) = true ⦄ ∧
  modinverse.I64.Insts.ModinverseModInverse.modinverse (mkI .I64 (-9223372036854775808)) a ⦃ r => invOk (-9223372036854775808) a.val (optI r) = true ⦄

def gold_i64_mod_one (a : Std.I64) : Prop :=
  modinverse.I64.Insts.ModinverseModInverse.modinverse a (mkI .I64 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I64.Insts.ModinverseModInverse.modinverse a (mkI .I64 (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I64.Insts.ModinverseModInverse.modinverse a (mkI .I64 0) ⦃ r => optI r = none ⦄


/-! ### `i128` -/

def gold_i128_some_valid (a m : Std.I128) (g : Std.U8) : Prop :=
  g.val % 5 = 0 → modinverse.I128.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_i128_none_iff (a m : Std.I128) (g : Std.U8) : Prop :=
  g.val % 5 = 0 → modinverse.I128.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_i128_small (a m : Std.U8) : Prop :=
  modinverse.I128.Insts.ModinverseModInverse.modinverse (mkI .I128 ((a.val : Int) - 128)) (mkI .I128 ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_i128_min (a : Std.I128) (g : Std.U8) : Prop :=
  g.val % 8 = 0 → modinverse.I128.Insts.ModinverseModInverse.modinverse a (mkI .I128 (-170141183460469231731687303715884105728)) ⦃ r => invOk a.val (-170141183460469231731687303715884105728) (optI r) = true ⦄ ∧
  modinverse.I128.Insts.ModinverseModInverse.modinverse (mkI .I128 (-170141183460469231731687303715884105728)) a ⦃ r => invOk (-170141183460469231731687303715884105728) a.val (optI r) = true ⦄

def gold_i128_mod_one (a : Std.I128) : Prop :=
  modinverse.I128.Insts.ModinverseModInverse.modinverse a (mkI .I128 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I128.Insts.ModinverseModInverse.modinverse a (mkI .I128 (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.I128.Insts.ModinverseModInverse.modinverse a (mkI .I128 0) ⦃ r => optI r = none ⦄


/-! ### `isize` -/

def gold_isize_some_valid (a m : Std.Isize) : Prop :=
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a m ⦃ r => someValid a.val m.val (optI r) = true ⦄

def gold_isize_none_iff (a m : Std.Isize) : Prop :=
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a m ⦃ r => noneIff a.val m.val (optI r) = true ⦄

/-- Small (also negative) moduli incl. `0`, `±1`, negative values. -/
def gold_isize_small (a m : Std.U8) : Prop :=
  modinverse.Isize.Insts.ModinverseModInverse.modinverse (mkI .Isize ((a.val : Int) - 128)) (mkI .Isize ((m.val % 41 : Nat) - 20 : Int)) ⦃ r =>
    invOk ((a.val : Int) - 128) ((m.val % 41 : Nat) - 20 : Int) (optI r) = true ⦄

/-- `T::MIN` as modulus or as value: no panic, correct result. -/
def gold_isize_min (a : Std.Isize) : Prop :=
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a (mkI .Isize (-9223372036854775808)) ⦃ r => invOk a.val (-9223372036854775808) (optI r) = true ⦄ ∧
  modinverse.Isize.Insts.ModinverseModInverse.modinverse (mkI .Isize (-9223372036854775808)) a ⦃ r => invOk (-9223372036854775808) a.val (optI r) = true ⦄

def gold_isize_mod_one (a : Std.Isize) : Prop :=
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a (mkI .Isize 1) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a (mkI .Isize (-1)) ⦃ r => optI r = some 0 ⦄ ∧
  modinverse.Isize.Insts.ModinverseModInverse.modinverse a (mkI .Isize 0) ⦃ r => optI r = none ⦄


/-! ### free function -/

def gold_free_fn (a m : Std.U32) (b c : Std.I16) : Prop :=
  modinverse.modinverse U32.Insts.ModinverseModInverse a m =
    U32.Insts.ModinverseModInverse.modinverse a m ∧
  modinverse.modinverse I16.Insts.ModinverseModInverse b c =
    I16.Insts.ModinverseModInverse.modinverse b c

/-! ### `egcd_u64` -/

def gold_egcd_gcd (a b : Std.U64) : Prop :=
  egcd_u64 a b ⦃ r => r.1.val = Nat.gcd a.val b.val ⦄

def gold_egcd_bezout (a b : Std.U64) : Prop :=
  egcd_u64 a b ⦃ r => egcdOk a.val b.val r = true ⦄

def gold_egcd_x_range (a b : Std.U64) : Prop :=
  0 < b.val → egcd_u64 a b ⦃ r => 0 ≤ r.2.1.val ∧ r.2.1.val < b.val ⦄

def gold_egcd_y_range (a b : Std.U64) : Prop :=
  egcd_u64 a b ⦃ r => -(2^64 : Int) < r.2.2.val ∧ r.2.2.val ≤ 1 ⦄

/-- Small inputs (many common divisors, `0`, `1`). -/
def gold_egcd_small (a b : Std.U8) : Prop :=
  egcd_u64 (mkU .U64 (a.val % 50)) (mkU .U64 (b.val % 50)) ⦃ r =>
    egcdOk (a.val % 50) (b.val % 50) r = true ∧
    (0 < b.val % 50 → 0 ≤ r.2.1.val ∧ r.2.1.val < (b.val % 50 : Nat)) ∧
    -(2^64 : Int) < r.2.2.val ∧ r.2.2.val ≤ 1 ⦄

/-- Multiples of a common factor (large gcds). -/
def gold_egcd_common (a b : Std.U32) (k : Std.U8) : Prop :=
  egcd_u64 (mkU .U64 (a.val * (k.val + 1))) (mkU .U64 (b.val * (k.val + 1))) ⦃ r =>
    egcdOk (a.val * (k.val + 1)) (b.val * (k.val + 1)) r = true ∧
    (0 < b.val → 0 ≤ r.2.1.val ∧ r.2.1.val < (b.val * (k.val + 1) : Nat)) ∧
    -(2^64 : Int) < r.2.2.val ∧ r.2.2.val ≤ 1 ⦄

/-! Differential-testing probes. -/

def diff_u8 (a m : Std.U8) := modinverse.U8.Insts.ModinverseModInverse.modinverse a m
def diff_u8_small (a m : Std.U8) := modinverse.U8.Insts.ModinverseModInverse.modinverse (mkU .U8 (a.val % 64)) (mkU .U8 (m.val % 41))
def diff_u16 (a m : Std.U16) := modinverse.U16.Insts.ModinverseModInverse.modinverse a m
def diff_u16_small (a m : Std.U8) := modinverse.U16.Insts.ModinverseModInverse.modinverse (mkU .U16 (a.val % 64)) (mkU .U16 (m.val % 41))
def diff_u32 (a m : Std.U32) := modinverse.U32.Insts.ModinverseModInverse.modinverse a m
def diff_u32_small (a m : Std.U8) := modinverse.U32.Insts.ModinverseModInverse.modinverse (mkU .U32 (a.val % 64)) (mkU .U32 (m.val % 41))
def diff_u64 (a m : Std.U64) := modinverse.U64.Insts.ModinverseModInverse.modinverse a m
def diff_u64_small (a m : Std.U8) := modinverse.U64.Insts.ModinverseModInverse.modinverse (mkU .U64 (a.val % 64)) (mkU .U64 (m.val % 41))
def diff_u128 (a m : Std.U128) := modinverse.U128.Insts.ModinverseModInverse.modinverse a m
def diff_u128_small (a m : Std.U8) := modinverse.U128.Insts.ModinverseModInverse.modinverse (mkU .U128 (a.val % 64)) (mkU .U128 (m.val % 41))
def diff_usize (a m : Std.Usize) := modinverse.Usize.Insts.ModinverseModInverse.modinverse a m
def diff_usize_small (a m : Std.U8) := modinverse.Usize.Insts.ModinverseModInverse.modinverse (mkU .Usize (a.val % 64)) (mkU .Usize (m.val % 41))
def diff_i8 (a m : Std.I8) := modinverse.I8.Insts.ModinverseModInverse.modinverse a m
def diff_i8_small (a m : Std.U8) := modinverse.I8.Insts.ModinverseModInverse.modinverse (mkI .I8 ((a.val : Int) - 128)) (mkI .I8 ((m.val % 41 : Nat) - 20 : Int))
def diff_i16 (a m : Std.I16) := modinverse.I16.Insts.ModinverseModInverse.modinverse a m
def diff_i16_small (a m : Std.U8) := modinverse.I16.Insts.ModinverseModInverse.modinverse (mkI .I16 ((a.val : Int) - 128)) (mkI .I16 ((m.val % 41 : Nat) - 20 : Int))
def diff_i32 (a m : Std.I32) := modinverse.I32.Insts.ModinverseModInverse.modinverse a m
def diff_i32_small (a m : Std.U8) := modinverse.I32.Insts.ModinverseModInverse.modinverse (mkI .I32 ((a.val : Int) - 128)) (mkI .I32 ((m.val % 41 : Nat) - 20 : Int))
def diff_i64 (a m : Std.I64) := modinverse.I64.Insts.ModinverseModInverse.modinverse a m
def diff_i64_small (a m : Std.U8) := modinverse.I64.Insts.ModinverseModInverse.modinverse (mkI .I64 ((a.val : Int) - 128)) (mkI .I64 ((m.val % 41 : Nat) - 20 : Int))
def diff_i128 (a m : Std.I128) := modinverse.I128.Insts.ModinverseModInverse.modinverse a m
def diff_i128_small (a m : Std.U8) := modinverse.I128.Insts.ModinverseModInverse.modinverse (mkI .I128 ((a.val : Int) - 128)) (mkI .I128 ((m.val % 41 : Nat) - 20 : Int))
def diff_isize (a m : Std.Isize) := modinverse.Isize.Insts.ModinverseModInverse.modinverse a m
def diff_isize_small (a m : Std.U8) := modinverse.Isize.Insts.ModinverseModInverse.modinverse (mkI .Isize ((a.val : Int) - 128)) (mkI .Isize ((m.val % 41 : Nat) - 20 : Int))
def diff_free (a m : Std.U32) := modinverse.modinverse U32.Insts.ModinverseModInverse a m
def diff_egcd (a b : Std.U64) := egcd_u64 a b
def diff_egcd_small (a b : Std.U8) := egcd_u64 (mkU .U64 (a.val % 50)) (mkU .U64 (b.val % 50))
def diff_egcd_common (a b : Std.U32) (k : Std.U8) := egcd_u64 (mkU .U64 (a.val * (k.val + 1))) (mkU .U64 (b.val * (k.val + 1)))

end Benchmark.V2.Modinverse.Modinv.Gold
