import Benchmark.V2.Prelude
import IntegerSqrtIsqrt.Extraction

/-! Hidden gold specification for target `integer_sqrt/isqrt`.

API: `IntegerSquareRoot::{integer_sqrt, integer_sqrt_checked}` for
`u8, i8, u32, i32, u64, i64, u128`. In Lean, `integer_sqrt_checked` is
`<Ty>.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x` and `integer_sqrt`
is the trait default `IntegerSquareRoot.integer_sqrt.default <Ty>.Insts.Integer_sqrtIntegerSquareRoot x`.

Contract (docs + README): the result is the integer square root, i.e. the largest
`r ≥ 0` with `r² ≤ x` (floor of the real square root); `integer_sqrt_checked`
returns `None` exactly for negative inputs, `integer_sqrt` panics on negative
input (`expect`) and otherwise returns the same value. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM integer_sqrt RSGB

namespace RSGBGold.IntegerSqrt.Isqrt

/-- Floor square root characterisation on integers. -/
def isRoot (x r : Int) : Bool := 0 ≤ r && r * r ≤ x && x < (r + 1) * (r + 1)

def optVal {α} (f : α → Int) : core.option.Option α → Option Int
  | core.option.Option.None => none
  | core.option.Option.Some r => some (f r)

/-- `checked` returns `Some r` with `r` the floor square root of `x`. -/
def okRoot (x : Int) : Option Int → Bool
  | some r => isRoot x r
  | none => false

-- checked / unchecked per type
def cU8 (x : Std.U8) := U8.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sU8 (x : Std.U8) := IntegerSquareRoot.integer_sqrt.default U8.Insts.Integer_sqrtIntegerSquareRoot x
def cI8 (x : Std.I8) := I8.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sI8 (x : Std.I8) := IntegerSquareRoot.integer_sqrt.default I8.Insts.Integer_sqrtIntegerSquareRoot x
def cU32 (x : Std.U32) := U32.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sU32 (x : Std.U32) := IntegerSquareRoot.integer_sqrt.default U32.Insts.Integer_sqrtIntegerSquareRoot x
def cI32 (x : Std.I32) := I32.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sI32 (x : Std.I32) := IntegerSquareRoot.integer_sqrt.default I32.Insts.Integer_sqrtIntegerSquareRoot x
def cU64 (x : Std.U64) := U64.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sU64 (x : Std.U64) := IntegerSquareRoot.integer_sqrt.default U64.Insts.Integer_sqrtIntegerSquareRoot x
def cI64 (x : Std.I64) := I64.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sI64 (x : Std.I64) := IntegerSquareRoot.integer_sqrt.default I64.Insts.Integer_sqrtIntegerSquareRoot x
def cU128 (x : Std.U128) := U128.Insts.Integer_sqrtIntegerSquareRoot.integer_sqrt_checked x
def sU128 (x : Std.U128) := IntegerSquareRoot.integer_sqrt.default U128.Insts.Integer_sqrtIntegerSquareRoot x

/-- Exhaustive check over all `u8` values. -/
def allU8 : Bool :=
  (List.range 256).all fun n =>
    let x := mkU .U8 n
    match cU8 x, sU8 x with
    | .ok o, .ok r => okRoot n (optVal (·.val) o) && o == some r
    | _, _ => false

/-- Exhaustive check over all `i8` values. -/
def allI8 : Bool :=
  (List.range 256).all fun n =>
    let v : Int := (n : Int) - 128
    let x := mkI .I8 v
    match cI8 x with
    | .ok o =>
      if v < 0 then o == none && sI8 x == fail .panic
      else okRoot v (optVal (·.val) o) && sI8 x == (match o with
        | some r => .ok r
        | none => .fail .panic)
    | _ => false

/-- Values near the top of a signed range: `max - k`. -/
def nearMaxI32 (k : Std.U16) : Std.I32 := mkI .I32 (2^31 - 1 - 8 * (k.val : Int))
def nearMaxI64 (k : Std.U16) : Std.I64 := mkI .I64 (2^63 - 1 - (k.val : Int))
def nearMaxU64 (k : Std.U16) : Std.U64 := mkU .U64 (2^64 - 1 - k.val)

end RSGBGold.IntegerSqrt.Isqrt

namespace Benchmark.V2.IntegerSqrt.Isqrt.Gold
open RSGBGold.IntegerSqrt.Isqrt

/-! ### Exhaustive small types -/

/-- Every `u8`: `checked` is `Some (floor √x)` and `integer_sqrt` agrees. -/
def gold_u8_exhaustive : Prop := allU8 = true

/-- Every `i8`: `None` / panic exactly on negatives, floor root otherwise. -/
def gold_i8_exhaustive : Prop := allI8 = true

/-! ### u32 -/

def gold_u32_checked (x : Std.U32) : Prop :=
  cU32 x ⦃ o => okRoot x.val (optVal (·.val) o) = true ⦄

def gold_u32_sqrt (x : Std.U32) : Prop :=
  sU32 x ⦃ r => isRoot x.val r.val = true ⦄

/-- Perfect squares and their predecessors/successors. -/
def gold_u32_squares (k : Std.U16) : Prop :=
  sU32 (mkU .U32 (k.val * k.val)) ⦃ r => r.val = k.val ⦄ ∧
  (0 < k.val → sU32 (mkU .U32 (k.val * k.val - 1)) ⦃ r => r.val + 1 = k.val ⦄)

/-! ### i32 -/

def gold_i32_checked (x : Std.I32) : Prop :=
  if x.val < 0 then cI32 x = ok core.option.Option.None
  else cI32 x ⦃ o => okRoot x.val (optVal (·.val) o) = true ⦄

def gold_i32_sqrt (x : Std.I32) : Prop :=
  if x.val < 0 then sI32 x = fail .panic
  else sI32 x ⦃ r => isRoot x.val r.val = true ⦄

def gold_i32_squares (k : Std.U16) : Prop :=
  k.val ≤ 46340 →
    sI32 (mkI .I32 (k.val * k.val)) ⦃ r => r.val = k.val ⦄ ∧
    (0 < k.val → sI32 (mkI .I32 (k.val * k.val - 1)) ⦃ r => r.val + 1 = k.val ⦄)

/-- Inputs right below `i32::MAX` (where `(r+1)²` no longer fits in `i32`). -/
def gold_i32_near_max (k : Std.U16) : Prop :=
  sI32 (nearMaxI32 k) ⦃ r => isRoot (nearMaxI32 k).val r.val = true ⦄

/-! ### u64 -/

def gold_u64_checked (x : Std.U64) : Prop :=
  cU64 x ⦃ o => okRoot x.val (optVal (·.val) o) = true ⦄

def gold_u64_sqrt (x : Std.U64) : Prop :=
  sU64 x ⦃ r => isRoot x.val r.val = true ⦄

def gold_u64_squares (k : Std.U32) : Prop :=
  sU64 (mkU .U64 (k.val * k.val)) ⦃ r => r.val = k.val ⦄ ∧
  (0 < k.val → sU64 (mkU .U64 (k.val * k.val - 1)) ⦃ r => r.val + 1 = k.val ⦄)

def gold_u64_near_max (k : Std.U16) : Prop :=
  sU64 (nearMaxU64 k) ⦃ r => isRoot (nearMaxU64 k).val r.val = true ⦄

/-! ### i64 -/

def gold_i64_checked (x : Std.I64) : Prop :=
  if x.val < 0 then cI64 x = ok core.option.Option.None
  else cI64 x ⦃ o => okRoot x.val (optVal (·.val) o) = true ⦄

def gold_i64_sqrt (x : Std.I64) : Prop :=
  if x.val < 0 then sI64 x = fail .panic
  else sI64 x ⦃ r => isRoot x.val r.val = true ⦄

def gold_i64_squares (k : Std.U32) : Prop :=
  k.val ≤ 3037000499 →
    sI64 (mkI .I64 (k.val * k.val)) ⦃ r => r.val = k.val ⦄ ∧
    (0 < k.val → sI64 (mkI .I64 (k.val * k.val - 1)) ⦃ r => r.val + 1 = k.val ⦄)

def gold_i64_near_max (k : Std.U16) : Prop :=
  sI64 (nearMaxI64 k) ⦃ r => isRoot (nearMaxI64 k).val r.val = true ⦄

/-! ### u128 -/

def gold_u128_checked (x : Std.U128) : Prop :=
  cU128 x ⦃ o => okRoot x.val (optVal (·.val) o) = true ⦄

def gold_u128_sqrt (x : Std.U128) : Prop :=
  sU128 x ⦃ r => isRoot x.val r.val = true ⦄

def gold_u128_squares (k : Std.U64) : Prop :=
  sU128 (mkU .U128 (k.val * k.val)) ⦃ r => r.val = k.val ⦄ ∧
  (0 < k.val → sU128 (mkU .U128 (k.val * k.val - 1)) ⦃ r => r.val + 1 = k.val ⦄)

/-! Differential-testing probes. -/

def diff_u8 (x : Std.U8) := cU8 x
def diff_u8_sqrt (x : Std.U8) := sU8 x
def diff_i8 (x : Std.I8) := cI8 x
def diff_i8_sqrt (x : Std.I8) := sI8 x
def diff_u32 (x : Std.U32) := cU32 x
def diff_u32_sqrt (x : Std.U32) := sU32 x
def diff_i32 (x : Std.I32) := cI32 x
def diff_i32_sqrt (x : Std.I32) := sI32 x
def diff_i32_top (k : Std.U16) := cI32 (nearMaxI32 k)
def diff_u64 (x : Std.U64) := cU64 x
def diff_u64_sqrt (x : Std.U64) := sU64 x
def diff_u64_sq (k : Std.U32) := cU64 (mkU .U64 (k.val * k.val))
def diff_i64 (x : Std.I64) := cI64 x
def diff_i64_sqrt (x : Std.I64) := sI64 x
def diff_u128 (x : Std.U128) := cU128 x
def diff_u128_sqrt (x : Std.U128) := sU128 x
def diff_u128_sq (k : Std.U64) := cU128 (mkU .U128 (k.val * k.val))

end Benchmark.V2.IntegerSqrt.Isqrt.Gold
