import Benchmark.V2.Prelude
import Benchmark.Exec.Runtime
import DashuBase.Extraction

/-! Hidden gold specification for target `dashu/base`.

API: the primitive-integer implementations of `dashu_base`'s ring traits
`DivRem::div_rem`, `DivRemAssign::div_rem_assign`, `RemEuclid::rem_euclid`,
`DivRemEuclid::div_rem_euclid` (all 12 primitive integer types) and of
`PowerOfTwo::{is_power_of_two, next_power_of_two}` (unsigned types).

Reference model: Lean's `Int.tdiv`/`Int.tmod` (truncated, Rust `/`/`%`) and
`Int.ediv`/`Int.emod` (Euclidean, `0 ≤ r < |b|`), `Nat` division for unsigned
types. Panics: division by zero, and for signed types `MIN / -1` (the quotient
overflows; Rust also panics on `MIN % -1` and `MIN.rem_euclid(-1)`).
`next_power_of_two` (Rust semantics, debug build) panics iff the result
overflows. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM dashu_base RSGB

namespace RSGBGold.Dashu.Base

/-- Panic condition of signed division. -/
def sBad {ty : IScalarTy} (a b : IScalar ty) : Bool :=
  b.val = 0 || (a.val = -(2 ^ (ty.numBits - 1) : Int) && b.val = -1)

/-- `(a / b, a % b)` for unsigned division. -/
def uDR {ty : UScalarTy} (r : RustM (UScalar ty × UScalar ty)) (a b : UScalar ty) : Bool :=
  if b.val = 0 then decide (r = fail .panic)
  else match r with
    | .ok (q, m) => q.val = a.val / b.val && m.val = a.val % b.val
    | _ => false

/-- `(a % b, a / b)` (the assign variant returns the remainder and the new `self`). -/
def uDRA {ty : UScalarTy} (r : RustM (UScalar ty × UScalar ty)) (a b : UScalar ty) : Bool :=
  if b.val = 0 then decide (r = fail .panic)
  else match r with
    | .ok (m, q) => q.val = a.val / b.val && m.val = a.val % b.val
    | _ => false

def uRE {ty : UScalarTy} (r : RustM (UScalar ty)) (a b : UScalar ty) : Bool :=
  if b.val = 0 then decide (r = fail .panic)
  else match r with
    | .ok m => m.val = a.val % b.val
    | _ => false

/-- Truncated signed division. -/
def sDR {ty : IScalarTy} (r : RustM (IScalar ty × IScalar ty)) (a b : IScalar ty) : Bool :=
  if sBad a b then decide (r = fail .panic)
  else match r with
    | .ok (q, m) => q.val = Int.tdiv a.val b.val && m.val = Int.tmod a.val b.val
    | _ => false

def sDRA {ty : IScalarTy} (r : RustM (IScalar ty × IScalar ty)) (a b : IScalar ty) : Bool :=
  if sBad a b then decide (r = fail .panic)
  else match r with
    | .ok (m, q) => q.val = Int.tdiv a.val b.val && m.val = Int.tmod a.val b.val
    | _ => false

/-- Euclidean signed division. -/
def sDRE {ty : IScalarTy} (r : RustM (IScalar ty × IScalar ty)) (a b : IScalar ty) : Bool :=
  if sBad a b then decide (r = fail .panic)
  else match r with
    | .ok (q, m) => q.val = Int.ediv a.val b.val && m.val = Int.emod a.val b.val
    | _ => false

def sRE {ty : IScalarTy} (r : RustM (IScalar ty)) (a b : IScalar ty) : Bool :=
  if sBad a b then decide (r = fail .panic)
  else match r with
    | .ok m => m.val = Int.emod a.val b.val
    | _ => false

/-- Least `k` with `n ≤ 2^k`. -/
def ceilLog2 (n : Nat) : Nat := (List.range 130).find? (fun k => n ≤ 2 ^ k) |>.getD 130

def isPow2 (n : Nat) : Bool := (List.range 128).any (fun k => n = 2 ^ k)

def pow2Spec {ty : UScalarTy} (r : RustM Bool) (x : UScalar ty) : Bool :=
  decide (r = ok (isPow2 x.val))

def nextPow2Spec {ty : UScalarTy} (r : RustM (UScalar ty)) (x : UScalar ty) : Bool :=
  if ceilLog2 x.val < ty.numBits then
    match r with
    | .ok y => y.val = 2 ^ ceilLog2 x.val
    | _ => false
  else decide (r = fail .panic)

/-- Corner values of a signed type: MIN, MIN+1, -3..3, MAX-1, MAX. -/
def sCorner (ty : IScalarTy) (i : Nat) : IScalar ty :=
  let m : Int := 2 ^ (ty.numBits - 1)
  mkI ty ([-m, -m + 1, -3, -2, -1, 0, 1, 2, 3, m - 2, m - 1].getD i 0)

/-- Corner values of an unsigned type. -/
def uCorner (ty : UScalarTy) (i : Nat) : UScalar ty :=
  let m : Nat := 2 ^ ty.numBits
  mkU ty ([0, 1, 2, 3, 4, m / 2 - 1, m / 2, m / 2 + 1, m - 2, m - 1].getD i 0)

def sAll {ty : IScalarTy} (f : IScalar ty → IScalar ty → Bool) : Bool :=
  (List.range 11).all fun i => (List.range 11).all fun j => f (sCorner ty i) (sCorner ty j)

def uAll {ty : UScalarTy} (f : UScalar ty → UScalar ty → Bool) : Bool :=
  (List.range 10).all fun i => (List.range 10).all fun j => f (uCorner ty i) (uCorner ty j)

end RSGBGold.Dashu.Base

namespace Benchmark.V2.Dashu.Base.Gold
open RSGBGold.Dashu.Base


/-! ### `u8` -/

def gold_div_rem_u8 (a b : Std.U8) : Prop := uDR (U8.Insts.Dashu_baseRingDivRemU8U8U8.div_rem a b) a b = true
def gold_div_rem_u8_corners : Prop := uAll (ty := .U8) (fun a b => uDR (U8.Insts.Dashu_baseRingDivRemU8U8U8.div_rem a b) a b) = true
def gold_div_rem_assign_u8 (a b : Std.U8) : Prop := uDRA (U8.Insts.Dashu_baseRingDivRemAssignU8U8.div_rem_assign a b) a b = true
def gold_div_rem_assign_u8_corners : Prop := uAll (ty := .U8) (fun a b => uDRA (U8.Insts.Dashu_baseRingDivRemAssignU8U8.div_rem_assign a b) a b) = true
def gold_rem_euclid_u8 (a b : Std.U8) : Prop := uRE (U8.Insts.Dashu_baseRingRemEuclidU8U8.rem_euclid a b) a b = true
def gold_rem_euclid_u8_corners : Prop := uAll (ty := .U8) (fun a b => uRE (U8.Insts.Dashu_baseRingRemEuclidU8U8.rem_euclid a b) a b) = true
def gold_div_rem_euclid_u8 (a b : Std.U8) : Prop := uDR (U8.Insts.Dashu_baseRingDivRemEuclidU8U8U8.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_u8_corners : Prop := uAll (ty := .U8) (fun a b => uDR (U8.Insts.Dashu_baseRingDivRemEuclidU8U8U8.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_u8 (x : Std.U8) : Prop := pow2Spec (U8.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_u8_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U8 (2 ^ (k.val % UScalarTy.U8.numBits) + d.val % 3 - 1)
  pow2Spec (U8.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_u8 (x : Std.U8) : Prop := nextPow2Spec (U8.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_u8_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U8 (2 ^ (k.val % UScalarTy.U8.numBits) + d.val % 3 - 1)
  nextPow2Spec (U8.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `u16` -/

def gold_div_rem_u16 (a b : Std.U16) : Prop := uDR (U16.Insts.Dashu_baseRingDivRemU16U16U16.div_rem a b) a b = true
def gold_div_rem_u16_corners : Prop := uAll (ty := .U16) (fun a b => uDR (U16.Insts.Dashu_baseRingDivRemU16U16U16.div_rem a b) a b) = true
def gold_div_rem_assign_u16 (a b : Std.U16) : Prop := uDRA (U16.Insts.Dashu_baseRingDivRemAssignU16U16.div_rem_assign a b) a b = true
def gold_div_rem_assign_u16_corners : Prop := uAll (ty := .U16) (fun a b => uDRA (U16.Insts.Dashu_baseRingDivRemAssignU16U16.div_rem_assign a b) a b) = true
def gold_rem_euclid_u16 (a b : Std.U16) : Prop := uRE (U16.Insts.Dashu_baseRingRemEuclidU16U16.rem_euclid a b) a b = true
def gold_rem_euclid_u16_corners : Prop := uAll (ty := .U16) (fun a b => uRE (U16.Insts.Dashu_baseRingRemEuclidU16U16.rem_euclid a b) a b) = true
def gold_div_rem_euclid_u16 (a b : Std.U16) : Prop := uDR (U16.Insts.Dashu_baseRingDivRemEuclidU16U16U16.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_u16_corners : Prop := uAll (ty := .U16) (fun a b => uDR (U16.Insts.Dashu_baseRingDivRemEuclidU16U16U16.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_u16 (x : Std.U16) : Prop := pow2Spec (U16.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_u16_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U16 (2 ^ (k.val % UScalarTy.U16.numBits) + d.val % 3 - 1)
  pow2Spec (U16.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_u16 (x : Std.U16) : Prop := nextPow2Spec (U16.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_u16_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U16 (2 ^ (k.val % UScalarTy.U16.numBits) + d.val % 3 - 1)
  nextPow2Spec (U16.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `u32` -/

def gold_div_rem_u32 (a b : Std.U32) : Prop := uDR (U32.Insts.Dashu_baseRingDivRemU32U32U32.div_rem a b) a b = true
def gold_div_rem_u32_corners : Prop := uAll (ty := .U32) (fun a b => uDR (U32.Insts.Dashu_baseRingDivRemU32U32U32.div_rem a b) a b) = true
def gold_div_rem_assign_u32 (a b : Std.U32) : Prop := uDRA (U32.Insts.Dashu_baseRingDivRemAssignU32U32.div_rem_assign a b) a b = true
def gold_div_rem_assign_u32_corners : Prop := uAll (ty := .U32) (fun a b => uDRA (U32.Insts.Dashu_baseRingDivRemAssignU32U32.div_rem_assign a b) a b) = true
def gold_rem_euclid_u32 (a b : Std.U32) : Prop := uRE (U32.Insts.Dashu_baseRingRemEuclidU32U32.rem_euclid a b) a b = true
def gold_rem_euclid_u32_corners : Prop := uAll (ty := .U32) (fun a b => uRE (U32.Insts.Dashu_baseRingRemEuclidU32U32.rem_euclid a b) a b) = true
def gold_div_rem_euclid_u32 (a b : Std.U32) : Prop := uDR (U32.Insts.Dashu_baseRingDivRemEuclidU32U32U32.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_u32_corners : Prop := uAll (ty := .U32) (fun a b => uDR (U32.Insts.Dashu_baseRingDivRemEuclidU32U32U32.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_u32 (x : Std.U32) : Prop := pow2Spec (U32.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_u32_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U32 (2 ^ (k.val % UScalarTy.U32.numBits) + d.val % 3 - 1)
  pow2Spec (U32.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_u32 (x : Std.U32) : Prop := nextPow2Spec (U32.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_u32_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U32 (2 ^ (k.val % UScalarTy.U32.numBits) + d.val % 3 - 1)
  nextPow2Spec (U32.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `u64` -/

def gold_div_rem_u64 (a b : Std.U64) : Prop := uDR (U64.Insts.Dashu_baseRingDivRemU64U64U64.div_rem a b) a b = true
def gold_div_rem_u64_corners : Prop := uAll (ty := .U64) (fun a b => uDR (U64.Insts.Dashu_baseRingDivRemU64U64U64.div_rem a b) a b) = true
def gold_div_rem_assign_u64 (a b : Std.U64) : Prop := uDRA (U64.Insts.Dashu_baseRingDivRemAssignU64U64.div_rem_assign a b) a b = true
def gold_div_rem_assign_u64_corners : Prop := uAll (ty := .U64) (fun a b => uDRA (U64.Insts.Dashu_baseRingDivRemAssignU64U64.div_rem_assign a b) a b) = true
def gold_rem_euclid_u64 (a b : Std.U64) : Prop := uRE (U64.Insts.Dashu_baseRingRemEuclidU64U64.rem_euclid a b) a b = true
def gold_rem_euclid_u64_corners : Prop := uAll (ty := .U64) (fun a b => uRE (U64.Insts.Dashu_baseRingRemEuclidU64U64.rem_euclid a b) a b) = true
def gold_div_rem_euclid_u64 (a b : Std.U64) : Prop := uDR (U64.Insts.Dashu_baseRingDivRemEuclidU64U64U64.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_u64_corners : Prop := uAll (ty := .U64) (fun a b => uDR (U64.Insts.Dashu_baseRingDivRemEuclidU64U64U64.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_u64 (x : Std.U64) : Prop := pow2Spec (U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_u64_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U64 (2 ^ (k.val % UScalarTy.U64.numBits) + d.val % 3 - 1)
  pow2Spec (U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_u64 (x : Std.U64) : Prop := nextPow2Spec (U64.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_u64_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U64 (2 ^ (k.val % UScalarTy.U64.numBits) + d.val % 3 - 1)
  nextPow2Spec (U64.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `u128` -/

def gold_div_rem_u128 (a b : Std.U128) : Prop := uDR (U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem a b) a b = true
def gold_div_rem_u128_corners : Prop := uAll (ty := .U128) (fun a b => uDR (U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem a b) a b) = true
def gold_div_rem_assign_u128 (a b : Std.U128) : Prop := uDRA (U128.Insts.Dashu_baseRingDivRemAssignU128U128.div_rem_assign a b) a b = true
def gold_div_rem_assign_u128_corners : Prop := uAll (ty := .U128) (fun a b => uDRA (U128.Insts.Dashu_baseRingDivRemAssignU128U128.div_rem_assign a b) a b) = true
def gold_rem_euclid_u128 (a b : Std.U128) : Prop := uRE (U128.Insts.Dashu_baseRingRemEuclidU128U128.rem_euclid a b) a b = true
def gold_rem_euclid_u128_corners : Prop := uAll (ty := .U128) (fun a b => uRE (U128.Insts.Dashu_baseRingRemEuclidU128U128.rem_euclid a b) a b) = true
def gold_div_rem_euclid_u128 (a b : Std.U128) : Prop := uDR (U128.Insts.Dashu_baseRingDivRemEuclidU128U128U128.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_u128_corners : Prop := uAll (ty := .U128) (fun a b => uDR (U128.Insts.Dashu_baseRingDivRemEuclidU128U128U128.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_u128 (x : Std.U128) : Prop := pow2Spec (U128.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_u128_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U128 (2 ^ (k.val % UScalarTy.U128.numBits) + d.val % 3 - 1)
  pow2Spec (U128.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_u128 (x : Std.U128) : Prop := nextPow2Spec (U128.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_u128_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .U128 (2 ^ (k.val % UScalarTy.U128.numBits) + d.val % 3 - 1)
  nextPow2Spec (U128.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `usize` -/

def gold_div_rem_usize (a b : Std.Usize) : Prop := uDR (Usize.Insts.Dashu_baseRingDivRemUsizeUsizeUsize.div_rem a b) a b = true
def gold_div_rem_usize_corners : Prop := uAll (ty := .Usize) (fun a b => uDR (Usize.Insts.Dashu_baseRingDivRemUsizeUsizeUsize.div_rem a b) a b) = true
def gold_div_rem_assign_usize (a b : Std.Usize) : Prop := uDRA (Usize.Insts.Dashu_baseRingDivRemAssignUsizeUsize.div_rem_assign a b) a b = true
def gold_div_rem_assign_usize_corners : Prop := uAll (ty := .Usize) (fun a b => uDRA (Usize.Insts.Dashu_baseRingDivRemAssignUsizeUsize.div_rem_assign a b) a b) = true
def gold_rem_euclid_usize (a b : Std.Usize) : Prop := uRE (Usize.Insts.Dashu_baseRingRemEuclidUsizeUsize.rem_euclid a b) a b = true
def gold_rem_euclid_usize_corners : Prop := uAll (ty := .Usize) (fun a b => uRE (Usize.Insts.Dashu_baseRingRemEuclidUsizeUsize.rem_euclid a b) a b) = true
def gold_div_rem_euclid_usize (a b : Std.Usize) : Prop := uDR (Usize.Insts.Dashu_baseRingDivRemEuclidUsizeUsizeUsize.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_usize_corners : Prop := uAll (ty := .Usize) (fun a b => uDR (Usize.Insts.Dashu_baseRingDivRemEuclidUsizeUsizeUsize.div_rem_euclid a b) a b) = true
def gold_is_power_of_two_usize (x : Std.Usize) : Prop := pow2Spec (Usize.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
/-- Exact powers of two and their neighbours. -/
def gold_is_power_of_two_usize_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .Usize (2 ^ (k.val % UScalarTy.Usize.numBits) + d.val % 3 - 1)
  pow2Spec (Usize.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x) x = true
def gold_next_power_of_two_usize (x : Std.Usize) : Prop := nextPow2Spec (Usize.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true
def gold_next_power_of_two_usize_pow (k : Std.U8) (d : Std.U8) : Prop :=
  let x := mkU .Usize (2 ^ (k.val % UScalarTy.Usize.numBits) + d.val % 3 - 1)
  nextPow2Spec (Usize.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two x) x = true

/-! ### `i8` -/

def gold_div_rem_i8 (a b : Std.I8) : Prop := sDR (I8.Insts.Dashu_baseRingDivRemI8I8I8.div_rem a b) a b = true
def gold_div_rem_i8_corners : Prop := sAll (ty := .I8) (fun a b => sDR (I8.Insts.Dashu_baseRingDivRemI8I8I8.div_rem a b) a b) = true
def gold_div_rem_assign_i8 (a b : Std.I8) : Prop := sDRA (I8.Insts.Dashu_baseRingDivRemAssignI8I8.div_rem_assign a b) a b = true
def gold_div_rem_assign_i8_corners : Prop := sAll (ty := .I8) (fun a b => sDRA (I8.Insts.Dashu_baseRingDivRemAssignI8I8.div_rem_assign a b) a b) = true
def gold_rem_euclid_i8 (a b : Std.I8) : Prop := sRE (I8.Insts.Dashu_baseRingRemEuclidI8I8.rem_euclid a b) a b = true
def gold_rem_euclid_i8_corners : Prop := sAll (ty := .I8) (fun a b => sRE (I8.Insts.Dashu_baseRingRemEuclidI8I8.rem_euclid a b) a b) = true
def gold_div_rem_euclid_i8 (a b : Std.I8) : Prop := sDRE (I8.Insts.Dashu_baseRingDivRemEuclidI8I8I8.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_i8_corners : Prop := sAll (ty := .I8) (fun a b => sDRE (I8.Insts.Dashu_baseRingDivRemEuclidI8I8I8.div_rem_euclid a b) a b) = true

/-! ### `i16` -/

def gold_div_rem_i16 (a b : Std.I16) : Prop := sDR (I16.Insts.Dashu_baseRingDivRemI16I16I16.div_rem a b) a b = true
def gold_div_rem_i16_corners : Prop := sAll (ty := .I16) (fun a b => sDR (I16.Insts.Dashu_baseRingDivRemI16I16I16.div_rem a b) a b) = true
def gold_div_rem_assign_i16 (a b : Std.I16) : Prop := sDRA (I16.Insts.Dashu_baseRingDivRemAssignI16I16.div_rem_assign a b) a b = true
def gold_div_rem_assign_i16_corners : Prop := sAll (ty := .I16) (fun a b => sDRA (I16.Insts.Dashu_baseRingDivRemAssignI16I16.div_rem_assign a b) a b) = true
def gold_rem_euclid_i16 (a b : Std.I16) : Prop := sRE (I16.Insts.Dashu_baseRingRemEuclidI16I16.rem_euclid a b) a b = true
def gold_rem_euclid_i16_corners : Prop := sAll (ty := .I16) (fun a b => sRE (I16.Insts.Dashu_baseRingRemEuclidI16I16.rem_euclid a b) a b) = true
def gold_div_rem_euclid_i16 (a b : Std.I16) : Prop := sDRE (I16.Insts.Dashu_baseRingDivRemEuclidI16I16I16.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_i16_corners : Prop := sAll (ty := .I16) (fun a b => sDRE (I16.Insts.Dashu_baseRingDivRemEuclidI16I16I16.div_rem_euclid a b) a b) = true

/-! ### `i32` -/

def gold_div_rem_i32 (a b : Std.I32) : Prop := sDR (I32.Insts.Dashu_baseRingDivRemI32I32I32.div_rem a b) a b = true
def gold_div_rem_i32_corners : Prop := sAll (ty := .I32) (fun a b => sDR (I32.Insts.Dashu_baseRingDivRemI32I32I32.div_rem a b) a b) = true
def gold_div_rem_assign_i32 (a b : Std.I32) : Prop := sDRA (I32.Insts.Dashu_baseRingDivRemAssignI32I32.div_rem_assign a b) a b = true
def gold_div_rem_assign_i32_corners : Prop := sAll (ty := .I32) (fun a b => sDRA (I32.Insts.Dashu_baseRingDivRemAssignI32I32.div_rem_assign a b) a b) = true
def gold_rem_euclid_i32 (a b : Std.I32) : Prop := sRE (I32.Insts.Dashu_baseRingRemEuclidI32I32.rem_euclid a b) a b = true
def gold_rem_euclid_i32_corners : Prop := sAll (ty := .I32) (fun a b => sRE (I32.Insts.Dashu_baseRingRemEuclidI32I32.rem_euclid a b) a b) = true
def gold_div_rem_euclid_i32 (a b : Std.I32) : Prop := sDRE (I32.Insts.Dashu_baseRingDivRemEuclidI32I32I32.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_i32_corners : Prop := sAll (ty := .I32) (fun a b => sDRE (I32.Insts.Dashu_baseRingDivRemEuclidI32I32I32.div_rem_euclid a b) a b) = true

/-! ### `i64` -/

def gold_div_rem_i64 (a b : Std.I64) : Prop := sDR (I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem a b) a b = true
def gold_div_rem_i64_corners : Prop := sAll (ty := .I64) (fun a b => sDR (I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem a b) a b) = true
def gold_div_rem_assign_i64 (a b : Std.I64) : Prop := sDRA (I64.Insts.Dashu_baseRingDivRemAssignI64I64.div_rem_assign a b) a b = true
def gold_div_rem_assign_i64_corners : Prop := sAll (ty := .I64) (fun a b => sDRA (I64.Insts.Dashu_baseRingDivRemAssignI64I64.div_rem_assign a b) a b) = true
def gold_rem_euclid_i64 (a b : Std.I64) : Prop := sRE (I64.Insts.Dashu_baseRingRemEuclidI64I64.rem_euclid a b) a b = true
def gold_rem_euclid_i64_corners : Prop := sAll (ty := .I64) (fun a b => sRE (I64.Insts.Dashu_baseRingRemEuclidI64I64.rem_euclid a b) a b) = true
def gold_div_rem_euclid_i64 (a b : Std.I64) : Prop := sDRE (I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_i64_corners : Prop := sAll (ty := .I64) (fun a b => sDRE (I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b) a b) = true

/-! ### `i128` -/

def gold_div_rem_i128 (a b : Std.I128) : Prop := sDR (I128.Insts.Dashu_baseRingDivRemI128I128I128.div_rem a b) a b = true
def gold_div_rem_i128_corners : Prop := sAll (ty := .I128) (fun a b => sDR (I128.Insts.Dashu_baseRingDivRemI128I128I128.div_rem a b) a b) = true
def gold_div_rem_assign_i128 (a b : Std.I128) : Prop := sDRA (I128.Insts.Dashu_baseRingDivRemAssignI128I128.div_rem_assign a b) a b = true
def gold_div_rem_assign_i128_corners : Prop := sAll (ty := .I128) (fun a b => sDRA (I128.Insts.Dashu_baseRingDivRemAssignI128I128.div_rem_assign a b) a b) = true
def gold_rem_euclid_i128 (a b : Std.I128) : Prop := sRE (I128.Insts.Dashu_baseRingRemEuclidI128I128.rem_euclid a b) a b = true
def gold_rem_euclid_i128_corners : Prop := sAll (ty := .I128) (fun a b => sRE (I128.Insts.Dashu_baseRingRemEuclidI128I128.rem_euclid a b) a b) = true
def gold_div_rem_euclid_i128 (a b : Std.I128) : Prop := sDRE (I128.Insts.Dashu_baseRingDivRemEuclidI128I128I128.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_i128_corners : Prop := sAll (ty := .I128) (fun a b => sDRE (I128.Insts.Dashu_baseRingDivRemEuclidI128I128I128.div_rem_euclid a b) a b) = true

/-! ### `isize` -/

def gold_div_rem_isize (a b : Std.Isize) : Prop := sDR (Isize.Insts.Dashu_baseRingDivRemIsizeIsizeIsize.div_rem a b) a b = true
def gold_div_rem_isize_corners : Prop := sAll (ty := .Isize) (fun a b => sDR (Isize.Insts.Dashu_baseRingDivRemIsizeIsizeIsize.div_rem a b) a b) = true
def gold_div_rem_assign_isize (a b : Std.Isize) : Prop := sDRA (Isize.Insts.Dashu_baseRingDivRemAssignIsizeIsize.div_rem_assign a b) a b = true
def gold_div_rem_assign_isize_corners : Prop := sAll (ty := .Isize) (fun a b => sDRA (Isize.Insts.Dashu_baseRingDivRemAssignIsizeIsize.div_rem_assign a b) a b) = true
def gold_rem_euclid_isize (a b : Std.Isize) : Prop := sRE (Isize.Insts.Dashu_baseRingRemEuclidIsizeIsize.rem_euclid a b) a b = true
def gold_rem_euclid_isize_corners : Prop := sAll (ty := .Isize) (fun a b => sRE (Isize.Insts.Dashu_baseRingRemEuclidIsizeIsize.rem_euclid a b) a b) = true
def gold_div_rem_euclid_isize (a b : Std.Isize) : Prop := sDRE (Isize.Insts.Dashu_baseRingDivRemEuclidIsizeIsizeIsize.div_rem_euclid a b) a b = true
def gold_div_rem_euclid_isize_corners : Prop := sAll (ty := .Isize) (fun a b => sDRE (Isize.Insts.Dashu_baseRingDivRemEuclidIsizeIsizeIsize.div_rem_euclid a b) a b) = true

/-! Differential-testing probes. -/

def diff_div_rem_u8 (a b : Std.U8) := U8.Insts.Dashu_baseRingDivRemU8U8U8.div_rem a b
def diff_div_rem_u8_c (i j : Std.U8) := U8.Insts.Dashu_baseRingDivRemU8U8U8.div_rem (uCorner .U8 (i.val % 10)) (uCorner .U8 (j.val % 10))
def diff_div_rem_assign_u8 (a b : Std.U8) := U8.Insts.Dashu_baseRingDivRemAssignU8U8.div_rem_assign a b
def diff_div_rem_assign_u8_c (i j : Std.U8) := U8.Insts.Dashu_baseRingDivRemAssignU8U8.div_rem_assign (uCorner .U8 (i.val % 10)) (uCorner .U8 (j.val % 10))
def diff_rem_euclid_u8 (a b : Std.U8) := U8.Insts.Dashu_baseRingRemEuclidU8U8.rem_euclid a b
def diff_rem_euclid_u8_c (i j : Std.U8) := U8.Insts.Dashu_baseRingRemEuclidU8U8.rem_euclid (uCorner .U8 (i.val % 10)) (uCorner .U8 (j.val % 10))
def diff_div_rem_euclid_u8 (a b : Std.U8) := U8.Insts.Dashu_baseRingDivRemEuclidU8U8U8.div_rem_euclid a b
def diff_div_rem_euclid_u8_c (i j : Std.U8) := U8.Insts.Dashu_baseRingDivRemEuclidU8U8U8.div_rem_euclid (uCorner .U8 (i.val % 10)) (uCorner .U8 (j.val % 10))
def diff_is_power_of_two_u8 (x : Std.U8) := U8.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_u8_pow (k : Std.U8) (d : Std.U8) := U8.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .U8 (2 ^ (k.val % UScalarTy.U8.numBits) + d.val % 3 - 1))
def diff_div_rem_u16 (a b : Std.U16) := U16.Insts.Dashu_baseRingDivRemU16U16U16.div_rem a b
def diff_div_rem_u16_c (i j : Std.U8) := U16.Insts.Dashu_baseRingDivRemU16U16U16.div_rem (uCorner .U16 (i.val % 10)) (uCorner .U16 (j.val % 10))
def diff_div_rem_assign_u16 (a b : Std.U16) := U16.Insts.Dashu_baseRingDivRemAssignU16U16.div_rem_assign a b
def diff_div_rem_assign_u16_c (i j : Std.U8) := U16.Insts.Dashu_baseRingDivRemAssignU16U16.div_rem_assign (uCorner .U16 (i.val % 10)) (uCorner .U16 (j.val % 10))
def diff_rem_euclid_u16 (a b : Std.U16) := U16.Insts.Dashu_baseRingRemEuclidU16U16.rem_euclid a b
def diff_rem_euclid_u16_c (i j : Std.U8) := U16.Insts.Dashu_baseRingRemEuclidU16U16.rem_euclid (uCorner .U16 (i.val % 10)) (uCorner .U16 (j.val % 10))
def diff_div_rem_euclid_u16 (a b : Std.U16) := U16.Insts.Dashu_baseRingDivRemEuclidU16U16U16.div_rem_euclid a b
def diff_div_rem_euclid_u16_c (i j : Std.U8) := U16.Insts.Dashu_baseRingDivRemEuclidU16U16U16.div_rem_euclid (uCorner .U16 (i.val % 10)) (uCorner .U16 (j.val % 10))
def diff_is_power_of_two_u16 (x : Std.U16) := U16.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_u16_pow (k : Std.U8) (d : Std.U8) := U16.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .U16 (2 ^ (k.val % UScalarTy.U16.numBits) + d.val % 3 - 1))
def diff_div_rem_u32 (a b : Std.U32) := U32.Insts.Dashu_baseRingDivRemU32U32U32.div_rem a b
def diff_div_rem_u32_c (i j : Std.U8) := U32.Insts.Dashu_baseRingDivRemU32U32U32.div_rem (uCorner .U32 (i.val % 10)) (uCorner .U32 (j.val % 10))
def diff_div_rem_assign_u32 (a b : Std.U32) := U32.Insts.Dashu_baseRingDivRemAssignU32U32.div_rem_assign a b
def diff_div_rem_assign_u32_c (i j : Std.U8) := U32.Insts.Dashu_baseRingDivRemAssignU32U32.div_rem_assign (uCorner .U32 (i.val % 10)) (uCorner .U32 (j.val % 10))
def diff_rem_euclid_u32 (a b : Std.U32) := U32.Insts.Dashu_baseRingRemEuclidU32U32.rem_euclid a b
def diff_rem_euclid_u32_c (i j : Std.U8) := U32.Insts.Dashu_baseRingRemEuclidU32U32.rem_euclid (uCorner .U32 (i.val % 10)) (uCorner .U32 (j.val % 10))
def diff_div_rem_euclid_u32 (a b : Std.U32) := U32.Insts.Dashu_baseRingDivRemEuclidU32U32U32.div_rem_euclid a b
def diff_div_rem_euclid_u32_c (i j : Std.U8) := U32.Insts.Dashu_baseRingDivRemEuclidU32U32U32.div_rem_euclid (uCorner .U32 (i.val % 10)) (uCorner .U32 (j.val % 10))
def diff_is_power_of_two_u32 (x : Std.U32) := U32.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_u32_pow (k : Std.U8) (d : Std.U8) := U32.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .U32 (2 ^ (k.val % UScalarTy.U32.numBits) + d.val % 3 - 1))
def diff_div_rem_u64 (a b : Std.U64) := U64.Insts.Dashu_baseRingDivRemU64U64U64.div_rem a b
def diff_div_rem_u64_c (i j : Std.U8) := U64.Insts.Dashu_baseRingDivRemU64U64U64.div_rem (uCorner .U64 (i.val % 10)) (uCorner .U64 (j.val % 10))
def diff_div_rem_assign_u64 (a b : Std.U64) := U64.Insts.Dashu_baseRingDivRemAssignU64U64.div_rem_assign a b
def diff_div_rem_assign_u64_c (i j : Std.U8) := U64.Insts.Dashu_baseRingDivRemAssignU64U64.div_rem_assign (uCorner .U64 (i.val % 10)) (uCorner .U64 (j.val % 10))
def diff_rem_euclid_u64 (a b : Std.U64) := U64.Insts.Dashu_baseRingRemEuclidU64U64.rem_euclid a b
def diff_rem_euclid_u64_c (i j : Std.U8) := U64.Insts.Dashu_baseRingRemEuclidU64U64.rem_euclid (uCorner .U64 (i.val % 10)) (uCorner .U64 (j.val % 10))
def diff_div_rem_euclid_u64 (a b : Std.U64) := U64.Insts.Dashu_baseRingDivRemEuclidU64U64U64.div_rem_euclid a b
def diff_div_rem_euclid_u64_c (i j : Std.U8) := U64.Insts.Dashu_baseRingDivRemEuclidU64U64U64.div_rem_euclid (uCorner .U64 (i.val % 10)) (uCorner .U64 (j.val % 10))
def diff_is_power_of_two_u64 (x : Std.U64) := U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_u64_pow (k : Std.U8) (d : Std.U8) := U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .U64 (2 ^ (k.val % UScalarTy.U64.numBits) + d.val % 3 - 1))
def diff_div_rem_u128 (a b : Std.U128) := U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem a b
def diff_div_rem_u128_c (i j : Std.U8) := U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem (uCorner .U128 (i.val % 10)) (uCorner .U128 (j.val % 10))
def diff_div_rem_assign_u128 (a b : Std.U128) := U128.Insts.Dashu_baseRingDivRemAssignU128U128.div_rem_assign a b
def diff_div_rem_assign_u128_c (i j : Std.U8) := U128.Insts.Dashu_baseRingDivRemAssignU128U128.div_rem_assign (uCorner .U128 (i.val % 10)) (uCorner .U128 (j.val % 10))
def diff_rem_euclid_u128 (a b : Std.U128) := U128.Insts.Dashu_baseRingRemEuclidU128U128.rem_euclid a b
def diff_rem_euclid_u128_c (i j : Std.U8) := U128.Insts.Dashu_baseRingRemEuclidU128U128.rem_euclid (uCorner .U128 (i.val % 10)) (uCorner .U128 (j.val % 10))
def diff_div_rem_euclid_u128 (a b : Std.U128) := U128.Insts.Dashu_baseRingDivRemEuclidU128U128U128.div_rem_euclid a b
def diff_div_rem_euclid_u128_c (i j : Std.U8) := U128.Insts.Dashu_baseRingDivRemEuclidU128U128U128.div_rem_euclid (uCorner .U128 (i.val % 10)) (uCorner .U128 (j.val % 10))
def diff_is_power_of_two_u128 (x : Std.U128) := U128.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_u128_pow (k : Std.U8) (d : Std.U8) := U128.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .U128 (2 ^ (k.val % UScalarTy.U128.numBits) + d.val % 3 - 1))
def diff_div_rem_usize (a b : Std.Usize) := Usize.Insts.Dashu_baseRingDivRemUsizeUsizeUsize.div_rem a b
def diff_div_rem_usize_c (i j : Std.U8) := Usize.Insts.Dashu_baseRingDivRemUsizeUsizeUsize.div_rem (uCorner .Usize (i.val % 10)) (uCorner .Usize (j.val % 10))
def diff_div_rem_assign_usize (a b : Std.Usize) := Usize.Insts.Dashu_baseRingDivRemAssignUsizeUsize.div_rem_assign a b
def diff_div_rem_assign_usize_c (i j : Std.U8) := Usize.Insts.Dashu_baseRingDivRemAssignUsizeUsize.div_rem_assign (uCorner .Usize (i.val % 10)) (uCorner .Usize (j.val % 10))
def diff_rem_euclid_usize (a b : Std.Usize) := Usize.Insts.Dashu_baseRingRemEuclidUsizeUsize.rem_euclid a b
def diff_rem_euclid_usize_c (i j : Std.U8) := Usize.Insts.Dashu_baseRingRemEuclidUsizeUsize.rem_euclid (uCorner .Usize (i.val % 10)) (uCorner .Usize (j.val % 10))
def diff_div_rem_euclid_usize (a b : Std.Usize) := Usize.Insts.Dashu_baseRingDivRemEuclidUsizeUsizeUsize.div_rem_euclid a b
def diff_div_rem_euclid_usize_c (i j : Std.U8) := Usize.Insts.Dashu_baseRingDivRemEuclidUsizeUsizeUsize.div_rem_euclid (uCorner .Usize (i.val % 10)) (uCorner .Usize (j.val % 10))
def diff_is_power_of_two_usize (x : Std.Usize) := Usize.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
def diff_is_power_of_two_usize_pow (k : Std.U8) (d : Std.U8) := Usize.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two (mkU .Usize (2 ^ (k.val % UScalarTy.Usize.numBits) + d.val % 3 - 1))
def diff_div_rem_i8 (a b : Std.I8) := I8.Insts.Dashu_baseRingDivRemI8I8I8.div_rem a b
def diff_div_rem_i8_c (i j : Std.U8) := I8.Insts.Dashu_baseRingDivRemI8I8I8.div_rem (sCorner .I8 (i.val % 11)) (sCorner .I8 (j.val % 11))
def diff_div_rem_assign_i8 (a b : Std.I8) := I8.Insts.Dashu_baseRingDivRemAssignI8I8.div_rem_assign a b
def diff_div_rem_assign_i8_c (i j : Std.U8) := I8.Insts.Dashu_baseRingDivRemAssignI8I8.div_rem_assign (sCorner .I8 (i.val % 11)) (sCorner .I8 (j.val % 11))
def diff_rem_euclid_i8 (a b : Std.I8) := I8.Insts.Dashu_baseRingRemEuclidI8I8.rem_euclid a b
def diff_rem_euclid_i8_c (i j : Std.U8) := I8.Insts.Dashu_baseRingRemEuclidI8I8.rem_euclid (sCorner .I8 (i.val % 11)) (sCorner .I8 (j.val % 11))
def diff_div_rem_euclid_i8 (a b : Std.I8) := I8.Insts.Dashu_baseRingDivRemEuclidI8I8I8.div_rem_euclid a b
def diff_div_rem_euclid_i8_c (i j : Std.U8) := I8.Insts.Dashu_baseRingDivRemEuclidI8I8I8.div_rem_euclid (sCorner .I8 (i.val % 11)) (sCorner .I8 (j.val % 11))
def diff_div_rem_i16 (a b : Std.I16) := I16.Insts.Dashu_baseRingDivRemI16I16I16.div_rem a b
def diff_div_rem_i16_c (i j : Std.U8) := I16.Insts.Dashu_baseRingDivRemI16I16I16.div_rem (sCorner .I16 (i.val % 11)) (sCorner .I16 (j.val % 11))
def diff_div_rem_assign_i16 (a b : Std.I16) := I16.Insts.Dashu_baseRingDivRemAssignI16I16.div_rem_assign a b
def diff_div_rem_assign_i16_c (i j : Std.U8) := I16.Insts.Dashu_baseRingDivRemAssignI16I16.div_rem_assign (sCorner .I16 (i.val % 11)) (sCorner .I16 (j.val % 11))
def diff_rem_euclid_i16 (a b : Std.I16) := I16.Insts.Dashu_baseRingRemEuclidI16I16.rem_euclid a b
def diff_rem_euclid_i16_c (i j : Std.U8) := I16.Insts.Dashu_baseRingRemEuclidI16I16.rem_euclid (sCorner .I16 (i.val % 11)) (sCorner .I16 (j.val % 11))
def diff_div_rem_euclid_i16 (a b : Std.I16) := I16.Insts.Dashu_baseRingDivRemEuclidI16I16I16.div_rem_euclid a b
def diff_div_rem_euclid_i16_c (i j : Std.U8) := I16.Insts.Dashu_baseRingDivRemEuclidI16I16I16.div_rem_euclid (sCorner .I16 (i.val % 11)) (sCorner .I16 (j.val % 11))
def diff_div_rem_i32 (a b : Std.I32) := I32.Insts.Dashu_baseRingDivRemI32I32I32.div_rem a b
def diff_div_rem_i32_c (i j : Std.U8) := I32.Insts.Dashu_baseRingDivRemI32I32I32.div_rem (sCorner .I32 (i.val % 11)) (sCorner .I32 (j.val % 11))
def diff_div_rem_assign_i32 (a b : Std.I32) := I32.Insts.Dashu_baseRingDivRemAssignI32I32.div_rem_assign a b
def diff_div_rem_assign_i32_c (i j : Std.U8) := I32.Insts.Dashu_baseRingDivRemAssignI32I32.div_rem_assign (sCorner .I32 (i.val % 11)) (sCorner .I32 (j.val % 11))
def diff_rem_euclid_i32 (a b : Std.I32) := I32.Insts.Dashu_baseRingRemEuclidI32I32.rem_euclid a b
def diff_rem_euclid_i32_c (i j : Std.U8) := I32.Insts.Dashu_baseRingRemEuclidI32I32.rem_euclid (sCorner .I32 (i.val % 11)) (sCorner .I32 (j.val % 11))
def diff_div_rem_euclid_i32 (a b : Std.I32) := I32.Insts.Dashu_baseRingDivRemEuclidI32I32I32.div_rem_euclid a b
def diff_div_rem_euclid_i32_c (i j : Std.U8) := I32.Insts.Dashu_baseRingDivRemEuclidI32I32I32.div_rem_euclid (sCorner .I32 (i.val % 11)) (sCorner .I32 (j.val % 11))
def diff_div_rem_i64 (a b : Std.I64) := I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem a b
def diff_div_rem_i64_c (i j : Std.U8) := I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem (sCorner .I64 (i.val % 11)) (sCorner .I64 (j.val % 11))
def diff_div_rem_assign_i64 (a b : Std.I64) := I64.Insts.Dashu_baseRingDivRemAssignI64I64.div_rem_assign a b
def diff_div_rem_assign_i64_c (i j : Std.U8) := I64.Insts.Dashu_baseRingDivRemAssignI64I64.div_rem_assign (sCorner .I64 (i.val % 11)) (sCorner .I64 (j.val % 11))
def diff_rem_euclid_i64 (a b : Std.I64) := I64.Insts.Dashu_baseRingRemEuclidI64I64.rem_euclid a b
def diff_rem_euclid_i64_c (i j : Std.U8) := I64.Insts.Dashu_baseRingRemEuclidI64I64.rem_euclid (sCorner .I64 (i.val % 11)) (sCorner .I64 (j.val % 11))
def diff_div_rem_euclid_i64 (a b : Std.I64) := I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b
def diff_div_rem_euclid_i64_c (i j : Std.U8) := I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid (sCorner .I64 (i.val % 11)) (sCorner .I64 (j.val % 11))
def diff_div_rem_i128 (a b : Std.I128) := I128.Insts.Dashu_baseRingDivRemI128I128I128.div_rem a b
def diff_div_rem_i128_c (i j : Std.U8) := I128.Insts.Dashu_baseRingDivRemI128I128I128.div_rem (sCorner .I128 (i.val % 11)) (sCorner .I128 (j.val % 11))
def diff_div_rem_assign_i128 (a b : Std.I128) := I128.Insts.Dashu_baseRingDivRemAssignI128I128.div_rem_assign a b
def diff_div_rem_assign_i128_c (i j : Std.U8) := I128.Insts.Dashu_baseRingDivRemAssignI128I128.div_rem_assign (sCorner .I128 (i.val % 11)) (sCorner .I128 (j.val % 11))
def diff_rem_euclid_i128 (a b : Std.I128) := I128.Insts.Dashu_baseRingRemEuclidI128I128.rem_euclid a b
def diff_rem_euclid_i128_c (i j : Std.U8) := I128.Insts.Dashu_baseRingRemEuclidI128I128.rem_euclid (sCorner .I128 (i.val % 11)) (sCorner .I128 (j.val % 11))
def diff_div_rem_euclid_i128 (a b : Std.I128) := I128.Insts.Dashu_baseRingDivRemEuclidI128I128I128.div_rem_euclid a b
def diff_div_rem_euclid_i128_c (i j : Std.U8) := I128.Insts.Dashu_baseRingDivRemEuclidI128I128I128.div_rem_euclid (sCorner .I128 (i.val % 11)) (sCorner .I128 (j.val % 11))
def diff_div_rem_isize (a b : Std.Isize) := Isize.Insts.Dashu_baseRingDivRemIsizeIsizeIsize.div_rem a b
def diff_div_rem_isize_c (i j : Std.U8) := Isize.Insts.Dashu_baseRingDivRemIsizeIsizeIsize.div_rem (sCorner .Isize (i.val % 11)) (sCorner .Isize (j.val % 11))
def diff_div_rem_assign_isize (a b : Std.Isize) := Isize.Insts.Dashu_baseRingDivRemAssignIsizeIsize.div_rem_assign a b
def diff_div_rem_assign_isize_c (i j : Std.U8) := Isize.Insts.Dashu_baseRingDivRemAssignIsizeIsize.div_rem_assign (sCorner .Isize (i.val % 11)) (sCorner .Isize (j.val % 11))
def diff_rem_euclid_isize (a b : Std.Isize) := Isize.Insts.Dashu_baseRingRemEuclidIsizeIsize.rem_euclid a b
def diff_rem_euclid_isize_c (i j : Std.U8) := Isize.Insts.Dashu_baseRingRemEuclidIsizeIsize.rem_euclid (sCorner .Isize (i.val % 11)) (sCorner .Isize (j.val % 11))
def diff_div_rem_euclid_isize (a b : Std.Isize) := Isize.Insts.Dashu_baseRingDivRemEuclidIsizeIsizeIsize.div_rem_euclid a b
def diff_div_rem_euclid_isize_c (i j : Std.U8) := Isize.Insts.Dashu_baseRingDivRemEuclidIsizeIsizeIsize.div_rem_euclid (sCorner .Isize (i.val % 11)) (sCorner .Isize (j.val % 11))

end Benchmark.V2.Dashu.Base.Gold
