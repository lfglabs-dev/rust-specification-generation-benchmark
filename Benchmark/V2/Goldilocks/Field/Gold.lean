import Benchmark.V2.Prelude
import Benchmark.Exec.Runtime
import GoldilocksField.Extraction

/-! Hidden gold specification for target `goldilocks/field`.

`P = 2^64 - 2^32 + 1`. Two layers:

* `field::Field` — an element of `F_P`. Its internal representation (a
  Montgomery form) is **not** part of the contract: every `Field` property is
  stated through the element it denotes, built with `Field::new(n mod P)`
  (`fe n`) and observed with `u64::from` (canonical value) / derived
  equality. Results are compared as `Field` values (`op (fe a) (fe b) = fe c`),
  which also pins canonicity of the stored value (derived `PartialEq`/`Hash`
  compare it bitwise). `From<i32>` is specified for `v ≠ i32::MIN` only
  (`-i32::MIN` overflows in debug builds: an accident, not a contract).
* `field::algo` (re-exported `generic` functions on raw `u64`): exact modular
  arithmetic on reduced values, Montgomery arithmetic with `R = 2^64`, and
  the `debug_assert!` preconditions (panic iff violated). `reduce_64(P)` returns
  `P` (an off-by-one in the crate: `n > MODULUS`); only the congruence is
  required there. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM RSGB

namespace RSGBGold.Goldilocks.Field
open goldilocks_ntt

def P : Nat := 18446744069414584321
/-- `R = 2^64 mod P` and its inverse. -/
def Rm : Nat := 4294967295
def Rinv : Nat := 18446744065119617025
def inv2 : Nat := 9223372034707292161

/-- `b^e mod m` for `e < 2^64` (square and multiply). -/
def powMod (b e m : Nat) : Nat :=
  ((List.range 64).foldl (fun (acc : Nat × Nat) i =>
    let (r, x) := acc
    ((if (e >>> i) % 2 = 1 then r * x % m else r), x * x % m)) (1 % m, b % m)).1

def invP (a : Nat) : Nat := powMod a (P - 2) P

abbrev F := field.Field

/-- The field element denoting `n mod P`. -/
def fe (n : Nat) : RustM F := field.Field.new (mkU .U64 (n % P))

def val (x : F) : RustM Std.U64 := goldilocks_ntt.U64.Insts.CoreConvertFromField.from x
def valRef (x : F) : RustM Std.U64 := goldilocks_ntt.U64.Insts.CoreConvertFromShared0Field.from x

def bin (f : F → F → RustM F) (a b : Nat) : RustM F := do
  let x ← fe a
  let y ← fe b
  f x y

def un (f : F → RustM F) (a : Nat) : RustM F := do
  let x ← fe a
  f x

def ordOf (a b : Nat) : core.cmp.Ordering :=
  if a < b then .Less else if a = b then .Equal else .Greater

/-- Canonical value of `root(order)` (if any). -/
def rootVal (order : Std.U64) : RustM (Option Nat) := do
  let o ← field.Field.root order
  match o with
  | .Some w => do let v ← val w; pure (some v.val)
  | .None => pure none

/-- `w` is a primitive `n`-th root of unity (`n ∣ P - 1`). -/
def primitive (w n : Nat) : Bool :=
  powMod w n P == 1 && [2, 3, 5, 17, 257, 65537].all (fun q => n % q != 0 || powMod w (n / q) P != 1)

def rootOk (o : Option Nat) (n : Nat) : Bool :=
  match o with
  | some w => primitive w n
  | none => false

/-- A divisor of `P - 1 = 2^32·3·5·17·257·65537` selected by two bytes. -/
def divisorOf (k m : Std.U8) : Nat :=
  2 ^ (k.val % 33) * (if m.val % 2 = 1 then 3 else 1) * (if m.val / 2 % 2 = 1 then 5 else 1) *
    (if m.val / 4 % 2 = 1 then 17 else 1) * (if m.val / 8 % 2 = 1 then 257 else 1) *
    (if m.val / 16 % 2 = 1 then 65537 else 1)

/-- Values next to `0` and `P`. -/
def near (k : Std.U8) : Nat := [0, 1, 2, 3, P - 1, P - 2, P - 3, P, P + 1, 2 ^ 64 - 1, 2 ^ 32, 2 ^ 32 - 1].getD (k.val % 12) 0

/-- Root of unity `W = root_384(1, 1)` used by `root_384`. -/
def w384 : RustM Std.U64 := field.algo.generic.root_384 1#u64 1#u64

/-- `Field::new v` succeeds and converts back to `v`. -/
def newOk (v : Std.U64) : Bool :=
  match field.Field.new v with
  | .ok x => decide (val x = ok v ∧ valRef x = ok v)
  | _ => false

/-- `root_384(a, i) = a·W^i mod P`. -/
def root384Ok (a i : Nat) : Bool :=
  match w384 with
  | .ok w => decide (field.algo.generic.root_384 (mkU .U64 a) (mkU .U64 i) = ok (mkU .U64 (a * powMod w.val i P % P)))
  | _ => false

end RSGBGold.Goldilocks.Field

namespace Benchmark.V2.Goldilocks.Field.Gold
open RSGBGold.Goldilocks.Field goldilocks_ntt

/-! ## `Field` -/

/-- `Field::new` accepts exactly the canonical values and `u64::from` returns them. -/
def gold_new_roundtrip (v : Std.U64) : Prop :=
  if v.val < P then newOk v = true
  else field.Field.new v = fail .panic

def gold_new_boundary (d : Std.U32) : Prop :=
  let v := mkU .U64 (P - 2 ^ 31 + d.val)
  if v.val < P then newOk v = true
  else field.Field.new v = fail .panic

def gold_from_u64 (v : Std.U64) : Prop :=
  field.Field.Insts.CoreConvertFromU64.from v = fe v.val

def gold_from_u64_edges (d : Std.U32) (top : Bool) : Prop :=
  let v := mkU .U64 (if top then 2 ^ 64 - 1 - d.val else P - 2 ^ 31 + d.val)
  field.Field.Insts.CoreConvertFromU64.from v = fe v.val

def gold_from_u128 (v : Std.U128) : Prop :=
  field.Field.Insts.CoreConvertFromU128.from v = fe v.val

def gold_from_u128_edges (k : Std.U64) (d : Std.U32) : Prop :=
  let v := mkU .U128 (k.val * P - 2 ^ 31 + d.val)
  field.Field.Insts.CoreConvertFromU128.from v = fe v.val

def gold_from_i32 (v : Std.I32) : Prop :=
  v.val ≠ -2147483648 → field.Field.Insts.CoreConvertFromI32.from v = fe (Int.toNat (v.val % (P : Int)))

def gold_add (a b : Std.U64) : Prop :=
  bin field.Field.Insts.CoreOpsArithAddFieldField.add a.val b.val = fe (a.val + b.val) ∧
  bin field.Field.Insts.CoreOpsArithAddAssignField.add_assign a.val b.val = fe (a.val + b.val)

def gold_add_edges (i j : Std.U8) : Prop :=
  bin field.Field.Insts.CoreOpsArithAddFieldField.add (near i) (near j) = fe (near i + near j) ∧
  bin field.Field.Insts.CoreOpsArithAddAssignField.add_assign (near i) (near j) = fe (near i + near j)

def gold_sub (a b : Std.U64) : Prop :=
  bin field.Field.Insts.CoreOpsArithSubFieldField.sub a.val b.val = fe (a.val % P + P - b.val % P) ∧
  bin field.Field.Insts.CoreOpsArithSubAssignField.sub_assign a.val b.val = fe (a.val % P + P - b.val % P)

def gold_sub_edges (i j : Std.U8) : Prop :=
  bin field.Field.Insts.CoreOpsArithSubFieldField.sub (near i) (near j) = fe (near i % P + P - near j % P) ∧
  bin field.Field.Insts.CoreOpsArithSubAssignField.sub_assign (near i) (near j) = fe (near i % P + P - near j % P)

def gold_neg (a : Std.U64) (i : Std.U8) : Prop :=
  un field.Field.Insts.CoreOpsArithNegField.neg a.val = fe (P - a.val % P) ∧
  un field.Field.Insts.CoreOpsArithNegField.neg (near i) = fe (P - near i % P)

def gold_mul (a b : Std.U64) : Prop :=
  bin field.Field.Insts.CoreOpsArithMulFieldField.mul a.val b.val = fe (a.val * b.val) ∧
  bin field.Field.Insts.CoreOpsArithMulAssignField.mul_assign a.val b.val = fe (a.val * b.val)

def gold_mul_edges (i j : Std.U8) : Prop :=
  bin field.Field.Insts.CoreOpsArithMulFieldField.mul (near i) (near j) = fe (near i * near j) ∧
  bin field.Field.Insts.CoreOpsArithMulAssignField.mul_assign (near i) (near j) = fe (near i * near j)

/-- Division by the inverse; dividing by zero gives zero (`inv(0) = 0`). -/
def gold_div (a b : Std.U64) : Prop :=
  bin field.Field.Insts.CoreOpsArithDivFieldField.div a.val b.val = fe (a.val * invP (b.val % P)) ∧
  bin field.Field.Insts.CoreOpsArithDivAssignField.div_assign a.val b.val = fe (a.val * invP (b.val % P))

def gold_div_edges (i j : Std.U8) : Prop :=
  bin field.Field.Insts.CoreOpsArithDivFieldField.div (near i) (near j) = fe (near i * invP (near j % P)) ∧
  bin field.Field.Insts.CoreOpsArithDivAssignField.div_assign (near i) (near j) = fe (near i * invP (near j % P))

/-- "Inverse of the field element, or zero." -/
def gold_inv (a : Std.U64) (i : Std.U8) : Prop :=
  un field.Field.inv a.val = fe (invP (a.val % P)) ∧
  un field.Field.inv (near i) = fe (invP (near i % P))

def gold_pow (a e : Std.U64) : Prop :=
  un (fun x => field.Field.pow x e) a.val = fe (powMod a.val e.val P)

def gold_pow_small (i : Std.U8) (e : Std.U8) : Prop :=
  un (fun x => field.Field.pow x (mkU .U64 e.val)) (near i) = fe (powMod (near i) e.val P)

/-- `root(order)` is `None` unless `order` is a nonzero divisor of `P - 1`. -/
def gold_root_none (order : Std.U64) : Prop :=
  (order.val = 0 ∨ (P - 1) % order.val ≠ 0) → field.Field.root order = ok .None

/-- For every divisor `n` of `P - 1`, `root(n)` is a primitive `n`-th root of unity. -/
def gold_root_primitive (k m : Std.U8) : Prop :=
  rootVal (mkU .U64 (divisorOf k m)) ⦃ o => rootOk o (divisorOf k m) = true ⦄

def gold_shl (a n : Std.U64) (k : Std.U8) : Prop :=
  un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x n) a.val = fe (a.val * powMod 2 n.val P) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x (mkU .U64 k.val)) a.val = fe (a.val * 2 ^ k.val) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShlAssignU64.shl_assign x (mkU .U64 k.val)) a.val = fe (a.val * 2 ^ k.val)

def gold_shr (a n : Std.U64) (k : Std.U8) : Prop :=
  un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x n) a.val = fe (a.val * powMod inv2 n.val P) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x (mkU .U64 k.val)) a.val = fe (a.val * powMod inv2 k.val P) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShrAssignU64.shr_assign x (mkU .U64 k.val)) a.val = fe (a.val * powMod inv2 k.val P)

/-- Ordering is the ordering of the canonical values. -/
def gold_cmp (a : Std.U64) (b : Std.U64) (d : Std.U8) : Prop :=
  let b' := if d.val % 4 = 0 then b.val % P else (a.val % P + d.val % 4) % P
  (do let x ← fe a.val; let y ← fe b'; field.Field.Insts.CoreCmpOrd.cmp x y) =
    ok (ordOf (a.val % P) b') ∧
  (do let x ← fe a.val; let y ← fe b'; field.Field.Insts.CoreCmpPartialOrdField.partial_cmp x y) =
    ok (.Some (ordOf (a.val % P) b'))

def gold_cmp_edges (i j : Std.U8) : Prop :=
  (do let x ← fe (near i); let y ← fe (near j); field.Field.Insts.CoreCmpOrd.cmp x y) =
    ok (ordOf (near i % P) (near j % P))

/-- Derived equality is equality of the denoted elements. -/
def gold_eq (a b : Std.U64) (i j : Std.U8) : Prop :=
  (do let x ← fe a.val; let y ← fe b.val; field.Field.Insts.CoreCmpPartialEqField.eq x y) =
    ok (decide (a.val % P = b.val % P)) ∧
  (do let x ← fe (near i); let y ← fe (near j); field.Field.Insts.CoreCmpPartialEqField.eq x y) =
    ok (decide (near i % P = near j % P))

def gold_default : Prop := field.Field.Insts.CoreDefaultDefault.default = fe 0

def gold_clone (a : Std.U64) : Prop :=
  un field.Field.Insts.CoreCloneClone.clone a.val = fe a.val

/-! ## `field::algo` (raw `u64` arithmetic) -/

def gold_algo_add (a b : Std.U64) (i j : Std.U8) : Prop :=
  (if a.val < P ∧ b.val < P then field.algo.generic.add a b = ok (mkU .U64 ((a.val + b.val) % P))
   else field.algo.generic.add a b = fail .panic) ∧
  (if near i < P ∧ near j < P then
    field.algo.generic.add (mkU .U64 (near i)) (mkU .U64 (near j)) = ok (mkU .U64 ((near i + near j) % P))
   else field.algo.generic.add (mkU .U64 (near i)) (mkU .U64 (near j)) = fail .panic)

def gold_algo_sub (a b : Std.U64) (i j : Std.U8) : Prop :=
  (if a.val < P ∧ b.val < P then field.algo.generic.sub a b = ok (mkU .U64 ((a.val + P - b.val) % P))
   else field.algo.generic.sub a b = fail .panic) ∧
  (if near i < P ∧ near j < P then
    field.algo.generic.sub (mkU .U64 (near i)) (mkU .U64 (near j)) = ok (mkU .U64 ((near i + P - near j) % P))
   else field.algo.generic.sub (mkU .U64 (near i)) (mkU .U64 (near j)) = fail .panic)

def gold_algo_mul (a b : Std.U64) (i j : Std.U8) : Prop :=
  (if a.val < P ∧ b.val < P then field.algo.generic.mul a b = ok (mkU .U64 (a.val * b.val % P))
   else field.algo.generic.mul a b = fail .panic) ∧
  (if near i < P ∧ near j < P then
    field.algo.generic.mul (mkU .U64 (near i)) (mkU .U64 (near j)) = ok (mkU .U64 (near i * near j % P))
   else field.algo.generic.mul (mkU .U64 (near i)) (mkU .U64 (near j)) = fail .panic)

/-- Montgomery product `a·b·R⁻¹ mod P` (canonical); panics iff `a·b ≥ P·2^64`. -/
def gold_mont_mul (a b : Std.U64) : Prop :=
  if a.val * b.val < P * 2 ^ 64 then field.algo.generic.mont_mul a b = ok (mkU .U64 (a.val * b.val * Rinv % P))
  else field.algo.generic.mont_mul a b = fail .panic

def gold_mont_mul_reduced (a b : Std.U64) (i j : Std.U8) : Prop :=
  field.algo.generic.mont_mul (mkU .U64 (a.val % P)) b = ok (mkU .U64 (a.val % P * b.val * Rinv % P)) ∧
  field.algo.generic.mont_mul (mkU .U64 (near i % P)) (mkU .U64 (near j)) =
    ok (mkU .U64 (near i % P * near j * Rinv % P))

def gold_mont_reduce_128 (x : Std.U128) : Prop :=
  if x.val < P * 2 ^ 64 then field.algo.generic.mont_reduce_128 x = ok (mkU .U64 (x.val * Rinv % P))
  else field.algo.generic.mont_reduce_128 x = fail .panic

def gold_mont_reduce_128_edges (d : Std.U32) (hi : Std.U64) : Prop :=
  let x := (if hi.val % 2 = 0 then P * 2 ^ 64 else (hi.val % P) * 2 ^ 64) - 2 ^ 31 + d.val
  if x < P * 2 ^ 64 then field.algo.generic.mont_reduce_128 (mkU .U128 x) = ok (mkU .U64 (x * Rinv % P))
  else field.algo.generic.mont_reduce_128 (mkU .U128 x) = fail .panic

/-- `reduce_64` reduces modulo `P` (at `n = P` only the congruence is required). -/
def gold_reduce_64 (n : Std.U64) (d : Std.U32) : Prop :=
  field.algo.generic.reduce_64 n ⦃ r => r.val % P = n.val % P ∧ (n.val ≠ P → r.val = n.val % P) ⦄ ∧
  field.algo.generic.reduce_64 (mkU .U64 (P - 2 ^ 31 + d.val)) ⦃ r =>
    r.val % P = (P - 2 ^ 31 + d.val) % P ∧ (P - 2 ^ 31 + d.val ≠ P → r.val = (P - 2 ^ 31 + d.val) % P) ⦄

def gold_reduce_128 (n : Std.U128) : Prop :=
  field.algo.generic.reduce_128 n = ok (mkU .U64 (n.val % P))

def gold_reduce_128_edges (k : Std.U64) (d : Std.U32) (m : Std.U8) : Prop :=
  let n := (k.val % 2 ^ (m.val % 129)) * P - 2 ^ 31 + d.val
  field.algo.generic.reduce_128 (mkU .U128 n) = ok (mkU .U64 (n % 2 ^ 128 % P))

/-- Montgomery exponentiation: `mont_pow(aR, e) = a^e R`; panics iff `a ≥ P`. -/
def gold_mont_pow (a e : Std.U64) : Prop :=
  if a.val < P then field.algo.generic.mont_pow a e = ok (mkU .U64 (powMod (a.val * Rinv) e.val P * Rm % P))
  else field.algo.generic.mont_pow a e = fail .panic

def gold_mont_pow_small (a : Std.U64) (e : Std.U8) : Prop :=
  field.algo.generic.mont_pow (mkU .U64 (a.val % P)) (mkU .U64 e.val) =
    ok (mkU .U64 (powMod (a.val % P * Rinv) e.val P * Rm % P))

/-- Plain modular inverse (`0` for `0`); panics iff `a ≥ P`. -/
def gold_algo_inv (a : Std.U64) (i : Std.U8) : Prop :=
  (if a.val < P then field.algo.generic.inv a = ok (mkU .U64 (invP a.val))
   else field.algo.generic.inv a = fail .panic) ∧
  (if near i < P then field.algo.generic.inv (mkU .U64 (near i)) = ok (mkU .U64 (invP (near i)))
   else field.algo.generic.inv (mkU .U64 (near i)) = fail .panic)

/-- `shift(a, n) = a·2^n mod P`; panics iff `a ≥ P`. -/
def gold_shift (a n : Std.U64) : Prop :=
  if a.val < P then field.algo.generic.shift a n = ok (mkU .U64 (a.val * powMod 2 n.val P % P))
  else field.algo.generic.shift a n = fail .panic

def gold_shift_small (a : Std.U64) (k : Std.U8) (i : Std.U8) : Prop :=
  field.algo.generic.shift (mkU .U64 (a.val % P)) (mkU .U64 k.val) = ok (mkU .U64 (a.val % P * 2 ^ k.val % P)) ∧
  field.algo.generic.shift (mkU .U64 (near i % P)) (mkU .U64 k.val) = ok (mkU .U64 (near i % P * 2 ^ k.val % P))

/-- Shifts by multiples of `96` (where `2^96 = -1`), on zero, `P - 1` and arbitrary values. -/
def gold_shift_multiples (a : Std.U64) (m : Std.U8) (z : Std.U8) : Prop :=
  let a' := [0, 1, P - 1, a.val % P].getD (z.val % 4) 0
  let n := 96 * (m.val % 8)
  field.algo.generic.shift (mkU .U64 a') (mkU .U64 n) = ok (mkU .U64 (a' * powMod 2 n P % P)) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x (mkU .U64 n)) a' = fe (a' * powMod 2 n P) ∧
  un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x (mkU .U64 n)) a' = fe (a' * powMod inv2 n P)

/-- `W = root_384(1, 1)` is a square root of `2` (hence a primitive 384-th root of unity). -/
def gold_root_384_sqrt2 : Prop :=
  w384 ⦃ w => w.val < P ∧ w.val * w.val % P = 2 ⦄

/-- `root_384(a, i) = a·W^i`; panics iff `a ≥ P` or `i ≥ 384`. -/
def gold_root_384 (a : Std.U64) (i : Std.U16) : Prop :=
  let i' := i.val % 400
  if a.val < P ∧ i' < 384 then root384Ok a.val i' = true
  else field.algo.generic.root_384 a (mkU .U64 i') = fail .panic

def gold_root_384_reduced (a : Std.U64) (i : Std.U16) : Prop :=
  let a' := a.val % P
  let i' := i.val % 384
  root384Ok a' i' = true

/-! Differential-testing probes. -/

def diff_new (v : Std.U64) (d : Std.U32) := (field.Field.new v, field.Field.new (mkU .U64 (P - 2 ^ 31 + d.val)))
def diff_val (a : Std.U64) := (do let x ← fe a.val; let v ← val x; let w ← valRef x; ok (v, w))
def diff_from_u64 (v : Std.U64) (d : Std.U32) :=
  (field.Field.Insts.CoreConvertFromU64.from v, field.Field.Insts.CoreConvertFromU64.from (mkU .U64 (P - 2 ^ 31 + d.val)))
def diff_from_u128 (v : Std.U128) := field.Field.Insts.CoreConvertFromU128.from v
def diff_from_i32 (v : Std.I32) := field.Field.Insts.CoreConvertFromI32.from v
def diff_add (a b : Std.U64) := (bin field.Field.Insts.CoreOpsArithAddFieldField.add a.val b.val,
  bin field.Field.Insts.CoreOpsArithAddAssignField.add_assign a.val b.val)
def diff_add_edges (i j : Std.U8) := (bin field.Field.Insts.CoreOpsArithAddFieldField.add (near i) (near j),
  bin field.Field.Insts.CoreOpsArithAddAssignField.add_assign (near i) (near j))
def diff_sub (a b : Std.U64) := (bin field.Field.Insts.CoreOpsArithSubFieldField.sub a.val b.val,
  bin field.Field.Insts.CoreOpsArithSubAssignField.sub_assign a.val b.val)
def diff_sub_edges (i j : Std.U8) := (bin field.Field.Insts.CoreOpsArithSubFieldField.sub (near i) (near j),
  bin field.Field.Insts.CoreOpsArithSubAssignField.sub_assign (near i) (near j))
def diff_neg (a : Std.U64) (i : Std.U8) := (un field.Field.Insts.CoreOpsArithNegField.neg a.val,
  un field.Field.Insts.CoreOpsArithNegField.neg (near i))
def diff_mul (a b : Std.U64) := (bin field.Field.Insts.CoreOpsArithMulFieldField.mul a.val b.val,
  bin field.Field.Insts.CoreOpsArithMulAssignField.mul_assign a.val b.val)
def diff_mul_edges (i j : Std.U8) := (bin field.Field.Insts.CoreOpsArithMulFieldField.mul (near i) (near j),
  bin field.Field.Insts.CoreOpsArithMulAssignField.mul_assign (near i) (near j))
def diff_div (a b : Std.U64) := (bin field.Field.Insts.CoreOpsArithDivFieldField.div a.val b.val,
  bin field.Field.Insts.CoreOpsArithDivAssignField.div_assign a.val b.val)
def diff_div_edges (i j : Std.U8) := (bin field.Field.Insts.CoreOpsArithDivFieldField.div (near i) (near j),
  bin field.Field.Insts.CoreOpsArithDivAssignField.div_assign (near i) (near j))
def diff_inv (a : Std.U64) (i : Std.U8) := (un field.Field.inv a.val, un field.Field.inv (near i))
def diff_pow (a e : Std.U64) := un (fun x => field.Field.pow x e) a.val
def diff_pow_small (i e : Std.U8) := un (fun x => field.Field.pow x (mkU .U64 e.val)) (near i)
def diff_root (order : Std.U64) := field.Field.root order
def diff_root_div (k m : Std.U8) := field.Field.root (mkU .U64 (divisorOf k m))
def diff_shl (a n : Std.U64) (k : Std.U8) := (un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x n) a.val,
  un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x (mkU .U64 k.val)) a.val,
  un (fun x => field.Field.Insts.CoreOpsBitShlAssignU64.shl_assign x (mkU .U64 k.val)) a.val)
def diff_shr (a n : Std.U64) (k : Std.U8) := (un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x n) a.val,
  un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x (mkU .U64 k.val)) a.val,
  un (fun x => field.Field.Insts.CoreOpsBitShrAssignU64.shr_assign x (mkU .U64 k.val)) a.val)
def diff_cmp (a : Std.U64) (b : Std.U64) (d : Std.U8) :=
  let b' := if d.val % 4 = 0 then b.val % P else (a.val % P + d.val % 4) % P
  (do let x ← fe a.val; let y ← fe b'; let o ← field.Field.Insts.CoreCmpOrd.cmp x y
      let o2 ← field.Field.Insts.CoreCmpPartialOrdField.partial_cmp x y
      let e ← field.Field.Insts.CoreCmpPartialEqField.eq x y; ok (o, o2, e))
def diff_cmp_edges (i j : Std.U8) :=
  (do let x ← fe (near i); let y ← fe (near j); let o ← field.Field.Insts.CoreCmpOrd.cmp x y
      let e ← field.Field.Insts.CoreCmpPartialEqField.eq x y; ok (o, e))
def diff_default (u : Std.U8) := (field.Field.Insts.CoreDefaultDefault.default, un field.Field.Insts.CoreCloneClone.clone u.val)
def diff_algo_add (a b : Std.U64) (i j : Std.U8) := (field.algo.generic.add a b,
  field.algo.generic.add (mkU .U64 (near i)) (mkU .U64 (near j)))
def diff_algo_sub (a b : Std.U64) (i j : Std.U8) := (field.algo.generic.sub a b,
  field.algo.generic.sub (mkU .U64 (near i)) (mkU .U64 (near j)))
def diff_algo_mul (a b : Std.U64) (i j : Std.U8) := (field.algo.generic.mul a b,
  field.algo.generic.mul (mkU .U64 (near i)) (mkU .U64 (near j)))
def diff_mont_mul (a b : Std.U64) := (field.algo.generic.mont_mul a b, field.algo.generic.mont_mul (mkU .U64 (a.val % P)) b)
def diff_mont_reduce_128 (x : Std.U128) := field.algo.generic.mont_reduce_128 x
def diff_mont_reduce_128_edges (d : Std.U32) (hi : Std.U64) :=
  field.algo.generic.mont_reduce_128 (mkU .U128 ((if hi.val % 2 = 0 then P * 2 ^ 64 else (hi.val % P) * 2 ^ 64) - 2 ^ 31 + d.val))
def diff_reduce_64 (n : Std.U64) (d : Std.U32) := (field.algo.generic.reduce_64 n,
  field.algo.generic.reduce_64 (mkU .U64 (P - 2 ^ 31 + d.val)))
def diff_reduce_128 (n : Std.U128) := field.algo.generic.reduce_128 n
def diff_reduce_128_edges (k : Std.U64) (d : Std.U32) (m : Std.U8) :=
  field.algo.generic.reduce_128 (mkU .U128 ((k.val % 2 ^ (m.val % 129)) * P - 2 ^ 31 + d.val))
def diff_mont_pow (a e : Std.U64) := (field.algo.generic.mont_pow a e, field.algo.generic.mont_pow (mkU .U64 (a.val % P)) e)
def diff_algo_inv (a : Std.U64) (i : Std.U8) := (field.algo.generic.inv a, field.algo.generic.inv (mkU .U64 (near i)))
def diff_shift (a n : Std.U64) := (field.algo.generic.shift a n, field.algo.generic.shift (mkU .U64 (a.val % P)) n)
def diff_shift_small (a : Std.U64) (k : Std.U8) := field.algo.generic.shift (mkU .U64 (a.val % P)) (mkU .U64 k.val)
def diff_root_384 (a : Std.U64) (i : Std.U16) := (field.algo.generic.root_384 a (mkU .U64 (i.val % 400)),
  field.algo.generic.root_384 (mkU .U64 (a.val % P)) (mkU .U64 (i.val % 384)))

def diff_shift_multiples (a : Std.U64) (m : Std.U8) (z : Std.U8) :=
  let a' := [0, 1, P - 1, a.val % P].getD (z.val % 4) 0
  (field.algo.generic.shift (mkU .U64 a') (mkU .U64 (96 * (m.val % 8))),
   un (fun x => field.Field.Insts.CoreOpsBitShlU64Field.shl x (mkU .U64 (96 * (m.val % 8)))) a',
   un (fun x => field.Field.Insts.CoreOpsBitShrU64Field.shr x (mkU .U64 (96 * (m.val % 8)))) a')

end Benchmark.V2.Goldilocks.Field.Gold
