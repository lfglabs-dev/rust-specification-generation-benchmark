import Benchmark.V2.Prelude
import AtoiRadix.Extraction

/-! Hidden gold specification for target `atoi/radix`.

API (crate `atoi` 3.1.1, builtin integer impls) for `T ∈ {u8, i8, i16, u16, i32, u64}`:
`FromRadix10::from_radix_10`, `FromRadix10Checked::from_radix_10_checked`,
`FromRadix16::from_radix_16`, `FromRadix16Checked::from_radix_16_checked`,
`FromRadix10Signed::from_radix_10_signed`,
`FromRadix10SignedChecked::from_radix_10_signed_checked`, and `atoi::<T>`.

Contract. Each parser reads the longest prefix of ASCII digits (radix 16: `0-9`,
`a-f`, `A-F`; the signed parsers first accept one optional `+`/`-`) and returns
`(value, index after the parsed number)`. Leading zeros are allowed, trailing
bytes are ignored, no digit gives value 0. Checked variants return `None`
exactly when the mathematical value is outside `T`'s range (including `MIN`
handled exactly, and arbitrarily many leading zeros), and still consume the whole
digit run; they never panic. The unchecked variants return the exact value when it
fits and otherwise overflow, i.e. panic under Rust debug semantics. `atoi`
returns `Some(v)` iff the input starts with an optionally signed digit run whose
value fits, `None` if it starts with no digit/sign or overflows.

Freedom: the number of digits parsed on the fast unchecked path (the private
`NUM_SAFE_DIGITS_*` constants) is an implementation detail; a lone sign without
digits yields value 0 but its consumed count (0 or 1) is not specified by the
docs (and `atoi(b"-")` returning `Some(0)` contradicts the `atoi` doc, so it is
left out of the gold spec). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM atoi RSGB

namespace RSGBGold.Atoi.Radix

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

def ch (c : Char) : Std.U8 := mkU .U8 c.toNat

def decV (b : Std.U8) : Option Nat := if 48 ≤ b.val ∧ b.val ≤ 57 then some (b.val - 48) else none

def hexV (b : Std.U8) : Option Nat :=
  if 48 ≤ b.val ∧ b.val ≤ 57 then some (b.val - 48)
  else if 65 ≤ b.val ∧ b.val ≤ 70 then some (b.val - 55)
  else if 97 ≤ b.val ∧ b.val ≤ 102 then some (b.val - 87)
  else none

/-- Digit values of the longest prefix accepted by `dv`. -/
def run (dv : Std.U8 → Option Nat) : List Std.U8 → List Nat
  | [] => []
  | b :: l => match dv b with
    | some d => d :: run dv l
    | none => []

def value (base : Nat) (ds : List Nat) : Nat := ds.foldl (fun a d => a * base + d) 0

/-- Unsigned model: `(value, digits consumed)`. -/
def model (base : Nat) (dv : Std.U8 → Option Nat) (t : List Std.U8) : Int × Nat :=
  let ds := run dv t; ((value base ds : Nat), ds.length)

/-- Signed model: `(value, consumed, sign present)`. -/
def smodel (t : List Std.U8) : Int × Nat × Bool :=
  match t with
  | b :: rest =>
    if b.val = 43 then let ds := run decV rest; ((value 10 ds : Int), ds.length + 1, true)
    else if b.val = 45 then let ds := run decV rest; (-(value 10 ds : Int), ds.length + 1, true)
    else let ds := run decV t; ((value 10 ds : Int), ds.length, false)
  | [] => (0, 0, false)

/-- Unchecked result: exact `(v, n)` if `v ∈ [lo, hi]`, a panic otherwise. -/
def okPlain (lo hi : Int) (r : RustM (Int × Nat)) (v : Int) (n : Nat) : Bool :=
  match r with
  | .ok (a, k) => lo ≤ v && v ≤ hi && a == v && k == n
  | .fail .panic => !(lo ≤ v && v ≤ hi)
  | _ => false

/-- Checked result: `(Some v | None, n)`, never a panic. -/
def okChecked (lo hi : Int) (r : RustM (Option Int × Nat)) (v : Int) (n : Nat) : Bool :=
  match r with
  | .ok (a, k) => k == n && a == (if lo ≤ v && v ≤ hi then some v else none)
  | _ => false

/-- Signed variants: as above, but a lone sign may count as consumed or not. -/
def okSPlain (lo hi : Int) (r : RustM (Int × Nat)) (t : List Std.U8) : Bool :=
  let (v, n, sg) := smodel t
  if sg && n == 1 then
    match r with | .ok (a, k) => a == 0 && (k == 0 || k == 1) | _ => false
  else okPlain lo hi r v n

def okSChecked (lo hi : Int) (r : RustM (Option Int × Nat)) (t : List Std.U8) : Bool :=
  let (v, n, sg) := smodel t
  if sg && n == 1 then
    match r with | .ok (a, k) => a == some 0 && (k == 0 || k == 1) | _ => false
  else okChecked lo hi r v n

/-- `atoi`: `Some v` iff a (signed) digit run that fits; `None` without digits or on overflow. -/
def okAtoi (lo hi : Int) (r : RustM (Option Int)) (t : List Std.U8) : Bool :=
  let (v, n, sg) := smodel t
  if sg && n == 1 then true
  else match r with
    | .ok a => a == (if n != 0 && lo ≤ v && v ≤ hi then some v else none)
    | _ => false

def optI {α} (f : α → Int) : core.option.Option α → Option Int
  | .Some x => some (f x)
  | .None => none

/-! Text generators. -/

def decDigits (n : Nat) : List Std.U8 := (Nat.toDigits 10 n).map ch

/-- Hex digits of `n`, letter case chosen by the bits of `mask`. -/
def hexDigits (n : Nat) (mask : Nat) : List Std.U8 :=
  ((Nat.toDigits 16 n).zipIdx).map fun (c, i) =>
    if c.isDigit then ch c else if (mask >>> (i % 16)) % 2 = 1 then ch c.toUpper else ch c

/-- Magnitude near interesting points of a `w`-bit range: arbitrary, around the
maximum (`2^w - 1`) / `2^(w-1)`, one digit too many, one digit fewer. -/
def mag (base w : Nat) (x : Nat) (d : Nat) : Nat :=
  match d % 6 with
  | 0 => x % 2 ^ (w + 1)
  | 1 => 2 ^ w + (d / 6) % 9 - 4
  | 2 => 2 ^ (w - 1) + (d / 6) % 9 - 4
  | 3 => (x % 2 ^ w) * base + (d / 6) % base
  | 4 => (x % 2 ^ w) / base
  | _ => x % 2 ^ w

/-- Leading zeros: none usually, sometimes many (beyond any fast-path digit count). -/
def zeros (z : Nat) : List Std.U8 := List.replicate (if z % 3 = 0 then z / 3 % 45 else 0) (ch '0')

def decText (w x d z : Nat) (sfx : List Std.U8) : List Std.U8 := zeros z ++ decDigits (mag 10 w x d) ++ sfx
def hexText (w x d z : Nat) (sfx : List Std.U8) : List Std.U8 := zeros z ++ hexDigits (mag 16 w x d) x ++ sfx

/-- Optionally signed decimal text (sign `+`, `-` or none; sometimes a lone sign). -/
def sText (w x d z s : Nat) (sfx : List Std.U8) : List Std.U8 :=
  let body := if s % 11 = 10 then sfx else decText w x d z sfx
  match s % 4 with
  | 0 => body
  | 1 => ch '+' :: body
  | _ => ch '-' :: body

end RSGBGold.Atoi.Radix

namespace Benchmark.V2.Atoi.Radix.Gold
open RSGBGold.Atoi.Radix

/-! ## `u8` -/
def r10_u8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10c_u8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r16_u8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r16c_u8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r10s_u8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10sc_u8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U8.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def atoi_u8 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi U8.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (fun v => (v.val : Int)) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `u8::MAX`. -/
def gold_u8_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^8 - 1) (r10_u8 (decText 8 x.val d.val z.val sfx)) (model 10 decV (decText 8 x.val d.val z.val sfx)).1 (model 10 decV (decText 8 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^8 - 1) (r10_u8 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_u8_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^8 - 1) (r10c_u8 (decText 8 x.val d.val z.val sfx)) (model 10 decV (decText 8 x.val d.val z.val sfx)).1 (model 10 decV (decText 8 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^8 - 1) (r10c_u8 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `u8::MAX`. -/
def gold_u8_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^8 - 1) (r16_u8 (hexText 8 x.val d.val z.val sfx)) (model 16 hexV (hexText 8 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 8 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^8 - 1) (r16_u8 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_u8_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^8 - 1) (r16c_u8 (hexText 8 x.val d.val z.val sfx)) (model 16 hexV (hexText 8 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 8 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^8 - 1) (r16c_u8 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_u8_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain 0 ((2:Int)^8 - 1) (r10s_u8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okSPlain 0 ((2:Int)^8 - 1) (r10s_u8 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_u8_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked 0 ((2:Int)^8 - 1) (r10sc_u8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okSChecked 0 ((2:Int)^8 - 1) (r10sc_u8 raw) raw = true

/-- `atoi::<u8>`. -/
def gold_u8_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi 0 ((2:Int)^8 - 1) (atoi_u8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okAtoi 0 ((2:Int)^8 - 1) (atoi_u8 raw) raw = true

/-! ## `i8` -/
def r10_i8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((·.val) v, n.val)
def r10c_i8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (·.val) v, n.val)
def r16_i8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((·.val) v, n.val)
def r16c_i8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (·.val) v, n.val)
def r10s_i8 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((·.val) v, n.val)
def r10sc_i8 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I8.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (·.val) v, n.val)
def atoi_i8 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi I8.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (·.val) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `i8::MAX`. -/
def gold_i8_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r10_i8 (decText 8 x.val d.val z.val sfx)) (model 10 decV (decText 8 x.val d.val z.val sfx)).1 (model 10 decV (decText 8 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r10_i8 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_i8_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r10c_i8 (decText 8 x.val d.val z.val sfx)) (model 10 decV (decText 8 x.val d.val z.val sfx)).1 (model 10 decV (decText 8 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r10c_i8 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `i8::MAX`. -/
def gold_i8_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r16_i8 (hexText 8 x.val d.val z.val sfx)) (model 16 hexV (hexText 8 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 8 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r16_i8 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_i8_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r16c_i8 (hexText 8 x.val d.val z.val sfx)) (model 16 hexV (hexText 8 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 8 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r16c_i8 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_i8_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r10s_i8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okSPlain (-(2:Int)^7) ((2:Int)^7 - 1) (r10s_i8 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_i8_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r10sc_i8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okSChecked (-(2:Int)^7) ((2:Int)^7 - 1) (r10sc_i8 raw) raw = true

/-- `atoi::<i8>`. -/
def gold_i8_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi (-(2:Int)^7) ((2:Int)^7 - 1) (atoi_i8 (sText 8 x.val d.val z.val s.val sfx)) (sText 8 x.val d.val z.val s.val sfx) = true ∧
  okAtoi (-(2:Int)^7) ((2:Int)^7 - 1) (atoi_i8 raw) raw = true

/-! ## `i16` -/
def r10_i16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((·.val) v, n.val)
def r10c_i16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (·.val) v, n.val)
def r16_i16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((·.val) v, n.val)
def r16c_i16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (·.val) v, n.val)
def r10s_i16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((·.val) v, n.val)
def r10sc_i16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I16.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (·.val) v, n.val)
def atoi_i16 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi I16.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (·.val) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `i16::MAX`. -/
def gold_i16_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r10_i16 (decText 16 x.val d.val z.val sfx)) (model 10 decV (decText 16 x.val d.val z.val sfx)).1 (model 10 decV (decText 16 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r10_i16 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_i16_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r10c_i16 (decText 16 x.val d.val z.val sfx)) (model 10 decV (decText 16 x.val d.val z.val sfx)).1 (model 10 decV (decText 16 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r10c_i16 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `i16::MAX`. -/
def gold_i16_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r16_i16 (hexText 16 x.val d.val z.val sfx)) (model 16 hexV (hexText 16 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 16 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r16_i16 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_i16_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r16c_i16 (hexText 16 x.val d.val z.val sfx)) (model 16 hexV (hexText 16 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 16 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r16c_i16 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_i16_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r10s_i16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okSPlain (-(2:Int)^15) ((2:Int)^15 - 1) (r10s_i16 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_i16_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r10sc_i16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okSChecked (-(2:Int)^15) ((2:Int)^15 - 1) (r10sc_i16 raw) raw = true

/-- `atoi::<i16>`. -/
def gold_i16_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi (-(2:Int)^15) ((2:Int)^15 - 1) (atoi_i16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okAtoi (-(2:Int)^15) ((2:Int)^15 - 1) (atoi_i16 raw) raw = true

/-! ## `u16` -/
def r10_u16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10c_u16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r16_u16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r16c_u16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r10s_u16 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10sc_u16 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U16.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def atoi_u16 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi U16.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (fun v => (v.val : Int)) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `u16::MAX`. -/
def gold_u16_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^16 - 1) (r10_u16 (decText 16 x.val d.val z.val sfx)) (model 10 decV (decText 16 x.val d.val z.val sfx)).1 (model 10 decV (decText 16 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^16 - 1) (r10_u16 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_u16_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^16 - 1) (r10c_u16 (decText 16 x.val d.val z.val sfx)) (model 10 decV (decText 16 x.val d.val z.val sfx)).1 (model 10 decV (decText 16 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^16 - 1) (r10c_u16 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `u16::MAX`. -/
def gold_u16_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^16 - 1) (r16_u16 (hexText 16 x.val d.val z.val sfx)) (model 16 hexV (hexText 16 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 16 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^16 - 1) (r16_u16 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_u16_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^16 - 1) (r16c_u16 (hexText 16 x.val d.val z.val sfx)) (model 16 hexV (hexText 16 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 16 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^16 - 1) (r16c_u16 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_u16_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain 0 ((2:Int)^16 - 1) (r10s_u16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okSPlain 0 ((2:Int)^16 - 1) (r10s_u16 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_u16_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked 0 ((2:Int)^16 - 1) (r10sc_u16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okSChecked 0 ((2:Int)^16 - 1) (r10sc_u16 raw) raw = true

/-- `atoi::<u16>`. -/
def gold_u16_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi 0 ((2:Int)^16 - 1) (atoi_u16 (sText 16 x.val d.val z.val s.val sfx)) (sText 16 x.val d.val z.val s.val sfx) = true ∧
  okAtoi 0 ((2:Int)^16 - 1) (atoi_u16 raw) raw = true

/-! ## `i32` -/
def r10_i32 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((·.val) v, n.val)
def r10c_i32 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (·.val) v, n.val)
def r16_i32 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((·.val) v, n.val)
def r16c_i32 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (·.val) v, n.val)
def r10s_i32 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((·.val) v, n.val)
def r10sc_i32 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← I32.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (·.val) v, n.val)
def atoi_i32 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi I32.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (·.val) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `i32::MAX`. -/
def gold_i32_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r10_i32 (decText 32 x.val d.val z.val sfx)) (model 10 decV (decText 32 x.val d.val z.val sfx)).1 (model 10 decV (decText 32 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r10_i32 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_i32_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r10c_i32 (decText 32 x.val d.val z.val sfx)) (model 10 decV (decText 32 x.val d.val z.val sfx)).1 (model 10 decV (decText 32 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r10c_i32 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `i32::MAX`. -/
def gold_i32_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r16_i32 (hexText 32 x.val d.val z.val sfx)) (model 16 hexV (hexText 32 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 32 x.val d.val z.val sfx)).2 = true ∧
  okPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r16_i32 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_i32_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r16c_i32 (hexText 32 x.val d.val z.val sfx)) (model 16 hexV (hexText 32 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 32 x.val d.val z.val sfx)).2 = true ∧
  okChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r16c_i32 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_i32_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r10s_i32 (sText 32 x.val d.val z.val s.val sfx)) (sText 32 x.val d.val z.val s.val sfx) = true ∧
  okSPlain (-(2:Int)^31) ((2:Int)^31 - 1) (r10s_i32 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_i32_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r10sc_i32 (sText 32 x.val d.val z.val s.val sfx)) (sText 32 x.val d.val z.val s.val sfx) = true ∧
  okSChecked (-(2:Int)^31) ((2:Int)^31 - 1) (r10sc_i32 raw) raw = true

/-- `atoi::<i32>`. -/
def gold_i32_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi (-(2:Int)^31) ((2:Int)^31 - 1) (atoi_i32 (sText 32 x.val d.val z.val s.val sfx)) (sText 32 x.val d.val z.val s.val sfx) = true ∧
  okAtoi (-(2:Int)^31) ((2:Int)^31 - 1) (atoi_i32 raw) raw = true

/-! ## `u64` -/
def r10_u64 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix10.from_radix_10 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10c_u64 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix10Checked.from_radix_10_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r16_u64 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix16.from_radix_16 (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r16c_u64 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix16Checked.from_radix_16_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def r10s_u64 (t : List Std.U8) : RustM (Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix10Signed.from_radix_10_signed (toSlice t); ok ((fun v => (v.val : Int)) v, n.val)
def r10sc_u64 (t : List Std.U8) : RustM (Option Int × Nat) := do
  let (v, n) ← U64.Insts.AtoiFromRadix10SignedChecked.from_radix_10_signed_checked (toSlice t); ok (optI (fun v => (v.val : Int)) v, n.val)
def atoi_u64 (t : List Std.U8) : RustM (Option Int) := do
  let v ← atoi U64.Insts.AtoiFromRadix10SignedChecked (toSlice t); ok (optI (fun v => (v.val : Int)) v)

/-- `from_radix_10`: exact value and digit count; panics (overflow) iff the value exceeds `u64::MAX`. -/
def gold_u64_radix_10 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^64 - 1) (r10_u64 (decText 64 x.val d.val z.val sfx)) (model 10 decV (decText 64 x.val d.val z.val sfx)).1 (model 10 decV (decText 64 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^64 - 1) (r10_u64 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_10_checked`: `None` exactly on overflow, whole digit run consumed, never panics. -/
def gold_u64_radix_10_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^64 - 1) (r10c_u64 (decText 64 x.val d.val z.val sfx)) (model 10 decV (decText 64 x.val d.val z.val sfx)).1 (model 10 decV (decText 64 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^64 - 1) (r10c_u64 raw) (model 10 decV raw).1 (model 10 decV raw).2 = true

/-- `from_radix_16`: hex digits in either case; panics iff the value exceeds `u64::MAX`. -/
def gold_u64_radix_16 (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okPlain 0 ((2:Int)^64 - 1) (r16_u64 (hexText 64 x.val d.val z.val sfx)) (model 16 hexV (hexText 64 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 64 x.val d.val z.val sfx)).2 = true ∧
  okPlain 0 ((2:Int)^64 - 1) (r16_u64 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

def gold_u64_radix_16_checked (x : Std.U128) (d z : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okChecked 0 ((2:Int)^64 - 1) (r16c_u64 (hexText 64 x.val d.val z.val sfx)) (model 16 hexV (hexText 64 x.val d.val z.val sfx)).1 (model 16 hexV (hexText 64 x.val d.val z.val sfx)).2 = true ∧
  okChecked 0 ((2:Int)^64 - 1) (r16c_u64 raw) (model 16 hexV raw).1 (model 16 hexV raw).2 = true

/-- `from_radix_10_signed`: optional sign; exact value in range, panic on over/underflow. -/
def gold_u64_radix_10_signed (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSPlain 0 ((2:Int)^64 - 1) (r10s_u64 (sText 64 x.val d.val z.val s.val sfx)) (sText 64 x.val d.val z.val s.val sfx) = true ∧
  okSPlain 0 ((2:Int)^64 - 1) (r10s_u64 raw) raw = true

/-- `from_radix_10_signed_checked`: `None` exactly when out of range (MIN included), never panics. -/
def gold_u64_radix_10_signed_checked (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okSChecked 0 ((2:Int)^64 - 1) (r10sc_u64 (sText 64 x.val d.val z.val s.val sfx)) (sText 64 x.val d.val z.val s.val sfx) = true ∧
  okSChecked 0 ((2:Int)^64 - 1) (r10sc_u64 raw) raw = true

/-- `atoi::<u64>`. -/
def gold_u64_atoi (x : Std.U128) (d z s : Std.U8) (sfx raw : List Std.U8) : Prop :=
  okAtoi 0 ((2:Int)^64 - 1) (atoi_u64 (sText 64 x.val d.val z.val s.val sfx)) (sText 64 x.val d.val z.val s.val sfx) = true ∧
  okAtoi 0 ((2:Int)^64 - 1) (atoi_u64 raw) raw = true

/-! ## Documented examples -/

def str (s : String) : List Std.U8 := s.toUTF8.toList.map (fun b => mkU .U8 b.toNat)

def gold_doc_examples : Prop :=
  r10_u8 (str "42 is the answer") = ok (42, 2) ∧
  r10_i32 (str "-42") = ok (0, 0) ∧
  r10_u64 (str "0042") = ok (42, 4) ∧
  r10c_u8 (str "256") = ok (none, 3) ∧
  r10c_u8 (str "1000") = ok (none, 4) ∧
  r10c_u8 (str "25Blub") = ok (some 25, 2) ∧
  r16c_u8 (str "ff") = ok (some 255, 2) ∧
  r16c_u8 (str "FF") = ok (some 255, 2) ∧
  r16c_u8 (str "100") = ok (none, 3) ∧
  r16_u16 (str "aB9z") = ok (0xAB9, 3) ∧
  r10sc_i16 (str "-32768") = ok (some (-32768), 6) ∧
  r10sc_i16 (str "-32769") = ok (none, 6) ∧
  r10sc_i8 (str "+127") = ok (some 127, 4) ∧
  r10sc_i8 (str "-128!") = ok (some (-128), 4) ∧
  atoi_i32 (str "-42") = ok (some (-42)) ∧
  atoi_u8 (str "256") = ok none ∧
  atoi_u8 (str "Sadly") = ok none

/-! Differential-testing probes. -/

def diff_u8_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_u8 (decText 8 x.val d.val z.val sfx)
def diff_u8_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_u8 (decText 8 x.val d.val z.val sfx)
def diff_u8_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_u8 (hexText 8 x.val d.val z.val sfx)
def diff_u8_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_u8 (hexText 8 x.val d.val z.val sfx)
def diff_u8_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_u8 (sText 8 x.val d.val z.val s.val sfx)
def diff_u8_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_u8 (sText 8 x.val d.val z.val s.val sfx)
def diff_u8_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_u8 (sText 8 x.val d.val z.val s.val sfx)
def diff_i8_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_i8 (decText 8 x.val d.val z.val sfx)
def diff_i8_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_i8 (decText 8 x.val d.val z.val sfx)
def diff_i8_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_i8 (hexText 8 x.val d.val z.val sfx)
def diff_i8_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_i8 (hexText 8 x.val d.val z.val sfx)
def diff_i8_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_i8 (sText 8 x.val d.val z.val s.val sfx)
def diff_i8_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_i8 (sText 8 x.val d.val z.val s.val sfx)
def diff_i8_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_i8 (sText 8 x.val d.val z.val s.val sfx)
def diff_i16_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_i16 (decText 16 x.val d.val z.val sfx)
def diff_i16_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_i16 (decText 16 x.val d.val z.val sfx)
def diff_i16_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_i16 (hexText 16 x.val d.val z.val sfx)
def diff_i16_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_i16 (hexText 16 x.val d.val z.val sfx)
def diff_i16_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_i16 (sText 16 x.val d.val z.val s.val sfx)
def diff_i16_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_i16 (sText 16 x.val d.val z.val s.val sfx)
def diff_i16_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_i16 (sText 16 x.val d.val z.val s.val sfx)
def diff_u16_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_u16 (decText 16 x.val d.val z.val sfx)
def diff_u16_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_u16 (decText 16 x.val d.val z.val sfx)
def diff_u16_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_u16 (hexText 16 x.val d.val z.val sfx)
def diff_u16_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_u16 (hexText 16 x.val d.val z.val sfx)
def diff_u16_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_u16 (sText 16 x.val d.val z.val s.val sfx)
def diff_u16_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_u16 (sText 16 x.val d.val z.val s.val sfx)
def diff_u16_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_u16 (sText 16 x.val d.val z.val s.val sfx)
def diff_i32_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_i32 (decText 32 x.val d.val z.val sfx)
def diff_i32_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_i32 (decText 32 x.val d.val z.val sfx)
def diff_i32_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_i32 (hexText 32 x.val d.val z.val sfx)
def diff_i32_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_i32 (hexText 32 x.val d.val z.val sfx)
def diff_i32_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_i32 (sText 32 x.val d.val z.val s.val sfx)
def diff_i32_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_i32 (sText 32 x.val d.val z.val s.val sfx)
def diff_i32_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_i32 (sText 32 x.val d.val z.val s.val sfx)
def diff_u64_r10 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10_u64 (decText 64 x.val d.val z.val sfx)
def diff_u64_r10c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r10c_u64 (decText 64 x.val d.val z.val sfx)
def diff_u64_r16 (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16_u64 (hexText 64 x.val d.val z.val sfx)
def diff_u64_r16c (x : Std.U128) (d z : Std.U8) (sfx : List Std.U8) := r16c_u64 (hexText 64 x.val d.val z.val sfx)
def diff_u64_r10s (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10s_u64 (sText 64 x.val d.val z.val s.val sfx)
def diff_u64_r10sc (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := r10sc_u64 (sText 64 x.val d.val z.val s.val sfx)
def diff_u64_atoi (x : Std.U128) (d z s : Std.U8) (sfx : List Std.U8) := atoi_u64 (sText 64 x.val d.val z.val s.val sfx)

end Benchmark.V2.Atoi.Radix.Gold
