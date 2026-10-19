import Benchmark.V2.Prelude
import JiffCivil.Extraction

/-! Hidden gold specification for target `jiff/civil`.

API: the civil time-of-day type `jiff_core::civil::Time` and its second /
nanosecond-of-day companions `TimeSecond`, `TimeNanosecond`:
constructors (`Time::new`, `civil::time`, `with_subsec_parts`,
`with_subsec_nanosecond`, `TimeSecond::new`/`constant`, `TimeNanosecond::new`),
accessors (`hour`, `minute`, `second`, `subsec_nanosecond`, `millisecond`,
`microsecond`, `nanosecond`, `TimeSecond::second`, `TimeNanosecond::nanosecond`),
conversions (`to_second`, `to_nanosecond`, `to_time`), the derived `Ord`/`Eq`
and `Time::on`.

Contract: the valid clock values are exactly `00:00:00.000000000 ..=
23:59:59.999999999`; constructors return `Err` (never panic) iff a component is
out of its range (`civil::time`, `TimeSecond::constant` and `Time::on` panic
instead); conversions are exact, mutually inverse and order preserving. Which
`RangeError` is reported when several components are invalid is not specified.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM jiff_core RSGB

namespace RSGBGold.Jiff.Civil

abbrev T := civil.time.Time
abbrev R (α : Type) := core.result.Result α bounds.RangeError

/-- Fold an unsigned draw into `0..n`, mapping the top draws onto the upper boundary. -/
def fold (x bits n : Nat) : Nat :=
  if 2 ^ bits - 4 ≤ x then n - 1 - (2 ^ bits - 1 - x) else x % n

def vt (h m s : Std.U8) (ns : Std.U32) : T :=
  { hour := mkI .I8 (fold h.val 8 24), minute := mkI .I8 (fold m.val 8 60),
    second := mkI .I8 (fold s.val 8 60),
    subsec_nanosecond := mkI .I32 (fold ns.val 32 1000000000) }

def hmsOk (h m s : Int) : Bool := 0 ≤ h ∧ h ≤ 23 ∧ 0 ≤ m ∧ m ≤ 59 ∧ 0 ≤ s ∧ s ≤ 59
def nsOk (n : Int) : Bool := 0 ≤ n ∧ n ≤ 999999999
def partOk (n : Int) : Bool := 0 ≤ n ∧ n ≤ 999

def isOk {α} : R α → Bool
  | .Ok _ => true
  | .Err _ => false

def okVal {α} : R α → Option α
  | .Ok v => some v
  | .Err _ => none

def nanosOf (t : T) : Int :=
  t.hour.val * 3600000000000 + t.minute.val * 60000000000 + t.second.val * 1000000000 +
    t.subsec_nanosecond.val

def secsOf (t : T) : Int := t.hour.val * 3600 + t.minute.val * 60 + t.second.val

def fields (t : T) : Int × Int × Int × Int :=
  (t.hour.val, t.minute.val, t.second.val, t.subsec_nanosecond.val)

def ordOf (a b : Int) : core.cmp.Ordering :=
  if a < b then .Less else if a = b then .Equal else .Greater

def toNs (t : T) := civil.time.Time.to_nanosecond t
def toS (t : T) := civil.time.Time.to_second t

/-- Gregorian calendar model (independent of the crate). -/
def leap (y : Int) : Bool := (y % 4 = 0 ∧ y % 100 ≠ 0) ∨ y % 400 = 0
def dim (y m : Int) : Int :=
  if m = 2 then (if leap y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31
def dateOk (y m d : Int) : Bool :=
  -9999 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ dim y m

/-- Raw draws folded into near-valid dates (months 0..13, days 0..32, years ±10000). -/
def yr (y : Std.I16) : Std.I16 := mkI .I16 (y.val % 10001)
def mo (m : Std.U8) : Std.I8 := mkI .I8 (m.val % 14)
def dy (d : Std.U8) : Std.I8 := mkI .I8 (d.val % 33)

/-- Near-range draws for components: `v ↦ v mod (n + 3) - 1` covers `-1 ..= n + 1`. -/
def near8 (x : Std.U8) (n : Nat) : Std.I8 := mkI .I8 ((x.val % (n + 3) : Int) - 1)
def near16 (x : Std.U16) (n : Nat) : Std.I16 := mkI .I16 ((x.val % (n + 3) : Int) - 1)

def tnsChk (x : Std.I64) : Option (Std.I64 × T × Std.I64) → Bool
  | some (k, t, k2) => k == x && k2 == x && nanosOf t == x.val &&
      hmsOk t.hour.val t.minute.val t.second.val && nsOk t.subsec_nanosecond.val
  | none => false

def tsChk (x : Std.I32) : Option (Std.I32 × T × Std.I32) → Bool
  | some (k, t, k2) => k == x && k2 == x && secsOf t == x.val && t.subsec_nanosecond.val == 0 &&
      hmsOk t.hour.val t.minute.val t.second.val
  | none => false

def ordB : core.cmp.Ordering → Nat
  | .Less => 0 | .Equal => 1 | .Greater => 2

/-- `o` (Time order) = `o2` (nanosecond order); the second order is weakly monotone and exact. -/
def monoChk (o o2 o3 : core.cmp.Ordering) (le : Bool) : Bool :=
  ordB o == ordB o2 && (ordB o != 0 || ordB o3 != 2) && ((ordB o3 != 2) == le)

end RSGBGold.Jiff.Civil

namespace Benchmark.V2.Jiff.Civil.Gold
open RSGBGold.Jiff.Civil

/-! ## `Time::new` / `civil::time`: exact range checking -/

def newSpec (h m s : Std.I8) (n : Std.I32) : Prop :=
  ((hmsOk h.val m.val s.val ∧ nsOk n.val) →
    civil.time.Time.new h m s n ⦃ r => okVal r = some { hour := h, minute := m, second := s, subsec_nanosecond := n } ⦄
  ) ∧ (¬ (hmsOk h.val m.val s.val ∧ nsOk n.val) → civil.time.Time.new h m s n ⦃ r => isOk r = false ⦄)

def gold_new_raw (h m s : Std.I8) (n : Std.I32) : Prop := newSpec h m s n
def gold_new_near (h m s : Std.U8) (n : Std.I32) : Prop :=
  newSpec (near8 h 23) (near8 m 59) (near8 s 59) n
def gold_new_valid (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  newSpec t.hour t.minute t.second t.subsec_nanosecond
def gold_new_nanos_edge (h m s : Std.U8) (k : Std.U8) : Prop :=
  let t := vt h m s 0#u32
  newSpec t.hour t.minute t.second (mkI .I32 (if k.val < 128 then (k.val % 4 : Int) - 2 else 999999998 + (k.val % 4 : Int)))

/-- `civil::time` is `Time::new(..).unwrap()`: panics exactly on invalid input. -/
def gold_time_ctor (h m s : Std.U8) (n : Std.I32) : Prop :=
  let (h', m', s') := (near8 h 23, near8 m 59, near8 s 59)
  if hmsOk h'.val m'.val s'.val ∧ nsOk n.val then
    civil.time h' m' s' n = ok { hour := h', minute := m', second := s', subsec_nanosecond := n }
  else civil.time h' m' s' n = fail .panic

/-- Accessors return the components. -/
def gold_getters (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  civil.time.Time.impl.hour t = ok t.hour ∧ civil.time.Time.impl.minute t = ok t.minute ∧
  civil.time.Time.impl.second t = ok t.second ∧
  civil.time.Time.impl.subsec_nanosecond t = ok t.subsec_nanosecond

def gold_min_max : Prop :=
  fields civil.time.Time.MIN = (0, 0, 0, 0) ∧ fields civil.time.Time.MAX = (23, 59, 59, 999999999)

/-! ## Sub-second components -/

def gold_subsec_parts (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  let v := t.subsec_nanosecond.val
  civil.time.Time.millisecond t ⦃ x => x.val = v / 1000000 ⦄ ∧
  civil.time.Time.microsecond t ⦃ x => x.val = v / 1000 % 1000 ⦄ ∧
  civil.time.Time.nanosecond t ⦃ x => x.val = v % 1000 ⦄

def withPartsSpec (t : T) (a b c : Std.I16) : Prop :=
  ((partOk a.val ∧ partOk b.val ∧ partOk c.val) →
    civil.time.Time.with_subsec_parts t a b c ⦃ r => okVal r = some { t with subsec_nanosecond := (mkI IScalarTy.I32 (a.val * 1000000 + b.val * 1000 + c.val)) } ⦄
  ) ∧ (¬ (partOk a.val ∧ partOk b.val ∧ partOk c.val) → civil.time.Time.with_subsec_parts t a b c ⦃ r => isOk r = false ⦄)

def gold_with_subsec_parts (h m s : Std.U8) (n : Std.U32) (a b c : Std.U16) : Prop :=
  withPartsSpec (vt h m s n) (near16 a 999) (near16 b 999) (near16 c 999)
def gold_with_subsec_parts_raw (h m s : Std.U8) (n : Std.U32) (a b c : Std.I16) : Prop :=
  withPartsSpec (vt h m s n) a b c

/-- Splitting and re-assembling the sub-second part is the identity. -/
def gold_subsec_parts_roundtrip (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  (do
    let a ← civil.time.Time.millisecond t
    let b ← civil.time.Time.microsecond t
    let c ← civil.time.Time.nanosecond t
    civil.time.Time.with_subsec_parts t a b c) ⦃ r => okVal r = some t ⦄

def withNsSpec (t : T) (n : Std.I32) : Prop :=
  ((nsOk n.val) →
    civil.time.Time.with_subsec_nanosecond t n ⦃ r => okVal r = some { t with subsec_nanosecond := n } ⦄
  ) ∧ (¬ (nsOk n.val) → civil.time.Time.with_subsec_nanosecond t n ⦃ r => isOk r = false ⦄)

def gold_with_subsec_nanosecond (h m s : Std.U8) (n : Std.U32) (x : Std.I32) : Prop :=
  withNsSpec (vt h m s n) x
def gold_with_subsec_nanosecond_edge (h m s : Std.U8) (n : Std.U32) (k : Std.U8) : Prop :=
  withNsSpec (vt h m s n) (mkI .I32 (if k.val < 128 then (k.val % 3 : Int) - 1 else 999999998 + (k.val % 3 : Int)))

/-! ## Second / nanosecond of the day -/

def gold_to_second (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  (do let x ← toS t; civil.time.TimeSecond.impl.second x) ⦃ x => x.val = secsOf t ⦄

def gold_to_nanosecond (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  (do let x ← toNs t; civil.time.TimeNanosecond.impl.nanosecond x) ⦃ x => x.val = nanosOf t ⦄

/-- Time → nanosecond-of-day → Time is the identity (upstream property). -/
def gold_nanosecond_roundtrip (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  (do let x ← toNs t; civil.time.TimeNanosecond.to_time x) = ok t

/-- Time → second-of-day → Time truncates the sub-second part. -/
def gold_second_roundtrip (h m s : Std.U8) (n : Std.U32) : Prop :=
  let t := vt h m s n
  (do let x ← toS t; civil.time.TimeSecond.to_time x) = ok { t with subsec_nanosecond := 0#i32 }

/-- `TimeNanosecond::new` accepts exactly `0 ..= 86_399_999_999_999`; `to_time` inverts `to_nanosecond`. -/
def tnsSpec (x : Std.I64) : Prop :=
  ((0 ≤ x.val ∧ x.val ≤ 86399999999999) →
    (do
      let r ← civil.time.TimeNanosecond.new x
      match r with
      | .Ok v => do
        let k ← civil.time.TimeNanosecond.impl.nanosecond v
        let t ← civil.time.TimeNanosecond.to_time v
        let back ← toNs t
        let k2 ← civil.time.TimeNanosecond.impl.nanosecond back
        ok (some (k, t, k2))
      | .Err _ => ok none) ⦃ o => tnsChk x o = true ⦄
  ) ∧ (¬ (0 ≤ x.val ∧ x.val ≤ 86399999999999) → civil.time.TimeNanosecond.new x ⦃ r => isOk r = false ⦄)

def gold_tns_raw (x : Std.I64) : Prop := tnsSpec x
def gold_tns_in_day (x : Std.U64) : Prop := tnsSpec (mkI .I64 (x.val % 86400000000000))
def gold_tns_edge (k : Std.U8) (d : Std.U8) : Prop :=
  tnsSpec (mkI .I64 (if k.val < 128 then (d.val % 4 : Int) - 2 else 86399999999998 + (d.val % 4 : Int)))
def gold_tns_round (x : Std.U16) (k : Std.U8) : Prop :=
  -- whole hours / minutes / seconds (the zero-remainder branches of `to_time`)
  tnsSpec (mkI .I64 ((x.val % 24) * 3600000000000 + (k.val % 4) * ((x.val / 24) % 60) * 60000000000 / 3 * 3
    + (if k.val ≥ 128 then (x.val % 60) * 1000000000 else 0) + (if k.val % 2 = 1 then (x.val % 7) else 0)))

/-- `TimeSecond::new` accepts exactly `0 ..= 86_399`; `to_time` inverts `to_second`. -/
def tsSpec (x : Std.I32) : Prop :=
  ((0 ≤ x.val ∧ x.val ≤ 86399) →
    (do
      let r ← civil.time.TimeSecond.new x
      match r with
      | .Ok v => do
        let k ← civil.time.TimeSecond.impl.second v
        let t ← civil.time.TimeSecond.to_time v
        let back ← toS t
        let k2 ← civil.time.TimeSecond.impl.second back
        ok (some (k, t, k2))
      | .Err _ => ok none) ⦃ o => tsChk x o = true ⦄
  ) ∧ (¬ (0 ≤ x.val ∧ x.val ≤ 86399) → civil.time.TimeSecond.new x ⦃ r => isOk r = false ⦄)

def gold_ts_raw (x : Std.I32) : Prop := tsSpec x
def gold_ts_in_day (x : Std.U32) : Prop := tsSpec (mkI .I32 (x.val % 86400))
def gold_ts_edge (k : Std.U8) : Prop :=
  tsSpec (mkI .I32 (if k.val < 128 then (k.val % 4 : Int) - 2 else 86398 + (k.val % 4 : Int)))
def gold_ts_round (x : Std.U16) (k : Std.U8) : Prop :=
  tsSpec (mkI .I32 ((x.val % 24) * 3600 + (if k.val % 2 = 1 then (x.val / 24 % 60) * 60 else 0)
    + (if k.val ≥ 128 then x.val % 60 else 0)))

/-- `TimeSecond::constant` panics exactly on out-of-range input. -/
def gold_ts_constant (x : Std.I32) (k : Std.U8) : Prop :=
  let y : Std.I32 := if k.val < 64 then mkI .I32 ((x.val % 86402) - 1) else x
  if 0 ≤ y.val ∧ y.val ≤ 86399 then
    (do let v ← civil.time.TimeSecond.constant y; civil.time.TimeSecond.impl.second v) = ok y
  else civil.time.TimeSecond.constant y = fail .panic

/-! ## Order and equality -/

/-- The derived order is chronological: it agrees with the nanosecond of the day. -/
def gold_cmp_chrono (h m s : Std.U8) (n : Std.U32) (h2 m2 s2 : Std.U8) (n2 : Std.U32) (k : Std.U8) : Prop :=
  let a := vt h m s n
  -- often share a prefix of components with `a`
  let b0 := vt h2 m2 s2 n2
  let b : T := if k.val % 4 = 0 then b0
    else if k.val % 4 = 1 then { a with subsec_nanosecond := b0.subsec_nanosecond }
    else if k.val % 4 = 2 then { a with second := b0.second, subsec_nanosecond := b0.subsec_nanosecond }
    else { a with minute := b0.minute }
  civil.time.Time.Insts.CoreCmpOrd.cmp a b = ok (ordOf (nanosOf a) (nanosOf b)) ∧
  civil.time.Time.Insts.CoreCmpPartialEqTime.eq a b = ok (decide (fields a = fields b))

/-- `to_nanosecond` / `to_second` are monotone (order preserving). -/
def gold_to_nanosecond_monotone (h m s : Std.U8) (n : Std.U32) (h2 m2 s2 : Std.U8) (n2 : Std.U32) : Prop :=
  let a := vt h m s n
  let b := vt h2 m2 s2 n2
  (do
    let o ← civil.time.Time.Insts.CoreCmpOrd.cmp a b
    let x ← toNs a
    let y ← toNs b
    let o2 ← civil.time.TimeNanosecond.Insts.CoreCmpOrd.cmp x y
    let p ← toS a
    let q ← toS b
    let o3 ← civil.time.TimeSecond.Insts.CoreCmpOrd.cmp p q
    ok (monoChk o o2 o3 (decide (secsOf a ≤ secsOf b)))) ⦃ b => b = true ⦄

/-! ## `Time::on` -/

def onSpec (t : T) (y : Std.I16) (m d : Std.I8) : Prop :=
  ((dateOk y.val m.val d.val) →
    civil.time.Time.on t y m d ⦃ dt => dt.time = t ∧ dt.date.year = y ∧ dt.date.month = m ∧ dt.date.day = d ⦄
  ) ∧ (¬ (dateOk y.val m.val d.val) → civil.time.Time.on t y m d = fail .panic)

def gold_on (h m s : Std.U8) (n : Std.U32) (y : Std.I16) (mm dd : Std.U8) : Prop :=
  onSpec (vt h m s n) (yr y) (mo mm) (dy dd)
def gold_on_raw (h m s : Std.U8) (n : Std.U32) (y : Std.I16) (mm dd : Std.I8) : Prop :=
  onSpec (vt h m s n) y mm dd
/-- Month ends and leap days around century years. -/
def gold_on_month_end (y : Std.U16) (mm : Std.U8) (k : Std.U8) : Prop :=
  let yy : Std.I16 := mkI .I16 (((y.val % 200 : Int) - 100) * (if k.val ≥ 128 then 4 else 1) * (if k.val % 2 = 0 then 25 else 1)
    + (if k.val % 4 = 1 then (k.val % 7 : Int) else 0))
  let m : Std.I8 := mkI .I8 (mm.val % 12 + 1)
  let d : Std.I8 := mkI .I8 (dim yy.val m.val + (k.val % 3 : Int) - 1)
  onSpec civil.time.Time.MIN yy m d
def gold_on_year_bounds (k : Std.U8) (mm dd : Std.U8) : Prop :=
  let yy : Std.I16 := mkI .I16 (if k.val < 128 then -10000 + (k.val % 3 : Int) else 9998 + (k.val % 3 : Int))
  onSpec civil.time.Time.MAX yy (mkI .I8 (mm.val % 12 + 1)) (mkI .I8 (dd.val % 28 + 1))

/-! Differential-testing probes. -/

def diff_new (h m s : Std.U8) (n : Std.I32) := (do
  let r ← civil.time.Time.new (near8 h 23) (near8 m 59) (near8 s 59) n; ok (okVal r))
def diff_time (h m s : Std.U8) (n : Std.U32) :=
  let t := vt h m s n; civil.time t.hour t.minute t.second t.subsec_nanosecond
def diff_parts (h m s : Std.U8) (n : Std.U32) := (do
  let t := vt h m s n
  let a ← civil.time.Time.millisecond t
  let b ← civil.time.Time.microsecond t
  let c ← civil.time.Time.nanosecond t
  ok (a, b, c))
def diff_with_parts (h m s : Std.U8) (n : Std.U32) (a b c : Std.U16) := (do
  let r ← civil.time.Time.with_subsec_parts (vt h m s n) (near16 a 999) (near16 b 999) (near16 c 999); ok (okVal r))
def diff_with_ns (h m s : Std.U8) (n : Std.U32) (x : Std.I32) := (do
  let r ← civil.time.Time.with_subsec_nanosecond (vt h m s n) x; ok (okVal r))
def diff_to_second (h m s : Std.U8) (n : Std.U32) := toS (vt h m s n)
def diff_to_ns (h m s : Std.U8) (n : Std.U32) := toNs (vt h m s n)
def diff_tns (x : Std.U64) := (do
  let r ← civil.time.TimeNanosecond.new (mkI .I64 (x.val % 86400000000002))
  match r with
  | .Ok v => do let t ← civil.time.TimeNanosecond.to_time v; ok (some t)
  | .Err _ => ok none)
def diff_ts (x : Std.U32) := (do
  let r ← civil.time.TimeSecond.new (mkI .I32 ((x.val % 86402 : Int) - 1))
  match r with
  | .Ok v => do let t ← civil.time.TimeSecond.to_time v; ok (some t)
  | .Err _ => ok none)
def diff_ts_constant (x : Std.U32) := civil.time.TimeSecond.constant (mkI .I32 ((x.val % 86402 : Int) - 1))
def diff_cmp (h m s : Std.U8) (n : Std.U32) (h2 : Std.U8) (n2 : Std.U32) (k : Std.U8) :=
  let a := vt h m s n
  let b := if k.val < 128 then { a with subsec_nanosecond := (vt h2 m s n2).subsec_nanosecond } else vt h2 m s n2
  (do let o ← civil.time.Time.Insts.CoreCmpOrd.cmp a b
      let e ← civil.time.Time.Insts.CoreCmpPartialEqTime.eq a b
      ok (o, e))
def diff_on (y : Std.I16) (mm dd : Std.U8) := civil.time.Time.on civil.time.Time.MIN (yr y) (mo mm) (dy dd)
def diff_on_month_end (y : Std.U16) (mm : Std.U8) (k : Std.U8) :=
  let yy : Std.I16 := mkI .I16 (((y.val % 200 : Int) - 100) * (if k.val ≥ 128 then 4 else 1) * (if k.val % 2 = 0 then 25 else 1))
  let m : Std.I8 := mkI .I8 (mm.val % 12 + 1)
  civil.time.Time.on civil.time.Time.MIN yy m (mkI .I8 (dim yy.val m.val + (k.val % 3 : Int) - 1))

end Benchmark.V2.Jiff.Civil.Gold
