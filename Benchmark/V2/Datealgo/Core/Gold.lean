import Benchmark.V2.Prelude
import DatealgoCore.Extraction

/-! Hidden gold specification for target `datealgo/core`.

Independent model: the proleptic Gregorian calendar written with plain `Int`
arithmetic (leap-year counting by floor division, month lengths by table),
day 0 = 1970-01-01 (a Thursday). The documented valid ranges are
`YEAR_MIN = -1467999 ..= YEAR_MAX = 1471744` (dates) and the corresponding
Rata Die / second ranges; every bound is a `debug_assert!`, i.e. a panic under
the benchmark's debug semantics. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM datealgo RSGB

namespace RSGBGold.Datealgo.Core

def YMIN : Int := -1467999
def YMAX : Int := 1471744

def leap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def dim (y m : Int) : Int :=
  if m == 2 then (if leap y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- Number of leap years in `[1, y)` (meaningful for any integer `y`, by floor division). -/
def leapsBefore (y : Int) : Int := (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400

def daysBeforeMonth (y m : Int) : Int :=
  ((List.range 12).filter (fun k => (k : Int) + 1 < m)).foldl (fun acc k => acc + dim y (k + 1)) 0

/-- Days since 1970-01-01 of a (valid) Gregorian date. -/
def rdOf (y m d : Int) : Int :=
  365 * (y - 1970) + (leapsBefore y - leapsBefore 1970) + daysBeforeMonth y m + (d - 1)

def RDMIN : Int := rdOf YMIN 1 1
def RDMAX : Int := rdOf YMAX 12 31
def SMIN : Int := RDMIN * 86400
def SMAX : Int := RDMAX * 86400 + 86399

def yearOk (y : Int) : Bool := decide (YMIN ≤ y ∧ y ≤ YMAX)
def rdOk (n : Int) : Bool := decide (RDMIN ≤ n ∧ n ≤ RDMAX)
def secsOk (s : Int) : Bool := decide (SMIN ≤ s ∧ s ≤ SMAX)

def dateOk (y m d : Int) : Bool := yearOk y && decide (1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ dim y m)

def timeOk (h mi s : Int) : Bool := decide (0 ≤ h ∧ h ≤ 23 ∧ 0 ≤ mi ∧ mi ≤ 59 ∧ 0 ≤ s ∧ s ≤ 59)

/-- ISO weekday (1 = Monday … 7 = Sunday); day 0 was a Thursday. -/
def wdOf (n : Int) : Int := (n + 3) % 7 + 1

/-- Monday of ISO week 1 of year `y` (the week containing January 4th). -/
def isoStart (y : Int) : Int := let j4 := rdOf y 1 4; j4 - (wdOf j4 - 1)

def isoWeeks (y : Int) : Int := (isoStart (y + 1) - isoStart y) / 7

def isoRd (y w d : Int) : Int := isoStart y + 7 * (w - 1) + (d - 1)

/-- Valid ISO week date whose day lies in the supported Rata Die range. -/
def isoOk (y w d : Int) : Bool :=
  yearOk y && decide (1 ≤ w ∧ w ≤ isoWeeks y ∧ 1 ≤ d ∧ d ≤ 7) && rdOk (isoRd y w d)

/-- Map an arbitrary sampled integer into `[lo, hi]`: values already inside are kept,
others are sent near the lower bound, near the upper bound, or uniformly inside. -/
def into (v lo hi : Int) : Int :=
  if lo ≤ v ∧ v ≤ hi then v
  else
    let a : Int := v.natAbs
    match v.natAbs % 3 with
    | 0 => lo + (a / 3) % 1500
    | 1 => hi - (a / 3) % 1500
    | _ => lo + a % (hi - lo + 1)

def yI (y : Std.I32) : Std.I32 := mkI .I32 (into y.val YMIN YMAX)
def mI (m : Std.U8) : Std.U8 := mkU .U8 (m.val % 12 + 1)
def dI (y : Std.I32) (m d : Std.U8) : Std.U8 :=
  mkU .U8 (d.val % (dim (yI y).val (mI m).val).toNat + 1)
def rdI (n : Std.I32) : Std.I32 := mkI .I32 (into n.val RDMIN RDMAX)
def sI (s : Std.I64) : Std.I64 := mkI .I64 (into s.val SMIN SMAX)
/-- Raw sample or its in-range image (so panic properties see both sides of every bound). -/
def yP (y : Std.I32) (b : Bool) : Std.I32 := if b then y else yI y
def wI (y : Std.I32) (w : Std.U8) : Std.U8 :=
  mkU .U8 (w.val % (isoWeeks (yI y).val).toNat + 1)
def wdI (d : Std.U8) : Std.U8 := mkU .U8 (d.val % 7 + 1)

/-- A century year (multiple of 100, sometimes of 400) inside the supported range. -/
def cI (y : Std.I32) : Std.I32 :=
  let c := (into y.val YMIN YMAX) / 100 * 100
  mkI .I32 (if c < YMIN then c + 100 else c)

def isPanic {α} (x : RustM α) : Bool := match x with | .fail .panic => true | _ => false

end RSGBGold.Datealgo.Core

namespace Benchmark.V2.Datealgo.Core.Gold
open RSGBGold.Datealgo.Core

/-! ## Calendar facts -/

def gold_is_leap_year (y : Std.I32) : Prop :=
  is_leap_year (yI y) ⦃ b => b = leap (yI y).val ⦄

def gold_is_leap_year_panics (y : Std.I32) (b : Bool) : Prop :=
  isPanic (is_leap_year (yP y b)) = !yearOk (yP y b).val

def gold_is_leap_year_century (y : Std.I32) : Prop :=
  is_leap_year (cI y) ⦃ b => b = leap (cI y).val ⦄

def gold_days_in_month_century (y : Std.I32) (m : Std.U8) : Prop :=
  days_in_month (cI y) (mI m) ⦃ r => r.val = dim (cI y).val (mI m).val ⦄

def gold_date_to_rd_century (y : Std.I32) (d : Std.U8) (b : Bool) : Prop :=
  let m : Std.U8 := if b then 2#u8 else 3#u8
  let dd : Std.U8 := mkU .U8 (d.val % (dim (cI y).val m.val).toNat + 1)
  date_to_rd (cI y, m, dd) ⦃ r => r.val = rdOf (cI y).val m.val dd.val ⦄

def gold_days_in_month (y : Std.I32) (m : Std.U8) : Prop :=
  days_in_month (yI y) (mI m) ⦃ r => r.val = dim (yI y).val (mI m).val ⦄

/-- Invalid month panics (whatever the year). -/
def gold_days_in_month_bad_month (y : Std.I32) (m : Std.U8) : Prop :=
  (m.val = 0 ∨ 12 < m.val) → days_in_month y m = fail .panic

def gold_days_in_month_feb_year (y : Std.I32) : Prop :=
  ¬ yearOk y.val → days_in_month y 2#u8 = fail .panic

/-! ## Rata Die <-> Gregorian date -/

def gold_date_to_rd (y : Std.I32) (m d : Std.U8) : Prop :=
  date_to_rd (yI y, mI m, dI y m d) ⦃ r => r.val = rdOf (yI y).val (mI m).val (dI y m d).val ⦄

def gold_date_to_rd_panics (y : Std.I32) (b : Bool) (m d : Std.U8) : Prop :=
  isPanic (date_to_rd (yP y b, m, d)) = !dateOk (yP y b).val m.val d.val

def gold_rd_to_date (n : Std.I32) : Prop :=
  rd_to_date (rdI n) ⦃ r => dateOk r.1.val r.2.1.val r.2.2.val ∧
    rdOf r.1.val r.2.1.val r.2.2.val = (rdI n).val ⦄

def gold_rd_to_date_panics (n : Std.I32) : Prop :=
  isPanic (rd_to_date n) = !rdOk n.val

def gold_date_rd_roundtrip (y : Std.I32) (m d : Std.U8) : Prop :=
  (do let n ← date_to_rd (yI y, mI m, dI y m d); rd_to_date n) = ok (yI y, mI m, dI y m d)

def gold_range_constants : Prop :=
  YEAR_MIN.val = YMIN ∧ YEAR_MAX.val = YMAX ∧
  (RD_MIN ⦃ r => r.val = RDMIN ⦄) ∧ (RD_MAX ⦃ r => r.val = RDMAX ⦄) ∧
  (RD_SECONDS_MIN ⦃ r => r.val = SMIN ⦄) ∧ (RD_SECONDS_MAX ⦃ r => r.val = SMAX ⦄)

/-! ## Day of week -/

def gold_rd_to_weekday (n : Std.I32) : Prop :=
  rd_to_weekday (rdI n) ⦃ r => r.val = wdOf (rdI n).val ⦄

def gold_rd_to_weekday_panics (n : Std.I32) : Prop :=
  isPanic (rd_to_weekday n) = !rdOk n.val

def gold_date_to_weekday (y : Std.I32) (m d : Std.U8) : Prop :=
  date_to_weekday (yI y, mI m, dI y m d) ⦃ r =>
    r.val = wdOf (rdOf (yI y).val (mI m).val (dI y m d).val) ⦄

def gold_date_to_weekday_panics (y : Std.I32) (b : Bool) (m d : Std.U8) : Prop :=
  isPanic (date_to_weekday (yP y b, m, d)) = !dateOk (yP y b).val m.val d.val

/-! ## Adjacent dates -/

def gold_next_date (y : Std.I32) (m d : Std.U8) : Prop :=
  ¬ ((yI y).val = YMAX ∧ (mI m).val = 12 ∧ (dI y m d).val = 31) →
  next_date (yI y, mI m, dI y m d) ⦃ r => dateOk r.1.val r.2.1.val r.2.2.val ∧
    rdOf r.1.val r.2.1.val r.2.2.val = rdOf (yI y).val (mI m).val (dI y m d).val + 1 ⦄

def gold_next_date_panics (y : Std.I32) (b : Bool) (m d : Std.U8) : Prop :=
  isPanic (next_date (yP y b, m, d)) =
    (!dateOk (yP y b).val m.val d.val || ((yP y b).val == YMAX && m.val == 12 && d.val == 31))

def gold_next_date_edge (d : Std.U8) : Prop :=
  isPanic (next_date (YEAR_MAX, 12#u8, mkU .U8 (d.val % 31 + 1))) = decide (d.val % 31 + 1 = 31)

def gold_prev_date_edge (d : Std.U8) : Prop :=
  isPanic (prev_date (YEAR_MIN, 1#u8, mkU .U8 (d.val % 31 + 1))) = decide (d.val % 31 + 1 = 1)

def gold_prev_date (y : Std.I32) (m d : Std.U8) : Prop :=
  ¬ ((yI y).val = YMIN ∧ (mI m).val = 1 ∧ (dI y m d).val = 1) →
  prev_date (yI y, mI m, dI y m d) ⦃ r => dateOk r.1.val r.2.1.val r.2.2.val ∧
    rdOf r.1.val r.2.1.val r.2.2.val + 1 = rdOf (yI y).val (mI m).val (dI y m d).val ⦄

def gold_prev_date_panics (y : Std.I32) (b : Bool) (m d : Std.U8) : Prop :=
  isPanic (prev_date (yP y b, m, d)) =
    (!dateOk (yP y b).val m.val d.val || ((yP y b).val == YMIN && m.val == 1 && d.val == 1))

/-! ## Seconds -/

def gold_secs_to_dhms (s : Std.I64) : Prop :=
  secs_to_dhms (sI s) ⦃ r => timeOk r.2.1.val r.2.2.1.val r.2.2.2.val ∧
    r.1.val * 86400 + r.2.1.val * 3600 + r.2.2.1.val * 60 + r.2.2.2.val = (sI s).val ⦄

def gold_secs_to_dhms_panics (s : Std.I64) : Prop :=
  isPanic (secs_to_dhms s) = !secsOk s.val

def gold_dhms_to_secs (n : Std.I32) (h mi s : Std.U8) : Prop :=
  dhms_to_secs (rdI n, mkU .U8 (h.val % 24), mkU .U8 (mi.val % 60), mkU .U8 (s.val % 60)) ⦃ r =>
    r.val = (rdI n).val * 86400 + (h.val % 24) * 3600 + (mi.val % 60) * 60 + s.val % 60 ⦄

def gold_dhms_to_secs_panics (n : Std.I32) (b : Bool) (h mi s : Std.U8) : Prop :=
  let n' := if b then n else rdI n
  isPanic (dhms_to_secs (n', h, mi, s)) = !(rdOk n'.val && timeOk h.val mi.val s.val)

def gold_secs_to_datetime (s : Std.I64) : Prop :=
  secs_to_datetime (sI s) ⦃ r =>
    dateOk r.1.val r.2.1.val r.2.2.1.val ∧ timeOk r.2.2.2.1.val r.2.2.2.2.1.val r.2.2.2.2.2.val ∧
    rdOf r.1.val r.2.1.val r.2.2.1.val * 86400 + r.2.2.2.1.val * 3600 + r.2.2.2.2.1.val * 60 +
      r.2.2.2.2.2.val = (sI s).val ⦄

def gold_secs_to_datetime_panics (s : Std.I64) : Prop :=
  isPanic (secs_to_datetime s) = !secsOk s.val

def gold_datetime_to_secs (y : Std.I32) (m d h mi s : Std.U8) : Prop :=
  datetime_to_secs (yI y, mI m, dI y m d, mkU .U8 (h.val % 24), mkU .U8 (mi.val % 60), mkU .U8 (s.val % 60))
    ⦃ r => r.val = rdOf (yI y).val (mI m).val (dI y m d).val * 86400 +
      (h.val % 24) * 3600 + (mi.val % 60) * 60 + s.val % 60 ⦄

def gold_datetime_to_secs_panics (y : Std.I32) (b : Bool) (m d h mi s : Std.U8) : Prop :=
  isPanic (datetime_to_secs (yP y b, m, d, h, mi, s)) =
    !(dateOk (yP y b).val m.val d.val && timeOk h.val mi.val s.val)

def gold_secs_roundtrip (s : Std.I64) : Prop :=
  (do let t ← secs_to_datetime (sI s); datetime_to_secs t) = ok (sI s)

/-! ## ISO week dates -/

def gold_isoweeks_in_year (y : Std.I32) : Prop :=
  isoweeks_in_year (yI y) ⦃ r => r.val = isoWeeks (yI y).val ⦄

def gold_isoweeks_in_year_panics (y : Std.I32) (b : Bool) : Prop :=
  isPanic (isoweeks_in_year (yP y b)) = !yearOk (yP y b).val

def gold_rd_to_isoweekdate (n : Std.I32) : Prop :=
  rd_to_isoweekdate (rdI n) ⦃ r => isoOk r.1.val r.2.1.val r.2.2.val ∧
    isoRd r.1.val r.2.1.val r.2.2.val = (rdI n).val ⦄

def gold_rd_to_isoweekdate_panics (n : Std.I32) : Prop :=
  isPanic (rd_to_isoweekdate n) = !rdOk n.val

def gold_isoweekdate_to_rd (y : Std.I32) (w d : Std.U8) : Prop :=
  isoOk (yI y).val (wI y w).val (wdI d).val →
  isoweekdate_to_rd (yI y, wI y w, wdI d) ⦃ r => r.val = isoRd (yI y).val (wI y w).val (wdI d).val ⦄

def gold_isoweekdate_to_rd_panics (y : Std.I32) (b : Bool) (w d : Std.U8) : Prop :=
  isPanic (isoweekdate_to_rd (yP y b, w, d)) = !isoOk (yP y b).val w.val d.val

def gold_isoweekdate_to_rd_last_week (d : Std.U8) : Prop :=
  isPanic (isoweekdate_to_rd (YEAR_MAX, 53#u8, wdI d)) = decide (4 < (wdI d).val)

def gold_date_to_isoweekdate (y : Std.I32) (m d : Std.U8) : Prop :=
  date_to_isoweekdate (yI y, mI m, dI y m d) ⦃ r => isoOk r.1.val r.2.1.val r.2.2.val ∧
    isoRd r.1.val r.2.1.val r.2.2.val = rdOf (yI y).val (mI m).val (dI y m d).val ⦄

def gold_date_to_isoweekdate_panics (y : Std.I32) (b : Bool) (m d : Std.U8) : Prop :=
  isPanic (date_to_isoweekdate (yP y b, m, d)) = !dateOk (yP y b).val m.val d.val

def gold_isoweekdate_to_date (y : Std.I32) (w d : Std.U8) : Prop :=
  isoOk (yI y).val (wI y w).val (wdI d).val →
  isoweekdate_to_date (yI y, wI y w, wdI d) ⦃ r => dateOk r.1.val r.2.1.val r.2.2.val ∧
    rdOf r.1.val r.2.1.val r.2.2.val = isoRd (yI y).val (wI y w).val (wdI d).val ⦄

def gold_isoweekdate_to_date_panics (y : Std.I32) (b : Bool) (w d : Std.U8) : Prop :=
  isPanic (isoweekdate_to_date (yP y b, w, d)) = !isoOk (yP y b).val w.val d.val

def gold_iso_roundtrip (n : Std.I32) : Prop :=
  (do let t ← rd_to_isoweekdate (rdI n); isoweekdate_to_rd t) = ok (rdI n)

/-! ## Differential-testing probes -/

def diff_is_leap_year (y : Std.I32) (b : Bool) := is_leap_year (yP y b)
def diff_is_leap_year_century (y : Std.I32) := is_leap_year (cI y)
def diff_days_in_month_century (y : Std.I32) (m : Std.U8) := days_in_month (cI y) (mI m)
def diff_date_to_rd_century (y : Std.I32) (d : Std.U8) (b : Bool) :=
  date_to_rd (cI y, (if b then 2#u8 else 3#u8), mkU .U8 (d.val % 28 + 1))
def diff_days_in_month (y : Std.I32) (b : Bool) (m : Std.U8) := days_in_month (yP y b) m
def diff_days_in_month_v (y : Std.I32) (m : Std.U8) := days_in_month (yI y) (mI m)
def diff_date_to_rd (y : Std.I32) (m d : Std.U8) := date_to_rd (yI y, mI m, dI y m d)
def diff_date_to_rd_raw (y : Std.I32) (b : Bool) (m d : Std.U8) := date_to_rd (yP y b, m, d)
def diff_rd_to_date (n : Std.I32) (b : Bool) := rd_to_date (if b then n else rdI n)
def diff_rd_to_weekday (n : Std.I32) (b : Bool) := rd_to_weekday (if b then n else rdI n)
def diff_date_to_weekday (y : Std.I32) (m d : Std.U8) := date_to_weekday (yI y, mI m, dI y m d)
def diff_date_to_weekday_raw (y : Std.I32) (b : Bool) (m d : Std.U8) := date_to_weekday (yP y b, m, d)
def diff_next_date (y : Std.I32) (m d : Std.U8) := next_date (yI y, mI m, dI y m d)
def diff_next_date_raw (y : Std.I32) (b : Bool) (m d : Std.U8) := next_date (yP y b, m, d)
def diff_next_date_edge (d : Std.U8) (b : Bool) :=
  next_date (if b then YEAR_MAX else YEAR_MIN, (if b then 12#u8 else 1#u8), mkU .U8 (d.val % 3 + 29))
def diff_prev_date_edge (d : Std.U8) (b : Bool) :=
  prev_date (if b then YEAR_MIN else YEAR_MAX, (if b then 1#u8 else 12#u8), mkU .U8 (d.val % 3 + 1))
def diff_prev_date (y : Std.I32) (m d : Std.U8) := prev_date (yI y, mI m, dI y m d)
def diff_prev_date_raw (y : Std.I32) (b : Bool) (m d : Std.U8) := prev_date (yP y b, m, d)
def diff_secs_to_dhms (s : Std.I64) (b : Bool) := secs_to_dhms (if b then s else sI s)
def diff_dhms_to_secs (n : Std.I32) (b : Bool) (h mi s : Std.U8) :=
  dhms_to_secs (if b then n else rdI n, h, mi, s)
def diff_dhms_to_secs_v (n : Std.I32) (h mi s : Std.U8) :=
  dhms_to_secs (rdI n, mkU .U8 (h.val % 24), mkU .U8 (mi.val % 60), mkU .U8 (s.val % 60))
def diff_secs_to_datetime (s : Std.I64) (b : Bool) := secs_to_datetime (if b then s else sI s)
def diff_datetime_to_secs (y : Std.I32) (m d h mi s : Std.U8) :=
  datetime_to_secs (yI y, mI m, dI y m d, mkU .U8 (h.val % 24), mkU .U8 (mi.val % 60), mkU .U8 (s.val % 60))
def diff_datetime_to_secs_raw (y : Std.I32) (b : Bool) (m d h mi s : Std.U8) :=
  datetime_to_secs (yP y b, m, d, h, mi, s)
def diff_isoweeks_in_year (y : Std.I32) (b : Bool) := isoweeks_in_year (yP y b)
def diff_rd_to_isoweekdate (n : Std.I32) (b : Bool) := rd_to_isoweekdate (if b then n else rdI n)
def diff_isoweekdate_to_rd (y : Std.I32) (w d : Std.U8) := isoweekdate_to_rd (yI y, wI y w, wdI d)
def diff_isoweekdate_to_rd_raw (y : Std.I32) (b : Bool) (w d : Std.U8) := isoweekdate_to_rd (yP y b, w, d)
def diff_isoweekdate_to_rd_last (d : Std.U8) := isoweekdate_to_rd (YEAR_MAX, 53#u8, d)
def diff_date_to_isoweekdate (y : Std.I32) (m d : Std.U8) := date_to_isoweekdate (yI y, mI m, dI y m d)
def diff_date_to_isoweekdate_raw (y : Std.I32) (b : Bool) (m d : Std.U8) := date_to_isoweekdate (yP y b, m, d)
def diff_isoweekdate_to_date (y : Std.I32) (w d : Std.U8) := isoweekdate_to_date (yI y, wI y w, wdI d)
def diff_isoweekdate_to_date_raw (y : Std.I32) (b : Bool) (w d : Std.U8) := isoweekdate_to_date (yP y b, w, d)
def diff_constants (_b : Bool) := (RD_MIN, RD_MAX, RD_SECONDS_MIN, RD_SECONDS_MAX, YEAR_MIN, YEAR_MAX)

end Benchmark.V2.Datealgo.Core.Gold
