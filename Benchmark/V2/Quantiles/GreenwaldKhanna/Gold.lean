import Benchmark.V2.Prelude
import QuantilesGreenwaldKhanna.Extraction

/-! Hidden gold specification for target `quantiles/greenwald_khanna`.

API: `greenwald_khanna::find_insert_pos::<i32>` and
`greenwald_khanna::find_insert_pos_linear::<i32>` (Lean: first argument
`core.I32.Insts.CoreCmpOrd`). `Slice` has no `Repr`, so slices are sampled
as lists and converted. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM quantiles RSGB

/-! Computable helpers (outside `Benchmark.` so the driver does not unfold them). -/
namespace RSGBGold.Quantiles.GreenwaldKhanna

def toSlice (l : List Std.I32) : Slice Std.I32 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

def ins (a : Std.I32) : List Std.I32 → List Std.I32
  | [] => [a]
  | b :: l => if a.val ≤ b.val then a :: b :: l else b :: ins a l

/-- Independent model: insertion sort on the integer values. -/
def isort : List Std.I32 → List Std.I32
  | [] => []
  | a :: l => ins a (isort l)

/-- Values squeezed into `[-2, 2]` (forces duplicates and hits). -/
def small (x : List Std.I32) : List Std.I32 := x.map (fun v => mkI .I32 (v.val % 5 - 2))

def logPos (vs : List Std.I32) (v : Std.I32) : RustM Nat := do
  let r ← greenwald_khanna.find_insert_pos core.I32.Insts.CoreCmpOrd (toSlice vs) v
  ok r.val

def linPos (vs : List Std.I32) (v : Std.I32) : RustM Nat := do
  let r ← greenwald_khanna.find_insert_pos_linear core.I32.Insts.CoreCmpOrd (toSlice vs) v
  ok r.val

/-- First index whose element is strictly greater than `v` (or the length). -/
def firstGreater (vs : List Std.I32) (v : Std.I32) : Nat :=
  vs.findIdx (fun x => decide (v.val < x.val))

/-- Number of elements `≤ v`. -/
def countLe (vs : List Std.I32) (v : Std.I32) : Nat :=
  (vs.filter (fun x => decide (x.val ≤ v.val))).length

/-- The documented insertion-position property of `r` (any slice). -/
def insertOk (vs : List Std.I32) (v : Std.I32) (r : Nat) : Bool :=
  decide (r ≤ vs.length) &&
  (r == 0 || decide ((vs.getD (r - 1) 0#i32).val ≤ v.val)) &&
  (r == vs.length || decide (v.val < (vs.getD r 0#i32).val))

def pick (vs : List Std.I32) (k : Std.U8) : Std.I32 := vs.getD (k.val % vs.length) 0#i32

end RSGBGold.Quantiles.GreenwaldKhanna

namespace Benchmark.V2.Quantiles.GreenwaldKhanna.Gold
open RSGBGold.Quantiles.GreenwaldKhanna

/-! ## `find_insert_pos_linear` -/

/-- Exact: index of the first element `> v`, or `len` (any slice, never panics). -/
def gold_linear_exact (vs : List Std.I32) (v : Std.I32) : Prop :=
  linPos vs v = ok (firstGreater vs v)

def gold_linear_exact_small (vs : List Std.I32) (v : Std.I32) : Prop :=
  linPos (small vs) (mkI .I32 (v.val % 7 - 3)) = ok (firstGreater (small vs) (mkI .I32 (v.val % 7 - 3)))

/-! ## `find_insert_pos` -/

/-- Sorted input: the upper-bound position (number of elements `≤ v`). -/
def gold_log_sorted (vs : List Std.I32) (v : Std.I32) : Prop :=
  logPos (isort vs) v = ok (countLe vs v)

def gold_log_sorted_small (vs : List Std.I32) (v : Std.I32) : Prop :=
  logPos (isort (small vs)) (mkI .I32 (v.val % 7 - 3)) = ok (countLe (small vs) (mkI .I32 (v.val % 7 - 3)))

/-- Sorted input, `v` an element of the slice. -/
def gold_log_sorted_member (vs : List Std.I32) (k : Std.U8) : Prop :=
  0 < vs.length → logPos (isort vs) (pick vs k) = ok (countLe vs (pick vs k))

def gold_log_sorted_member_small (vs : List Std.I32) (k : Std.U8) : Prop :=
  0 < vs.length → logPos (isort (small vs)) (pick (small vs) k) = ok (countLe (small vs) (pick (small vs) k))

/-- Sorted input: agrees with the linear scan (upstream property, any `v`). -/
def gold_log_eq_linear_sorted (vs : List Std.I32) (v : Std.I32) : Prop :=
  logPos (isort (small vs)) (mkI .I32 (v.val % 7 - 3)) = linPos (isort (small vs)) (mkI .I32 (v.val % 7 - 3)) ∧
  logPos (isort vs) v = linPos (isort vs) v

/-- Any (unsorted) slice: never panics and the result is a valid insertion
position in the documented sense (`vs[r-1] ≤ v < vs[r]` where defined). -/
def gold_log_insert_ok (vs : List Std.I32) (v : Std.I32) : Prop :=
  logPos vs v ⦃ r => insertOk vs v r = true ⦄

def gold_log_insert_ok_small (vs : List Std.I32) (v : Std.I32) : Prop :=
  logPos (small vs) (mkI .I32 (v.val % 7 - 3)) ⦃ r => insertOk (small vs) (mkI .I32 (v.val % 7 - 3)) r = true ⦄

/-! Differential-testing probes. -/

def diff_linear (vs : List Std.I32) (v : Std.I32) := linPos vs v
def diff_linear_small (vs : List Std.I32) (v : Std.I32) := linPos (small vs) (mkI .I32 (v.val % 7 - 3))
def diff_log (vs : List Std.I32) (v : Std.I32) := logPos vs v
def diff_log_small (vs : List Std.I32) (v : Std.I32) := logPos (small vs) (mkI .I32 (v.val % 7 - 3))
def diff_log_sorted (vs : List Std.I32) (v : Std.I32) := logPos (isort vs) v
def diff_log_sorted_small (vs : List Std.I32) (v : Std.I32) := logPos (isort (small vs)) (mkI .I32 (v.val % 7 - 3))

end Benchmark.V2.Quantiles.GreenwaldKhanna.Gold
