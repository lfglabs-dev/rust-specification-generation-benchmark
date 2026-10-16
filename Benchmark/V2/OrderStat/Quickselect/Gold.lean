import Benchmark.V2.Prelude
import OrderStatQuickselect.Extraction

/-! Hidden gold specification for target `order_stat/quickselect`.

API: `quickselect::select::<i32>` (Lean: `quickselect.select core.I32.Insts.CoreCmpOrd x k`),
the `&mut [i32]` argument threaded functionally (the result is the final slice). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM order_stat RSGB

/-! Computable helpers live outside `Benchmark.` so that the test driver does
not delta-expand them when searching for `Decidable` instances. -/
namespace RSGBGold.OrderStat.Quickselect

/-- Independent model: insertion sort on integer values. -/
def ins (a : Int) : List Int → List Int
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

def isort : List Int → List Int
  | [] => []
  | a :: l => ins a (isort l)

def vals (l : List Std.I32) : List Int := l.map (·.val)

/-- Same multiset of values (permutation). -/
def samePerm (a b : List Std.I32) : Bool := isort (vals a) == isort (vals b)

/-- `Slice` has no `Repr` instance, so inputs are sampled as lists. -/
def toSlice (l : List Std.I32) : Slice Std.I32 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- Values squeezed into `{-1, 0, 1}` to force many duplicates. -/
def small (x : List Std.I32) : List Std.I32 :=
  x.map (fun v => mkI .I32 (v.val % 3 - 1))

def sel (x : List Std.I32) (k : Std.Usize) : RustM (List Std.I32) := do
  let r ← quickselect.select core.I32.Insts.CoreCmpOrd (toSlice x) k
  ok r

/-- Index in range derived from a byte. -/
def kIn (x : List Std.I32) (k : Std.U8) : Std.Usize := mkU .Usize (k.val % x.length)

end RSGBGold.OrderStat.Quickselect

namespace Benchmark.V2.OrderStat.Quickselect.Gold
open RSGBGold.OrderStat.Quickselect

/-- Full contract for an in-range `k`: no panic, the result is a permutation of
the input, position `k` holds the `k`-th smallest element of the input, and the
slice is partitioned around it. -/
def selectSpec (x : List Std.I32) (k : Std.Usize) : Prop :=
  sel x k ⦃ r =>
    r.length = x.length ∧ samePerm r x = true ∧
    (isort (vals x))[k.val]? = (r[k.val]?).map (·.val) ∧
    (∀ i < r.length, i < k.val → (r[i]!).val ≤ (r[k.val]!).val) ∧
    (∀ i < r.length, k.val < i → (r[k.val]!).val ≤ (r[i]!).val) ⦄

def gold_select_kth (x : List Std.I32) (k : Std.U8) : Prop :=
  0 < x.length → selectSpec x (kIn x k)

def gold_select_kth_dups (x : List Std.I32) (k : Std.U8) : Prop :=
  0 < x.length → selectSpec (small x) (kIn x k)

/-- The `k`-th element against the upstream formulation on arbitrary `usize` `k`. -/
def gold_select_kth_any (x : List Std.I32) (k : Std.Usize) : Prop :=
  k.val < x.length → selectSpec x k

/-- For an out-of-range `k` the call still returns (no panic) a permutation of the input. -/
def gold_select_out_of_range (x : List Std.I32) (k : Std.U8) : Prop :=
  sel x (mkU .Usize (x.length + k.val)) ⦃ r => samePerm r x = true ⦄

def gold_select_out_of_range_any (x : List Std.I32) (k : Std.Usize) : Prop :=
  x.length ≤ k.val → sel x k ⦃ r => samePerm r x = true ⦄

def gold_select_out_of_range_dups (x : List Std.I32) (k : Std.U8) : Prop :=
  sel (small x) (mkU .Usize (x.length + k.val)) ⦃ r => samePerm r (small x) = true ⦄

/-! Differential-testing probes. -/

def diff_select (x : List Std.I32) (k : Std.U8) := sel x (mkU .Usize (k.val % 70))
def diff_select_dups (x : List Std.I32) (k : Std.U8) := sel (small x) (mkU .Usize (k.val % 70))

end Benchmark.V2.OrderStat.Quickselect.Gold
