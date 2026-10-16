import Benchmark.V2.Prelude
import BlueScrunchBinarySearch.Extraction

/-! Hidden gold specification for target `blue/scrunch_binary_search`.

API: `binary_search::binary_search_by(first, last, search)` and
`binary_search::partition_by(first, last, search)`, generic over the closure.
The properties instantiate the closure with small Lean closure types whose
`call_mut` evaluates a function of the probe index and *panics* when probed
outside `[first, last)` or when a call budget of `⌊log₂(last - first)⌋ + 1`
calls is exceeded (so "never evaluates `search(last)`", "only probes inside the
range" and "logarithmically many probes" are observable). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM scrunch RSGB

/-! Computable helpers (outside `Benchmark.` so the driver does not unfold them). -/
namespace RSGBGold.Blue.ScrunchBinarySearch

/-- Ordering-valued closure state. -/
structure OProbe where
  f : Nat → core.cmp.Ordering
  lo : Nat
  hi : Nat
  budget : Nat

def OProbe.step (c : OProbe) (x : Std.Usize) : RustM (core.cmp.Ordering × OProbe) :=
  if x.val < c.lo ∨ c.hi ≤ x.val ∨ c.budget = 0 then fail .panic
  else ok (c.f x.val, { c with budget := c.budget - 1 })

def OProbe.inst : core.ops.function.FnMut OProbe Std.Usize core.cmp.Ordering where
  FnOnceInst := { call_once := fun c x => do let (o, _) ← c.step x; ok o }
  call_mut := OProbe.step

/-- Bool-valued closure state. -/
structure BProbe where
  f : Nat → Bool
  lo : Nat
  hi : Nat
  budget : Nat

def BProbe.step (c : BProbe) (x : Std.Usize) : RustM (Bool × BProbe) :=
  if x.val < c.lo ∨ c.hi ≤ x.val ∨ c.budget = 0 then fail .panic
  else ok (c.f x.val, { c with budget := c.budget - 1 })

def BProbe.inst : core.ops.function.FnMut BProbe Std.Usize Bool where
  FnOnceInst := { call_once := fun c x => do let (o, _) ← c.step x; ok o }
  call_mut := BProbe.step

def budget (first last : Nat) : Nat := Nat.log2 (last - first) + 1

def cmpNat (a b : Nat) : core.cmp.Ordering :=
  if a < b then .Less else if a = b then .Equal else .Greater

def isLess : core.cmp.Ordering → Bool | .Less => true | _ => false
def isEqual : core.cmp.Ordering → Bool | .Equal => true | _ => false
def isGreater : core.cmp.Ordering → Bool | .Greater => true | _ => false

def ordOf (v : Std.U8) : core.cmp.Ordering :=
  if v.val % 3 = 0 then .Less else if v.val % 3 = 1 then .Equal else .Greater

/-- Guarded call of `binary_search_by` on `[first, last)` with comparator `f`. -/
def bs (first last : Nat) (f : Nat → core.cmp.Ordering) : RustM Std.Usize :=
  binary_search.binary_search_by OProbe.inst (mkU .Usize first) (mkU .Usize last)
    { f, lo := first, hi := last, budget := budget first last }

def pb (first last : Nat) (f : Nat → Bool) : RustM Std.Usize :=
  binary_search.partition_by BProbe.inst (mkU .Usize first) (mkU .Usize last)
    { f, lo := first, hi := last, budget := budget first last }

/-- Unguarded calls (for differential probes); the call budget turns infinite loops into panics. -/
def bsFree (first last : Std.Usize) (f : Nat → core.cmp.Ordering) : RustM Std.Usize :=
  binary_search.binary_search_by OProbe.inst first last { f, lo := 0, hi := 2^64, budget := 300 }

def pbFree (first last : Std.Usize) (f : Nat → Bool) : RustM Std.Usize :=
  binary_search.partition_by BProbe.inst first last { f, lo := 0, hi := 2^64, budget := 300 }

/-- Monotone comparator on `[first, first + n)`: `a` × Less, `b` × Equal, then Greater. -/
def mono (first a b : Nat) (x : Nat) : core.cmp.Ordering :=
  if x < first + a then .Less else if x < first + a + b then .Equal else .Greater

/-- Comparator read from a table (index relative to `first`). -/
def tblOrd (first : Nat) (t : List Std.U8) (x : Nat) : core.cmp.Ordering :=
  ordOf (t.getD (x - first) 0#u8)

def tblBool (first : Nat) (t : List Bool) (x : Nat) : Bool := t.getD (x - first) false

end RSGBGold.Blue.ScrunchBinarySearch

namespace Benchmark.V2.Blue.ScrunchBinarySearch.Gold
open RSGBGold.Blue.ScrunchBinarySearch

/-! ## `binary_search_by` -/

/-- Searching the identity sequence for `t` (comparator `x.cmp(&t)`): exact result,
no panic for any `usize` bounds (no overflow), only probes inside `[first, last)`,
at most `⌊log₂(last-first)⌋+1` probes. Empty/inverted ranges return `first`. -/
def gold_bs_identity (first last t : Std.Usize) : Prop :=
  bs first.val last.val (fun x => cmpNat x t.val) =
    ok (if first.val < last.val then mkU .Usize (min (max t.val first.val) last.val) else first)

/-- Empty or inverted range: returns `first` without calling `search`. -/
def gold_bs_empty (first last : Std.Usize) (t : List Std.U8) : Prop :=
  last.val ≤ first.val → bs first.val last.val (tblOrd first.val t) = ok first

/-- Monotone comparator (Less* Equal* Greater*) on a range anywhere in `usize`:
with an `Equal` block inside the range the result lies in that block; otherwise
it is the first index whose comparison is not `Less` (or `last`). -/
def gold_bs_monotone (first : Std.Usize) (n a b : Std.U16) : Prop :=
  first.val + n.val ≤ Usize.max →
    bs first.val (first.val + n.val) (mono first.val a.val b.val) ⦃ r =>
      if a.val < n.val ∧ 0 < b.val then
        first.val + a.val ≤ r.val ∧ r.val < first.val + min (a.val + b.val) n.val
      else r.val = first.val + min a.val n.val ⦄

/-- Arbitrary (not necessarily sorted) comparator: never panics, stays in
`[first, last]`, and the result is a local witness: either `search(r) = Equal`,
or (`r = first` or `search(r-1) = Less`) and (`r = last` or `search(r) = Greater`). -/
def gold_bs_arbitrary (first : Std.Usize) (t : List Std.U8) : Prop :=
  first.val + t.length ≤ Usize.max →
    bs first.val (first.val + t.length) (tblOrd first.val t) ⦃ r =>
      first.val ≤ r.val ∧ r.val ≤ first.val + t.length ∧
      ((r.val < first.val + t.length ∧ isEqual (tblOrd first.val t r.val)) ∨
       ((r.val = first.val ∨ isLess (tblOrd first.val t (r.val - 1))) ∧
        (r.val = first.val + t.length ∨ isGreater (tblOrd first.val t r.val)))) ⦄

/-- Upstream shape: sorted distinct vector, search position `i` over `[0, len-1]`. -/
def gold_bs_sorted_vec (gaps : List Std.U8) (i : Std.U8) : Prop :=
  let elems : List Nat := (gaps.foldl (fun (acc : List Nat × Nat) g => (acc.1 ++ [acc.2 + g.val + 1], acc.2 + g.val + 1)) ([], 0)).1
  0 < elems.length →
    let k := i.val % elems.length
    bs 0 (elems.length - 1) (fun x => cmpNat (elems.getD x 0) (elems.getD k 0)) = ok (mkU .Usize k)

/-! ## `partition_by` -/

/-- Predicate `x < t` on the identity sequence: exact result. -/
def gold_pb_identity (first last t : Std.Usize) : Prop :=
  pb first.val last.val (fun x => decide (x < t.val)) =
    ok (if first.val < last.val then mkU .Usize (min (max t.val first.val) last.val) else first)

/-- Partitioned predicate (`a` trues then falses): the first false index in
`[first, last)`, or `last` if all are true. -/
def gold_pb_partitioned (first : Std.Usize) (n a : Std.U16) : Prop :=
  first.val + n.val ≤ Usize.max →
    pb first.val (first.val + n.val) (fun x => decide (x < first.val + a.val)) =
      ok (mkU .Usize (first.val + min a.val n.val))

def gold_pb_empty (first last : Std.Usize) (t : List Bool) : Prop :=
  last.val ≤ first.val → pb first.val last.val (tblBool first.val t) = ok first

/-- Arbitrary predicate: never panics, result in `[first, last]`, with
(`r = first` or `search(r-1)`) and (`r = last` or `¬search(r)`). -/
def gold_pb_arbitrary (first : Std.Usize) (t : List Bool) : Prop :=
  first.val + t.length ≤ Usize.max →
    pb first.val (first.val + t.length) (tblBool first.val t) ⦃ r =>
      first.val ≤ r.val ∧ r.val ≤ first.val + t.length ∧
      (r.val = first.val ∨ tblBool first.val t (r.val - 1) = true) ∧
      (r.val = first.val + t.length ∨ tblBool first.val t r.val = false) ⦄

/-! Differential-testing probes. -/

def diff_bs_identity (first last t : Std.Usize) := bsFree first last (fun x => cmpNat x t.val)
def diff_bs_small (first last t : Std.U8) :=
  bsFree (mkU .Usize first.val) (mkU .Usize last.val) (fun x => cmpNat x t.val)
def diff_bs_table (first : Std.U8) (t : List Std.U8) :=
  bsFree (mkU .Usize first.val) (mkU .Usize (first.val + t.length)) (tblOrd first.val t)
def diff_pb_identity (first last t : Std.Usize) := pbFree first last (fun x => decide (x < t.val))
def diff_pb_small (first last t : Std.U8) :=
  pbFree (mkU .Usize first.val) (mkU .Usize last.val) (fun x => decide (x < t.val))
def diff_pb_table (first : Std.U8) (t : List Bool) :=
  pbFree (mkU .Usize first.val) (mkU .Usize (first.val + t.length)) (tblBool first.val t)

end Benchmark.V2.Blue.ScrunchBinarySearch.Gold
