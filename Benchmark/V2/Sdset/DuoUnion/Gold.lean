import Benchmark.V2.Prelude
import SdsetDuoUnion.Extraction

/-! Hidden gold specification for target `sdset/duo_union` (elements instantiated at `i32`). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM sdset RSGB


/-! ## Data helpers (kept outside the `Benchmark` namespace so that the test
driver does not unfold them). -/
namespace RSGBGold.SdsetDuoUnion

/-- A slice from a list (lists from the generator are short). -/
def toSlice (l : List Std.I32) : Slice Std.I32 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- Sorted, deduplicated version of `l` (a valid `Set`). -/
def setOf (l : List Std.I32) : Slice Std.I32 :=
  toSlice ((l.mergeSort (fun x y => decide (x.val ≤ y.val))).eraseDups)

abbrev It := duo.union.UnionIter Std.I32

def nxt (s : It) := duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next core.I32.Insts.CoreCmpOrd s

/-- `Vec::from_iter`: call `next` until `None`, at most `fuel` times (`none` if
the fuel runs out, i.e. the iterator did not finish). -/
def collect : Nat → It → RustM (Option (List Std.I32))
  | 0, _ => ok none
  | n + 1, s => do
    let (o, s') ← nxt s
    match o with
    | none => ok (some [])
    | some x => do
      let r ← collect n s'
      ok (r.map (x :: ·))

def vals (l : List Std.I32) : List Int := l.map (·.val)

def mkUnion (a b : Slice Std.I32) : duo.union.Union Std.I32 := { a := a, b := b }
def fuel (a b : Slice Std.I32) : Nat := a.val.length + b.val.length + 2

def hd (l : List Std.I32) : Std.I32 := l.headD 0#i32

/-- Expected item of one `next` step on the sets `a`, `b`. -/
def expHead (a b : List Std.I32) : Option Std.I32 :=
  if a = [] then b.head? else if b = [] then a.head?
  else if (hd a).val ≤ (hd b).val then a.head? else b.head?

/-- What remains to be merged after that step. -/
def expRest (a b : List Std.I32) : List Std.I32 × List Std.I32 :=
  if a = [] then ([], b.tail) else if b = [] then (a.tail, [])
  else if (hd a).val < (hd b).val then (a.tail, b)
  else if (hd a).val = (hd b).val then (a.tail, b.tail) else (a, b.tail)

end RSGBGold.SdsetDuoUnion

namespace Benchmark.V2.Sdset.DuoUnion.Gold

open RSGBGold.SdsetDuoUnion

/-- `r` is the sorted union of the sets `a` and `b`: strictly increasing and
containing exactly the elements of `a` and of `b`. -/
def IsUnion (a b r : List Std.I32) : Prop :=
  (vals r).Pairwise (· < ·) ∧ (∀ x ∈ vals r, x ∈ vals a ∨ x ∈ vals b) ∧
  (∀ x ∈ vals a, x ∈ vals r) ∧ (∀ x ∈ vals b, x ∈ vals r)

/-! ## The union iterator yields exactly the sorted union, once each -/

/-- Iterating `Union::new(a, b)` (by value) terminates without panicking and
yields the sorted, deduplicated union. -/
def gold_union_iter (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let u ← duo.union.Union.new a b
      let it ← duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
      collect (fuel a b) it) ⦃ r => r.isSome ∧ IsUnion a.val b.val (r.getD []) ⦄

/-- Same through `IntoIterator for &Union`. -/
def gold_union_iter_ref (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let u ← duo.union.Union.new a b
      let it ← SharedAUnion.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
      collect (fuel a b) it) ⦃ r => r.isSome ∧ IsUnion a.val b.val (r.getD []) ⦄

/-- Exact length: `|a ∪ b| = |a| + |b| - |a ∩ b|`. -/
def gold_union_length (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let it ← duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd (mkUnion a b)
      collect (fuel a b) it) ⦃ r => r.isSome ∧
        (r.getD []).length + (vals a.val).countP (· ∈ vals b.val) = a.val.length + b.val.length ⦄

/-- The union is symmetric (as a sequence of values). -/
def gold_union_comm (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let r1 ← collect (fuel a b) { a := a, b := b }
      let r2 ← collect (fuel a b) { a := b, b := a }
      ok (r1, r2)) ⦃ (r1, r2) => r1.map vals = r2.map vals ⦄

/-- Union with the empty set (either side) is the identity; union with itself too. -/
def gold_union_identity (la : List Std.I32) : Prop :=
  let a := setOf la
  collect (fuel a a) { a := a, b := toSlice [] } = ok (some a.val) ∧
  collect (fuel a a) { a := toSlice [], b := a } = ok (some a.val) ∧
  collect (fuel a a) { a := a, b := a } = ok (some a.val)

/-! ## One step of `next` -/

/-- `next` returns `None` exactly when both sides are exhausted, otherwise the
smaller head (once, if both heads are equal); the remaining iterator yields the
union of what is left. -/
def gold_next_step (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let r ← nxt { a := a, b := b }
      let rest ← collect (fuel a b) r.2
      ok (r.1, rest)) ⦃ p =>
    p.1 = expHead a.val b.val ∧ p.2.isSome ∧
    IsUnion (expRest a.val b.val).1 (expRest a.val b.val).2 (p.2.getD []) ⦄

/-- Once exhausted, the iterator stays exhausted (fused) and unchanged. -/
def gold_next_fused (_u : Std.U8) : Prop :=
  nxt { a := toSlice [], b := toSlice [] } = ok (none, { a := toSlice [], b := toSlice [] })

/-! ## Plumbing -/

def gold_new_and_into_iter (la lb : List Std.I32) : Prop :=
  let a := setOf la
  let b := setOf lb
  (do let u ← duo.union.Union.new a b
      let i1 ← duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
      let i2 ← SharedAUnion.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
      let r1 ← collect (fuel a b) i1
      let r2 ← collect (fuel a b) i2
      let r3 ← collect (fuel a b) { a := a, b := b }
      ok (r1, r2, r3)) ⦃ (r1, r2, r3) => r1 = r3 ∧ r2 = r3 ⦄

def gold_as_slice_clone (la lb : List Std.I32) : Prop :=
  set.Set.as_slice (toSlice la) = ok (toSlice la) ∧
  (do let u ← duo.union.Union.Insts.CoreCloneClone.clone core.I32.Insts.CoreCloneClone (mkUnion (toSlice la) (toSlice lb))
      ok (u.a, u.b)) = ok (toSlice la, toSlice lb)

/-! Differential-testing probes. -/

def diff_union (la lb : List Std.I32) :=
  let a := setOf la
  let b := setOf lb
  do let u ← duo.union.Union.new a b
     let it ← duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
     collect (fuel a b) it
def diff_union_ref (la lb : List Std.I32) :=
  let a := setOf la
  let b := setOf lb
  do let u ← duo.union.Union.new a b
     let it ← SharedAUnion.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter
        core.I32.Insts.CoreCmpOrd u
     collect (fuel a b) it
def diff_next (la lb : List Std.I32) :=
  do let (o, s) ← nxt { a := setOf la, b := setOf lb }
     ok (o, s.a.val, s.b.val)
def diff_clone (la lb : List Std.I32) :=
  do let u ← duo.union.Union.Insts.CoreCloneClone.clone core.I32.Insts.CoreCloneClone (mkUnion (toSlice la) (toSlice lb))
     ok (u.a.val, u.b.val)
def diff_as_slice (la : List Std.I32) := do let s ← set.Set.as_slice (toSlice la); ok s.val

end Benchmark.V2.Sdset.DuoUnion.Gold
