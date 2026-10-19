import Benchmark.V2.Prelude
import PulzBitsetBitset.Extraction

/-! Hidden gold specification for target `pulz_bitset/bitset`.

API: `BitSet::new`, `clear`, `from_range`, `insert_range`, `contains`, `is_empty`,
`contains_all`, `insert`, `remove`, `find_next`, `extend_bitset` (union),
`remove_bitset` (difference), `retain_bitset` (intersection), `is_disjoint`.

Model-based: a `BitSet` is a finite set of `usize`. An input is a list of operations run
on the real bitset and on a model (a duplicate-free `List Nat`); results and queries are
compared after every operation, and the full contents (window of `contains`, the
`find_next` chain) at the end.

Contract freedom: the word vector may carry trailing zero words (only `remove`/
`remove_bitset`/`retain_bitset` trim them); siblings that never trim must pass.

Known defects of the shipped code that the gold spec has to steer around (not graded):
* `insert_range(a..b)` with `a ≥ b`, `b % 64 = 0` and `b/64 ≥` the word count panics
  (indexes past the vector) instead of being a no-op — only empty ranges with
  `b % 64 ≠ 0` are generated;
* `contains_all(other)` is `false` whenever `other` has more (trailing zero) words than
  `self`, even if `other` is a subset — completeness is only required for `other`
  built by a non-empty `from_range`;
* `find_next(usize::MAX)` overflows (panics) — only `value < usize::MAX` is tested. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM pulz_bitset RSGB

set_option linter.dupNamespace false

namespace RSGBGold.PulzBitset.Bitset

abbrev B := pulz_bitset.BitSet
abbrev Op := Std.U8 × Std.U16 × Std.U16

def range (a b : Nat) : core.ops.range.Range Std.Usize := { start := mkU .Usize a, «end» := mkU .Usize b }

/-- Elements: mostly in `[0, 192)` (three words), sometimes up to 400 (gaps of words). -/
def elem (x : Std.U16) : Nat := if x.val % 16 = 15 then x.val % 400 else x.val % 192

inductive Kind where
  | insert | remove | insertRange | emptyRange | clear | extend | removeSet | retainSet
  | containsAll | disjoint | findNext
  deriving DecidableEq, Repr

def kindOf (op : Op) : Kind :=
  match op.1.val % 16 with
  | 0 | 1 | 2 | 3 => .insert
  | 4 | 5 | 6 => .remove
  | 7 => .insertRange
  | 8 => if (op.1.val / 16) % 2 = 0 then .emptyRange else .insertRange
  | 9 => if (op.1.val / 16) % 4 = 0 then .clear else .insert
  | 10 => .extend
  | 11 => .removeSet
  | 12 => .retainSet
  | 13 => .containsAll
  | 14 => .disjoint
  | _ => .findNext

def aOf (op : Op) : Nat := elem op.2.1
def bOf (op : Op) : Nat := elem op.2.2
/-- Non-empty range `[a, a + 1 + b % 130)`. -/
def hiOf (op : Op) : Nat := aOf op + 1 + op.2.2.val % 130
/-- Empty range `[a', b')` with `a' ≥ b'` and `b' % 64 ≠ 0` (no panic). -/
def emptyLo (op : Op) : Nat := aOf op + 1 + op.2.2.val % 70
def emptyHi (op : Op) : Nat := if aOf op % 64 = 0 then aOf op + 1 else aOf op
/-- The "other" operand: `from_range(a .. a + b % 150)` (possibly empty → trailing zeros). -/
def otherHi (op : Op) : Nat := aOf op + op.2.2.val % 150

def other (op : Op) : RustM B := BitSet.from_range (range (aOf op) (otherHi op))

def optNat : core.option.Option Std.Usize → Option Nat
  | core.option.Option.None => none
  | core.option.Option.Some x => some x.val

/-- Result of an operation plus two cheap queries (`contains(q)`, `is_empty`). -/
structure Obs where
  res : Option Bool
  next : Option (Option Nat)
  cq : Bool
  empty : Bool
  deriving DecidableEq, Repr

def obs (s : B) (q : Nat) (res : Option Bool) (next : Option (Option Nat)) : RustM Obs := do
  let c ← BitSet.contains s (mkU .Usize q)
  let e ← BitSet.is_empty s
  ok { res, next, cq := c, empty := e }

def realStep (s : B) (op : Op) : RustM (B × Obs) := do
  let q := bOf op
  match kindOf op with
  | .insert => do
    let (r, s') ← BitSet.insert s (mkU .Usize (aOf op))
    let o ← obs s' q (some r) none
    ok (s', o)
  | .remove => do
    let (r, s') ← BitSet.remove s (mkU .Usize (aOf op))
    let o ← obs s' q (some r) none
    ok (s', o)
  | .insertRange => do
    let s' ← BitSet.insert_range s (range (aOf op) (hiOf op))
    let o ← obs s' q none none
    ok (s', o)
  | .emptyRange => do
    let s' ← BitSet.insert_range s (range (emptyLo op) (emptyHi op))
    let o ← obs s' q none none
    ok (s', o)
  | .clear => do
    let s' ← BitSet.clear s
    let o ← obs s' q none none
    ok (s', o)
  | .extend => do
    let t ← other op
    let s' ← BitSet.extend_bitset s t
    let o ← obs s' q none none
    ok (s', o)
  | .removeSet => do
    let t ← other op
    let s' ← BitSet.remove_bitset s t
    let o ← obs s' q none none
    ok (s', o)
  | .retainSet => do
    let t ← other op
    let s' ← BitSet.retain_bitset s t
    let o ← obs s' q none none
    ok (s', o)
  | .containsAll => do
    let t ← other op
    let r ← BitSet.contains_all s t
    let o ← obs s q (some r) none
    ok (s, o)
  | .disjoint => do
    let t ← other op
    let r ← BitSet.is_disjoint s t
    let o ← obs s q (some r) none
    ok (s, o)
  | .findNext => do
    let r ← BitSet.find_next s (mkU .Usize q)
    let o ← obs s q none (some (optNat r))
    ok (s, o)

def realRun (s : B) : List Op → RustM (B × List Obs)
  | [] => ok (s, [])
  | op :: ops => do
    let (s', o) ← realStep s op
    let (sf, r) ← realRun s' ops
    ok (sf, o :: r)

/-! ### Model: duplicate-free list of elements -/

def M := List Nat
def mins (m : List Nat) (x : Nat) : List Nat := if m.contains x then m else x :: m
def mdel (m : List Nat) (x : Nat) : List Nat := m.filter (· != x)
def rng (a b : Nat) : List Nat := (List.range (b - a)).map (· + a)
def munion (m t : List Nat) : List Nat := t.foldl mins m
def mnext (m : List Nat) (q : Nat) : Option Nat := (m.filter (· > q)).min?
def subset (t m : List Nat) : Bool := t.all m.contains

/-- Aspects compared along the trace. -/
inductive Aspect where
  | insRes | remRes | contains | empty | next | allSound | allComplete | disjoint
  deriving DecidableEq

def check (a : Aspect) : List Nat → List Op → List Obs → Bool
  | _, [], [] => true
  | m, op :: ops, o :: tr =>
    let t := rng (aOf op) (otherHi op)
    let (m', ok1) : List Nat × Bool :=
      match kindOf op with
      | .insert => (mins m (aOf op), a != .insRes || o.res == some (!m.contains (aOf op)))
      | .remove => (mdel m (aOf op), a != .remRes || o.res == some (m.contains (aOf op)))
      | .insertRange => (munion m (rng (aOf op) (hiOf op)), true)
      | .emptyRange => (m, true)
      | .clear => ([], true)
      | .extend => (munion m t, true)
      | .removeSet => (m.filter (fun x => !t.contains x), true)
      | .retainSet => (m.filter t.contains, true)
      | .containsAll =>
        (m, match a with
            | .allSound => o.res != some true || subset t m
            | .allComplete => !(subset t m && otherHi op > aOf op) || o.res == some true
            | _ => true)
      | .disjoint => (m, a != .disjoint || o.res == some (!t.any m.contains))
      | .findNext => (m, a != .next || o.next == some (mnext m (bOf op)))
    let ok2 : Bool :=
      match a with
      | .contains => o.cq == m'.contains (bOf op)
      | .empty => o.empty == m'.isEmpty
      | _ => true
    ok1 && ok2 && check a m' ops tr
  | _, _, _ => false

def modelOf (ops : List Op) : List Nat :=
  ops.foldl (fun m op =>
    match kindOf op with
    | .insert => mins m (aOf op)
    | .remove => mdel m (aOf op)
    | .insertRange => munion m (rng (aOf op) (hiOf op))
    | .clear => []
    | .extend => munion m (rng (aOf op) (otherHi op))
    | .removeSet => m.filter (fun x => !(rng (aOf op) (otherHi op)).contains x)
    | .retainSet => m.filter (rng (aOf op) (otherHi op)).contains
    | _ => m) []

def runNew (ops : List Op) : RustM (B × List Obs) := do
  let s ← BitSet.new
  realRun s ops

/-- `contains` on `[0, w)`. -/
def window (s : B) : Nat → RustM (List Bool)
  | 0 => ok []
  | n+1 => do
    let r ← window s n
    let c ← BitSet.contains s (mkU .Usize n)
    ok (r ++ [c])

/-- The `find_next` chain starting after `q`, at most `fuel` steps. -/
def chain (s : B) (q : Nat) : Nat → RustM (List Nat)
  | 0 => ok []
  | n+1 => do
    let r ← BitSet.find_next s (mkU .Usize q)
    match r with
    | core.option.Option.None => ok []
    | core.option.Option.Some x => do
      let rest ← chain s x.val n
      ok (x.val :: rest)

def W : Nat := 600

end RSGBGold.PulzBitset.Bitset

namespace Benchmark.V2.PulzBitset.Bitset.Gold
open RSGBGold.PulzBitset.Bitset

/-! ### Model-based traces -/

def gold_insert_result (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .insRes [] ops r.2 = true ⦄
def gold_remove_result (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .remRes [] ops r.2 = true ⦄
def gold_contains_after_each_op (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .contains [] ops r.2 = true ⦄
def gold_is_empty_after_each_op (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .empty [] ops r.2 = true ⦄
def gold_find_next_model (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .next [] ops r.2 = true ⦄
def gold_contains_all_sound (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .allSound [] ops r.2 = true ⦄
def gold_contains_all_complete (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .allComplete [] ops r.2 = true ⦄
def gold_is_disjoint_model (ops : List Op) : Prop :=
  runNew ops ⦃ r => check .disjoint [] ops r.2 = true ⦄

/-- Final contents: `contains` on a window covering every possible element. -/
def gold_final_contents (ops : List Op) : Prop :=
  (do let (s, _) ← runNew ops; window s W)
    ⦃ ws => ws = (List.range W).map (modelOf ops).contains ⦄

/-- Final contents through the `find_next` chain from 0 (plus `contains 0`). -/
def gold_final_find_next_chain (ops : List Op) : Prop :=
  (do
    let (s, _) ← runNew ops
    let c0 ← BitSet.contains s 0#usize
    let ch ← chain s 0 W
    ok ((if c0 then [0] else []) ++ ch))
    ⦃ l => l = (List.range W).filter (modelOf ops).contains ⦄

/-! ### `from_range` -/

/-- `from_range(a..b)` contains exactly `[a, b)` (empty when `a ≥ b`). -/
def gold_from_range_contents (a b : Std.U16) : Prop :=
  (do let s ← BitSet.from_range (range (a.val % 300) (b.val % 300)); window s 340)
    ⦃ ws => ws = (List.range 340).map (fun i => decide (a.val % 300 ≤ i ∧ i < b.val % 300)) ⦄

def gold_from_range_is_empty (a b : Std.U16) : Prop :=
  BitSet.from_range (range (a.val % 300) (b.val % 300)) ⦃ s =>
    BitSet.is_empty s = ok (decide (b.val % 300 ≤ a.val % 300)) ⦄

def gold_from_range_find_next (a b : Std.U16) (q : Std.U16) : Prop :=
  (do let s ← BitSet.from_range (range (a.val % 300) (b.val % 300)); BitSet.find_next s (mkU .Usize (q.val % 340)))
    ⦃ r => optNat r = mnext (rng (a.val % 300) (b.val % 300)) (q.val % 340) ⦄

/-- `insert_range` on a fresh set is `from_range` (as a set). -/
def gold_insert_range_like_from_range (a b : Std.U16) : Prop :=
  (do
    let s ← BitSet.new
    let s1 ← BitSet.insert_range s (range (a.val % 300) (a.val % 300 + 1 + b.val % 300))
    window s1 640)
    ⦃ ws => ws = (List.range 640).map
        (fun i => decide (a.val % 300 ≤ i ∧ i < a.val % 300 + 1 + b.val % 300)) ⦄

/-! ### Fresh set, huge values -/

def gold_new_empty (q : Std.Usize) : Prop :=
  (do
    let s ← BitSet.new
    let e ← BitSet.is_empty s
    let c ← BitSet.contains s q
    let (r, s1) ← BitSet.remove s q
    let e1 ← BitSet.is_empty s1
    ok (e && !c && !r && e1)) ⦃ r => r = true ⦄

/-- `contains` / `remove` / `find_next` with arbitrary (mostly huge) values. -/
def gold_huge_values (ops : List Op) (q : Std.Usize) : Prop :=
  q.val < Usize.max →
  (do
    let (s, _) ← runNew ops
    let c ← BitSet.contains s q
    let n ← BitSet.find_next s q
    let (r, s1) ← BitSet.remove s q
    let c1 ← BitSet.contains s1 q
    let e1 ← BitSet.is_empty s1
    ok (c, optNat n, r, c1, e1))
    ⦃ x => x = ((modelOf ops).contains q.val, mnext (modelOf ops) q.val, (modelOf ops).contains q.val,
               false, (mdel (modelOf ops) q.val).isEmpty) ⦄

/-- After `clear` the set is empty. -/
def gold_clear (ops : List Op) : Prop :=
  (do
    let (s, _) ← runNew ops
    let s1 ← BitSet.clear s
    let e ← BitSet.is_empty s1
    let ws ← window s1 W
    ok (e && ws.all (· == false))) ⦃ r => r = true ⦄

/-! Differential-testing probes. -/

def diff_trace (ops : List Op) := (do let (s, o) ← runNew ops; let w ← window s 400; ok (o, w))
def diff_from_range (a b : Std.U16) :=
  (do let s ← BitSet.from_range (range (a.val % 300) (b.val % 300)); window s 340)
def diff_huge (ops : List Op) (q : Std.Usize) := (do
  let (s, _) ← runNew ops
  let c ← BitSet.contains s q
  let n ← if q.val < Usize.max then BitSet.find_next s q else ok core.option.Option.None
  ok (c, optNat n))

end Benchmark.V2.PulzBitset.Bitset.Gold
