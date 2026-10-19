import Benchmark.V2.Prelude
import FixedbitsetBitset.Extraction

/-! Hidden gold specification for target `fixedbitset/bitset` (fixedbitset 0.4.2).

API: `FixedBitSet::{new, with_capacity, grow, len, is_empty, contains, insert, put,
toggle, set, copy_bit, set_range, insert_range, toggle_range, as_slice}` with the
`IndexRange` impls for `Range`, `RangeFrom`, `RangeTo`, `RangeFull`.

Model: a bit set of length `n` is a list of `n` booleans. `contains` is `false`
outside the capacity; the point operations panic iff the index is `≥ len`
(`copy_bit` only checks `to`; an out-of-range `from` reads `false`); the range
operations panic iff `start > end` or `end > len` (`..`, `a..`, `..b` default to
`0` / `len`); `grow(k)` raises the length to `max(len, k)` with new bits clear;
`put` returns the previous value. `as_slice` exposes the `u32` blocks: bit `i` is
bit `i % 32` of block `i / 32`, bits past `len` are clear. How many blocks are kept
(beyond the `⌈len/32⌉` needed) is not promised. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM fixedbitset RSGB

namespace RSGBGold.Fixedbitset.Bitset

abbrev Op := Std.U8 × Std.U8 × Std.U8 × Bool

def RI := core.ops.range.Range.Insts.FixedbitsetRangeIndexRange core.Usize.Insts.CoreMarkerCopy
def RFromI := core.ops.range.RangeFrom.Insts.FixedbitsetRangeIndexRange core.Usize.Insts.CoreMarkerCopy
def RToI := core.ops.range.RangeTo.Insts.FixedbitsetRangeIndexRange core.Usize.Insts.CoreMarkerCopy
def RFullI := core.ops.range.RangeFull.Insts.FixedbitsetRangeIndexRange Std.Usize

def us (n : Nat) : Std.Usize := mkU .Usize n

/-- Operation families (the tag is remapped so that one property exercises a subset). -/
inductive Fam | all | point | range | boundary | grow

def tagOf : Fam → Nat → Nat
  | .all, t => t % 12
  | .point, t => t % 5
  | .range, t => [5, 6, 7, 9, 10, 11].getD (t % 6) 5
  | .boundary, t => [5, 6, 7, 10, 11, 4].getD (t % 6) 5
  | .grow, t => [8, 0, 1, 5, 7, 4, 2].getD (t % 7) 8

/-- Point index: mostly in range, out of range for large draws (or an empty set). -/
def idx (n x : Nat) : Nat := if 240 ≤ x ∨ n = 0 then n + x % 8 else x % n

/-- One raw range endpoint: near the length, or at block boundaries. -/
def endp (f : Fam) (n x : Nat) : Nat :=
  match f with
  | .boundary => [0, 1, 31, 32, 33, 63, 64, 65, 95, 96, 97, n, n + 1, n - 1].getD (x % 14) 0
  | _ => x % (n + 4)

/-- Range `(start, end)`: usually a valid range (sorted, clamped to `n`); for large `y`
the raw endpoints (possibly reversed or past the end). -/
def rng2 (f : Fam) (n x y : Nat) : Nat × Nat :=
  let a := endp f n x
  let b := endp f n y
  if 224 ≤ y then (a, b) else (min (min a b) n, min (max a b) n)

/-! Model: `(len, bits)`; `none` = panic. -/

abbrev St := Nat × List Bool

def getB (l : List Bool) (i : Nat) : Bool := l.getD i false

def setRange (l : List Bool) (a b : Nat) (g : Bool → Bool) : List Bool :=
  (List.range l.length).map (fun j => if a ≤ j ∧ j < b then g (getB l j) else getB l j)

def mRange (s : St) (a b : Nat) (g : Bool → Bool) : Option St :=
  if a ≤ b ∧ b ≤ s.1 then some (s.1, setRange s.2 a b g) else none

def mPoint (s : St) (i : Nat) (v : Bool) : Option St :=
  if i < s.1 then some (s.1, s.2.set i v) else none

def mStep (f : Fam) (s : St) (o : Op) : Option (St × List Bool) :=
  let (t, x, y, b) := o
  let n := s.1
  let i := idx n x.val
  let (a, c) := rng2 f n x.val y.val
  match tagOf f t.val with
  | 0 => (mPoint s i true).map (·, [])
  | 1 => (mPoint s i true).map (·, [getB s.2 i])
  | 2 => (mPoint s i (!getB s.2 i)).map (·, [])
  | 3 => (mPoint s i b).map (·, [])
  | 4 => (mPoint s (idx n y.val) (getB s.2 i)).map (·, [])
  | 5 => (mRange s a c (fun _ => b)).map (·, [])
  | 6 => (mRange s a c (fun _ => true)).map (·, [])
  | 7 => (mRange s a c (fun v => !v)).map (·, [])
  | 8 =>
    let k := x.val % 150
    some ((if k > n then (k, s.2 ++ List.replicate (k - n) false) else s), [])
  | 9 => (mRange s 0 n (fun _ => b)).map (·, [])
  | 10 => (mRange s a n (fun v => !v)).map (·, [])
  | _ => (mRange s 0 c (fun _ => true)).map (·, [])

def mRun (f : Fam) : St → List Op → Option (St × List Bool)
  | s, [] => some (s, [])
  | s, o :: os => match mStep f s o with
    | none => none
    | some (s', p) => (mRun f s' os).map (fun (s'', ps) => (s'', p ++ ps))

/-! Implementation driver (public API only). -/

def iStep (f : Fam) (s : FixedBitSet) (o : Op) : RustM (FixedBitSet × List Bool) := do
  let (t, x, y, b) := o
  let nn ← FixedBitSet.len s
  let n := nn.val
  let i := us (idx n x.val)
  let (a0, c0) := rng2 f n x.val y.val
  let a := us a0
  let c := us c0
  match tagOf f t.val with
  | 0 => do let s' ← FixedBitSet.insert s i; ok (s', [])
  | 1 => let (p, s') ← FixedBitSet.put s i; ok (s', [p])
  | 2 => do let s' ← FixedBitSet.toggle s i; ok (s', [])
  | 3 => do let s' ← FixedBitSet.set s i b; ok (s', [])
  | 4 => do let s' ← FixedBitSet.copy_bit s i (us (idx n y.val)); ok (s', [])
  | 5 => do let s' ← FixedBitSet.set_range RI s ⟨a, c⟩ b; ok (s', [])
  | 6 => do let s' ← FixedBitSet.insert_range RI s ⟨a, c⟩; ok (s', [])
  | 7 => do let s' ← FixedBitSet.toggle_range RI s ⟨a, c⟩; ok (s', [])
  | 8 => do let s' ← FixedBitSet.grow s (us (x.val % 150)); ok (s', [])
  | 9 => do let s' ← FixedBitSet.set_range RFullI s () b; ok (s', [])
  | 10 => do let s' ← FixedBitSet.toggle_range RFromI s ⟨a⟩; ok (s', [])
  | _ => do let s' ← FixedBitSet.insert_range RToI s ⟨c⟩; ok (s', [])

def iRun (f : Fam) : FixedBitSet → List Op → RustM (FixedBitSet × List Bool)
  | s, [] => ok (s, [])
  | s, o :: os => do
    let (s', p) ← iStep f s o
    let (s'', ps) ← iRun f s' os
    ok (s'', p ++ ps)

/-- Observations: length and `contains` on `[0, len + 40)`. -/
def obs (s : FixedBitSet) : RustM (Nat × List Bool) := do
  let nn ← FixedBitSet.len s
  let n := nn.val
  let l ← (List.range (n + 40)).mapM (fun i => FixedBitSet.contains s (us i))
  ok (n, l)

def cap (c : Std.U8) : Nat := c.val % 130

def start (c : Std.U8) : RustM FixedBitSet := FixedBitSet.with_capacity (us (cap c))

def mObs (s : St) : Nat × List Bool := (s.1, s.2 ++ List.replicate 40 false)

/-- The run panics exactly when the model does; otherwise the observations agree. -/
def seqContainsOk (f : Fam) (c : Std.U8) (ops : List Op) : Bool :=
  let r := (do let s0 ← start c; let (s, _) ← iRun f s0 ops; obs s)
  match mRun f (cap c, List.replicate (cap c) false) ops, r with
  | none, .fail .panic => true
  | some (s, _), .ok o => o == mObs s
  | _, _ => false

def seqPanicOk (f : Fam) (c : Std.U8) (ops : List Op) : Bool :=
  let r := (do let s0 ← start c; let _ ← iRun f s0 ops; ok ())
  match mRun f (cap c, List.replicate (cap c) false) ops, r with
  | none, .fail .panic => true
  | some _, .ok _ => true
  | _, _ => false

def seqPutOk (c : Std.U8) (ops : List Op) : Bool :=
  match mRun .all (cap c, List.replicate (cap c) false) ops,
        (do let s0 ← start c; let (_, ps) ← iRun .all s0 ops; ok ps) with
  | some (_, ps), .ok ps' => ps == ps'
  | _, _ => true

def blockBit (sl : List Std.U32) (i : Nat) : Bool := ((sl.getD (i / 32) ⟨0#32⟩).val >>> (i % 32)) % 2 == 1

def sliceOk (s : St) (sl : List Std.U32) : Bool :=
  decide (s.1 ≤ 32 * sl.length) &&
  (List.range (32 * sl.length)).all (fun i => blockBit sl i == (decide (i < s.1) && getB s.2 i))

def seqSliceOk (c : Std.U8) (ops : List Op) : Bool :=
  match mRun .all (cap c, List.replicate (cap c) false) ops,
        (do let s0 ← start c; let (s, _) ← iRun .all s0 ops; let sl ← FixedBitSet.as_slice s; ok sl.val) with
  | some (s, _), .ok sl => sliceOk s sl
  | _, _ => true

end RSGBGold.Fixedbitset.Bitset

namespace Benchmark.V2.Fixedbitset.Bitset.Gold
open RSGBGold.Fixedbitset.Bitset

/-- Mixed operation sequences behave like the bit-list model (contents, length, panics). -/
def gold_seq_all (c : Std.U8) (ops : List Op) : Prop := seqContainsOk .all c ops = true

/-- Point operations (`insert`, `put`, `toggle`, `set`, `copy_bit`). -/
def gold_seq_point (c : Std.U8) (ops : List Op) : Prop := seqContainsOk .point c ops = true

/-- Range operations with all range kinds. -/
def gold_seq_range (c : Std.U8) (ops : List Op) : Prop := seqContainsOk .range c ops = true

/-- Range endpoints on 32-bit block boundaries and around the length. -/
def gold_seq_boundary (c : Std.U8) (ops : List Op) : Prop := seqContainsOk .boundary c ops = true

/-- Interleaving `grow` with updates: new bits are clear, old bits kept, length = max. -/
def gold_seq_grow (c : Std.U8) (ops : List Op) : Prop := seqContainsOk .grow c ops = true

/-- Panics happen exactly at out-of-range indices / invalid ranges. -/
def gold_seq_panics (c : Std.U8) (ops : List Op) : Prop := seqPanicOk .all c ops = true

def gold_seq_panics_boundary (c : Std.U8) (ops : List Op) : Prop := seqPanicOk .boundary c ops = true

/-- `put` returns the previous value of the bit. -/
def gold_seq_put (c : Std.U8) (ops : List Op) : Prop := seqPutOk c ops = true

/-- `as_slice`: block layout (bit `i` = bit `i % 32` of block `i / 32`), clear past `len`. -/
def gold_seq_slice (c : Std.U8) (ops : List Op) : Prop := seqSliceOk c ops = true

/-- Constructors. -/
def gold_new : Prop :=
  (do let s ← FixedBitSet.new; let n ← FixedBitSet.len s; let e ← FixedBitSet.is_empty s
      let b ← FixedBitSet.contains s (us 0); ok (n.val, e, b)) = ok (0, true, false)

def gold_with_capacity (c : Std.U16) (i : Std.Usize) : Prop :=
  (do let s ← FixedBitSet.with_capacity (us (c.val % 2000)); let n ← FixedBitSet.len s
      let e ← FixedBitSet.is_empty s; let b ← FixedBitSet.contains s i; ok (n.val, e, b))
    = ok (c.val % 2000, decide (c.val % 2000 = 0), false)

def growOk (c k : Std.U8) (ops : List Op) : Bool :=
  match mRun .point (cap c, List.replicate (cap c) false) ops with
  | none => true
  | some (s, _) =>
    let m := max s.1 k.val
    (do let s0 ← start c
        let (t, _) ← iRun .point s0 ops
        let t ← FixedBitSet.grow t (us k.val)
        let n ← FixedBitSet.len t; let e ← FixedBitSet.is_empty t
        let l ← (List.range (n.val + 8)).mapM (fun i => FixedBitSet.contains t (us i))
        ok (n.val, e, l)) == ok (m, decide (m = 0), s.2 ++ List.replicate (m - s.1 + 8) false)

/-- `grow` and `is_empty` on a populated set. -/
def gold_grow_len (c k : Std.U8) (ops : List Op) : Prop := growOk c k ops = true

/-- `contains` never panics, any index (incl. huge ones). -/
def gold_contains_total (c : Std.U8) (i : Std.Usize) : Prop :=
  (do let s ← start c; let s ← FixedBitSet.insert_range RFullI s (); FixedBitSet.contains s i)
    = ok (decide (i.val < cap c))

/-! Differential-testing probes. -/

def diff_seq (c : Std.U8) (ops : List Op) := do let s0 ← start c; let (s, p) ← iRun .all s0 ops; let o ← obs s; ok (o, p)
def diff_seq_boundary (c : Std.U8) (ops : List Op) := do let s0 ← start c; let (s, p) ← iRun .boundary s0 ops; let o ← obs s; ok (o, p)
def diff_seq_grow (c : Std.U8) (ops : List Op) := do let s0 ← start c; let (s, p) ← iRun .grow s0 ops; let o ← obs s; ok (o, p)
def diff_slice (c : Std.U8) (ops : List Op) :=
  do let s0 ← start c; let (s, _) ← iRun .all s0 ops; let sl ← FixedBitSet.as_slice s; ok (sl.val.map (fun (x : Std.U32) => x.val))
def diff_contains (c : Std.U8) (i : Std.Usize) :=
  do let s ← start c; let s ← FixedBitSet.insert_range RFullI s (); FixedBitSet.contains s i

end Benchmark.V2.Fixedbitset.Bitset.Gold
