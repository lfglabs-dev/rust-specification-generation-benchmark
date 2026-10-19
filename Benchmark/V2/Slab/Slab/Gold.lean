import Benchmark.V2.Prelude
import SlabSlab.Extraction

/-! Hidden gold specification for target `slab/slab`.

API (instantiated at `T = u32`): `Slab::new`, `with_capacity`, `insert`, `vacant_key`,
`vacant_entry` + `VacantEntry::key` / `VacantEntry::insert`, `try_remove`, `remove`, `get`,
`get_mut`, `contains`, `len`, `is_empty`, `clear`.

Model-based: an input is a short list of operations, run on the real slab while an
abstract model (a finite map key ↦ value plus the number `H` of slots ever handed out)
is stepped alongside. Observables are compared after every operation.

Contract freedom: *which* vacant key `insert` reuses is not promised ("keys may be
reused"); only that the key is vacant, equals `vacant_key()`, and that a vacant slot is
reused before a new one is created (the slab never grows while it has holes; keys of a
fresh slab are handed out as `0, 1, 2, …`). A sibling implementation with a different
free-list discipline checks that the gold spec does not pin the LIFO order. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM slab RSGB

set_option linter.dupNamespace false

namespace RSGBGold.Slab.Slab

abbrev S := slab.Slab Std.U32
abbrev Op := Std.U8 × Std.U8 × Std.U32

def optNat : core.option.Option Std.U32 → Option Nat
  | core.option.Option.None => none
  | core.option.Option.Some x => some x.val

/-- Result of one operation. -/
inductive Res where
  | ins (k : Nat)
  | val (o : Option Nat)
  | unit
  | panic
  deriving DecidableEq, Repr

/-- Everything observable after one operation (`get`/`contains` on a window of keys). -/
structure Obs where
  res : Res
  len : Nat
  empty : Bool
  vkey : Nat
  gets : List (Option Nat)
  conts : List Bool
  deriving DecidableEq, Repr

inductive Kind where
  | insert | remove | tryRemove | setMut | entry | clear | get
  deriving DecidableEq, Repr

def kindOf (op : Op) : Kind :=
  match op.1.val % 16 with
  | 0 | 1 | 2 | 3 | 4 | 5 => .insert
  | 6 | 7 => .remove
  | 8 | 9 => .tryRemove
  | 10 => .setMut
  | 11 | 12 => .entry
  | 13 => if (op.1.val / 16) % 2 = 0 then .clear else .insert
  | 14 => .get
  | _ => .tryRemove

/-- Keys mostly in a small window (hits present keys and holes), sometimes huge. -/
def keyOf (op : Op) : Nat :=
  if op.2.1.val ≥ 248 then op.2.1.val * 2^40 + op.2.1.val else op.2.1.val % 12

def valOf (op : Op) : Std.U32 := op.2.2

def snapshot (s : S) : Nat → RustM (List (Option Nat) × List Bool)
  | 0 => ok ([], [])
  | n+1 => do
    let (gs, cs) ← snapshot s n
    let g ← slab.Slab.get s (mkU .Usize n)
    let c ← slab.Slab.contains s (mkU .Usize n)
    ok (gs ++ [optNat g], cs ++ [c])

def observe (s : S) (res : Res) (w : Nat) : RustM Obs := do
  let n ← slab.Slab.impl.len s
  let e ← slab.Slab.is_empty s
  let v ← slab.Slab.vacant_key s
  let (gs, cs) ← snapshot s w
  ok { res, len := n.val, empty := e, vkey := v.val, gets := gs, conts := cs }

/-- Insert through `vacant_entry`: returns (entry key, value reference, new slab). -/
def entryInsert (s : S) (x : Std.U32) : RustM (Nat × Nat × S) := do
  let (ve, back) ← slab.Slab.vacant_entry s
  let k ← slab.VacantEntry.impl.key ve
  let (r, back2) ← slab.VacantEntry.insert ve x
  ok (k.val, r.val, back (back2 r))

/-- Run the operations on the real slab. `hw` is one more than the largest key seen so
far; the snapshot window covers keys `< hw + 2`. A panicking operation ends the trace. -/
def realRun (s : S) (hw : Nat) : List Op → RustM (List Obs)
  | [] => do
    let o ← observe s .unit (hw + 2)
    ok [o]
  | op :: ops => do
    let k := mkU .Usize (keyOf op)
    match kindOf op with
    | .insert =>
      let (key, s') ← slab.Slab.insert s (valOf op)
      let hw' := max hw (key.val + 1)
      let o ← observe s' (.ins key.val) 14
      let r ← realRun s' hw' ops
      ok (o :: r)
    | .entry =>
      let (key, rv, s') ← entryInsert s (valOf op)
      let hw' := max hw (key + 1)
      let o ← observe s' (if rv = (valOf op).val then .ins key else .panic) 14
      let r ← realRun s' hw' ops
      ok (o :: r)
    | .remove =>
      match slab.Slab.remove s k with
      | .ok (v, s') =>
        let o ← observe s' (.val (some v.val)) 14
        let r ← realRun s' hw ops
        ok (o :: r)
      | .fail _ =>
        let o ← observe s .panic 14
        ok [o]
      | .div => ok []
    | .tryRemove =>
      let (v, s') ← slab.Slab.try_remove s k
      let o ← observe s' (.val (optNat v)) 14
      let r ← realRun s' hw ops
      ok (o :: r)
    | .setMut =>
      let (v, back) ← slab.Slab.get_mut s k
      let s' := back (core.option.Option.Some (valOf op))
      let o ← observe s' (.val (optNat v)) 14
      let r ← realRun s' hw ops
      ok (o :: r)
    | .clear =>
      let s' ← slab.Slab.clear s
      let o ← observe s' .unit 14
      let r ← realRun s' hw ops
      ok (o :: r)
    | .get =>
      let v ← slab.Slab.get s k
      let o ← observe s (.val (optNat v)) 14
      let r ← realRun s hw ops
      ok (o :: r)

def runNew (ops : List Op) : RustM (List Obs) := do
  let s ← slab.Slab.new Std.U32
  realRun s 0 ops

/-! ### Abstract model: association list key ↦ value, plus `H` (slots handed out). -/

def lookup (m : List (Nat × Nat)) (k : Nat) : Option Nat := (m.find? (·.1 == k)).map (·.2)
def erase (m : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) := m.filter (·.1 != k)
def put (m : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) := (k, v) :: erase m k
def mem (m : List (Nat × Nat)) (k : Nat) : Bool := (lookup m k).isSome

/-- Some slot below `H` is vacant. -/
def hasHole (m : List (Nat × Nat)) (h : Nat) : Bool := (List.range h).any (fun k => !mem m k)

/-- Aspects of the contract checked along a trace. -/
inductive Aspect where
  | fresh      -- inserted key was vacant
  | vkeyIns    -- inserted key = `vacant_key()` just before (also for `vacant_entry`)
  | dense      -- holes are reused before a new slot is created (fresh slab: 0,1,2,…)
  | vkeyVacant -- `vacant_key()` is itself a vacant key obeying the same rule
  | gets       -- `get` agrees with the model on every key of the window
  | conts      -- `contains` agrees with the model
  | len        -- `len` / `is_empty`
  | removal    -- `remove`/`try_remove` results; `remove` panics iff the key is absent
  | getMut     -- `get_mut` returns the old value (the update is checked through `gets`)
  | getRes     -- result of `get`
  | entryVal   -- `VacantEntry::insert` returns (a reference to) the inserted value
  deriving DecidableEq

/-- What the key `k` of an insertion must satisfy in model state `(m, h)`. -/
def insertOk (m : List (Nat × Nat)) (h k : Nat) : Bool :=
  if hasHole m h then k < h && !mem m k else k == h

def check (a : Aspect) : List (Nat × Nat) → Nat → Nat → List Op → List Obs → Bool
  | m, h, _, [], [o] =>
    match a with
    | .gets => o.gets == (List.range o.gets.length).map (lookup m)
    | .conts => o.conts == (List.range o.conts.length).map (mem m)
    | .len => o.len == m.length && o.empty == m.isEmpty
    | .vkeyVacant => insertOk m h o.vkey
    | _ => true
  | _, _, _, [], _ => false
  | m, h, pv, op :: ops, tr =>
    match tr with
    | [] => false
    | o :: tr' =>
      let k := keyOf op
      -- the state after this operation (model), using the real key for insertions
      let step : Option (List (Nat × Nat) × Nat × Bool) :=
        match kindOf op, o.res with
        | .insert, .ins key =>
          some (put m key (valOf op).val, max h (key + 1),
            match a with
            | .fresh => !mem m key
            | .vkeyIns => key == pv
            | .dense => insertOk m h key
            | _ => true)
        | .entry, .ins key =>
          some (put m key (valOf op).val, max h (key + 1),
            match a with
            | .fresh => !mem m key
            | .vkeyIns => key == pv
            | .dense => insertOk m h key
            | _ => true)
        | .entry, .panic => some (m, h, a != .entryVal)
        | .insert, _ | .entry, _ => none
        | .remove, .val r => some (erase m k, h, a != .removal || (r == lookup m k && r.isSome))
        | .remove, .panic => some (m, h, a != .removal || !mem m k)
        | .remove, _ => none
        | .tryRemove, .val r => some (erase m k, h, a != .removal || r == lookup m k)
        | .tryRemove, _ => none
        | .setMut, .val r =>
          some ((if mem m k then put m k (valOf op).val else m), h, a != .getMut || r == lookup m k)
        | .setMut, _ => none
        | .clear, .unit => some ([], h, true)
        | .clear, _ => none
        | .get, .val r => some (m, h, a != .getRes || r == lookup m k)
        | .get, _ => none
      match step with
      | none => false
      | some (m', h', okStep) =>
        let w := o.gets.length
        let obsOk : Bool :=
          match a with
          | .gets => o.gets == (List.range w).map (lookup m')
          | .conts => o.conts == (List.range o.conts.length).map (mem m')
          | .len => o.len == m'.length && o.empty == m'.isEmpty
          | .vkeyVacant => insertOk m' h' o.vkey
          | _ => true
        okStep && obsOk &&
          (if o.res == .panic then tr'.isEmpty && ops.isEmpty || tr'.isEmpty else check a m' h' o.vkey ops tr')

def holds (a : Aspect) (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check a [] 0 0 ops tr = true ⦄

def insertAll (s : S) : List Std.U32 → RustM (List Nat)
  | [] => ok []
  | x :: xs => do
    let (k, s') ← slab.Slab.insert s x
    let r ← insertAll s' xs
    ok (k.val :: r)

def applyOps (s : S) : List Op → RustM S
  | [] => ok s
  | op :: ops =>
    let k := mkU .Usize (keyOf op)
    match kindOf op with
    | .insert | .entry => do
      let (_, s') ← slab.Slab.insert s (valOf op)
      applyOps s' ops
    | .remove | .tryRemove => do
      let (_, s') ← slab.Slab.try_remove s k
      applyOps s' ops
    | .setMut => do
      let (_, back) ← slab.Slab.get_mut s k
      applyOps (back (core.option.Option.Some (valOf op))) ops
    | .clear => do
      let s' ← slab.Slab.clear s
      applyOps s' ops
    | .get => applyOps s ops

def stateAfter (ops : List Op) : RustM S := do
  let s ← slab.Slab.new Std.U32
  applyOps s ops

def obsAll (s : S) : RustM Obs := observe s .unit 70

end RSGBGold.Slab.Slab

namespace Benchmark.V2.Slab.Slab.Gold
open RSGBGold.Slab.Slab

/-! ### Fresh slab -/

/-- `new()`: empty, `vacant_key() = 0`, every key absent (`get`/`contains`/`try_remove`),
`remove` panics. -/
def gold_new (k : Std.Usize) : Prop :=
  (do
    let s ← slab.Slab.new Std.U32
    let n ← slab.Slab.impl.len s
    let e ← slab.Slab.is_empty s
    let v ← slab.Slab.vacant_key s
    let g ← slab.Slab.get s k
    let c ← slab.Slab.contains s k
    let (t, s') ← slab.Slab.try_remove s k
    let n' ← slab.Slab.impl.len s'
    let pan := match slab.Slab.remove s k with
      | .fail .panic => true
      | _ => false
    ok (n.val == 0 && e && v.val == 0 && optNat g == none && !c && optNat t == none &&
        n'.val == 0 && pan))
    ⦃ r => r = true ⦄

/-- `with_capacity(c)` behaves exactly like `new()` (the capacity is only a hint). -/
def gold_with_capacity_like_new (c : Std.U16) (ops : List Op) : Prop :=
  (do let s ← slab.Slab.with_capacity Std.U32 (mkU .Usize c.val); realRun s 0 ops) = runNew ops

/-! ### Model-based traces -/

def gold_insert_returns_vacant_key (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .fresh [] 0 0 ops tr = true ⦄
def gold_insert_key_is_vacant_key (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .vkeyIns [] 0 0 ops tr = true ⦄
def gold_insert_reuses_holes_first (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .dense [] 0 0 ops tr = true ⦄
def gold_vacant_key_is_next_key (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .vkeyVacant [] 0 0 ops tr = true ⦄
def gold_get_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .gets [] 0 0 ops tr = true ⦄
def gold_contains_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .conts [] 0 0 ops tr = true ⦄
def gold_len_is_empty_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .len [] 0 0 ops tr = true ⦄
def gold_remove_try_remove_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .removal [] 0 0 ops tr = true ⦄
def gold_get_mut_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .getMut [] 0 0 ops tr = true ⦄
def gold_get_result_model (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .getRes [] 0 0 ops tr = true ⦄
def gold_vacant_entry_insert_value (ops : List Op) : Prop :=
  runNew ops ⦃ tr => check .entryVal [] 0 0 ops tr = true ⦄

/-! ### Relational laws at an arbitrary reachable state -/


/-- Inserting then removing the returned key gives the value back and restores the
contents (`len`, `get`, `contains`); `vacant_key` may differ (reuse order is free). -/
def gold_insert_remove_roundtrip (ops : List Op) (x : Std.U32) : Prop :=
  (do
    let s ← stateAfter ops
    let b ← obsAll s
    let (k, s1) ← slab.Slab.insert s x
    let g ← slab.Slab.get s1 k
    let (v, s2) ← slab.Slab.remove s1 k
    let a ← obsAll s2
    ok (optNat g == some x.val && v.val == x.val && a.len == b.len && a.gets == b.gets &&
        a.conts == b.conts && b.vkey == k.val))
    ⦃ r => r = true ⦄

/-- `try_remove`/`remove`/`get_mut` on an absent key change nothing (incl. `vacant_key`);
`remove` panics. -/
def gold_absent_key_noop (ops : List Op) (k : Std.Usize) : Prop :=
  (do
    let s ← stateAfter ops
    let c ← slab.Slab.contains s k
    if c then ok true else
    let before ← obsAll s
    let (t, s1) ← slab.Slab.try_remove s k
    let a1 ← obsAll s1
    let (gm, back) ← slab.Slab.get_mut s k
    let a2 ← obsAll (back (core.option.Option.Some 7#u32))
    let pan := match slab.Slab.remove s k with
      | .fail .panic => true
      | _ => false
    ok (optNat t == none && a1 == before && optNat gm == none && a2 == before && pan))
    ⦃ r => r = true ⦄

/-- `remove` and `try_remove` agree on present keys (value and resulting state). -/
def gold_remove_eq_try_remove (ops : List Op) (k8 : Std.U8) : Prop :=
  (do
    let s ← stateAfter ops
    let k := mkU .Usize (k8.val % 16)
    let c ← slab.Slab.contains s k
    if c then
      let (v1, s1) ← slab.Slab.remove s k
      let (v2, s2) ← slab.Slab.try_remove s k
      let o1 ← obsAll s1
      let o2 ← obsAll s2
      ok (optNat v2 == some v1.val && o1 == o2)
    else ok true) ⦃ r => r = true ⦄

/-- `vacant_entry().key()` is `vacant_key()`, and inserting through the entry is the same
as `insert`. -/
def gold_vacant_entry_like_insert (ops : List Op) (x : Std.U32) : Prop :=
  (do
    let s ← stateAfter ops
    let vk ← slab.Slab.vacant_key s
    let (k1, r, s1) ← entryInsert s x
    let (k2, s2) ← slab.Slab.insert s x
    let o1 ← obsAll s1
    let o2 ← obsAll s2
    ok (k1 == vk.val && k1 == k2.val && r == x.val && o1 == o2)) ⦃ r => r = true ⦄

/-- After `clear`, the slab is empty and every key is absent. -/
def gold_clear_empties (ops : List Op) (k : Std.Usize) : Prop :=
  (do
    let s ← stateAfter ops
    let s1 ← slab.Slab.clear s
    let o ← obsAll s1
    let g ← slab.Slab.get s1 k
    let c ← slab.Slab.contains s1 k
    ok (o.len, o.empty, o.gets.all (· == none), optNat g, c))
    ⦃ r => r = (0, true, true, none, false) ⦄

/-- `n` insertions into a fresh slab return the keys `0, 1, …, n-1`. -/
def gold_fresh_keys_sequential (xs : List Std.U32) : Prop :=
  (do let s ← slab.Slab.new Std.U32; insertAll s xs) ⦃ ks => ks = List.range xs.length ⦄

/-! Differential-testing probes. -/

def diff_trace (ops : List Op) := runNew ops
def diff_new (k : Std.Usize) := (do
  let s ← slab.Slab.new Std.U32
  let o ← obsAll s
  let (t, _) ← slab.Slab.try_remove s k
  ok (o, optNat t))
def diff_with_capacity (c : Std.U16) (ops : List Op) :=
  (do let s ← slab.Slab.with_capacity Std.U32 (mkU .Usize c.val); realRun s 0 ops)
def diff_entry (ops : List Op) (x : Std.U32) := (do
  let s ← stateAfter ops
  let (k, r, s1) ← entryInsert s x
  let o ← obsAll s1
  ok (k, r, o))
def diff_remove_absent (ops : List Op) (k : Std.Usize) := (do
  let s ← stateAfter ops
  let (t, s1) ← slab.Slab.try_remove s k
  let o ← obsAll s1
  ok (optNat t, o))

end Benchmark.V2.Slab.Slab.Gold
