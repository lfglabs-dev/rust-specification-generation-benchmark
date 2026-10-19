import Benchmark.V2.Prelude
import CircularQueueQueue.Extraction

/-! Hidden gold specification for target `circular_queue/queue`.

API (instantiated at `T = u32`): `CircularQueue::with_capacity`, `len`, `is_empty`,
`is_full`, `capacity`, `clear`, `push`, `iter`, `asc_iter`, `into_vec`.

Model-based: an input is a capacity and a short list of operations
(`(k, v)`: `k % 8 = 0` is `clear`, otherwise `push v`). The operations are run on the
real queue and on an abstract model (the list of stored values, newest first, at most
`capacity` long; pushing into a full queue drops and returns the oldest value), and
every observable is compared after every operation. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM circular_queue RSGB

namespace RSGBGold.CircularQueue.Queue

abbrev Q := CircularQueue Std.U32

/-- Drain an iterator into a list (bounded by `fuel`). -/
def drainIt {I T : Type} (inst : core.iter.traits.iterator.Iterator I T) : Nat → I → RustM (List T)
  | 0, _ => ok []
  | n+1, it => do
    let (o, it') ← inst.next it
    match o with
    | core.option.Option.None => ok []
    | core.option.Option.Some x => do
      let r ← drainIt inst n it'
      ok (x :: r)

abbrev RevIt := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
    (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT Std.U32)
def descInst := core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator RevIt RevIt
def ascInst := core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator
  (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32)
  (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT Std.U32)

def optNat : core.option.Option Std.U32 → Option Nat
  | core.option.Option.None => none
  | core.option.Option.Some x => some x.val

/-- Everything observable after one operation. -/
structure Obs where
  popped : Option Nat
  len : Nat
  empty : Bool
  full : Bool
  cap : Nat
  desc : List Nat
  asc : List Nat
  vec : List Nat
  deriving DecidableEq, Repr

def fuel : Nat := 400

def observe (q : Q) (popped : Option Nat) : RustM Obs := do
  let n ← CircularQueue.len q
  let e ← CircularQueue.is_empty q
  let f ← CircularQueue.is_full q
  let c ← CircularQueue.impl.capacity q
  let it ← CircularQueue.iter q
  let d ← drainIt descInst fuel it
  let it2 ← CircularQueue.asc_iter q
  let a ← drainIt ascInst fuel it2
  let v ← CircularQueue.into_vec q
  ok { popped, len := n.val, empty := e, full := f, cap := c.val,
       desc := d.map (·.val), asc := a.map (·.val), vec := v.val.map (·.val) }

def isClear (op : Std.U8 × Std.U32) : Bool := op.1.val % 8 == 0

/-- Run the operations on the real queue, observing after each one. -/
def realRun (q : Q) : List (Std.U8 × Std.U32) → RustM (List Obs)
  | [] => ok []
  | op :: ops => do
    if isClear op then
      let q' ← CircularQueue.clear q
      let o ← observe q' none
      let r ← realRun q' ops
      ok (o :: r)
    else
      let (p, q') ← CircularQueue.push q op.2
      let o ← observe q' (optNat p)
      let r ← realRun q' ops
      ok (o :: r)

/-- Abstract model: stored values, newest first. -/
def mpush (cap : Nat) (xs : List Nat) (x : Nat) : Option Nat × List Nat :=
  if cap = 0 then (none, xs)
  else if xs.length < cap then (none, x :: xs)
  else (xs.getLast?, x :: xs.dropLast)

def mobs (cap : Nat) (xs : List Nat) (p : Option Nat) : Obs :=
  { popped := p, len := xs.length, empty := xs.isEmpty, full := xs.length == cap, cap,
    desc := xs, asc := xs.reverse, vec := xs }

def modelRun (cap : Nat) (xs : List Nat) : List (Std.U8 × Std.U32) → List Obs
  | [] => []
  | op :: ops =>
    if isClear op then mobs cap [] none :: modelRun cap [] ops
    else
      let (p, ys) := mpush cap xs op.2.val
      mobs cap ys p :: modelRun cap ys ops

/-- Small capacities (wrap-around happens often). -/
def capOf (c : Std.U8) : Nat := c.val % 10

def runFrom (cap : Nat) (ops : List (Std.U8 × Std.U32)) : RustM (List Obs) := do
  let q ← CircularQueue.with_capacity Std.U32 (mkU .Usize cap)
  realRun q ops

end RSGBGold.CircularQueue.Queue

namespace Benchmark.V2.CircularQueue.Queue.Gold
open RSGBGold.CircularQueue.Queue

/-! ### Fresh queue -/

/-- `with_capacity(c)`: empty, `capacity() = c`, full iff `c = 0`, iterators empty. -/
def gold_fresh (c : Std.U16) : Prop :=
  (do let q ← CircularQueue.with_capacity Std.U32 (mkU .Usize c.val); observe q none)
    ⦃ o => o = mobs c.val [] none ⦄

/-! ### Model-based traces (every observable after every operation) -/

/-- `push` returns exactly the overwritten (oldest) value, `None` otherwise; never panics. -/
def gold_push_popped (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.popped) = (modelRun (capOf c) [] ops).map (·.popped) ⦄

def gold_len (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.len) = (modelRun (capOf c) [] ops).map (·.len) ⦄

def gold_is_empty (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.empty) = (modelRun (capOf c) [] ops).map (·.empty) ⦄

def gold_is_full (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.full) = (modelRun (capOf c) [] ops).map (·.full) ⦄

def gold_capacity_constant (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => ∀ o ∈ tr, o.cap = capOf c ⦄

/-- `iter()` goes from the most recently pushed value to the oldest one. -/
def gold_iter_newest_first (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.desc) = (modelRun (capOf c) [] ops).map (·.desc) ⦄

/-- `asc_iter()` goes from the oldest value to the newest one. -/
def gold_asc_iter_oldest_first (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.asc) = (modelRun (capOf c) [] ops).map (·.asc) ⦄

/-- `into_vec()` lists the values newest first. -/
def gold_into_vec (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => tr.map (·.vec) = (modelRun (capOf c) [] ops).map (·.vec) ⦄

/-! ### Relational invariants -/

def gold_asc_is_reverse_of_iter (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => ∀ o ∈ tr, o.asc = o.desc.reverse ∧ o.vec = o.desc ⦄

def gold_len_consistent (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom (capOf c) ops ⦃ tr => ∀ o ∈ tr,
    o.len ≤ o.cap ∧ o.desc.length = o.len ∧ (o.empty ↔ o.len = 0) ∧ (o.full ↔ o.len = o.cap) ⦄

/-! ### Larger capacities (mostly no wrap-around) and zero capacity -/

def gold_trace_any_capacity (c : Std.U8) (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom c.val ops ⦃ tr => tr = modelRun c.val [] ops ⦄

/-- A zero-capacity queue accepts pushes (no panic), stores nothing, and is both empty and full. -/
def gold_zero_capacity (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom 0 ops ⦃ tr => ∀ o ∈ tr, o = mobs 0 [] none ⦄

/-- Capacity one: every push into the full queue returns the previous value. -/
def gold_capacity_one (ops : List (Std.U8 × Std.U32)) : Prop :=
  runFrom 1 ops ⦃ tr => tr = modelRun 1 [] ops ⦄

/-! Differential-testing probes. -/

def diff_trace (c : Std.U8) (ops : List (Std.U8 × Std.U32)) := runFrom (capOf c) ops
def diff_trace_big (c : Std.U8) (ops : List (Std.U8 × Std.U32)) := runFrom c.val ops
def diff_fresh (c : Std.U16) :=
  (do let q ← CircularQueue.with_capacity Std.U32 (mkU .Usize c.val); observe q none)

end Benchmark.V2.CircularQueue.Queue.Gold
