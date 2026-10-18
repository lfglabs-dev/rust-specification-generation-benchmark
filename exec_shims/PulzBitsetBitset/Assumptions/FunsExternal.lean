-- [pulz_bitset]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import PulzBitsetBitset.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open pulz_bitset


/-! Executable-copy shim (grader side): models of Rust core items missing from
CoreModels — `Iterator::any` on slice iterators and `Ord::min` (default method).
No pulz_bitset code here. -/

def CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.anyAux
    {T F : Type} (fInst : core.ops.function.FnMut F T Bool) (f : F) :
    Nat → core.slice.iter.Iter T → RustM (Bool × core.slice.iter.Iter T)
  | 0, it => ok (false, it)
  | n+1, it => do
    let (o, it') ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next it
    match o with
    | core.option.Option.None => ok (false, it')
    | core.option.Option.Some x => do
      let (b, f') ← fInst.call_mut f x
      if b then ok (true, it')
      else CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.anyAux fInst f' n it'

/-- `Iterator::any` (short-circuits; consumes up to and including the first match). -/
def CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (fInst : core.ops.function.FnMut F T Bool) (it : core.slice.iter.Iter T) (f : F) :
    RustM (Bool × core.slice.iter.Iter T) := do
  let n ← rust_primitives.sequence.seq_len it
  CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.anyAux fInst f (n.val + 1) it

/-- `Ord::min`: `self` unless `other < self` (std `min_by`: Less | Equal => self). -/
def CoreModels.core.cmp.Ord.min.default {Self : Type} (inst : core.cmp.Ord Self) (a b : Self) :
    RustM Self := do
  let o ← inst.cmp a b
  match o with
  | core.cmp.Ordering.Greater => ok b
  | _ => ok a
