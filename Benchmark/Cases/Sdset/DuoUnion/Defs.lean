import SdsetDuoUnion.Extraction
import Mathlib.Data.Finset.Sort

/-!
# sdset (duo union) — specifications

Implementation: `extracted/SdsetDuoUnion` (verbatim `cargo hax extract
sdset-duo-union` output for Kerollmops/sdset@e86d44b1, rooted at the module
`sdset::duo::union`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Shared
references `&'a T` are represented by the referenced values (Aeneas), so the
iterator items of `UnionIter<'a, i32>` are `Std.I32` values and `.cloned()` is
the identity on them.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Sdset.DuoUnion

open sdset

/-- Semantics of `iter.collect::<Vec<_>>()` for an iterator whose (extracted)
`Iterator::next` is `next`: starting from the iterator state `s`, the successive
calls to `next` terminate without panicking and return `Some x₁`, …, `Some xₙ`
and then `None`, where `xs = [x₁, …, xₙ]`. This is exactly how
`Vec::from_iter` consumes an iterator (it calls `next` until the first `None`
and pushes every item in order), so `CollectsTo next s xs` holds iff collecting
the iterator `s` into a `Vec` succeeds and yields `xs` (the relation is
functional in `xs`, because `next` is a deterministic function). -/
def CollectsTo {S T : Type} (next : S → RustM (core.option.Option T × S)) :
    S → List T → Prop
  | s, [] => next s ⦃ r => r.1 = core.option.Option.None ⦄
  | s, x :: xs => next s ⦃ r => r.1 = core.option.Option.Some x ∧ CollectsTo next r.2 xs ⦄

/-- Model of the test's reference side
`BTreeSet::from_iter(a).union(&BTreeSet::from_iter(b)).cloned().collect::<Vec<_>>()`:
the elements of `a ∪ b` (as mathematical integers — `i32`'s `Ord` is the order
of the integer values), each once, in increasing order (`BTreeSet` iteration
order). -/
def btreeset_union_vec (a b : List Std.I32) : List Int :=
  Finset.sort ((a.map (·.val)).toFinset ∪ (b.map (·.val)).toFinset)

end Benchmark.Cases.Sdset.DuoUnion
