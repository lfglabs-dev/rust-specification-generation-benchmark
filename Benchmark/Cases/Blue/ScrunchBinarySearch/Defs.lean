import BlueScrunchBinarySearch.Extraction

/-!
# blue/scrunch — `binary_search` specifications

Implementation: `extracted/BlueScrunchBinarySearch` (verbatim `cargo hax extract
blue-scrunch-binary-search` output for rescrv/blue@3db46b7c, crate `scrunch`,
module `scrunch::binary_search`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property test under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Blue.ScrunchBinarySearch

open scrunch

/-- State of the test's closure `|x| elements[x].cmp(&elements[i])`
(scrunch/src/binary_search.rs:101): it captures the test vector `elements`
(only read through its slice: `elements[x]`) and the loop index `i`. The
closure is part of the property test, not of the crate, so it is not
extracted; this is its direct transcription. -/
structure ProbeClosure where
  elements : Slice Std.Usize
  i : Std.Usize

/-- Body of the test closure: `elements[x].cmp(&elements[i])`. Both indexings
are Rust `Index<usize>` on the vector (panic when out of bounds, modelled by
`Slice.index_usize`); `cmp` is `Ord::cmp` for `usize` (CoreModels). -/
def ProbeClosure.call (c : ProbeClosure) (x : Std.Usize) :
    RustM core.cmp.Ordering := do
  let a ← Slice.index_usize c.elements x
  let b ← Slice.index_usize c.elements c.i
  core.Usize.Insts.CoreCmpOrd.cmp a b

/-- `FnOnce` instance of the test closure. -/
def ProbeClosure.Insts.FnOnce :
    core.ops.function.FnOnce ProbeClosure Std.Usize core.cmp.Ordering where
  call_once := ProbeClosure.call

/-- `FnMut` instance of the test closure (its captured state is never
mutated). -/
def ProbeClosure.Insts.FnMut :
    core.ops.function.FnMut ProbeClosure Std.Usize core.cmp.Ordering where
  FnOnceInst := ProbeClosure.Insts.FnOnce
  call_mut := fun c x => do
    let o ← ProbeClosure.call c x
    ok (o, c)

/-- Value of the std call `elements.partition_point(|x| *x < v)` on a slice
that is partitioned by the predicate (all elements satisfying it come first,
as for a sorted slice): the index of the first element that does not satisfy
it (Rust docs of `slice::partition_point`). std is not extracted, so it is
stated directly. -/
def partitionPointLt (elements : Slice Std.Usize) (v : Std.Usize) : Nat :=
  elements.val.findIdx (fun x => !decide (x.val < v.val))

end Benchmark.Cases.Blue.ScrunchBinarySearch
