import Benchmark.Cases.RustCrdt.Dot.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

/-- For all `Dot<u8>` values `a` and `b`, the pair `a.partial_cmp(&b)` /
`b.partial_cmp(&a)` behaves exactly as a consistent partial order on dots
requires: both are `None` iff the actors differ, both are `Some` with mirrored
`Less`/`Greater` iff the actors are equal and the counters differ, and both
are `Some(Equal)` iff actor and counter agree. -/
def prop_partial_order_spec (a b : dot.Dot Std.U8) : Prop :=
  (do
    let cmp_ab ←
      dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp
        core.U8.Insts.CoreCmpPartialOrdU8 a b
    let cmp_ba ←
      dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp
        core.U8.Insts.CoreCmpPartialOrdU8 b a
    match cmp_ab, cmp_ba with
    | core.option.Option.None, core.option.Option.None =>
        core.U8.Insts.CoreCmpPartialEqU8.ne a.actor b.actor
    | core.option.Option.Some core.cmp.Ordering.Less,
      core.option.Option.Some core.cmp.Ordering.Greater => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let lt ← core.U64.Insts.CoreCmpPartialOrdU64.lt a.counter b.counter
      ok (eq && lt)
    | core.option.Option.Some core.cmp.Ordering.Greater,
      core.option.Option.Some core.cmp.Ordering.Less => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let gt ← core.U64.Insts.CoreCmpPartialOrdU64.gt a.counter b.counter
      ok (eq && gt)
    | core.option.Option.Some core.cmp.Ordering.Equal,
      core.option.Option.Some core.cmp.Ordering.Equal => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let eqc ← core.U64.Insts.CoreCmpPartialEqU64.eq a.counter b.counter
      ok (eq && eqc)
    | _, _ => ok false) ⦃ eq => eq = true ⦄

end Benchmark.Cases.RustCrdt.Dot
