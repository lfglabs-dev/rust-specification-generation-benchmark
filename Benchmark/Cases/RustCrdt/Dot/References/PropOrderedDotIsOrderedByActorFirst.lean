import Benchmark.Cases.RustCrdt.Dot.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

/-- For all `Dot<u8>` values `a` and `b`, converting both to `OrdDot` and
comparing: the actor comparison decides the `OrdDot` order (`Less` when
`a.actor < b.actor`, `Greater` when `a.actor > b.actor`), and on equal actors
the full `OrdDot` comparison agrees with the counter comparison. -/
def prop_ordered_dot_is_ordered_by_actor_first_spec (a b : dot.Dot Std.U8) :
    Prop :=
  (do
    let oa ← dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd a
    let ob ← dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd b
    let actor_cmp ← core.U8.Insts.CoreCmpOrd.cmp oa.actor ob.actor
    let ord_inst := dot.OrdDot.Insts.CoreCmpOrd core.U8.Insts.CoreCmpOrd
      core.U8.Insts.CoreCmpOrd
    match actor_cmp with
    | core.cmp.Ordering.Less =>
        core.cmp.PartialOrd.lt.default ord_inst.PartialOrdInst oa ob
    | core.cmp.Ordering.Greater =>
        core.cmp.PartialOrd.gt.default ord_inst.PartialOrdInst oa ob
    | core.cmp.Ordering.Equal => do
      let counter_cmp ← core.U64.Insts.CoreCmpOrd.cmp oa.counter ob.counter
      let full_cmp ← core.cmp.PartialOrd.partial_cmp
        ord_inst.PartialOrdInst oa ob
      let some_full <-
        match full_cmp with
        | core.option.Option.Some o => ok o
        | core.option.Option.None => .fail .panic
      core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq counter_cmp some_full)
    ⦃ eq => eq = true ⦄

end Benchmark.Cases.RustCrdt.Dot
