import Benchmark.Cases.RustCrdt.Dot.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts
open Benchmark.Cases.RustCrdt.Dot

namespace Benchmark.Cases.RustCrdt.Dot.Oracle

/-- PBT `crdts::dot::test::prop_partial_order` (src/dot.rs:160): the four
outcomes of `a.partial_cmp(&b)` / `b.partial_cmp(&a)` exactly mirror the actor
equality and the counter order. -/
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

/-- PBT `crdts::dot::test::prop_ordered_dot_is_ordered_by_actor_first`
(src/dot.rs:180): converting two `Dot`s to `OrdDot` and comparing, the actor
comparison decides the order, and on equal actors the `OrdDot` order agrees
with the counter order. -/
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

axiom prop_ordered_dot_is_ordered_by_actor_first (a b : dot.Dot Std.U8) :
    prop_ordered_dot_is_ordered_by_actor_first_spec a b

axiom prop_partial_order (a b : dot.Dot Std.U8) :
    prop_partial_order_spec a b

end Benchmark.Cases.RustCrdt.Dot.Oracle
