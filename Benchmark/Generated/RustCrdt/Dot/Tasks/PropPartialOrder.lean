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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.RustCrdt.Dot
