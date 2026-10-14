import Benchmark.Cases.Uint.U64.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ethereum_types

namespace Benchmark.Cases.Uint.U64

/-- `(x + y) + z == x + (y + z)` holds whenever the test does not discard. -/
def associative_add_spec (x y z : uint.U64) : Prop :=
  (do
    let xy ← add x y
    let lhs ← add xy z
    let yz ← add y z
    let rhs ← add x yz
    uint.U64.Insts.CoreCmpPartialEqU64.eq lhs rhs) ⦃ b => b = true ⦄

end Benchmark.Cases.Uint.U64
