import Benchmark.Cases.Fastdivide.Divider.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

/-- Dividing by the precomputed `DividerU64::divide_by(11)` (the 64-bit-magic
`Fast` path) never panics and agrees with `n / 11`. -/
def divide_by_11_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 11#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 11 ⦄

end Benchmark.Cases.Fastdivide.Divider
