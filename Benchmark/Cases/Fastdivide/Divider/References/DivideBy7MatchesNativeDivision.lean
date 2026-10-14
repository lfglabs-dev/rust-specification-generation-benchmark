import Benchmark.Cases.Fastdivide.Divider.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

/-- Dividing by the precomputed `DividerU64::divide_by(7)` (the 65-bit-magic
`General` path) never panics and agrees with `n / 7`. -/
def divide_by_7_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 7#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 7 ⦄

end Benchmark.Cases.Fastdivide.Divider
