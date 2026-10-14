import Benchmark.Cases.Fastdivide.Divider.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

/-- For every divisor `d` and dividend `n` drawn from the property-test
strategies, precomputing `DividerU64::divide_by(d)` and dividing `n` with it
never panics and returns exactly `n / d`. -/
def divide_matches_native_division_spec (n d : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by d
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / d.val ⦄

end Benchmark.Cases.Fastdivide.Divider
