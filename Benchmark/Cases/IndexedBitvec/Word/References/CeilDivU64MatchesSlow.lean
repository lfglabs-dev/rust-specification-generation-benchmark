import Benchmark.Cases.IndexedBitvec.Word.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

/-- For every `u64` dividend `x` and divisor `d` in `1..999999`, the wrapping
fast path `ceil_div_u64(x, d)` never panics and returns the same value as the
reference `ceil_div_u64_slow(x, d) = x / d + (x % d > 0)`. -/
def ceil_div_u64_matches_slow_spec (x d : Std.U64) : Prop :=
  (do
    let slow ← ceil_div_u64_slow x d
    let fast ← ceil_div_u64 x d
    ok (slow, fast)) ⦃ (slow, fast) => slow = fast ⦄

end Benchmark.Cases.IndexedBitvec.Word
