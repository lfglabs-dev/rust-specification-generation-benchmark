import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- The branch-free Goldilocks subtraction `algo::sub` equals `(a - b).rem_euclid(MODULUS)` on reduced inputs. -/
def sub_matches_naive_spec (a b : Std.U64) : Prop :=
  field.algo.generic.sub a b ⦃ value =>
    (value.val : Int) = ((a.val : Int) - (b.val : Int)) % (2^64 - 2^32 + 1) ⦄

end Benchmark.Cases.Goldilocks.Field
