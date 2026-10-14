import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/-- The branch-free Goldilocks addition `algo::add` equals `(a + b) mod MODULUS` on reduced inputs. -/
def add_matches_naive_spec (a b : Std.U64) : Prop :=
  field.algo.generic.add a b ⦃ value =>
    value.val = (a.val + b.val) % (2^64 - 2^32 + 1) ⦄

end Benchmark.Cases.Goldilocks.Field
