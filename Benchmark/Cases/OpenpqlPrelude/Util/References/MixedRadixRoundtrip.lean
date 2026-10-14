import Benchmark.Cases.OpenpqlPrelude.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- For block sizes in `[1, 65536]` and digits below their block sizes, building `MixedRadix::new(block_sizes)`, encoding the digits and decoding the index panics exactly when all block sizes are `65536` (the product `2^64` overflows: an upstream bug) and otherwise never panics and returns the original digits. -/
def mixed_radix_roundtrip_spec (block_sizes digits : Std.Array Std.U64 4#usize) : Prop :=
  let run : RustM (Std.Array Std.U64 4#usize) := do
    let radix ← waugh_indexer.mixed_radix.MixedRadix.new block_sizes
    let idx ← waugh_indexer.mixed_radix.MixedRadix.encode radix digits
    waugh_indexer.mixed_radix.MixedRadix.decode radix idx
  ((∀ b ∈ block_sizes.val, b.val = 65536) → run = fail .panic) ∧
  ((¬ ∀ b ∈ block_sizes.val, b.val = 65536) → run ⦃ decoded => decoded = digits ⦄)

end Benchmark.Cases.OpenpqlPrelude.Util
