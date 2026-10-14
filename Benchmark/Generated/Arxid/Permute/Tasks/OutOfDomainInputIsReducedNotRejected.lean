import Benchmark.Cases.Arxid.Permute.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid

namespace Benchmark.Cases.Arxid.Permute

/-- For every 64-bit key and every 64-bit input `id`, the bits of `id` above the
40-bit domain are ignored: `obfuscate(id, key) == obfuscate(id & MAX_ID, key)`,
and deobfuscating `obfuscate(id, key)` returns exactly `id & MAX_ID`; no call
panics. -/
def out_of_domain_input_is_reduced_not_rejected_spec (key id : Std.U64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Arxid.Permute
