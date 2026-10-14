import Benchmark.Cases.Tinyset.Fits64.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open tinyset

namespace Benchmark.Cases.Tinyset.Fits64

/-- For every `i64` value `x`, the branch-free `Fits64` encoding into a `u64`
(`x ↦ 2x` for `x ≥ 0`, `x ↦ 2·!x + 1` for `x < 0`, selected with bit masks)
never panics, `from_u64` decodes it back to `x`, and re-encoding the decoded
value reproduces the same word. -/
def fits_i64_roundtrip_spec (x : Std.I64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Tinyset.Fits64
