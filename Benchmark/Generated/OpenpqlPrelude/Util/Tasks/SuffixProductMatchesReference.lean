import Benchmark.Cases.OpenpqlPrelude.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- On every nonempty slice of `u64` values in `[1, 65535]` whose total product fits in a `u64`, the in-place `suffix_product` never panics and replaces entry `i` by the product of the entries after position `i`. -/
def suffix_product_spec (xs : Slice Std.U64) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.OpenpqlPrelude.Util
