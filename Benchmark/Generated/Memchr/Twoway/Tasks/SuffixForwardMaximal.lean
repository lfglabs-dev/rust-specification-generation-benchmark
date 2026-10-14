import Benchmark.Cases.Memchr.Twoway.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open memchr

namespace Benchmark.Cases.Memchr.Twoway

/-- For every non-empty byte string, the Crochemore-Perrin maximal-suffix
routine `Suffix::forward(bytes, SuffixKind::Maximal)` of the Two-Way
substring searcher terminates without panicking, and `&bytes[s.pos..]` is
the lexicographically greatest non-empty suffix of `bytes` (the value of the
naive sort-all-suffixes reference implementation). -/
def suffix_forward_maximal_spec (bytes : Slice Std.U8) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Memchr.Twoway
