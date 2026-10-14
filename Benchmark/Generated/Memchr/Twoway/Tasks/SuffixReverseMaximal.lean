import Benchmark.Cases.Memchr.Twoway.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open memchr

namespace Benchmark.Cases.Memchr.Twoway

/-- For every non-empty byte string, the reverse maximal-suffix routine
`Suffix::reverse(bytes, SuffixKind::Maximal)` of the Two-Way substring
searcher terminates without panicking, and `&bytes[..s.pos]` is the reversal
of the lexicographically greatest non-empty suffix of the reversed byte
string (the value of the naive reference implementation). -/
def suffix_reverse_maximal_spec (bytes : Slice Std.U8) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Memchr.Twoway
