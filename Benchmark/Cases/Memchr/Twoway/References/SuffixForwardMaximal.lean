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
  (do
    let s ← arch.all.twoway.Suffix.forward bytes arch.all.twoway.SuffixKind.Maximal
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      bytes { start := s.pos })
  ⦃ got => IsNaiveMaximalSuffix bytes.val got.val ⦄

end Benchmark.Cases.Memchr.Twoway
