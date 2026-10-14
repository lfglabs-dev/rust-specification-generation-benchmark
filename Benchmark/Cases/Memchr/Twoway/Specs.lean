import Benchmark.Cases.Memchr.Twoway.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open memchr
open Benchmark.Cases.Memchr.Twoway

namespace Benchmark.Cases.Memchr.Twoway.Oracle

/-- PBT `arch::all::twoway::tests::qc_suffix_forward_maximal`
(src/arch/all/twoway.rs:845):
```rust
fn qc_suffix_forward_maximal(bytes: Vec<u8>) -> bool {
    if bytes.is_empty() { return true; }
    let (got, _) = get_suffix_forward(&bytes, SuffixKind::Maximal);
    let expected = naive_maximal_suffix_forward(&bytes);
    got == expected
}
```
where `get_suffix_forward(needle, kind)` runs `Suffix::forward(needle, kind)`
and returns `&needle[s.pos..]` (executed here with the CoreModels `RangeFrom`
slice index, which panics when `s.pos > needle.len()`). -/
def suffix_forward_maximal_spec (bytes : Slice Std.U8) : Prop :=
  (do
    let s ← arch.all.twoway.Suffix.forward bytes arch.all.twoway.SuffixKind.Maximal
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      bytes { start := s.pos })
  ⦃ got => IsNaiveMaximalSuffix bytes.val got.val ⦄

/-- PBT `arch::all::twoway::tests::qc_suffix_reverse_maximal`
(src/arch/all/twoway.rs:855):
```rust
fn qc_suffix_reverse_maximal(bytes: Vec<u8>) -> bool {
    if bytes.is_empty() { return true; }
    let (got, _) = get_suffix_reverse(&bytes, SuffixKind::Maximal);
    let expected = naive_maximal_suffix_reverse(&bytes);
    expected == got
}
```
where `get_suffix_reverse(needle, kind)` runs `Suffix::reverse(needle, kind)`
and returns `&needle[..s.pos]` (executed here with the CoreModels `RangeTo`
slice index, which panics when `s.pos > needle.len()`), and
`naive_maximal_suffix_reverse(needle)` reverses `needle`, takes
`naive_maximal_suffix_forward` of it and reverses the result. Hence
`expected == got` iff `got` reversed is the naive maximal suffix of `needle`
reversed. -/
def suffix_reverse_maximal_spec (bytes : Slice Std.U8) : Prop :=
  (do
    let s ← arch.all.twoway.Suffix.reverse bytes arch.all.twoway.SuffixKind.Maximal
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      bytes { «end» := s.pos })
  ⦃ got => IsNaiveMaximalSuffix bytes.val.reverse got.val.reverse ⦄

axiom suffix_forward_maximal (bytes : Slice Std.U8)
    (h_assume_nonempty : 0 < bytes.length) :
    suffix_forward_maximal_spec bytes

axiom suffix_reverse_maximal (bytes : Slice Std.U8)
    (h_assume_nonempty : 0 < bytes.length) :
    suffix_reverse_maximal_spec bytes

end Benchmark.Cases.Memchr.Twoway.Oracle
