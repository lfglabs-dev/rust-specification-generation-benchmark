import MemchrTwoway.Extraction

/-!
# memchr — Two-Way maximal-suffix computation — specifications

Implementation: `extracted/MemchrTwoway` (verbatim `cargo hax extract
memchr-twoway` output for BurntSushi/memchr@bd6068c3).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, index
out of bounds panics), which is the configuration `cargo test` runs the
original property tests under.

## The test's reference side

The two property tests compare the suffix computed by `Suffix::forward` /
`Suffix::reverse` against test-only helpers (`#[cfg(test)]`, not part of the
extracted crate):

```rust
fn suffixes(bytes: &[u8]) -> Vec<&[u8]> {
    (0..bytes.len()).map(|i| &bytes[i..]).collect()
}
fn naive_maximal_suffix_forward(needle: &[u8]) -> &[u8] {
    let mut sufs = suffixes(needle);
    sufs.sort();
    sufs.pop().unwrap()
}
```

For a non-empty `needle` this returns the greatest element of
`[needle[i..] for i in 0..needle.len()]` under `Ord for [u8]`, i.e. the
lexicographic order on byte strings (a proper prefix is smaller). This order is
total and the candidates are pairwise distinct (different lengths), so a byte
string `got` equals that result iff `got` is one of the candidates and is
`>=` every candidate. `IsNaiveMaximalSuffix needle got` states exactly this.
The order is spelled out explicitly (`BytesLe`) with the core inductive
`List.Lex (· < ·)` on the byte values (`List Nat`), which has the same
definition as Rust's slice `Ord` (compare element-wise; a proper prefix is
smaller).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Memchr.Twoway

open memchr

/-- The byte values of a byte string. -/
def byteVals (l : List Std.U8) : List Nat := l.map (fun b => b.val)

/-- `a <= b` for byte strings under Rust's `Ord for [u8]`: `a` is strictly
smaller in the lexicographic order `List.Lex (· < ·)` on the byte values (first
differing byte smaller, or `a` a proper prefix of `b`), or `a` and `b` are
equal. -/
def BytesLe (a b : List Std.U8) : Prop :=
  List.Lex (· < ·) (byteVals a) (byteVals b) ∨ byteVals a = byteVals b

/-- `got == naive_maximal_suffix_forward(needle)` for a non-empty `needle`:
`got` is one of the suffixes `needle[i..]` (`i < needle.len()`), and it is
`>=` every such suffix (it is the last element after sorting them). -/
def IsNaiveMaximalSuffix (needle got : List Std.U8) : Prop :=
  (∃ i, i < needle.length ∧ got = needle.drop i) ∧
  ∀ i, i < needle.length → BytesLe (needle.drop i) got

end Benchmark.Cases.Memchr.Twoway
