import OpenpqlPreludeUtil.Extraction

/-!
# openpql-prelude — specifications (combinatorial index arithmetic)

Implementation: `extracted/OpenpqlPreludeUtil` (verbatim `cargo hax extract
openpql-prelude-util` output for solve-poker/Poker-Query-Language@157235d6,
crate `openpql-prelude`): `iterator::binomial::coefficient::binom`,
`waugh_indexer::util::{suffix_product, dot_product, const_sort}` and
`waugh_indexer::mixed_radix::MixedRadix::{new, encode, decode}`.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (`+ - * /` panic on
overflow / division by zero, `debug_assert!` is checked), which is the
configuration `cargo test` runs the original quickcheck properties under.
Every quickcheck property here fails on a panic, so panics falsify the specs.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.OpenpqlPrelude.Util

open openpql_prelude

/-- The test's reference value for `suffix_product`:
`xs.iter().enumerate().map(|(i, _)| xs[i + 1..].iter().product::<u64>())`,
i.e. entry `i` is the product of the entries strictly after position `i`
(the empty product is `1`). -/
def suffixProducts (xs : List Nat) : List Nat :=
  (List.range xs.length).map (fun i => (xs.drop (i + 1)).prod)

end Benchmark.Cases.OpenpqlPrelude.Util
