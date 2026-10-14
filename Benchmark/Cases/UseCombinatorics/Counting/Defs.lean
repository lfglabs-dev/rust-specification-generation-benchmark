import UseCombinatoricsCounting.Extraction

/-!
# use-combinatorics (RustUse/use-math) — specifications

Implementation: `extracted/UseCombinatoricsCounting` (verbatim `cargo hax extract
use-combinatorics-counting` output for RustUse/use-math@183d26ec, crate
`crates/use-combinatorics`): `use_combinatorics.counting.factorial` and
`use_combinatorics.counting.permutations` with their loops.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The property tests compare the library against test-local reference helpers
(`factorial_reference`, `permutations_reference` in
`tests/property_counting.rs`). Those helpers live in an integration-test file,
which hax does not extract, so they are transcribed below line by line:
`u128::checked_mul` becomes `checkedMulU128` (a `u128` is a natural number
`< 2^128`; `checked_mul` returns `None` exactly when the product does not fit),
the `for factor in a..=b { result = result.checked_mul(factor)?; }` loop becomes
a `List.foldlM` in the `Option` monad over `List.range' a (b + 1 - a)` (the
`?` short-circuits on the first `None`, as `Option.bind` does).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.UseCombinatorics.Counting

open use_combinatorics

/-- `u128::checked_mul` on the values of two `u128`s: `Some (a * b)` if the product
fits in 128 bits, `None` otherwise. -/
def checkedMulU128 (a b : Nat) : Option Nat :=
  if a * b < 2^128 then some (a * b) else none

/-- Transcription of the test helper (tests/property_counting.rs:4-12)
```rust
fn factorial_reference(n: u8) -> Option<u128> {
    let mut result = 1_u128;
    for factor in 2..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }
    Some(result)
}
```
`2..=n` enumerates `List.range' 2 (n + 1 - 2)`. -/
def factorial_reference (n : Nat) : Option Nat :=
  (List.range' 2 (n + 1 - 2)).foldlM checkedMulU128 1

/-- Transcription of the test helper (tests/property_counting.rs:14-27)
```rust
fn permutations_reference(n: u8, k: u8) -> Option<u128> {
    if k > n {
        return None;
    }
    let mut result = 1_u128;
    let start = u64::from(n - k) + 1;
    for factor in start..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }
    Some(result)
}
```
(`n - k` cannot underflow after the `k > n` guard; `start ≤ 256` cannot overflow.)
`start..=n` enumerates `List.range' start (n + 1 - start)`. -/
def permutations_reference (n k : Nat) : Option Nat :=
  if k > n then none
  else
    let start := (n - k) + 1
    (List.range' start (n + 1 - start)).foldlM checkedMulU128 1

end Benchmark.Cases.UseCombinatorics.Counting
