import Benchmark.Cases.Fastdivide.Divider.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide
open Benchmark.Cases.Fastdivide.Divider

namespace Benchmark.Cases.Fastdivide.Divider.Oracle

/-- PBT `tests::test_proptest` (src/lib.rs:236):
`DividerU64::divide_by(d).divide(n) == n / d`. -/
def divide_matches_native_division_spec (n d : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by d
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / d.val ⦄

/-- PBT `tests::test_proptest_divide_by_7` (src/lib.rs:246):
`DividerU64::divide_by(7).divide(n) == n / 7` (exercises the `General` path). -/
def divide_by_7_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 7#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 7 ⦄

/-- PBT `tests::test_proptest_divide_by_11` (src/lib.rs:256):
`DividerU64::divide_by(11).divide(n) == n / 11` (exercises the `Fast` path). -/
def divide_by_11_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 11#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 11 ⦄

axiom divide_by_11_matches_native_division (n : Std.U64)
    (h_n : n.val < 2^64 - 1) :
    divide_by_11_matches_native_division_spec n

axiom divide_by_7_matches_native_division (n : Std.U64)
    (h_n : n.val < 2^64 - 1) :
    divide_by_7_matches_native_division_spec n

axiom divide_matches_native_division (n d : Std.U64)
    (h_n : n.val < 2^64 - 1)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 2^64 - 1) :
    divide_matches_native_division_spec n d

end Benchmark.Cases.Fastdivide.Divider.Oracle
