import Benchmark.Cases.Dashu.Base.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base
open Benchmark.Cases.Dashu.Base

namespace Benchmark.Cases.Dashu.Base.Oracle

/-- PBT `u128_tests::div_rem` (fuzz/tests/base.rs:154-161, `gen_uint!(u128_tests, u128)`):
```
let (q, r) = a.div_rem(b);
prop_assert_eq!((q as u128) * (b as u128) + (r as u128), a as u128);
prop_assert!((r as u128) < (b as u128));
```
The `as u128` casts are identities at this width, so the reconstruction
`q * b + r` is computed with the checked (debug-build) `u128` operations of the
test: an overflow there would make the test panic, and the spec false. -/
def u128_div_rem_reconstructs_spec (a b : Std.U128) : Prop :=
  (do
    let (q, r) ← U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem a b
    let qb ← q * b
    let recon ← qb + r
    ok (recon, r)) ⦃ res => res.1.val = a.val ∧ res.2.val < b.val ⦄

/-- PBT `i64_tests::div_rem` (fuzz/tests/base.rs:232-240, `gen_int!(i64_tests, i64)`):
```
let (q, r) = a.div_rem(b);
prop_assert_eq!((q as i128) * (b as i128) + (r as i128), a as i128);
prop_assert!((r as i128).abs() < (b as i128).abs());
```
The test widens to `i128` before reconstructing; for `i64` operands none of
these `i128` operations can overflow (|q·b| ≤ 2^126, and `abs` of a widened
`i64` is at most 2^63), so they are stated over `Int` (`.val`) with the same
values. -/
def i64_div_rem_reconstructs_spec (a b : Std.I64) : Prop :=
  I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem a b ⦃ res =>
    res.1.val * b.val + res.2.val = a.val ∧ |res.2.val| < |b.val| ⦄

/-- PBT `i64_tests::div_rem_euclid` (fuzz/tests/base.rs:242-256, `gen_int!(i64_tests, i64)`):
```
let (q, r) = a.div_rem_euclid(b);
prop_assert_eq!(q.wrapping_mul(b).wrapping_add(r), a);
prop_assert!((r as i128) >= 0 && (r as i128) < (b as i128).abs());
prop_assert_eq!(q as i128, (a as i128).div_euclid(b as i128));
prop_assert_eq!(r as i128, (a as i128).rem_euclid(b as i128));
```
`wrapping_mul`/`wrapping_add` are executed with the CoreModels `i64` models.
The `i128` side cannot overflow for widened `i64` operands (`b ≠ 0`, and the
only overflowing `div_euclid` input `i128::MIN / -1` is out of range), so it is
stated over `Int`: Rust's `div_euclid`/`rem_euclid` are exactly Lean's
`Int.ediv`/`Int.emod` (quotient with remainder `0 ≤ r < |b|`). -/
def i64_div_rem_euclid_matches_std_spec (a b : Std.I64) : Prop :=
  (do
    let (q, r) ← I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b
    let qb ← core.num.I64.wrapping_mul q b
    let recon ← core.num.I64.wrapping_add qb r
    ok (q, r, recon)) ⦃ res =>
      res.2.2 = a ∧
      (0 ≤ res.2.1.val ∧ res.2.1.val < |b.val|) ∧
      res.1.val = Int.ediv a.val b.val ∧
      res.2.1.val = Int.emod a.val b.val ⦄

/-- PBT `u64_tests::is_power_of_two` (fuzz/tests/base.rs:172-178, `gen_uint!(u64_tests, u64)`):
```
prop_assert_eq!(PowerOfTwo::is_power_of_two(&x), x.count_ones() == 1);
```
dashu's `PowerOfTwo` impl (called via UFCS) is compared with the population
count `u64::count_ones` (CoreModels model). -/
def u64_is_power_of_two_iff_one_bit_spec (x : Std.U64) : Prop :=
  (do
    let p ← U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two x
    let c ← core.num.U64.count_ones x
    ok (p, c)) ⦃ res => (res.1 = true ↔ res.2.val = 1) ⦄

axiom i64_div_rem_euclid_matches_std (a b : Std.I64)
    (h_assume_b_nonzero : b.val ≠ 0)
    (h_assume_no_overflow : ¬ (a.val = -2^63 ∧ b.val = -1)) :
    i64_div_rem_euclid_matches_std_spec a b

axiom i64_div_rem_reconstructs (a b : Std.I64)
    (h_assume_b_nonzero : b.val ≠ 0)
    (h_assume_no_overflow : ¬ (a.val = -2^63 ∧ b.val = -1)) :
    i64_div_rem_reconstructs_spec a b

axiom u128_div_rem_reconstructs (a b : Std.U128)
    (h_assume_b_nonzero : b.val ≠ 0) :
    u128_div_rem_reconstructs_spec a b

axiom u64_is_power_of_two_iff_one_bit (x : Std.U64) :
    u64_is_power_of_two_iff_one_bit_spec x

end Benchmark.Cases.Dashu.Base.Oracle
