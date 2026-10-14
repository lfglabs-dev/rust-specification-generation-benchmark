import Benchmark.Cases.Ruint.GcdMatrix.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint
open Benchmark.Cases.Ruint.GcdMatrix

namespace Benchmark.Cases.Ruint.GcdMatrix.Oracle

/-- PBT `algorithms::gcd::matrix::tests::test_from_u64`
(src/algorithms/gcd/matrix.rs:380-390):
```
proptest!(|(a: u64, b: u64)| {
    let (a, b) = (max(a,b), min(a,b));
    let m = Matrix::from_u64(a, b);
    let (c, d) = m.apply_u128(a as u128, b as u128);
    assert!(c >= d);
    assert_eq!(c, gcd(a as u128, b as u128));
    assert_eq!(d, 0);
});
```
`max`/`min` are `core::cmp::max`/`min` on `u64` (`max(a, b)` returns `b` when
`a <= b`, `min(a, b)` returns `a` when `a <= b`). `gcd` is the test-local
Euclidean helper on `u128` (`while b != 0 { a %= b; swap(&mut a, &mut b) }`),
which cannot panic and returns the mathematical gcd, stated with `Nat.gcd`.
`x as u128` is the zero-extending cast `UScalar.cast .U128`. -/
def from_u64_gcd_spec (a b : Std.U64) : Prop :=
  let hi := if a.val ≤ b.val then b else a -- max(a, b)
  let lo := if a.val ≤ b.val then a else b -- min(a, b)
  (do
    let m ← algorithms.gcd.matrix.Matrix.from_u64 hi lo
    algorithms.gcd.matrix.Matrix.apply_u128 m (UScalar.cast .U128 hi) (UScalar.cast .U128 lo))
  ⦃ cd => cd.1.val ≥ cd.2.val ∧ cd.1.val = Nat.gcd hi.val lo.val ∧ cd.2.val = 0 ⦄

/-- PBT `algorithms::gcd::matrix::tests::test_from_u64_prefix`
(src/algorithms/gcd/matrix.rs:392-412):
```
proptest!(|(a: u128, b: u128)| {
    let (a, b) = (max(a,b), min(a,b));
    let s = a.leading_zeros();
    let (sa, sb) = (a << s, b << s);
    let m = Matrix::from_u64_prefix((sa >> 64) as u64, (sb >> 64) as u64);
    let (c, d) = m.apply_u128(a, b);
    assert!(c >= d);
    if m == Matrix::IDENTITY {
        assert_eq!(c, a);
        assert_eq!(d, b);
    } else {
        assert!(c <= a);
        assert!(d < b);
        assert_eq!(gcd(a, b), gcd(c, d));
    }
});
```
`max`/`min` as in `from_u64_gcd_spec`; `a.leading_zeros()` is the CoreModels
`core.num.U128.leading_zeros`; `a << s` / `b << s` (u128 by u32) and `sa >> 64`
are the extracted checked shifts (a shift amount `>= 128` panics in a debug
build); `x as u64` is the truncating cast `UScalar.cast .U64`; `m ==
Matrix::IDENTITY` is the extracted derived `PartialEq::eq`; `gcd` is the
test-local Euclid helper, stated with `Nat.gcd`.

At `a = b = 0`, `max(a, b) = 0`, `leading_zeros` is 128 and `0 << 128` panics
in a debug build ("attempt to shift left with overflow": an upstream bug,
essentially never sampled by proptest). The spec states the test's actual
outcome on its whole domain: the computation panics exactly when `a = b = 0`
and otherwise satisfies the assertions above. -/
def from_u64_prefix_spec (a b : Std.U128) : Prop :=
  let hi := if a.val ≤ b.val then b else a -- max(a, b)
  let lo := if a.val ≤ b.val then a else b -- min(a, b)
  let run : RustM ((Std.U128 × Std.U128) × Bool) := do
    let s ← core.num.U128.leading_zeros hi
    let sa ← hi <<< s
    let sb ← lo <<< s
    let sa64 ← sa >>> 64#i32
    let sb64 ← sb >>> 64#i32
    let m ← algorithms.gcd.matrix.Matrix.from_u64_prefix (UScalar.cast .U64 sa64) (UScalar.cast .U64 sb64)
    let cd ← algorithms.gcd.matrix.Matrix.apply_u128 m hi lo
    let isId ← algorithms.gcd.matrix.Matrix.Insts.CoreCmpPartialEqMatrix.eq m
      algorithms.gcd.matrix.Matrix.IDENTITY
    ok (cd, isId)
  ((a.val = 0 ∧ b.val = 0) → run = fail .panic) ∧
  (¬ (a.val = 0 ∧ b.val = 0) →
    run ⦃ r => r.1.1.val ≥ r.1.2.val ∧
      (if r.2 then r.1.1 = hi ∧ r.1.2 = lo
       else r.1.1.val ≤ hi.val ∧ r.1.2.val < lo.val ∧
         Nat.gcd hi.val lo.val = Nat.gcd r.1.1.val r.1.2.val) ⦄)

axiom from_u64_gcd (a b : Std.U64) :
    from_u64_gcd_spec a b

axiom from_u64_prefix_gcd (a b : Std.U128) :
    from_u64_prefix_spec a b

end Benchmark.Cases.Ruint.GcdMatrix.Oracle
