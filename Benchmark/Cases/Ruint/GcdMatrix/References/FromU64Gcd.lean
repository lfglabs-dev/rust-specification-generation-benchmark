import Benchmark.Cases.Ruint.GcdMatrix.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.GcdMatrix

/-- For all `a b : u64`, with `(a, b) := (max(a, b), min(a, b))`, the Lehmer
matrix `Matrix::from_u64(a, b)` (a full 64-bit extended Euclid run) never
panics, and applying it with `apply_u128` to `(a, b)` yields `(c, d)` with
`c >= d`, `c = gcd(a, b)` and `d = 0`. -/
def from_u64_gcd_spec (a b : Std.U64) : Prop :=
  let hi := if a.val ≤ b.val then b else a -- max(a, b)
  let lo := if a.val ≤ b.val then a else b -- min(a, b)
  (do
    let m ← algorithms.gcd.matrix.Matrix.from_u64 hi lo
    algorithms.gcd.matrix.Matrix.apply_u128 m (UScalar.cast .U128 hi) (UScalar.cast .U128 lo))
  ⦃ cd => cd.1.val ≥ cd.2.val ∧ cd.1.val = Nat.gcd hi.val lo.val ∧ cd.2.val = 0 ⦄

end Benchmark.Cases.Ruint.GcdMatrix
