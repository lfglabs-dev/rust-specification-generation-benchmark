import Benchmark.Cases.Ruint.GcdMatrix.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.GcdMatrix

/-- For all `a b : u128`, with `(a, b) := (max(a, b), min(a, b))` normalised so
that the top bit of `a` is set, the Lehmer matrix computed by
`Matrix::from_u64_prefix` from the 64-bit prefixes (Jebelean's double-digit
condition, packed 32-bit cofactors) panics exactly when `a = b = 0`
(`leading_zeros` is 128 and `a << 128` overflows: an upstream bug) and
otherwise never panics, and applying it to the full `(a, b)` with
`apply_u128` yields `(c, d)` with `c >= d`; either the matrix is the
identity and `(c, d) = (a, b)`, or `c <= a`, `d < b` and
`gcd(a, b) = gcd(c, d)`. -/
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

end Benchmark.Cases.Ruint.GcdMatrix
