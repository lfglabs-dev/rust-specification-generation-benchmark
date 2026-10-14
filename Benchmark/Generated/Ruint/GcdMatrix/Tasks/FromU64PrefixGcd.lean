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
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Ruint.GcdMatrix
