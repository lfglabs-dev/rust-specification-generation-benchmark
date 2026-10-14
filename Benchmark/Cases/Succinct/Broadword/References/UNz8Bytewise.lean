import Benchmark.Cases.Succinct.Broadword.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open succinct

namespace Benchmark.Cases.Succinct.Broadword

/-- The broadword "parallel > 0" `u_nz8(n) = (((n | H8) - L8) | n) & H8` never
panics and, for each of the eight bytes, sets byte `i` of the result to
`0x80` exactly when byte `i` of `n` is non-zero. -/
def u_nz8_bytewise_spec (n : Std.U64) : Prop :=
  broadword.u_nz8 n ⦃ r => ∀ i, i < 8 → (byteAt n i ≠ 0 ↔ byteAt r i = 0x80) ⦄

end Benchmark.Cases.Succinct.Broadword
