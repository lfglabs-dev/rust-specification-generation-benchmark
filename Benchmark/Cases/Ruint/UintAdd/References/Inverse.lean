import Benchmark.Cases.Ruint.UintAdd.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.UintAdd

/-- For every supported width `BITS` (with `LIMBS = nlimbs(BITS)`) and every
`a : Uint<BITS, LIMBS>` produced by the proptest strategy, wrapping negation is
an additive inverse and an involution: `a + (-a) == U::ZERO`,
`a - a == U::ZERO` and `-(-a) == a`. -/
def inverse_spec (BITS LIMBS : Std.Usize) (la : Array Std.U64 LIMBS) : Prop :=
  (do
    let a ← Uint.from_limbs_unmasked BITS la -- a: U
    let na ← Uint.Insts.CoreOpsArithNegUint.neg a -- -a
    let s ← Uint.Insts.CoreOpsArithAddUintUint.add a na -- a + (-a)
    let z ← Uint.ZERO BITS LIMBS -- U::ZERO
    let d ← Uint.Insts.CoreOpsArithSubUintUint.sub a a -- a - a
    let z' ← Uint.ZERO BITS LIMBS -- U::ZERO
    let na' ← Uint.Insts.CoreOpsArithNegUint.neg a -- -a
    let nna ← Uint.Insts.CoreOpsArithNegUint.neg na' -- -(-a)
    ok (a, s, z, d, z', nna))
  ⦃ r => r.2.1 = r.2.2.1 ∧ r.2.2.2.1 = r.2.2.2.2.1 ∧ r.2.2.2.2.2 = r.1 ⦄

end Benchmark.Cases.Ruint.UintAdd
