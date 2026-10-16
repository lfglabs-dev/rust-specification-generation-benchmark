import Aeneas
import CoreModels

/-!
# RSGB v2 prelude

Small helpers available to every v2 specification (candidate and gold):
building scalars from natural numbers without proof obligations (the value is
reduced modulo `2^bits`).
-/

open Aeneas Aeneas.Std

namespace RSGB

/-- `n mod 2^bits` as an unsigned Rust scalar. -/
def mkU (ty : UScalarTy) (n : Nat) : UScalar ty := ⟨BitVec.ofNat _ n⟩

/-- `n mod 2^bits` (two's complement) as a signed Rust scalar. -/
def mkI (ty : IScalarTy) (n : Int) : IScalar ty := ⟨BitVec.ofInt _ n⟩

end RSGB
