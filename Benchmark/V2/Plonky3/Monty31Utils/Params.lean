import Plonky3Monty31Utils.Extraction

/-! Concrete `MontyParameters` instances for target `plonky3/monty31_utils`
(shared by the gold specification, the upstream oracles and candidates).

`RSGB.Monty31.BB` / `RSGB.Monty31.KB` are the BabyBear / KoalaBear parameters
(`PRIME = 0x78000001` / `0x7f000001`, `MONTY_BITS = 32`,
`MONTY_MU = 0x88000001` / `0x81000001`, `MONTY_MASK = 0xffffffff`, the trait's
default) on the marker type `Unit`; the supertrait instances are trivial. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_monty_31

namespace RSGB.Monty31

/-- Montgomery parameters with prime `p`, `MONTY_BITS = 32` and `MONTY_MU = mu`. -/
def mk (p mu : Std.U32) : data_traits.MontyParameters Unit where
  PRIME := .ok p
  MONTY_BITS := .ok 32#u32
  MONTY_MU := .ok mu
  MONTY_MASK := .ok 4294967295#u32
  coremarkerCopyInst := ⟨⟨fun x => .ok x, fun _ y => .ok y⟩⟩
  coredefaultDefaultInst := ⟨.ok ()⟩
  corefmtDebugInst := ⟨fun _ f => .ok (.Ok (), f)⟩
  corecmpEqInst := ⟨⟨fun _ _ => .ok true, fun _ _ => .ok false⟩⟩
  corecmpPartialEqInst := ⟨fun _ _ => .ok true, fun _ _ => .ok false⟩
  corehashHashInst := ⟨fun _ _ h => .ok h⟩

/-- BabyBear: `P = 2^31 - 2^27 + 1 = 2013265921`, `MONTY_MU = 0x88000001`. -/
def BB : data_traits.MontyParameters Unit := mk 2013265921#u32 2281701377#u32

/-- KoalaBear: `P = 2^31 - 2^24 + 1 = 2130706433`, `MONTY_MU = 0x81000001`. -/
def KB : data_traits.MontyParameters Unit := mk 2130706433#u32 2164260865#u32

end RSGB.Monty31
