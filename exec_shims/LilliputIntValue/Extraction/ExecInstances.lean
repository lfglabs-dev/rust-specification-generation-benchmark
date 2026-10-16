import LilliputIntValue.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for lilliput_core.sealed.Sealed
deriving instance Repr for lilliput_core.sealed.Sealed
deriving instance Plausible.Arbitrary for lilliput_core.sealed.Sealed
deriving instance DecidableEq for lilliput_core.value.int.unsigned.UnsignedIntValue
deriving instance Repr for lilliput_core.value.int.unsigned.UnsignedIntValue
deriving instance Plausible.Arbitrary for lilliput_core.value.int.unsigned.UnsignedIntValue
deriving instance DecidableEq for lilliput_core.value.int.signed.SignedIntValue
deriving instance Repr for lilliput_core.value.int.signed.SignedIntValue
deriving instance Plausible.Arbitrary for lilliput_core.value.int.signed.SignedIntValue
deriving instance DecidableEq for lilliput_core.value.int.IntValue
deriving instance Repr for lilliput_core.value.int.IntValue
deriving instance Plausible.Arbitrary for lilliput_core.value.int.IntValue
