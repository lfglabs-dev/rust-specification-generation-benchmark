import AtoiRadix.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for atoi.Sign
deriving instance Repr for atoi.Sign
deriving instance Plausible.Arbitrary for atoi.Sign
deriving instance DecidableEq for atoi.builtin.SafeDigits
deriving instance Repr for atoi.builtin.SafeDigits
