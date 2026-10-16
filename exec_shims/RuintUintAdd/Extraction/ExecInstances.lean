import RuintUintAdd.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for ruint.Uint
deriving instance Repr for ruint.Uint
deriving instance Plausible.Arbitrary for ruint.Uint
