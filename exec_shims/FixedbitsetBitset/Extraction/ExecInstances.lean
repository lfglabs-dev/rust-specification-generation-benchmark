import FixedbitsetBitset.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for fixedbitset.Masks
deriving instance Repr for fixedbitset.Masks
deriving instance Plausible.Arbitrary for fixedbitset.Masks
