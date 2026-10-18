import SlabSlab.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for slab.Entry
deriving instance Repr for slab.Entry
deriving instance Plausible.Arbitrary for slab.Entry
