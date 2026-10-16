import UseCombinatoricsCounting.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for use_combinatorics.error.CombinatoricsError
deriving instance Repr for use_combinatorics.error.CombinatoricsError
deriving instance Plausible.Arbitrary for use_combinatorics.error.CombinatoricsError
