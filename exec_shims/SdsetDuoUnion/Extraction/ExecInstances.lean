import SdsetDuoUnion.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for sdset.duo.union.Union
deriving instance Repr for sdset.duo.union.Union
deriving instance Plausible.Arbitrary for sdset.duo.union.Union
deriving instance DecidableEq for sdset.duo.union.UnionIter
deriving instance Repr for sdset.duo.union.UnionIter
deriving instance Plausible.Arbitrary for sdset.duo.union.UnionIter
