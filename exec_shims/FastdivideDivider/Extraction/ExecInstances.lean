import FastdivideDivider.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for fastdivide.DividerU64
deriving instance Repr for fastdivide.DividerU64
deriving instance Plausible.Arbitrary for fastdivide.DividerU64
