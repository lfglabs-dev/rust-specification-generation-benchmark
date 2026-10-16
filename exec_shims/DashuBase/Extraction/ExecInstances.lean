import DashuBase.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for dashu_base.bit.BitTest
deriving instance Repr for dashu_base.bit.BitTest
