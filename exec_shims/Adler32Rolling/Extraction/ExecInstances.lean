import Adler32Rolling.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for adler32.RollingAdler32
deriving instance Repr for adler32.RollingAdler32
deriving instance Plausible.Arbitrary for adler32.RollingAdler32
