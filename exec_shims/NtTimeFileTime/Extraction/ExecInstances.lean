import NtTimeFileTime.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for nt_time.error.FileTimeRangeErrorKind
deriving instance Repr for nt_time.error.FileTimeRangeErrorKind
deriving instance Plausible.Arbitrary for nt_time.error.FileTimeRangeErrorKind
