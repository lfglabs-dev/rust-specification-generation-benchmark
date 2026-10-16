import RustCrdtDot.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for crdts.dot.Dot
deriving instance Repr for crdts.dot.Dot
deriving instance Plausible.Arbitrary for crdts.dot.Dot
deriving instance DecidableEq for crdts.dot.OrdDot
deriving instance Repr for crdts.dot.OrdDot
deriving instance Plausible.Arbitrary for crdts.dot.OrdDot
