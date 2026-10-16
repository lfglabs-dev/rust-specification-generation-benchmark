import IndexedBitvecWord.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for indexed_bitvec_core.ones_or_zeros.ZeroBits
deriving instance Repr for indexed_bitvec_core.ones_or_zeros.ZeroBits
deriving instance DecidableEq for indexed_bitvec_core.ones_or_zeros.private.Sealed
deriving instance Repr for indexed_bitvec_core.ones_or_zeros.private.Sealed
deriving instance Plausible.Arbitrary for indexed_bitvec_core.ones_or_zeros.private.Sealed
