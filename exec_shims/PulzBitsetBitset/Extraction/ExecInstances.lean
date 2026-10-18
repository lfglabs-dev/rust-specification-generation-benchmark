import PulzBitsetBitset.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for pulz_bitset.BitSetIter
deriving instance Repr for pulz_bitset.BitSetIter
deriving instance Plausible.Arbitrary for pulz_bitset.BitSetIter
