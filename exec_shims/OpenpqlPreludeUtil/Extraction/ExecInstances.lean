import OpenpqlPreludeUtil.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for openpql_prelude.waugh_indexer.mixed_radix.MixedRadix
deriving instance Repr for openpql_prelude.waugh_indexer.mixed_radix.MixedRadix
deriving instance Plausible.Arbitrary for openpql_prelude.waugh_indexer.mixed_radix.MixedRadix
