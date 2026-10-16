import CryptoBigintUint.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for crypto_bigint.uint.Uint
deriving instance Repr for crypto_bigint.uint.Uint
deriving instance Plausible.Arbitrary for crypto_bigint.uint.Uint
