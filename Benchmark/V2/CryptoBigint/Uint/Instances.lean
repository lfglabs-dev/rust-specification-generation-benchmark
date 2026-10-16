import Benchmark.Exec.Runtime
import CryptoBigintUint.Extraction

/-! Grader-side instances for target `crypto_bigint/uint`: decidable equality /
`Repr` for `Uint` (gold spec and diff probes) and `Arbitrary`
for `Uint` (so that the upstream oracle, whose inputs are `U256` values, can be
executed by `baseline`). -/

open CoreModels Aeneas Aeneas.Std

deriving instance DecidableEq, Repr for crypto_bigint.uint.Uint
deriving instance Plausible.Arbitrary for crypto_bigint.uint.Uint
