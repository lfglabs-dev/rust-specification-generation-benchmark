import Benchmark.Exec.Runtime
import RuintUintAdd.Extraction

/-! Grader-side instances for target `ruint/uint_add`: decidable equality /
`Repr` for `Uint` (gold spec and diff probes). -/

open CoreModels Aeneas Aeneas.Std

deriving instance DecidableEq, Repr for ruint.Uint
