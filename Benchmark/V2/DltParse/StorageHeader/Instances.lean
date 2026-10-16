import Benchmark.Exec.Runtime
import DltParseStorageHeader.Extraction

/-! Grader-side instances for target `dlt_parse/storage_header`: decidable
equality / `Repr` for the result types (gold spec and diff probes) and
`Arbitrary` for `StorageHeader` (so that the upstream oracle, whose input is a
header, can be executed by `baseline`). -/

open CoreModels Aeneas Aeneas.Std


deriving instance DecidableEq, Repr for CoreModels.core.result.Result
deriving instance DecidableEq, Repr for dlt_parse.storage.storage_header.StorageHeader
deriving instance DecidableEq, Repr for
  dlt_parse.error.storage_header_start_pattern_error.StorageHeaderStartPatternError
deriving instance Plausible.Arbitrary for dlt_parse.storage.storage_header.StorageHeader
