import DltParseStorageHeader.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for dlt_parse.error.storage_header_start_pattern_error.StorageHeaderStartPatternError
deriving instance Repr for dlt_parse.error.storage_header_start_pattern_error.StorageHeaderStartPatternError
deriving instance Plausible.Arbitrary for dlt_parse.error.storage_header_start_pattern_error.StorageHeaderStartPatternError
deriving instance DecidableEq for dlt_parse.storage.storage_header.StorageHeader
deriving instance Repr for dlt_parse.storage.storage_header.StorageHeader
deriving instance Plausible.Arbitrary for dlt_parse.storage.storage_header.StorageHeader
