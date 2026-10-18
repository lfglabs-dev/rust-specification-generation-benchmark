import CrcReflected.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for crc.crc16.Digest
deriving instance Repr for crc.crc16.Digest
deriving instance Plausible.Arbitrary for crc.crc16.Digest
deriving instance DecidableEq for crc.crc32.Digest
deriving instance Repr for crc.crc32.Digest
deriving instance DecidableEq for crc.crc64.Digest
deriving instance Repr for crc.crc64.Digest
