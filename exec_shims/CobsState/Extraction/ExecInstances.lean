import CobsState.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for cobs.dec.DecoderState
deriving instance Repr for cobs.dec.DecoderState
deriving instance Plausible.Arbitrary for cobs.dec.DecoderState
deriving instance DecidableEq for cobs.dec.DecodeResult
deriving instance Repr for cobs.dec.DecodeResult
deriving instance Plausible.Arbitrary for cobs.dec.DecodeResult
deriving instance DecidableEq for cobs.dec.DecodeError
deriving instance Repr for cobs.dec.DecodeError
deriving instance Plausible.Arbitrary for cobs.dec.DecodeError
deriving instance DecidableEq for cobs.enc.EncoderState
deriving instance Repr for cobs.enc.EncoderState
deriving instance Plausible.Arbitrary for cobs.enc.EncoderState
deriving instance DecidableEq for cobs.enc.PushResult
deriving instance Repr for cobs.enc.PushResult
deriving instance Plausible.Arbitrary for cobs.enc.PushResult
