import JiffCivil.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for jiff_core.bounds.BoundsError
deriving instance DecidableEq for jiff_core.bounds.SpecialBoundsError
deriving instance Repr for jiff_core.bounds.SpecialBoundsError
deriving instance Plausible.Arbitrary for jiff_core.bounds.SpecialBoundsError
deriving instance DecidableEq for jiff_core.bounds.RangeErrorKind
deriving instance Repr for jiff_core.bounds.RangeErrorKind
deriving instance DecidableEq for jiff_core.bounds.RangeError
deriving instance Repr for jiff_core.bounds.RangeError
deriving instance Plausible.Arbitrary for jiff_core.bounds.RangeError
deriving instance DecidableEq for jiff_core.civil.date.Date
deriving instance Repr for jiff_core.civil.date.Date
deriving instance Plausible.Arbitrary for jiff_core.civil.date.Date
deriving instance DecidableEq for jiff_core.civil.time.Time
deriving instance Repr for jiff_core.civil.time.Time
deriving instance Plausible.Arbitrary for jiff_core.civil.time.Time
deriving instance DecidableEq for jiff_core.civil.datetime.DateTime
deriving instance Repr for jiff_core.civil.datetime.DateTime
deriving instance Plausible.Arbitrary for jiff_core.civil.datetime.DateTime
deriving instance DecidableEq for jiff_core.civil.time.TimeSecond
deriving instance Repr for jiff_core.civil.time.TimeSecond
deriving instance Plausible.Arbitrary for jiff_core.civil.time.TimeSecond
deriving instance DecidableEq for jiff_core.civil.time.TimeNanosecond
deriving instance Repr for jiff_core.civil.time.TimeNanosecond
deriving instance Plausible.Arbitrary for jiff_core.civil.time.TimeNanosecond
