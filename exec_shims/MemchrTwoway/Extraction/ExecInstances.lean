import MemchrTwoway.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for memchr.arch.all.twoway.Shift
deriving instance Repr for memchr.arch.all.twoway.Shift
deriving instance Plausible.Arbitrary for memchr.arch.all.twoway.Shift
deriving instance DecidableEq for memchr.arch.all.twoway.TwoWay
deriving instance Repr for memchr.arch.all.twoway.TwoWay
deriving instance Plausible.Arbitrary for memchr.arch.all.twoway.TwoWay
deriving instance DecidableEq for memchr.arch.all.twoway.SuffixKind
deriving instance Repr for memchr.arch.all.twoway.SuffixKind
deriving instance Plausible.Arbitrary for memchr.arch.all.twoway.SuffixKind
deriving instance DecidableEq for memchr.arch.all.twoway.SuffixOrdering
deriving instance Repr for memchr.arch.all.twoway.SuffixOrdering
deriving instance Plausible.Arbitrary for memchr.arch.all.twoway.SuffixOrdering
deriving instance DecidableEq for memchr.arch.all.twoway.Suffix
deriving instance Repr for memchr.arch.all.twoway.Suffix
deriving instance Plausible.Arbitrary for memchr.arch.all.twoway.Suffix
