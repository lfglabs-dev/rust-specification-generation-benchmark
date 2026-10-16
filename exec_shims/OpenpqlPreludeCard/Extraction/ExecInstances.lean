import OpenpqlPreludeCard.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for openpql_prelude.card.suit.Suit
deriving instance Repr for openpql_prelude.card.suit.Suit
deriving instance Plausible.Arbitrary for openpql_prelude.card.suit.Suit
deriving instance DecidableEq for openpql_prelude.card.rank.Rank
deriving instance Repr for openpql_prelude.card.rank.Rank
deriving instance Plausible.Arbitrary for openpql_prelude.card.rank.Rank
deriving instance DecidableEq for openpql_prelude.card.card.Card
deriving instance Repr for openpql_prelude.card.card.Card
deriving instance Plausible.Arbitrary for openpql_prelude.card.card.Card
