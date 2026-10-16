import Benchmark.Exec.Runtime
import RuintUintAdd.Extraction

/-! Grader-side instances for target `ruint/uint_add`: decidable equality /
`Repr` for limb arrays and `Uint` (gold spec and diff probes). -/

open CoreModels Aeneas Aeneas.Std

namespace Benchmark.V2.Ruint.UintAdd

instance instDecEqStdArray {α : Type} [DecidableEq α] {n : Usize} : DecidableEq (Std.Array α n) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance instReprStdArray {α : Type} [Repr α] {n : Usize} : Repr (Std.Array α n) where
  reprPrec a p := reprPrec a.val p

end Benchmark.V2.Ruint.UintAdd

open Benchmark.V2.Ruint.UintAdd

deriving instance DecidableEq, Repr for ruint.Uint
