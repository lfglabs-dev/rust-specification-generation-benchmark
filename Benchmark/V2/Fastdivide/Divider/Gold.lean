import Benchmark.V2.Prelude
import FastdivideDivider.Extraction

/-! Hidden gold specification for target `fastdivide/divider`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM fastdivide RSGB

/-! Computable helpers kept outside the `Benchmark.` namespace so that the test
driver does not delta-expand them. -/
namespace RSGBGold.Fastdivide

/-- Observable encoding of a divider: `(variant tag, magic, shift)`. -/
def enc : DividerU64 → Nat × Nat × Nat
  | .Fast m s => (0, m.val, s.val)
  | .BitShift s => (1, 0, s.val)
  | .General m s => (2, m.val, s.val)

/-- Does the computation panic? -/
def panics {α} : RustM α → Bool
  | .fail .panic => true
  | _ => false

end RSGBGold.Fastdivide

open RSGBGold.Fastdivide

namespace Benchmark.V2.Fastdivide.Divider.Gold

/-- `divide_by` panics exactly on a zero divisor. -/
def gold_divide_by_zero_panics (b : Bool) : Prop :=
  b = b → panics (DividerU64.divide_by 0#u64) = true

/-- `divide_by` is total for every non-zero divisor. -/
def gold_divide_by_total (d : Std.U64) : Prop :=
  d.val ≠ 0 → DividerU64.divide_by d ⦃ _ => True ⦄

/-- Exact quotient for every dividend and every non-zero divisor (incl. `u64::MAX`). -/
def gold_divide_exact (n d : Std.U64) : Prop :=
  d.val ≠ 0 →
    (do let v ← DividerU64.divide_by d; DividerU64.divide v n) ⦃ q => q.val = n.val / d.val ⦄

/-- Same, with small divisors (dense coverage of the `General`/`Fast` cases). -/
def gold_divide_exact_small (n : Std.U64) (d : Std.U16) : Prop :=
  d.val ≠ 0 →
    (do let v ← DividerU64.divide_by (mkU .U64 d.val); DividerU64.divide v n)
      ⦃ q => q.val = n.val / d.val ⦄

/-- Same, with a dividend close to `u64::MAX` (the overflow-prone region). -/
def gold_divide_exact_high (k : Std.U16) (d : Std.U64) : Prop :=
  d.val ≠ 0 →
    (do let v ← DividerU64.divide_by d; DividerU64.divide v (mkU .U64 (2^64 - 1 - k.val)))
      ⦃ q => q.val = (2^64 - 1 - k.val) / d.val ⦄

/-- Divisor `2^e + j - 2` near a power of two. -/
def nearD (e j : Std.U8) : Nat := 2^(e.val % 64) + (j.val % 5) - 2

/-- A dividend `q * d + c - 1` next to a multiple of `d`. -/
def nearM (d : Nat) (n : Std.U64) (c : Std.U8) : Nat := (n.val % (2^64 / d)) * d + (c.val % 3) - 1

/-- Divisors near a power of two, dividends next to a multiple of the divisor. -/
def gold_divide_exact_near_pow2 (e j : Std.U8) (n : Std.U64) (c : Std.U8) : Prop :=
  0 < nearD e j → nearD e j < 2^64 → nearM (nearD e j) n c < 2^64 →
    (do let v ← DividerU64.divide_by (mkU .U64 (nearD e j)); DividerU64.divide v (mkU .U64 (nearM (nearD e j) n c)))
      ⦃ q => q.val = nearM (nearD e j) n c / nearD e j ⦄

/-- The `u64 / DividerU64` operator is the same exact division. -/
def gold_div_op (n d : Std.U64) : Prop :=
  d.val ≠ 0 →
    (do let v ← DividerU64.divide_by d; U64.Insts.CoreOpsArithDivDividerU64U64.div n v)
      ⦃ q => q.val = n.val / d.val ⦄

/-- Powers of two are handled by a plain shift by `log2 d` (crate test `test_divide_by_4`). -/
def gold_pow2_bitshift (k : Std.U8) : Prop :=
  k.val < 64 → DividerU64.divide_by (mkU .U64 (2^k.val)) ⦃ v => enc v = (1, 0, k.val) ⦄

/-- Non-powers of two never use the `BitShift` representation. -/
def gold_non_pow2_not_bitshift (d : Std.U64) : Prop :=
  d.val ≠ 0 → (d.val &&& (d.val - 1)) ≠ 0 → DividerU64.divide_by d ⦃ v => (enc v).1 ≠ 1 ⦄

/-- Crate test vectors: 11 → `Fast { magic: 13415813871788764812, shift: 3 }`,
7 → `General { .. }`. -/
def info_test_vectors (b : Bool) : Prop :=
  b = b →
    DividerU64.divide_by 11#u64 ⦃ v => enc v = (0, 13415813871788764812, 3) ⦄ ∧
    DividerU64.divide_by 7#u64 ⦃ v => (enc v).1 = 2 ⦄

/-! Differential-testing probes. -/

def diff_divide_by (d : Std.U64) := do
  let v ← DividerU64.divide_by d; ok (enc v)
def diff_divide_by_small (d : Std.U16) := do
  let v ← DividerU64.divide_by (mkU .U64 d.val); ok (enc v)
def diff_divide (n d : Std.U64) := do
  let v ← DividerU64.divide_by d; DividerU64.divide v n
def diff_divide_small (n : Std.U64) (d : Std.U16) := do
  let v ← DividerU64.divide_by (mkU .U64 d.val); DividerU64.divide v n
def diff_div (n d : Std.U64) := do
  let v ← DividerU64.divide_by d; U64.Insts.CoreOpsArithDivDividerU64U64.div n v

end Benchmark.V2.Fastdivide.Divider.Gold
