import Benchmark.V2.Prelude
import Benchmark.Exec.Runtime
import Plonky3Monty31Utils.Extraction
import Benchmark.V2.Plonky3.Monty31Utils.Params

/-! Hidden gold specification for target `plonky3/monty31_utils`.

API: `p3_monty_31::utils::{to_monty, to_monty_64, from_monty, monty_reduce,
large_monty_reduce, monty_reduce_u128, add, sub}`, generic over
`MP: MontyParameters`, instantiated with the BabyBear (`RSGB.Monty31.BB`) and
KoalaBear (`RSGB.Monty31.KB`) parameters (`Params.lean`). `R = 2^MONTY_BITS = 2^32`.

Contract (from the doc comments):
* `to_monty(x)`, `to_monty_64(x)`: `x·R mod P` (no constraint on the input);
* `from_monty(x)`: the `r < P` with `r·R ≡ x (mod P)` (no constraint);
* `monty_reduce(x)` for `x < R·P`, `large_monty_reduce(x)` for `x < 2·R·P`,
  `monty_reduce_u128(x)` for `x < 2^96`: the `r < P` with `r·R ≡ x (mod P)`;
  outside their documented domains ("must be", "Preconditions") the
  reductions are unspecified (the `debug_assert!` of `monty_reduce_u128` is not
  a promise: the historical `%`-based implementation does not panic there);
* `add(a, b)` for `a + b ≤ 2P`: `a + b` reduced once (`= P` iff `a + b = 2P`);
* `sub(a, b)` for `|a - b| ≤ P`: `a - b`, plus `P` if negative.
Outside these input ranges `add`/`sub` are unspecified ("may be incorrect"). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM p3_monty_31 RSGB

namespace RSGBGold.Plonky3.Monty31Utils

def R : Nat := 2 ^ 32

/-- `r` is the Montgomery reduction of `x` modulo `P`. -/
def redc (P : Nat) (r : RustM Std.U32) (x : Nat) : Bool :=
  match r with
  | .ok v => v.val < P && (v.val * R) % P == x % P
  | _ => false

def isVal (r : RustM Std.U32) (n : Nat) : Bool :=
  match r with
  | .ok v => v.val == n
  | _ => false

def addModel (P a b : Nat) : Nat := if a + b ≥ P then a + b - P else a + b
def subModel (P a b : Nat) : Nat := if a < b then a + P - b else a - b

end RSGBGold.Plonky3.Monty31Utils

namespace Benchmark.V2.Plonky3.Monty31Utils.Gold
open RSGBGold.Plonky3.Monty31Utils RSGB.Monty31


/-! ### `BB` (`P = 2013265921`) -/

def gold_to_monty_bb (x : Std.U32) : Prop :=
  isVal (utils.to_monty BB x) (x.val * R % 2013265921) = true

def gold_to_monty_64_bb (x : Std.U64) : Prop :=
  isVal (utils.to_monty_64 BB x) (x.val * R % 2013265921) = true

def gold_from_monty_bb (x : Std.U32) : Prop :=
  redc 2013265921 (utils.from_monty BB x) x.val = true

def gold_monty_reduce_bb (x : Std.U64) : Prop :=
  x.val < 8646911288846319616 → redc 2013265921 (utils.monty_reduce BB x) x.val = true

/-- Just below the end of the domain `[0, R·P)`. -/
def gold_monty_reduce_top_bb (d : Std.U32) : Prop :=
  let x := 8646911288846319616 - 1 - d.val
  redc 2013265921 (utils.monty_reduce BB (mkU .U64 x)) x = true

/-- Products of two reduced values (Montgomery multiplication). -/
def gold_monty_reduce_mul_bb (a b : Std.U32) : Prop :=
  let x := (a.val % 2013265921) * (b.val % 2013265921)
  redc 2013265921 (utils.monty_reduce BB (mkU .U64 x)) x = true

def gold_large_monty_reduce_bb (x : Std.U64) : Prop :=
  x.val < 17293822577692639232 → redc 2013265921 (utils.large_monty_reduce BB x) x.val = true

/-- Around `R·P` (the pre-reduction threshold) and just below `2·R·P`. -/
def gold_large_monty_reduce_edges_bb (d : Std.U32) (top : Bool) : Prop :=
  let x := if top then 17293822577692639232 - 1 - d.val else 8646911288846319616 - 2 ^ 31 + d.val
  redc 2013265921 (utils.large_monty_reduce BB (mkU .U64 x)) x = true

def gold_monty_reduce_u128_bb (x : Std.U128) : Prop :=
  x.val < 2 ^ 96 → redc 2013265921 (utils.monty_reduce_u128 BB x) x.val = true

def gold_monty_reduce_u128_limbs_bb (lo : Std.U64) (hi : Std.U32) : Prop :=
  let x := hi.val * 2 ^ 64 + lo.val
  redc 2013265921 (utils.monty_reduce_u128 BB (mkU .U128 x)) x = true

/-- Low limb around `2·R·P` (where the low limb is pre-reduced) and near `2^64`. -/
def gold_monty_reduce_u128_edges_bb (d : Std.U32) (hi : Std.U32) (top : Bool) : Prop :=
  let lo := if top then 2 ^ 64 - 1 - d.val else 17293822577692639232 - 2 ^ 31 + d.val
  let x := hi.val * 2 ^ 64 + lo
  redc 2013265921 (utils.monty_reduce_u128 BB (mkU .U128 x)) x = true

/-- Low limb exactly at the pre-reduction threshold `2·R·P` (± 1). -/
def gold_monty_reduce_u128_two_rp_bb (hi : Std.U32) (k : Std.U8) : Prop :=
  let x := hi.val * 2 ^ 64 + (17293822577692639232 + k.val % 3 - 1)
  redc 2013265921 (utils.monty_reduce_u128 BB (mkU .U128 x)) x = true

/-- Inputs just below the end of the domain `2^96`. -/
def gold_monty_reduce_u128_bound_bb (d : Std.U32) : Prop :=
  let x := 2 ^ 96 - 2 ^ 31 + d.val
  x < 2 ^ 96 → redc 2013265921 (utils.monty_reduce_u128 BB (mkU .U128 x)) x = true

def gold_add_bb (a b : Std.U32) : Prop :=
  a.val + b.val ≤ 2 * 2013265921 → isVal (utils.add BB a b) (addModel 2013265921 a.val b.val) = true

def gold_add_range_bb (a b : Std.U32) : Prop :=
  let a' := a.val % (2013265921 + 1)
  let b' := b.val % (2013265921 + 1)
  isVal (utils.add BB (mkU .U32 a') (mkU .U32 b')) (addModel 2013265921 a' b') = true

/-- Sums around `P` and `2P`. -/
def gold_add_edges_bb (a b : Std.U8) : Prop :=
  let a' := 2013265921 - a.val % 4
  let b' := [0, 1, 2, 3, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (b.val % 7) 0
  isVal (utils.add BB (mkU .U32 a') (mkU .U32 b')) (addModel 2013265921 a' b') = true ∧
  isVal (utils.add BB (mkU .U32 b') (mkU .U32 a')) (addModel 2013265921 a' b') = true

def gold_sub_bb (a b : Std.U32) : Prop :=
  (a.val ≤ b.val + 2013265921 ∧ b.val ≤ a.val + 2013265921) →
    isVal (utils.sub BB a b) (subModel 2013265921 a.val b.val) = true

def gold_sub_range_bb (a b : Std.U32) : Prop :=
  let a' := a.val % (2013265921 + 1)
  let b' := b.val % (2013265921 + 1)
  isVal (utils.sub BB (mkU .U32 a') (mkU .U32 b')) (subModel 2013265921 a' b') = true

/-- Differences around `0` and `±P`. -/
def gold_sub_edges_bb (a b : Std.U8) : Prop :=
  let a' := [0, 1, 2, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (a.val % 6) 0
  let b' := [0, 1, 2, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (b.val % 6) 0
  isVal (utils.sub BB (mkU .U32 a') (mkU .U32 b')) (subModel 2013265921 a' b') = true


/-! ### `KB` (`P = 2130706433`) -/

def gold_to_monty_kb (x : Std.U32) : Prop :=
  isVal (utils.to_monty KB x) (x.val * R % 2130706433) = true

def gold_to_monty_64_kb (x : Std.U64) : Prop :=
  isVal (utils.to_monty_64 KB x) (x.val * R % 2130706433) = true

def gold_from_monty_kb (x : Std.U32) : Prop :=
  redc 2130706433 (utils.from_monty KB x) x.val = true

def gold_monty_reduce_kb (x : Std.U64) : Prop :=
  x.val < 9151314447111815168 → redc 2130706433 (utils.monty_reduce KB x) x.val = true

/-- Just below the end of the domain `[0, R·P)`. -/
def gold_monty_reduce_top_kb (d : Std.U32) : Prop :=
  let x := 9151314447111815168 - 1 - d.val
  redc 2130706433 (utils.monty_reduce KB (mkU .U64 x)) x = true

/-- Products of two reduced values (Montgomery multiplication). -/
def gold_monty_reduce_mul_kb (a b : Std.U32) : Prop :=
  let x := (a.val % 2130706433) * (b.val % 2130706433)
  redc 2130706433 (utils.monty_reduce KB (mkU .U64 x)) x = true

def gold_large_monty_reduce_kb (x : Std.U64) : Prop :=
  x.val < 18302628894223630336 → redc 2130706433 (utils.large_monty_reduce KB x) x.val = true

/-- Around `R·P` (the pre-reduction threshold) and just below `2·R·P`. -/
def gold_large_monty_reduce_edges_kb (d : Std.U32) (top : Bool) : Prop :=
  let x := if top then 18302628894223630336 - 1 - d.val else 9151314447111815168 - 2 ^ 31 + d.val
  redc 2130706433 (utils.large_monty_reduce KB (mkU .U64 x)) x = true

def gold_monty_reduce_u128_kb (x : Std.U128) : Prop :=
  x.val < 2 ^ 96 → redc 2130706433 (utils.monty_reduce_u128 KB x) x.val = true

def gold_monty_reduce_u128_limbs_kb (lo : Std.U64) (hi : Std.U32) : Prop :=
  let x := hi.val * 2 ^ 64 + lo.val
  redc 2130706433 (utils.monty_reduce_u128 KB (mkU .U128 x)) x = true

/-- Low limb around `2·R·P` (where the low limb is pre-reduced) and near `2^64`. -/
def gold_monty_reduce_u128_edges_kb (d : Std.U32) (hi : Std.U32) (top : Bool) : Prop :=
  let lo := if top then 2 ^ 64 - 1 - d.val else 18302628894223630336 - 2 ^ 31 + d.val
  let x := hi.val * 2 ^ 64 + lo
  redc 2130706433 (utils.monty_reduce_u128 KB (mkU .U128 x)) x = true

/-- Low limb exactly at the pre-reduction threshold `2·R·P` (± 1). -/
def gold_monty_reduce_u128_two_rp_kb (hi : Std.U32) (k : Std.U8) : Prop :=
  let x := hi.val * 2 ^ 64 + (18302628894223630336 + k.val % 3 - 1)
  redc 2130706433 (utils.monty_reduce_u128 KB (mkU .U128 x)) x = true

/-- Inputs just below the end of the domain `2^96`. -/
def gold_monty_reduce_u128_bound_kb (d : Std.U32) : Prop :=
  let x := 2 ^ 96 - 2 ^ 31 + d.val
  x < 2 ^ 96 → redc 2130706433 (utils.monty_reduce_u128 KB (mkU .U128 x)) x = true

def gold_add_kb (a b : Std.U32) : Prop :=
  a.val + b.val ≤ 2 * 2130706433 → isVal (utils.add KB a b) (addModel 2130706433 a.val b.val) = true

def gold_add_range_kb (a b : Std.U32) : Prop :=
  let a' := a.val % (2130706433 + 1)
  let b' := b.val % (2130706433 + 1)
  isVal (utils.add KB (mkU .U32 a') (mkU .U32 b')) (addModel 2130706433 a' b') = true

/-- Sums around `P` and `2P`. -/
def gold_add_edges_kb (a b : Std.U8) : Prop :=
  let a' := 2130706433 - a.val % 4
  let b' := [0, 1, 2, 3, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (b.val % 7) 0
  isVal (utils.add KB (mkU .U32 a') (mkU .U32 b')) (addModel 2130706433 a' b') = true ∧
  isVal (utils.add KB (mkU .U32 b') (mkU .U32 a')) (addModel 2130706433 a' b') = true

def gold_sub_kb (a b : Std.U32) : Prop :=
  (a.val ≤ b.val + 2130706433 ∧ b.val ≤ a.val + 2130706433) →
    isVal (utils.sub KB a b) (subModel 2130706433 a.val b.val) = true

def gold_sub_range_kb (a b : Std.U32) : Prop :=
  let a' := a.val % (2130706433 + 1)
  let b' := b.val % (2130706433 + 1)
  isVal (utils.sub KB (mkU .U32 a') (mkU .U32 b')) (subModel 2130706433 a' b') = true

/-- Differences around `0` and `±P`. -/
def gold_sub_edges_kb (a b : Std.U8) : Prop :=
  let a' := [0, 1, 2, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (a.val % 6) 0
  let b' := [0, 1, 2, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (b.val % 6) 0
  isVal (utils.sub KB (mkU .U32 a') (mkU .U32 b')) (subModel 2130706433 a' b') = true


/-! Differential-testing probes. -/

def diff_to_monty_bb (x : Std.U32) := utils.to_monty BB x
def diff_to_monty_64_bb (x : Std.U64) := utils.to_monty_64 BB x
def diff_from_monty_bb (x : Std.U32) := utils.from_monty BB x
def diff_monty_reduce_bb (x : Std.U64) := utils.monty_reduce BB (mkU .U64 (x.val % 8646911288846319616))
def diff_monty_reduce_top_bb (d : Std.U32) := utils.monty_reduce BB (mkU .U64 (8646911288846319616 - 1 - d.val))
def diff_large_monty_reduce_bb (x : Std.U64) := utils.large_monty_reduce BB (mkU .U64 (x.val % 17293822577692639232))
def diff_large_monty_reduce_edges_bb (d : Std.U32) (top : Bool) := utils.large_monty_reduce BB (mkU .U64 (if top then 17293822577692639232 - 1 - d.val else 8646911288846319616 - 2 ^ 31 + d.val))
def diff_monty_reduce_u128_bb (x : Std.U128) := utils.monty_reduce_u128 BB x
def diff_monty_reduce_u128_limbs_bb (lo : Std.U64) (hi : Std.U32) := utils.monty_reduce_u128 BB (mkU .U128 (hi.val * 2 ^ 64 + lo.val))
def diff_monty_reduce_u128_edges_bb (d : Std.U32) (hi : Std.U32) (top : Bool) := utils.monty_reduce_u128 BB (mkU .U128 (hi.val * 2 ^ 64 + (if top then 2 ^ 64 - 1 - d.val else 17293822577692639232 - 2 ^ 31 + d.val)))
def diff_monty_reduce_u128_bound_bb (d : Std.U32) := utils.monty_reduce_u128 BB (mkU .U128 (2 ^ 96 - 2 ^ 31 + d.val))
def diff_add_bb (a b : Std.U32) := utils.add BB (mkU .U32 (a.val % (2013265921 + 1))) (mkU .U32 (b.val % (2013265921 + 1)))
def diff_add_edges_bb (a b : Std.U8) := utils.add BB (mkU .U32 (2013265921 - a.val % 4)) (mkU .U32 ([0, 1, 2, 3, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (b.val % 7) 0))
def diff_sub_bb (a b : Std.U32) := utils.sub BB (mkU .U32 (a.val % (2013265921 + 1))) (mkU .U32 (b.val % (2013265921 + 1)))
def diff_sub_edges_bb (a b : Std.U8) := utils.sub BB (mkU .U32 ([0, 1, 2, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (a.val % 6) 0)) (mkU .U32 ([0, 1, 2, 2013265921 - 2, 2013265921 - 1, 2013265921].getD (b.val % 6) 0))
def diff_to_monty_kb (x : Std.U32) := utils.to_monty KB x
def diff_to_monty_64_kb (x : Std.U64) := utils.to_monty_64 KB x
def diff_from_monty_kb (x : Std.U32) := utils.from_monty KB x
def diff_monty_reduce_kb (x : Std.U64) := utils.monty_reduce KB (mkU .U64 (x.val % 9151314447111815168))
def diff_monty_reduce_top_kb (d : Std.U32) := utils.monty_reduce KB (mkU .U64 (9151314447111815168 - 1 - d.val))
def diff_large_monty_reduce_kb (x : Std.U64) := utils.large_monty_reduce KB (mkU .U64 (x.val % 18302628894223630336))
def diff_large_monty_reduce_edges_kb (d : Std.U32) (top : Bool) := utils.large_monty_reduce KB (mkU .U64 (if top then 18302628894223630336 - 1 - d.val else 9151314447111815168 - 2 ^ 31 + d.val))
def diff_monty_reduce_u128_kb (x : Std.U128) := utils.monty_reduce_u128 KB x
def diff_monty_reduce_u128_limbs_kb (lo : Std.U64) (hi : Std.U32) := utils.monty_reduce_u128 KB (mkU .U128 (hi.val * 2 ^ 64 + lo.val))
def diff_monty_reduce_u128_edges_kb (d : Std.U32) (hi : Std.U32) (top : Bool) := utils.monty_reduce_u128 KB (mkU .U128 (hi.val * 2 ^ 64 + (if top then 2 ^ 64 - 1 - d.val else 18302628894223630336 - 2 ^ 31 + d.val)))
def diff_monty_reduce_u128_bound_kb (d : Std.U32) := utils.monty_reduce_u128 KB (mkU .U128 (2 ^ 96 - 2 ^ 31 + d.val))
def diff_add_kb (a b : Std.U32) := utils.add KB (mkU .U32 (a.val % (2130706433 + 1))) (mkU .U32 (b.val % (2130706433 + 1)))
def diff_add_edges_kb (a b : Std.U8) := utils.add KB (mkU .U32 (2130706433 - a.val % 4)) (mkU .U32 ([0, 1, 2, 3, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (b.val % 7) 0))
def diff_sub_kb (a b : Std.U32) := utils.sub KB (mkU .U32 (a.val % (2130706433 + 1))) (mkU .U32 (b.val % (2130706433 + 1)))
def diff_sub_edges_kb (a b : Std.U8) := utils.sub KB (mkU .U32 ([0, 1, 2, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (a.val % 6) 0)) (mkU .U32 ([0, 1, 2, 2130706433 - 2, 2130706433 - 1, 2130706433].getD (b.val % 6) 0))

def diff_monty_reduce_u128_two_rp_bb (hi : Std.U32) (k : Std.U8) := utils.monty_reduce_u128 BB (mkU .U128 (hi.val * 2 ^ 64 + (17293822577692639232 + k.val % 3 - 1)))
def diff_monty_reduce_u128_two_rp_kb (hi : Std.U32) (k : Std.U8) := utils.monty_reduce_u128 KB (mkU .U128 (hi.val * 2 ^ 64 + (18302628894223630336 + k.val % 3 - 1)))
end Benchmark.V2.Plonky3.Monty31Utils.Gold
