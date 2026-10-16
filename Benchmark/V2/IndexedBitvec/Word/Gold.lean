import Benchmark.V2.Prelude
import IndexedBitvecWord.Extraction

/-! Hidden gold specification for target `indexed_bitvec/word`.

Model: a `Word` is a `u64` whose bits are indexed MSB-first (`get(i)` is bit `63 - i`).
`get`/`set_copy`/`set` return `None` (no change) for `i ≥ 64`; `rank_ones(i)` counts the
ones at positions `< i` for `i < 64` and is `None` for `i ≥ 64` (note: also for
`i = 64 = len()`, as the crate's own test asserts); `select_ones(n)` is the position
of the `n`-th one (0-based) or `None` if `n ≥ count_ones`; `select_zeros` likewise for
zeros. `select_ones_u16(x, n)` is the MSB-first position of the `n`-th one of the
16-bit `x`, or `16` when `count_ones(x) ≤ n ≤ 16` (for `x ≠ 0` and `n ≥ 32` it panics on
a shift overflow; out of its intended domain, left unspecified).
`ceil_div(n, d) = ⌈n / d⌉` without overflow for `d ≥ 1`, panics for `d = 0`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM indexed_bitvec_core RSGB

namespace RSGBGold.IndexedBitvecWord

def optB : core.option.Option Bool → Option Bool
  | .None => none
  | .Some b => some b

def optN : core.option.Option Std.U32 → Option Nat
  | .None => none
  | .Some v => some v.val

def optW : core.option.Option Std.U64 → Option Nat
  | .None => none
  | .Some v => some v.val

def optU : core.option.Option Unit → Bool
  | .None => false
  | .Some _ => true

/-- Bit `i` (MSB-first) of a 64-bit word. -/
def bitAt (x i : Nat) : Bool := x.testBit (63 - i)

def getM (x i : Nat) : Option Bool := if i < 64 then some (bitAt x i) else none

def setBit (x i : Nat) (b : Bool) : Nat :=
  let p := 2^(63 - i)
  if b then (if bitAt x i then x else x + p) else (if bitAt x i then x - p else x)

def setCopyM (x i : Nat) (b : Bool) : Option Nat := if i < 64 then some (setBit x i b) else none

def setM (x i : Nat) (b : Bool) : Bool × Nat :=
  if i < 64 then (true, setBit x i b) else (false, x)

def popM (x : Nat) : Nat := ((List.range 64).filter (bitAt x)).length

def rankOnesM (x i : Nat) : Option Nat :=
  if i < 64 then some ((List.range i).filter (bitAt x)).length else none

def rankZerosM (x i : Nat) : Option Nat :=
  if i < 64 then some ((List.range i).filter (fun j => !bitAt x j)).length else none

def selOnesM (x n : Nat) : Option Nat :=
  let ps := (List.range 64).filter (bitAt x)
  if n < ps.length then some (ps.getD n 0) else none

def selZerosM (x n : Nat) : Option Nat :=
  let ps := (List.range 64).filter (fun j => !bitAt x j)
  if n < ps.length then some (ps.getD n 0) else none

def selU16M (x n : Nat) : Nat :=
  let ps := (List.range 16).filter (fun j => x.testBit (15 - j))
  if n < ps.length then ps.getD n 0 else 16

def ceilM (n d : Nat) : RustM Nat := if d = 0 then fail .panic else ok ((n + d - 1) / d)

def getObs (x : Std.U64) (i : Nat) : RustM (Option Bool) := do
  let r ← word.Word.get x (mkU .Usize i)
  ok (optB r)

def setCopyObs (x : Std.U64) (i : Nat) (b : Bool) : RustM (Option Nat) := do
  let r ← word.Word.set_copy x (mkU .Usize i) b
  ok (optW r)

def setObs (x : Std.U64) (i : Nat) (b : Bool) : RustM (Bool × Nat) := do
  let (r, w) ← word.Word.set x (mkU .Usize i) b
  ok (optU r, w.val)

def rankOnesObs (x : Std.U64) (i : Nat) : RustM (Option Nat) := do
  let r ← word.Word.rank_ones x (mkU .Usize i)
  ok (optN r)

def rankZerosObs (x : Std.U64) (i : Nat) : RustM (Option Nat) := do
  let r ← word.Word.rank_zeros x (mkU .Usize i)
  ok (optN r)

def selOnesObs (x : Std.U64) (n : Nat) : RustM (Option Nat) := do
  let r ← word.Word.select_ones x (mkU .U32 n)
  ok (optN r)

def selZerosObs (x : Std.U64) (n : Nat) : RustM (Option Nat) := do
  let r ← word.Word.select_zeros x (mkU .U32 n)
  ok (optN r)

def selU16Obs (x : Std.U16) (n : Nat) : RustM Nat := do
  let r ← word.select_ones_u16 x (mkU .U32 n)
  ok r.val

def wObs (r : RustM Std.U64) : RustM Nat := do
  let w ← r
  ok w.val

def u32Obs (r : RustM Std.U32) : RustM Nat := do
  let w ← r
  ok w.val

def usizeObs (r : RustM Std.Usize) : RustM Nat := do
  let w ← r
  ok w.val

/-- `set_copy x i b` followed by `get j` (`none` if `set_copy` returned `None`). -/
def getAfterSetObs (x : Std.U64) (i j : Nat) (b : Bool) : RustM (Option (Option Bool)) := do
  let o ← word.Word.set_copy x (mkU .Usize i) b
  match o with
  | .None => ok none
  | .Some w => do
    let g ← word.Word.get w (mkU .Usize j)
    ok (some (optB g))

/-- `(count_ones, select_ones n, rank_ones (select ..), get (select ..))`. -/
def selRankObs (x : Std.U64) (n : Nat) : RustM (Nat × Option Nat × Option Nat × Option Bool) := do
  let s ← selOnesObs x n
  let c ← u32Obs (word.Word.count_ones x)
  match s with
  | none => ok (c, none, none, none)
  | some p => do
    let r ← rankOnesObs x p
    let g ← getObs x p
    ok (c, some p, r, g)

def selZerosRankObs (x : Std.U64) (n : Nat) : RustM (Nat × Option Nat × Option Nat × Option Bool) := do
  let s ← selZerosObs x n
  let c ← u32Obs (word.Word.count_ones x)
  match s with
  | none => ok (c, none, none, none)
  | some p => do
    let r ← rankZerosObs x p
    let g ← getObs x p
    ok (c, some p, r, g)

/-- Inverse check for `select_ones`/`select_zeros` observations: `None` iff `n ≥ avail`,
otherwise the rank at the result is `n` and the bit there is `bitv`. -/
def selInvOk (avail n : Nat) (bitv : Bool) (t : Nat × Option Nat × Option Nat × Option Bool) : Bool :=
  match t with
  | (_, none, _, _) => decide (avail ≤ n)
  | (_, some _, r, g) => decide (n < avail) && r == some n && g == some bitv

end RSGBGold.IndexedBitvecWord

namespace Benchmark.V2.IndexedBitvec.Word.Gold
open RSGBGold.IndexedBitvecWord

/-! ## get / set_copy / set / len / conversions -/

def gold_get_exact (x : Std.U64) (i : Std.U8) : Prop :=
  getObs x (i.val % 72) = ok (getM x.val (i.val % 72))

def gold_get_out_of_range (x : Std.U64) (i : Std.Usize) : Prop :=
  64 ≤ i.val → getObs x i.val = ok none

def gold_set_copy_exact (x : Std.U64) (i : Std.U8) (b : Bool) : Prop :=
  setCopyObs x (i.val % 72) b = ok (setCopyM x.val (i.val % 72) b)

def gold_set_exact (x : Std.U64) (i : Std.U8) (b : Bool) : Prop :=
  setObs x (i.val % 72) b = ok (setM x.val (i.val % 72) b)

/-- Out of range `set` returns `None` and leaves the word unchanged (any `usize`). -/
def gold_set_out_of_range (x : Std.U64) (i : Std.Usize) (b : Bool) : Prop :=
  64 ≤ i.val → (setObs x i.val b = ok (false, x.val) ∧ setCopyObs x i.val b = ok none)

/-- `get` after `set_copy` sees the new bit at `i` and the old bits elsewhere. -/
def gold_get_after_set (x : Std.U64) (i j : Std.U8) (b : Bool) : Prop :=
  let i' := i.val % 64
  let j' := j.val % 64
  getAfterSetObs x i' j' b = ok (some (if i' = j' then some b else getM x.val j'))

def gold_len (x : Std.U64) : Prop :=
  usizeObs (word.Word.len x) = ok 64

def gold_from_into (x : Std.U64) : Prop :=
  (do
    let w ← word.Word.Insts.CoreConvertFromU64.from x
    let y ← U64.Insts.CoreConvertFromWord.from w
    ok y.val) = ok x.val

/-! ## complement / count_ones -/

def gold_complement_exact (x : Std.U64) : Prop :=
  wObs (word.Word.complement x) = ok (2^64 - 1 - x.val)

def gold_complement_flips (x : Std.U64) (i : Std.U8) : Prop :=
  (do
    let y ← word.Word.complement x
    getObs y (i.val % 64)) = ok (some (!bitAt x.val (i.val % 64)))

def gold_count_ones_exact (x : Std.U64) : Prop :=
  u32Obs (word.Word.count_ones x) = ok (popM x.val)

/-! ## rank -/

def gold_rank_ones_exact (x : Std.U64) (i : Std.U8) : Prop :=
  rankOnesObs x (i.val % 72) = ok (rankOnesM x.val (i.val % 72))

def gold_rank_zeros_exact (x : Std.U64) (i : Std.U8) : Prop :=
  rankZerosObs x (i.val % 72) = ok (rankZerosM x.val (i.val % 72))

def gold_rank_out_of_range (x : Std.U64) (i : Std.Usize) : Prop :=
  64 ≤ i.val → (rankOnesObs x i.val = ok none ∧ rankZerosObs x i.val = ok none)

/-- `rank_ones(i) + rank_zeros(i) = i` for `i < 64`. -/
def gold_rank_sum (x : Std.U64) (i : Std.U8) : Prop :=
  let i' := i.val % 64
  (do
    let a ← rankOnesObs x i'
    let b ← rankZerosObs x i'
    ok ((a.getD 0) + (b.getD 0), a.isSome && b.isSome)) = ok (i', true)

/-- `rank_ones(i+1) = rank_ones(i) + [get(i)]` for `i < 63`. -/
def gold_rank_step (x : Std.U64) (i : Std.U8) : Prop :=
  let i' := i.val % 63
  (do
    let a ← rankOnesObs x i'
    let b ← rankOnesObs x (i' + 1)
    let g ← getObs x i'
    ok (a, b, g)) ⦃ (a, b, g) =>
      b = a.map (fun r => r + (if g = some true then 1 else 0)) ⦄

/-! ## select -/

def gold_select_ones_exact (x : Std.U64) (n : Std.U8) : Prop :=
  selOnesObs x (n.val % 70) = ok (selOnesM x.val (n.val % 70))

def gold_select_ones_big (x : Std.U64) (n : Std.U32) : Prop :=
  selOnesObs x n.val = ok (selOnesM x.val n.val)

def gold_select_zeros_exact (x : Std.U64) (n : Std.U8) : Prop :=
  selZerosObs x (n.val % 70) = ok (selZerosM x.val (n.val % 70))

def gold_select_zeros_big (x : Std.U64) (n : Std.U32) : Prop :=
  selZerosObs x n.val = ok (selZerosM x.val n.val)

/-- `select_ones` inverts `rank_ones` (documented invariant), `None` iff `n ≥ count_ones`. -/
def gold_select_rank_inverse (x : Std.U64) (n : Std.U8) : Prop :=
  let n' := n.val % 66
  (do
    let t ← selRankObs x n'
    ok (selInvOk t.1 n' true t)) = ok true

/-- `select_zeros` inverts `rank_zeros` (documented invariant). -/
def gold_select_zeros_rank_inverse (x : Std.U64) (n : Std.U8) : Prop :=
  let n' := n.val % 66
  (do
    let t ← selZerosRankObs x n'
    ok (selInvOk (64 - t.1) n' false t)) = ok true

/-! ## select_ones_u16 -/

/-- Exact on its domain `n ≤ 16`. -/
def gold_select_u16_exact (x : Std.U16) (n : Std.U8) : Prop :=
  selU16Obs x (n.val % 17) = ok (selU16M x.val (n.val % 17))

/-- With no ones, the answer is always 16. -/
def gold_select_u16_zero (n : Std.U32) : Prop :=
  selU16Obs (mkU .U16 0) n.val = ok 16

/-- Agrees with `select_ones` on the word holding `x` in its top 16 bits. -/
def gold_select_u16_vs_word (x : Std.U16) (n : Std.U8) : Prop :=
  let n' := n.val % 16
  (do
    let a ← selU16Obs x n'
    let b ← selOnesObs (mkU .U64 (x.val * 2^48)) n'
    ok (a, b)) ⦃ (a, b) => (b = some a) ∨ (b = none ∧ a = 16) ⦄

/-! ## ceil_div -/

def gold_ceil_div_exact (n d : Std.Usize) : Prop :=
  usizeObs (ceil_div n d) = ceilM n.val d.val

def gold_ceil_div_small_d (n : Std.Usize) (d : Std.U8) : Prop :=
  usizeObs (ceil_div n (mkU .Usize d.val)) = ceilM n.val d.val

def gold_ceil_div_u64_exact (n d : Std.U64) : Prop :=
  wObs (ceil_div_u64 n d) = ceilM n.val d.val

def gold_ceil_div_u64_small_d (n : Std.U64) (d : Std.U8) : Prop :=
  wObs (ceil_div_u64 n (mkU .U64 d.val)) = ceilM n.val d.val

/-- Near the top of the range (where `n + d - 1` wraps). -/
def gold_ceil_div_u64_near_max (k : Std.U8) (d : Std.U16) : Prop :=
  let n := 2^64 - 1 - k.val
  wObs (ceil_div_u64 (mkU .U64 n) (mkU .U64 d.val)) = ceilM n d.val ∧
  usizeObs (ceil_div (mkU .Usize n) (mkU .Usize d.val)) = ceilM n d.val

/-- Characterisation: `(q-1)·d < n ≤ q·d` for `d ≥ 1`. -/
def gold_ceil_div_bounds (n d : Std.U64) : Prop :=
  1 ≤ d.val →
    (wObs (ceil_div_u64 n d)) ⦃ q => n.val ≤ q * d.val ∧ q * d.val < n.val + d.val ⦄

/-! Differential-testing probes. -/

def diff_get (x : Std.U64) (i : Std.U8) := getObs x (i.val % 72)
def diff_get_big (x : Std.U64) (i : Std.Usize) := getObs x i.val
def diff_set_copy (x : Std.U64) (i : Std.U8) (b : Bool) := setCopyObs x (i.val % 72) b
def diff_set (x : Std.U64) (i : Std.U8) (b : Bool) := setObs x (i.val % 72) b
def diff_set_big (x : Std.U64) (i : Std.Usize) (b : Bool) := setObs x i.val b
def diff_complement (x : Std.U64) := wObs (word.Word.complement x)
def diff_count (x : Std.U64) := u32Obs (word.Word.count_ones x)
def diff_len (x : Std.U64) := usizeObs (word.Word.len x)
def diff_rank_ones (x : Std.U64) (i : Std.U8) := rankOnesObs x (i.val % 72)
def diff_rank_zeros (x : Std.U64) (i : Std.U8) := rankZerosObs x (i.val % 72)
def diff_rank_big (x : Std.U64) (i : Std.Usize) := (rankOnesObs x i.val, rankZerosObs x i.val)
def diff_select_ones (x : Std.U64) (n : Std.U8) := selOnesObs x (n.val % 70)
def diff_select_zeros (x : Std.U64) (n : Std.U8) := selZerosObs x (n.val % 70)
def diff_select_big (x : Std.U64) (n : Std.U32) := (selOnesObs x n.val, selZerosObs x n.val)
def diff_select_u16 (x : Std.U16) (n : Std.U8) := selU16Obs x (n.val % 17)
def diff_ceil_div (n d : Std.Usize) := usizeObs (ceil_div n d)
def diff_ceil_div_small (n : Std.Usize) (d : Std.U8) := usizeObs (ceil_div n (mkU .Usize d.val))
def diff_ceil_div_u64 (n d : Std.U64) := wObs (ceil_div_u64 n d)
def diff_ceil_div_u64_small (n : Std.U64) (d : Std.U8) := wObs (ceil_div_u64 n (mkU .U64 d.val))
def diff_ceil_near_max (k : Std.U8) (d : Std.U16) :=
  (wObs (ceil_div_u64 (mkU .U64 (2^64 - 1 - k.val)) (mkU .U64 d.val)),
   usizeObs (ceil_div (mkU .Usize (2^64 - 1 - k.val)) (mkU .Usize d.val)))

end Benchmark.V2.IndexedBitvec.Word.Gold
