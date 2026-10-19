import Benchmark.V2.Prelude
import MemchrTwoway.Extraction

/-! Hidden gold specification for target `memchr/twoway`.

API (`memchr::arch::all::twoway`):
* `Suffix::forward(needle, kind)` / `Suffix::reverse(needle, kind)`: the
  Crochemore–Perrin critical-factorisation helpers. For `Maximal` the forward
  suffix `needle[pos..]` is the lexicographically greatest non-empty suffix
  (Rust `Ord for [u8]`: a proper prefix is smaller); for `Minimal` it is the
  greatest suffix for the *inverted* byte order (the doc: "given the choice
  between `a` and `aa` this will choose the latter"). `period` is the (least)
  period of that suffix. `reverse` is the mirror image: `needle[..pos]` read
  backwards is the corresponding suffix of the reversed needle.
* `FinderRev::new(needle)` + `FinderRev::rfind(haystack, needle)`: the last
  occurrence of `needle` in `haystack` (`Some(haystack.len())` for an empty
  needle). The searcher's internal state is not part of the contract.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM memchr RSGB

namespace RSGBGold.Memchr.Twoway

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

def vals (l : List Std.U8) : List Nat := l.map (·.val)

/-- Rust's `Ord for [u8]` (`≤`): lexicographic, a proper prefix is smaller. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys => if a < b then true else if b < a then false else lexLe xs ys

/-- Start of the lexicographically greatest non-empty suffix (brute force). -/
def maxSufPos (s : List Nat) : Nat :=
  (List.range s.length).foldl (fun best i => if lexLe (s.drop best) (s.drop i) then i else best) 0

/-- Inverted byte order. -/
def inv (s : List Nat) : List Nat := s.map (255 - ·)

def hasPeriod (s : List Nat) (p : Nat) : Bool :=
  (List.range (s.length - p)).all (fun i => s[i]! == s[i + p]!)

/-- Least period `p ≥ 1` of a non-empty string. -/
def minPeriod (s : List Nat) : Nat :=
  ((List.range s.length).map (· + 1)).find? (hasPeriod s) |>.getD s.length

def kindOf (b : Bool) : arch.all.twoway.SuffixKind :=
  if b then .Maximal else .Minimal

/-- The order used by a kind: identity for `Maximal`, inverted for `Minimal`. -/
def keyed (b : Bool) (s : List Nat) : List Nat := if b then s else inv s

/-- Expected forward position. -/
def fwdPos (b : Bool) (n : List Std.U8) : Nat := maxSufPos (keyed b (vals n))

/-- Expected reverse (exclusive end) position. -/
def revPos (b : Bool) (n : List Std.U8) : Nat :=
  n.length - maxSufPos (keyed b (vals n).reverse)

def fwd (n : List Std.U8) (b : Bool) := arch.all.twoway.Suffix.forward (toSlice n) (kindOf b)
def rev (n : List Std.U8) (b : Bool) := arch.all.twoway.Suffix.reverse (toSlice n) (kindOf b)

/-- Bytes squeezed into a small alphabet (many repetitions and ties). -/
def sq (k : Nat) (l : List Std.U8) : List Std.U8 := l.map (fun v => mkU .U8 (v.val % k))

/-- Naive last occurrence. -/
def isAt (h n : List Nat) (i : Nat) : Bool := (h.drop i).take n.length == n

def naiveRfind (h n : List Std.U8) : Option Nat :=
  if n.length ≤ h.length then
    ((List.range (h.length - n.length + 1)).reverse).find? (isAt (vals h) (vals n))
  else none

def rfindOf (h n : List Std.U8) : RustM (Option Nat) := do
  let f ← arch.all.twoway.FinderRev.new (toSlice n)
  let r ← arch.all.twoway.FinderRev.rfind f (toSlice h) (toSlice n)
  ok (match r with | some v => some v.val | none => none)

end RSGBGold.Memchr.Twoway

namespace Benchmark.V2.Memchr.Twoway.Gold
open RSGBGold.Memchr.Twoway

/-! ## `Suffix::forward` -/

def fwdPosSpec (n : List Std.U8) (b : Bool) : Prop :=
  0 < n.length → fwd n b ⦃ s => s.pos.val = fwdPos b n ⦄

def fwdPeriodSpec (n : List Std.U8) (b : Bool) : Prop :=
  0 < n.length → fwd n b ⦃ s => s.period.val = minPeriod ((vals n).drop (fwdPos b n)) ⦄

/-- Maximal: `needle[pos..]` is the greatest non-empty suffix. -/
def gold_fwd_max_pos (n : List Std.U8) : Prop := fwdPosSpec n true
def gold_fwd_max_pos_bin (n : List Std.U8) : Prop := fwdPosSpec (sq 2 n) true
def gold_fwd_max_pos_tri (n : List Std.U8) : Prop := fwdPosSpec (sq 3 n) true
/-- Minimal: the greatest suffix for the inverted byte order (longest on prefix ties). -/
def gold_fwd_min_pos (n : List Std.U8) : Prop := fwdPosSpec n false
def gold_fwd_min_pos_bin (n : List Std.U8) : Prop := fwdPosSpec (sq 2 n) false
def gold_fwd_min_pos_tri (n : List Std.U8) : Prop := fwdPosSpec (sq 3 n) false
/-- `period` is the least period of the chosen suffix. -/
def gold_fwd_max_period (n : List Std.U8) : Prop := fwdPeriodSpec n true
def gold_fwd_max_period_bin (n : List Std.U8) : Prop := fwdPeriodSpec (sq 2 n) true
def gold_fwd_max_period_tri (n : List Std.U8) : Prop := fwdPeriodSpec (sq 3 n) true
def gold_fwd_min_period (n : List Std.U8) : Prop := fwdPeriodSpec n false
def gold_fwd_min_period_bin (n : List Std.U8) : Prop := fwdPeriodSpec (sq 2 n) false
def gold_fwd_min_period_tri (n : List Std.U8) : Prop := fwdPeriodSpec (sq 3 n) false

/-- Empty needle: no panic, the (empty) suffix starts at 0. -/
def gold_fwd_empty (b : Bool) : Prop := fwd [] b ⦃ s => s.pos.val = 0 ⦄

/-! ## `Suffix::reverse` -/

def revPosSpec (n : List Std.U8) (b : Bool) : Prop :=
  0 < n.length → rev n b ⦃ s => s.pos.val = revPos b n ⦄

def revPeriodSpec (n : List Std.U8) (b : Bool) : Prop :=
  0 < n.length → rev n b ⦃ s => s.period.val = minPeriod ((vals n).take (revPos b n)) ⦄

def gold_rev_max_pos (n : List Std.U8) : Prop := revPosSpec n true
def gold_rev_max_pos_bin (n : List Std.U8) : Prop := revPosSpec (sq 2 n) true
def gold_rev_max_pos_tri (n : List Std.U8) : Prop := revPosSpec (sq 3 n) true
def gold_rev_min_pos (n : List Std.U8) : Prop := revPosSpec n false
def gold_rev_min_pos_bin (n : List Std.U8) : Prop := revPosSpec (sq 2 n) false
def gold_rev_min_pos_tri (n : List Std.U8) : Prop := revPosSpec (sq 3 n) false
def gold_rev_max_period (n : List Std.U8) : Prop := revPeriodSpec n true
def gold_rev_max_period_bin (n : List Std.U8) : Prop := revPeriodSpec (sq 2 n) true
def gold_rev_max_period_tri (n : List Std.U8) : Prop := revPeriodSpec (sq 3 n) true
def gold_rev_min_period (n : List Std.U8) : Prop := revPeriodSpec n false
def gold_rev_min_period_bin (n : List Std.U8) : Prop := revPeriodSpec (sq 2 n) false
def gold_rev_min_period_tri (n : List Std.U8) : Prop := revPeriodSpec (sq 3 n) false

/-- Empty needle: no panic, the (empty) reverse suffix ends at 0. -/
def gold_rev_empty (b : Bool) : Prop := rev [] b ⦃ s => s.pos.val = 0 ⦄

/-- Mirror law: `reverse` on a needle is `forward` on the reversed needle. -/
def gold_rev_mirror (n : List Std.U8) (b : Bool) : Prop :=
  0 < n.length →
    (do let r ← rev (sq 3 n) b; let f ← fwd (sq 3 n).reverse b; ok (r, f))
      ⦃ (r, f) => r.pos.val + f.pos.val = n.length ∧ r.period = f.period ⦄

/-! ## `FinderRev::new` + `FinderRev::rfind`: the last occurrence -/

def rfindSpec (h n : List Std.U8) : Prop :=
  rfindOf h n ⦃ r => r = naiveRfind h n ⦄

def gold_rfind (h n : List Std.U8) : Prop := rfindSpec h n
/-- Binary alphabet, short needle: many (overlapping) occurrences. -/
def gold_rfind_bin (h n : List Std.U8) (k : Std.U8) : Prop :=
  rfindSpec (sq 2 h) ((sq 2 n).take (k.val % 9))
def gold_rfind_tri (h n : List Std.U8) (k : Std.U8) : Prop :=
  rfindSpec (sq 3 h) ((sq 3 n).take (k.val % 12))
/-- A planted occurrence (periodic needles: small-period search path). -/
def gold_rfind_planted (a n c : List Std.U8) : Prop :=
  rfindSpec (sq 2 a ++ sq 2 n ++ sq 2 c) (sq 2 n)
def gold_rfind_planted_rep (a n c : List Std.U8) (k : Std.U8) : Prop :=
  let p := (sq 3 n).take (k.val % 4 + 1)
  let m := (List.replicate (k.val / 64 + 1) p).flatten ++ p.take (k.val % 3)
  rfindSpec (sq 3 a ++ m ++ sq 3 c ++ m.take (k.val % 5)) m
/-- An empty needle matches at `haystack.len()`. -/
def gold_rfind_empty (h : List Std.U8) : Prop :=
  rfindOf h [] ⦃ r => r = some h.length ⦄
/-- A needle longer than the haystack never matches. -/
def gold_rfind_too_long (h n : List Std.U8) : Prop :=
  h.length < n.length → rfindOf h n ⦃ r => r = none ⦄

/-! Differential-testing probes. -/

def diff_fwd (n : List Std.U8) (b : Bool) := fwd n b
def diff_fwd_bin (n : List Std.U8) (b : Bool) := fwd (sq 2 n) b
def diff_rev (n : List Std.U8) (b : Bool) := rev n b
def diff_rev_bin (n : List Std.U8) (b : Bool) := rev (sq 2 n) b
def diff_new (n : List Std.U8) := arch.all.twoway.FinderRev.new (toSlice (sq 3 n))
def diff_rfind (h n : List Std.U8) := rfindOf h n
def diff_rfind_bin (h n : List Std.U8) (k : Std.U8) := rfindOf (sq 2 h) ((sq 2 n).take (k.val % 9))
def diff_rfind_planted (a n c : List Std.U8) := rfindOf (sq 2 a ++ sq 2 n ++ sq 2 c) (sq 2 n)

end Benchmark.V2.Memchr.Twoway.Gold
