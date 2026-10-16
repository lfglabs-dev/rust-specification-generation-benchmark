import Benchmark.V2.Prelude
import SuccinctBroadword.Extraction

/-! Hidden gold specification for target `succinct/broadword`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM succinct RSGB

/-! Simple reference models (outside `Benchmark.` so the driver does not unfold them). -/
namespace RSGBGold.SuccinctBroadword

/-- Number of set bits among the low 64 bits. -/
def popcount (n : Nat) : Nat := ((List.range 64).filter (fun i => n.testBit i)).length

/-- Byte `i` (little-endian) of a word. -/
def byte (w : Nat) (i : Nat) : Nat := w / 256 ^ i % 256

/-- Word whose byte `i` is `0x80` iff `p i`, all other bits zero. -/
def flags (p : Nat → Bool) : Nat :=
  (List.range 8).foldl (fun acc i => if p i then acc + 0x80 * 256 ^ i else acc) 0

end RSGBGold.SuccinctBroadword

open RSGBGold.SuccinctBroadword

namespace Benchmark.V2.Succinct.Broadword.Gold

/-- `count_ones` never panics and returns the population count. -/
def gold_count_ones_exact (x : Std.U64) : Prop :=
  broadword.count_ones x ⦃ c => c.val = popcount x.val ⦄

/-- `count_ones` of a single set bit, and of all-ones below a bit, is exact. -/
def gold_count_ones_masks (k : Std.U8) : Prop :=
  k.val < 64 →
    broadword.count_ones (mkU .U64 (2^k.val)) ⦃ c => c.val = 1 ⦄ ∧
    broadword.count_ones (mkU .U64 (2^(k.val + 1) - 1)) ⦃ c => c.val = k.val + 1 ⦄

/-- Complement law: `count_ones(!x) = 64 - count_ones(x)`. -/
def gold_count_ones_complement (x : Std.U64) : Prop :=
  (do
    let a ← broadword.count_ones x
    let b ← broadword.count_ones (mkU .U64 (2^64 - 1 - x.val))
    ok (a, b)) ⦃ (a, b) => a.val + b.val = 64 ⦄

/-- Inclusion–exclusion: `|x ∪ y| + |x ∩ y| = |x| + |y|`. -/
def gold_count_ones_union (x y : Std.U64) : Prop :=
  (do
    let a ← broadword.count_ones (mkU .U64 (x.val ||| y.val))
    let b ← broadword.count_ones (mkU .U64 (x.val &&& y.val))
    let c ← broadword.count_ones x
    let d ← broadword.count_ones y
    ok (a, b, c, d)) ⦃ (a, b, c, d) => a.val + b.val = c.val + d.val ⦄

/-- `u_nz8` never panics; byte `i` of the result is `0x80` iff byte `i` of `x`
is non-zero, and every other bit is clear. -/
def gold_u_nz8_exact (x : Std.U64) : Prop :=
  broadword.u_nz8 x ⦃ r => r.val = flags (fun i => byte x.val i != 0) ⦄

/-- `u_nz8` on words built from bytes in `{0, 1, 0x7f, 0x80, 0xff}`. -/
def gold_u_nz8_bytes (a b c d : Std.U8) : Prop :=
  broadword.u_nz8 (mkU .U64 (a.val + 256 * b.val + 65536 * (c.val % 2) + 2^56 * d.val))
    ⦃ r => r.val = flags (fun i => byte (a.val + 256 * b.val + 65536 * (c.val % 2) + 2^56 * d.val) i != 0) ⦄

/-- `u_le8` never panics; byte `i` of the result is `0x80` iff byte `i` of `x`
≤ byte `i` of `y` (unsigned), every other bit is clear. -/
def gold_u_le8_exact (x y : Std.U64) : Prop :=
  broadword.u_le8 x y ⦃ r => r.val = flags (fun i => decide (byte x.val i ≤ byte y.val i)) ⦄

/-- `u_le8` on words whose bytes are close to each other (equal / ±1 / sign bit). -/
def gold_u_le8_close (x : Std.U64) (d : Std.U8) (s : Std.U8) : Prop :=
  broadword.u_le8 x (mkU .U64 (x.val ^^^ (d.val * 0x0101010101010101 * (s.val % 2))))
    ⦃ r => r.val = flags (fun i => decide (byte x.val i ≤ byte (x.val ^^^ (d.val * 0x0101010101010101 * (s.val % 2))) i)) ⦄

/-- Reflexivity and the `0 ≤ y` / `x ≤ 0xff..` edge cases. -/
def gold_u_le8_edges (x : Std.U64) : Prop :=
  broadword.u_le8 x x ⦃ r => r.val = 0x8080808080808080 ⦄ ∧
  broadword.u_le8 0#u64 x ⦃ r => r.val = 0x8080808080808080 ⦄ ∧
  broadword.u_le8 x 18446744073709551615#u64 ⦃ r => r.val = 0x8080808080808080 ⦄

/-- `u_nz8 x = H8 xor u_le8 x 0` (non-zero iff not ≤ 0). -/
def gold_nz8_vs_le8 (x : Std.U64) : Prop :=
  (do
    let a ← broadword.u_nz8 x
    let b ← broadword.u_le8 x 0#u64
    ok (a, b)) ⦃ (a, b) => a.val = b.val ^^^ 0x8080808080808080 ⦄

/-- Totality / antisymmetry: for every byte, `x ≤ y` or `y ≤ x`, both iff equal. -/
def gold_u_le8_total (x y : Std.U64) : Prop :=
  (do
    let a ← broadword.u_le8 x y
    let b ← broadword.u_le8 y x
    ok (a, b)) ⦃ (a, b) => a.val ||| b.val = 0x8080808080808080 ∧
      a.val &&& b.val = flags (fun i => byte x.val i == byte y.val i) ⦄

/-! Differential-testing probes. -/

def diff_count_ones (x : Std.U64) := broadword.count_ones x
def diff_u_nz8 (x : Std.U64) := broadword.u_nz8 x
def diff_u_nz8_bytes (a b c d : Std.U8) :=
  broadword.u_nz8 (mkU .U64 (a.val + 256 * b.val + 65536 * (c.val % 2) + 2^56 * d.val))
def diff_u_le8 (x y : Std.U64) := broadword.u_le8 x y
def diff_u_le8_close (x : Std.U64) (d : Std.U8) := broadword.u_le8 x (mkU .U64 (x.val ^^^ (d.val * 0x0101010101010101)))

end Benchmark.V2.Succinct.Broadword.Gold
