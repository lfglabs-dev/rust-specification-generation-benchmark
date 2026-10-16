import Benchmark.V2.Prelude
import RevBitsU32.Extraction

/-! Hidden gold specification for target `rev_bits/u32`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM rev_bits RSGB

/-! Reference models (outside `Benchmark.` so the driver does not unfold them). -/
namespace RSGBGold.RevBitsU32

/-- Little-endian value of the first 32 booleans (`l[i]` is bit `i`). -/
def bitsVal (l : List Bool) : Nat :=
  ((l.take 32).zipIdx).foldl (fun acc (b, i) => if b then acc + 2 ^ i else acc) 0

/-- The 32 bits of `x`, least significant first. -/
def bitList (x : Nat) : List Bool := (List.range 32).map (fun i => x.testBit i)

/-- A slice holding `l` (all lists used here are short). -/
def mkSlice (l : List Bool) : Slice Bool :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

end RSGBGold.RevBitsU32

open RSGBGold.RevBitsU32

namespace Benchmark.V2.RevBits.U32.Gold

/-! ### `range::{identity, increment, decrement}` (clamping to bit indices `0..=31`) -/

def gold_identity_exact (x : Std.U32) : Prop :=
  u32.range.identity x ⦃ r => r.val = min x.val 31 ⦄

def gold_identity_small (x : Std.U8) : Prop :=
  u32.range.identity (mkU .U32 x.val) ⦃ r => r.val = min x.val 31 ∧ r.val < 32 ⦄

def gold_increment_exact (x : Std.U32) : Prop :=
  u32.range.increment x ⦃ r => r.val = min (x.val + 1) 31 ⦄

def gold_increment_small (x : Std.U8) : Prop :=
  u32.range.increment (mkU .U32 x.val) ⦃ r => r.val = min (x.val + 1) 31 ∧ r.val < 32 ⦄

def gold_decrement_exact (x : Std.U32) : Prop :=
  u32.range.decrement x ⦃ r => r.val = min (x.val - 1) 31 ⦄

def gold_decrement_small (x : Std.U8) : Prop :=
  u32.range.decrement (mkU .U32 x.val) ⦃ r => r.val = min (x.val - 1) 31 ∧ r.val < 32 ⦄

/-- Inclusive/exclusive bound conversions agree: `increment x = identity (x+1)`
and `decrement (x+1) = identity x` (for `x + 1` representable). -/
def gold_bounds_consistent (x : Std.U32) : Prop :=
  x.val < 2^32 - 1 →
    (do
      let a ← u32.range.increment x
      let b ← u32.range.identity (mkU .U32 (x.val + 1))
      let c ← u32.range.decrement (mkU .U32 (x.val + 1))
      let d ← u32.range.identity x
      ok (a, b, c, d)) ⦃ (a, b, c, d) => a = b ∧ c = d ⦄

/-! ### `ref_impl::{to_array, to_u32}` -/

/-- `to_array` never panics; element `i` is bit `i` of the input. -/
def gold_to_array_bits (x : Std.U32) : Prop :=
  u32.ref_impl.to_array x ⦃ a => a.val = bitList x.val ⦄

/-- `to_u32` never panics, for any slice length; element `i` (for `i < 32`) is
bit `i` of the result, elements beyond 32 are shifted out. -/
def gold_to_u32_value (l : List Bool) : Prop :=
  u32.ref_impl.to_u32 (mkSlice l) ⦃ r => r.val = bitsVal l ⦄

/-- Same on short slices built from the bits of a number. -/
def gold_to_u32_prefix (x : Std.U32) (k : Std.U8) : Prop :=
  u32.ref_impl.to_u32 (mkSlice ((bitList x.val).take (k.val % 33)))
    ⦃ r => r.val = x.val % 2 ^ (k.val % 33) ⦄

/-- `to_u32 ∘ to_array = id`. -/
def gold_roundtrip (x : Std.U32) : Prop :=
  (do
    let a ← u32.ref_impl.to_array x
    let s ← lift (Array.to_slice a)
    u32.ref_impl.to_u32 s) ⦃ r => r = x ⦄

/-- `to_array ∘ to_u32` is the identity on 32-element slices. -/
def gold_roundtrip_inv (x : Std.U32) (flip : Std.U32) : Prop :=
  (do
    let r ← u32.ref_impl.to_u32 (mkSlice ((bitList x.val).zipWith (· != ·) (bitList flip.val)))
    u32.ref_impl.to_array r) ⦃ a => a.val = (bitList x.val).zipWith (· != ·) (bitList flip.val) ⦄

/-! Differential-testing probes. -/

def diff_identity (x : Std.U32) := u32.range.identity x
def diff_identity_small (x : Std.U8) := u32.range.identity (mkU .U32 x.val)
def diff_increment (x : Std.U32) := u32.range.increment x
def diff_increment_small (x : Std.U8) := u32.range.increment (mkU .U32 x.val)
def diff_decrement (x : Std.U32) := u32.range.decrement x
def diff_decrement_small (x : Std.U8) := u32.range.decrement (mkU .U32 x.val)
def diff_to_array (x : Std.U32) := do
  let a ← u32.ref_impl.to_array x; ok a.val
def diff_to_u32 (l : List Bool) := u32.ref_impl.to_u32 (mkSlice l)

end Benchmark.V2.RevBits.U32.Gold
