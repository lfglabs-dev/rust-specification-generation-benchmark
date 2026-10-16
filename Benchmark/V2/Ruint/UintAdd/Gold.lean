import Benchmark.V2.Prelude
import Benchmark.V2.Ruint.UintAdd.Instances
import RuintUintAdd.Extraction

/-! Hidden gold specification for target `ruint/uint_add`.

`Uint<BITS, LIMBS>` is a little-endian array of `LIMBS = ceil(BITS / 64)` limbs
whose value is below `2^BITS` (the top limb is masked). The API is specified
against the mathematical value `val` of the limbs at several concrete widths
(BITS ∈ {0, 1, 2, 63, 64, 65, 127, 128, 129, 191, 192}). Inputs are arbitrary
limb arrays reduced modulo `2^BITS` (independent model of a valid `Uint`). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM ruint RSGB

/-! Model and per-width contracts. They live outside the `Benchmark` namespace and
are `Bool`-valued so that the test driver evaluates them instead of unfolding
them symbolically. -/
namespace RuintUintAddGoldModel

/-- Little-endian value of a list of 64-bit limbs. -/
def limbsVal (l : List Std.U64) : Nat :=
  l.foldr (fun x acc => x.val + 2^64 * acc) 0

/-- Mathematical value of a `Uint`. -/
def val {B L : Std.Usize} (a : Uint B L) : Nat := limbsVal a.limbs.val

/-- The canonical `Uint<B, L>` holding `n mod 2^B` (limb `i` = bits `64 i ..`). -/
def ofNat (B L : Std.Usize) (n : Nat) : Uint B L :=
  ⟨⟨List.ofFn (n := L.val) (fun i => mkU .U64 ((n % 2^B.val) / 2^(64 * i.val))), by simp⟩⟩

/-- An arbitrary valid `Uint<B, L>` built from a raw limb array. -/
def inp (B : Std.Usize) {L : Std.Usize} (la : Std.Array Std.U64 L) : Uint B L :=
  ofNat B L (limbsVal la.val)

/-! ## Generic contracts (one width) -/

/-- Addition family on valid inputs `a`, `b`. -/
def addSpec {B L : Std.Usize} (a b : Uint B L) : Bool := decide <|
  let s := val a + val b
  let ovf := decide (2^B.val ≤ s)
  add.Uint.overflowing_add a b = ok (ofNat B L s, ovf) ∧
  add.Uint.wrapping_add a b = ok (ofNat B L s) ∧
  Uint.Insts.CoreOpsArithAddUintUint.add a b = ok (ofNat B L s) ∧
  add.Uint.checked_add a b = ok (if ovf then none else some (ofNat B L s)) ∧
  add.Uint.strict_add a b = (if ovf then fail .panic else ok (ofNat B L s)) ∧
  add.Uint.saturating_add a b = ok (if ovf then ofNat B L (2^B.val - 1) else ofNat B L s)

/-- Subtraction family on valid inputs `a`, `b`. -/
def subSpec {B L : Std.Usize} (a b : Uint B L) : Bool := decide <|
  let d := val a + 2^B.val - val b
  let ovf := decide (val a < val b)
  add.Uint.overflowing_sub a b = ok (ofNat B L d, ovf) ∧
  add.Uint.wrapping_sub a b = ok (ofNat B L d) ∧
  Uint.Insts.CoreOpsArithSubUintUint.sub a b = ok (ofNat B L d) ∧
  add.Uint.checked_sub a b = ok (if ovf then none else some (ofNat B L d)) ∧
  add.Uint.strict_sub a b = (if ovf then fail .panic else ok (ofNat B L d)) ∧
  add.Uint.saturating_sub a b = ok (if ovf then ofNat B L 0 else ofNat B L d)

/-- Negation family on a valid input `a`. -/
def negSpec {B L : Std.Usize} (a : Uint B L) : Bool := decide <|
  let n := 2^B.val - val a
  let ovf := decide (val a ≠ 0)
  add.Uint.overflowing_neg a = ok (ofNat B L n, ovf) ∧
  add.Uint.wrapping_neg a = ok (ofNat B L n) ∧
  Uint.Insts.CoreOpsArithNegUint.neg a = ok (ofNat B L n) ∧
  add.Uint.checked_neg a = ok (if ovf then none else some (ofNat B L n)) ∧
  add.Uint.strict_neg a = (if ovf then fail .panic else ok (ofNat B L n))

/-- Algebraic laws of the operators (the crate's own property tests). -/
def lawSpec {B L : Std.Usize} (a b c : Uint B L) : Bool := decide <|
  (do
    let x ← Uint.Insts.CoreOpsArithAddUintUint.add a b
    let y ← Uint.Insts.CoreOpsArithAddUintUint.add b a
    let bc ← Uint.Insts.CoreOpsArithAddUintUint.add b c
    let l ← Uint.Insts.CoreOpsArithAddUintUint.add a bc
    let ab ← Uint.Insts.CoreOpsArithAddUintUint.add a b
    let r ← Uint.Insts.CoreOpsArithAddUintUint.add ab c
    let na ← Uint.Insts.CoreOpsArithNegUint.neg a
    let z ← Uint.Insts.CoreOpsArithAddUintUint.add a na
    let nna ← Uint.Insts.CoreOpsArithNegUint.neg na
    let d ← Uint.Insts.CoreOpsArithSubUintUint.sub a b
    let back ← Uint.Insts.CoreOpsArithAddUintUint.add d b
    ok (x, y, l, r, z, nna, back))
  ⦃ r => r.1 = r.2.1 ∧ r.2.2.1 = r.2.2.2.1 ∧ r.2.2.2.2.1 = ofNat B L 0 ∧
      r.2.2.2.2.2.1 = a ∧ r.2.2.2.2.2.2 = a ⦄

/-- `from_limbs` accepts exactly the in-range limb arrays (and panics otherwise). -/
def fromLimbsSpec (B : Std.Usize) {L : Std.Usize} (la : Std.Array Std.U64 L) : Bool := decide <|
  Uint.from_limbs B la = (if limbsVal la.val < 2^B.val then ok ⟨la⟩ else fail .panic)

/-- Everything at one width, for raw inputs `la lb lc`. -/
def allSpec (B : Std.Usize) {L : Std.Usize} (la lb lc : Std.Array Std.U64 L) : Bool := decide <|
  let a := inp B la
  let b := inp B lb
  let c := inp B lc
  addSpec a b ∧ subSpec a b ∧ negSpec a ∧ lawSpec a b c ∧ fromLimbsSpec B la ∧
  fromLimbsSpec B (a.limbs)

/-- Inputs right at the carry / borrow boundary: `b = 2^B - a + k - 2`, `k < 4`. -/
def boundarySpec (B : Std.Usize) {L : Std.Usize} (la : Std.Array Std.U64 L) (k : Nat) : Bool := decide <|
  let a := inp B la
  let b := ofNat B L (2^B.val - val a + k % 4 - 2)
  let c := ofNat B L (val a + k % 4 - 2)
  addSpec a b ∧ addSpec b a ∧ subSpec a c ∧ subSpec c a ∧ negSpec b

end RuintUintAddGoldModel

open RuintUintAddGoldModel

namespace Benchmark.V2.Ruint.UintAdd.Gold

/-! ## Gold properties -/

/-- `BITS = 0`: the only value is zero; all operations return it without overflow. -/
def gold_zero_width (la lb : Std.Array Std.U64 0#usize) : Prop :=
  allSpec 0#usize la lb la ∧
  add.Uint.overflowing_add (⟨la⟩ : Uint 0#usize 0#usize) ⟨lb⟩ = ok (⟨la⟩, false) ∧
  Uint.ZERO 0#usize 0#usize = ok ⟨la⟩ ∧ Uint.MAX 0#usize 0#usize = ok ⟨la⟩

/-- One-limb widths. -/
def gold_one_limb (la lb lc : Std.Array Std.U64 1#usize) : Prop :=
  allSpec 1#usize la lb lc ∧ allSpec 2#usize la lb lc ∧
  allSpec 63#usize la lb lc ∧ allSpec 64#usize la lb lc

/-- Two-limb widths. -/
def gold_two_limbs (la lb lc : Std.Array Std.U64 2#usize) : Prop :=
  allSpec 65#usize la lb lc ∧ allSpec 127#usize la lb lc ∧ allSpec 128#usize la lb lc

/-- Three-limb widths. -/
def gold_three_limbs (la lb lc : Std.Array Std.U64 3#usize) : Prop :=
  allSpec 129#usize la lb lc ∧ allSpec 191#usize la lb lc ∧ allSpec 192#usize la lb lc

/-- Carry / borrow boundary, one limb. -/
def gold_boundary_one (la : Std.Array Std.U64 1#usize) (k : Std.U8) : Prop :=
  boundarySpec 1#usize la k.val ∧ boundarySpec 2#usize la k.val ∧
  boundarySpec 63#usize la k.val ∧ boundarySpec 64#usize la k.val

/-- Carry / borrow boundary, two limbs. -/
def gold_boundary_two (la : Std.Array Std.U64 2#usize) (k : Std.U8) : Prop :=
  boundarySpec 65#usize la k.val ∧ boundarySpec 127#usize la k.val ∧ boundarySpec 128#usize la k.val

/-- Carry / borrow boundary, three limbs. -/
def gold_boundary_three (la : Std.Array Std.U64 3#usize) (k : Std.U8) : Prop :=
  boundarySpec 129#usize la k.val ∧ boundarySpec 191#usize la k.val ∧ boundarySpec 192#usize la k.val

/-- Carries that ripple through a run of all-ones limbs (`a = 2^(64 j) - 1`, `b = 1 + 2^(64 j) t`). -/
def gold_ripple (j : Std.U8) (t : Std.U64) : Prop :=
  let j := j.val % 4
  let a3 := ofNat 192#usize 3#usize (2^(64 * j) - 1)
  let b3 := ofNat 192#usize 3#usize (1 + 2^(64 * j) * t.val)
  let a2 := ofNat 128#usize 2#usize (2^(64 * j) - 1)
  let b2 := ofNat 128#usize 2#usize (1 + 2^(64 * j) * t.val)
  let a2' := ofNat 65#usize 2#usize (2^(64 * j) - 1)
  let b2' := ofNat 65#usize 2#usize (1 + 2^(64 * j) * t.val)
  addSpec a3 b3 ∧ subSpec b3 a3 ∧ subSpec (ofNat 192#usize 3#usize (2^(64 * j))) b3 ∧
  addSpec a2 b2 ∧ subSpec b2 a2 ∧ addSpec a2' b2' ∧ subSpec b2' a2' ∧ negSpec b3 ∧ negSpec a2'

/-- `ZERO` and `MAX` at every tested width. -/
def gold_constants (_x : Std.U8) : Prop :=
  Uint.ZERO 1#usize 1#usize = ok (ofNat 1#usize 1#usize 0) ∧
  Uint.MAX 1#usize 1#usize = ok (ofNat 1#usize 1#usize 1) ∧
  Uint.ZERO 63#usize 1#usize = ok (ofNat 63#usize 1#usize 0) ∧
  Uint.MAX 63#usize 1#usize = ok (ofNat 63#usize 1#usize (2^63 - 1)) ∧
  Uint.ZERO 64#usize 1#usize = ok (ofNat 64#usize 1#usize 0) ∧
  Uint.MAX 64#usize 1#usize = ok (ofNat 64#usize 1#usize (2^64 - 1)) ∧
  Uint.ZERO 65#usize 2#usize = ok (ofNat 65#usize 2#usize 0) ∧
  Uint.MAX 65#usize 2#usize = ok (ofNat 65#usize 2#usize (2^65 - 1)) ∧
  Uint.ZERO 128#usize 2#usize = ok (ofNat 128#usize 2#usize 0) ∧
  Uint.MAX 128#usize 2#usize = ok (ofNat 128#usize 2#usize (2^128 - 1)) ∧
  Uint.ZERO 129#usize 3#usize = ok (ofNat 129#usize 3#usize 0) ∧
  Uint.MAX 129#usize 3#usize = ok (ofNat 129#usize 3#usize (2^129 - 1)) ∧
  Uint.MAX 192#usize 3#usize = ok (ofNat 192#usize 3#usize (2^192 - 1))

/-- `mask bits` is the top-limb mask: 0 for 0 bits, `u64::MAX` for multiples
of 64, otherwise `2^(bits mod 64) - 1`; total. -/
def gold_mask (bits : Std.Usize) : Prop :=
  mask bits = ok (mkU .U64 (if bits.val = 0 then 0
    else if bits.val % 64 = 0 then 2^64 - 1 else 2^(bits.val % 64) - 1))

/-- `nlimbs bits = ceil(bits / 64)`; total. -/
def gold_nlimbs (bits : Std.Usize) : Prop :=
  nlimbs bits = ok (mkU .Usize ((bits.val + 63) / 64))

/-- `mask` / `nlimbs` on small widths (dense coverage of `bits mod 64`). -/
def gold_mask_small (bits : Std.U16) : Prop :=
  let b := bits.val % 600
  mask (mkU .Usize b) = ok (mkU .U64 (if b = 0 then 0 else if b % 64 = 0 then 2^64 - 1 else 2^(b % 64) - 1)) ∧
  nlimbs (mkU .Usize b) = ok (mkU .Usize ((b + 63) / 64))

/-! ## Differential-testing probes -/

def diff_oadd1 (la lb : Std.Array Std.U64 1#usize) := add.Uint.overflowing_add (inp 63#usize la) (inp 63#usize lb)
def diff_oadd1' (la lb : Std.Array Std.U64 1#usize) := add.Uint.overflowing_add (inp 64#usize la) (inp 64#usize lb)
def diff_oadd2 (la lb : Std.Array Std.U64 2#usize) := add.Uint.overflowing_add (inp 65#usize la) (inp 65#usize lb)
def diff_oadd3 (la lb : Std.Array Std.U64 3#usize) := add.Uint.overflowing_add (inp 192#usize la) (inp 192#usize lb)
def diff_osub1 (la lb : Std.Array Std.U64 1#usize) := add.Uint.overflowing_sub (inp 63#usize la) (inp 63#usize lb)
def diff_osub2 (la lb : Std.Array Std.U64 2#usize) := add.Uint.overflowing_sub (inp 65#usize la) (inp 65#usize lb)
def diff_osub3 (la lb : Std.Array Std.U64 3#usize) := add.Uint.overflowing_sub (inp 192#usize la) (inp 192#usize lb)
def diff_oneg2 (la : Std.Array Std.U64 2#usize) := add.Uint.overflowing_neg (inp 127#usize la)
def diff_checked (la lb : Std.Array Std.U64 2#usize) :=
  (add.Uint.checked_add (inp 65#usize la) (inp 65#usize lb), add.Uint.checked_sub (inp 65#usize la) (inp 65#usize lb),
   add.Uint.checked_neg (inp 65#usize la))
def diff_strict (la lb : Std.Array Std.U64 2#usize) :=
  (add.Uint.strict_add (inp 128#usize la) (inp 128#usize lb), add.Uint.strict_sub (inp 128#usize la) (inp 128#usize lb),
   add.Uint.strict_neg (inp 128#usize la))
def diff_saturating (la lb : Std.Array Std.U64 2#usize) :=
  (add.Uint.saturating_add (inp 65#usize la) (inp 65#usize lb), add.Uint.saturating_sub (inp 65#usize la) (inp 65#usize lb))
def diff_ops (la lb : Std.Array Std.U64 2#usize) :=
  (Uint.Insts.CoreOpsArithAddUintUint.add (inp 127#usize la) (inp 127#usize lb),
   Uint.Insts.CoreOpsArithSubUintUint.sub (inp 127#usize la) (inp 127#usize lb),
   Uint.Insts.CoreOpsArithNegUint.neg (inp 127#usize la),
   add.Uint.wrapping_add (inp 127#usize la) (inp 127#usize lb),
   add.Uint.wrapping_sub (inp 127#usize la) (inp 127#usize lb),
   add.Uint.wrapping_neg (inp 127#usize la))
def diff_zero (la lb : Std.Array Std.U64 0#usize) :=
  (add.Uint.overflowing_add (⟨la⟩ : Uint 0#usize 0#usize) ⟨lb⟩, add.Uint.overflowing_sub (⟨la⟩ : Uint 0#usize 0#usize) ⟨lb⟩)
def diff_from_limbs (la : Std.Array Std.U64 2#usize) :=
  (Uint.from_limbs 65#usize la, Uint.from_limbs 100#usize la, Uint.from_limbs 128#usize la)
def diff_from_limbs1 (la : Std.Array Std.U64 1#usize) :=
  (Uint.from_limbs 1#usize la, Uint.from_limbs 63#usize la, Uint.from_limbs 64#usize la)
def diff_mask (bits : Std.U16) := (mask (mkU .Usize (bits.val % 600)), nlimbs (mkU .Usize (bits.val % 600)))
def diff_consts (_x : Std.U8) :=
  (Uint.ZERO 65#usize 2#usize, Uint.MAX 65#usize 2#usize, Uint.ZERO 128#usize 2#usize,
   Uint.MAX 128#usize 2#usize, Uint.ZERO 1#usize 1#usize, Uint.MAX 1#usize 1#usize,
   Uint.MAX 63#usize 1#usize, Uint.MAX 64#usize 1#usize, Uint.MAX 129#usize 3#usize)

end Benchmark.V2.Ruint.UintAdd.Gold
