import Benchmark.V2.Prelude
import Benchmark.V2.CryptoBigint.Uint.Instances
import CryptoBigintUint.Extraction

/-! Hidden gold specification for target `crypto_bigint/uint`.

`Uint<LIMBS>` is a little-endian array of 64-bit limbs; every API function is
specified against the mathematical value `val` of the limbs (an independent
`Nat` model), at `LIMBS ∈ {0, 1, 2, 4}` (`U256 = Uint<4>` is the type the
crate's property tests use). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM crypto_bigint RSGB

/-! Model and per-width contracts. They live outside the `Benchmark` namespace and
are `Bool`-valued so that the test driver evaluates them instead of unfolding
them symbolically. -/
namespace CryptoBigintUintGoldModel

abbrev U (L : Std.Usize) := uint.Uint L

/-- Little-endian value of a list of 64-bit limbs. -/
def limbsVal (l : List Std.U64) : Nat :=
  l.foldr (fun x acc => x.val + 2^64 * acc) 0

/-- Mathematical value of a `Uint`. -/
def val {L : Std.Usize} (a : U L) : Nat := limbsVal a.limbs.val

/-- Bit width `64 * LIMBS`. -/
def bits (L : Std.Usize) : Nat := 64 * L.val

/-- The `Uint<L>` holding `n mod 2^(64 L)`. -/
def ofNat (L : Std.Usize) (n : Nat) : U L :=
  ⟨⟨List.ofFn (n := L.val) (fun i => mkU .U64 ((n % 2^(bits L)) / 2^(64 * i.val))), by simp⟩⟩

/-- The value whose every limb is `l`. -/
def rep (L : Std.Usize) (l : Nat) : Nat := (List.range L.val).foldr (fun i acc => acc + l * 2^(64 * i)) 0

/-- Little-endian / big-endian value of a byte list. -/
def leVal (l : List Std.U8) : Nat := l.foldr (fun b acc => b.val + 256 * acc) 0
def beVal (l : List Std.U8) : Nat := l.foldl (fun acc b => 256 * acc + b.val) 0

/-- The `n` low little-endian bytes of `v`. -/
def leBytes (n : Std.Usize) (v : Nat) : Std.Array Std.U8 n :=
  ⟨List.ofFn (n := n.val) (fun i => mkU .U8 (v / 2^(8 * i.val))), by simp⟩

def MAXW : Std.U64 := mkU .U64 (2^64 - 1)

/-! ## Limb-level contracts -/

def limbSpec (x y c : Std.U64) : Bool := decide (
  limb.add.Limb.carrying_add x y c =
    ok (mkU .U64 (x.val + y.val + c.val), mkU .U64 ((x.val + y.val + c.val) / 2^64)) ∧
  limb.add.Limb.overflowing_add x y = ok (mkU .U64 (x.val + y.val), mkU .U64 ((x.val + y.val) / 2^64)) ∧
  limb.sub.Limb.borrowing_sub x y c =
    ok (mkU .U64 (x.val + 2^64 - y.val - c.val / 2^63),
        if x.val < y.val + c.val / 2^63 then MAXW else mkU .U64 0) ∧
  limb.bit_and.Limb.bitand x y = ok (mkU .U64 (x.val &&& y.val)) ∧
  limb.bit_or.Limb.bitor x y = ok (mkU .U64 (x.val ||| y.val)) ∧
  limb.bit_xor.Limb.bitxor x y = ok (mkU .U64 (x.val ^^^ y.val)))

/-! ## `Uint` contracts at one width -/

/-- Addition: exact sum with carry word `⌊(a + b + carry) / 2^(64 L)⌋`. -/
def addSpec {L : Std.Usize} (a b : U L) (c : Std.U64) : Bool := decide (
  uint.add.Uint.carrying_add a b c =
    ok (ofNat L (val a + val b + c.val), mkU .U64 ((val a + val b + c.val) / 2^(bits L))) ∧
  uint.add.Uint.adc a b c = uint.add.Uint.carrying_add a b c ∧
  uint.add.Uint.wrapping_add a b = ok (ofNat L (val a + val b)))

/-- Subtraction: `a - (b + borrow_bit)` with borrow word `MAX` / `0`; the incoming
borrow only counts through its top bit. With no limbs the borrow is passed through. -/
def subSpec {L : Std.Usize} (a b : U L) (bw : Std.U64) : Bool := decide (
  uint.sub.Uint.borrowing_sub a b bw =
    ok (ofNat L (val a + 2^(bits L) - val b - bw.val / 2^63),
        if L.val = 0 then bw else if val a < val b + bw.val / 2^63 then MAXW else mkU .U64 0) ∧
  uint.sub.Uint.sbb a b bw = uint.sub.Uint.borrowing_sub a b bw ∧
  uint.sub.Uint.wrapping_sub a b = ok (ofNat L (val a + 2^(bits L) - val b)))

/-- Bitwise operations on the values. -/
def bitSpec {L : Std.Usize} (a b : U L) (l : Std.U64) : Bool := decide (
  uint.bit_and.Uint.bitand a b = ok (ofNat L (val a &&& val b)) ∧
  uint.bit_and.Uint.wrapping_and a b = ok (ofNat L (val a &&& val b)) ∧
  uint.bit_or.Uint.bitor a b = ok (ofNat L (val a ||| val b)) ∧
  uint.bit_or.Uint.wrapping_or a b = ok (ofNat L (val a ||| val b)) ∧
  uint.bit_xor.Uint.bitxor a b = ok (ofNat L (val a ^^^ val b)) ∧
  uint.bit_xor.Uint.wrapping_xor a b = ok (ofNat L (val a ^^^ val b)) ∧
  uint.bit_and.Uint.bitand_limb a l = ok (ofNat L (val a &&& rep L l.val)))

/-- `sub_mod`: `(a - b) mod p` under the documented precondition (`a, b < p`;
the result outside it is unspecified). -/
def subModSpec {L : Std.Usize} (a b p : U L) : Bool := decide (
  val a < val p → val b < val p →
    uint.sub_mod.Uint.sub_mod a b p ⦃ r => val r = (val a + val p - val b) % val p ∧ r = ofNat L (val r) ⦄)

/-- `sub_mod_special` with `p = 2^(64 L) - c`: `(a - b) mod p` under the
documented precondition (`a, b < p`, `c ≠ 0`, at least one limb). -/
def subModSpecialSpec {L : Std.Usize} (a b : U L) (c : Std.U64) : Bool := decide (
  0 < L.val → 0 < c.val → val a < 2^(bits L) - c.val → val b < 2^(bits L) - c.val →
    uint.sub_mod.Uint.sub_mod_special a b c ⦃ r =>
      val r = (val a + (2^(bits L) - c.val) - val b) % (2^(bits L) - c.val) ⦄)

/-- Constructors and decoding. -/
def ctorSpec {L : Std.Usize} (la : Std.Array Std.U64 L) : Bool := decide (
  uint.Uint.new la = ok ⟨la⟩ ∧
  uint.encoding.Uint.from_le_slice L (Array.to_slice (leBytes (mkU .Usize (8 * L.val)) (limbsVal la.val))) = ok ⟨la⟩)

/-- Everything at one width. -/
def allSpec {L : Std.Usize} (la lb lp : Std.Array Std.U64 L) (c : Std.U64) : Bool :=
  let a : U L := ⟨la⟩
  let b : U L := ⟨lb⟩
  let p : U L := ⟨lp⟩
  let c' := mkU .U64 (c.val % 2^(bits L))
  addSpec a b c && subSpec a b c && bitSpec a b c && subModSpec a b p &&
  subModSpec (ofNat L (val a % (val p + 1))) (ofNat L (val b % (val p + 1))) (ofNat L (val p + 1)) &&
  subModSpecialSpec a b c &&
  subModSpecialSpec (ofNat L (val a % (2^(bits L) - c'.val))) (ofNat L (val b % (2^(bits L) - c'.val))) c' &&
  ctorSpec la

/-- Inputs at the carry / borrow boundary: `b = 2^(64 L) - a + k - 2`. -/
def boundarySpec {L : Std.Usize} (la : Std.Array Std.U64 L) (k : Nat) (c : Std.U64) : Bool :=
  let a : U L := ⟨la⟩
  let b := ofNat L (2^(bits L) - val a + k % 4 - 2)
  let d := ofNat L (val a + k % 4 - 2)
  addSpec a b (mkU .U64 (k / 4 % 3)) && addSpec b a c && subSpec a d (mkU .U64 (2^63 * (k / 4 % 2))) &&
  subSpec d a c &&
  -- `a` as the modulus, operands at the edges of `[0, a)`
  subModSpec (ofNat L (val a - 1)) (ofNat L (k % 4)) a && subModSpec (ofNat L (k % 4)) (ofNat L (val a - 1)) a &&
  subModSpec (ofNat L (val a - 1)) (ofNat L (val a - 1 - k % 4)) a &&
  -- special modulus `2^(64 L) - c` with operands at the edges of `[0, p)`
  subModSpecialSpec (ofNat L (2^(bits L) - c.val - 1)) (ofNat L (k % 4)) c &&
  subModSpecialSpec (ofNat L (k % 4)) (ofNat L (2^(bits L) - c.val - 1)) c &&
  subModSpecialSpec (ofNat L (k % 4)) (ofNat L (2^(bits L) - c.val - 1 - k / 4 % 4)) c

end CryptoBigintUintGoldModel

open CryptoBigintUintGoldModel

namespace Benchmark.V2.CryptoBigint.Uint.Gold

/-! ## Gold properties -/

/-- Limb primitives: exact sum / carry, difference / borrow mask, bitwise ops. -/
def gold_limb (x y c : Std.U64) : Prop := limbSpec x y c

/-- Limb primitives at the carry / borrow boundary (`y = MAX - x + k`). -/
def gold_limb_boundary (x : Std.U64) (k : Std.U8) (c : Std.U64) : Prop :=
  limbSpec x (mkU .U64 (2^64 - 1 - x.val + k.val % 3)) c ∧
  limbSpec x (mkU .U64 (x.val + k.val % 3 - 1)) (mkU .U64 (2^63 * (k.val / 3 % 2) + k.val / 6 % 3))

/-- `LIMBS = 0`: values are empty, carries / borrows pass through. -/
def gold_zero_limbs (la lb : Std.Array Std.U64 0#usize) (c : Std.U64) : Prop :=
  allSpec la lb la c ∧
  uint.add.Uint.carrying_add (⟨la⟩ : U 0#usize) ⟨lb⟩ c = ok (⟨la⟩, c) ∧
  uint.sub.Uint.borrowing_sub (⟨la⟩ : U 0#usize) ⟨lb⟩ c = ok (⟨la⟩, c)

def gold_one_limb (la lb lp : Std.Array Std.U64 1#usize) (c : Std.U64) : Prop := allSpec la lb lp c
def gold_two_limbs (la lb lp : Std.Array Std.U64 2#usize) (c : Std.U64) : Prop := allSpec la lb lp c
def gold_four_limbs (la lb lp : Std.Array Std.U64 4#usize) (c : Std.U64) : Prop := allSpec la lb lp c

def gold_boundary_one (la : Std.Array Std.U64 1#usize) (k : Std.U8) (c : Std.U64) : Prop := boundarySpec la k.val c
def gold_boundary_two (la : Std.Array Std.U64 2#usize) (k : Std.U8) (c : Std.U64) : Prop := boundarySpec la k.val c
def gold_boundary_four (la : Std.Array Std.U64 4#usize) (k : Std.U8) (c : Std.U64) : Prop := boundarySpec la k.val c

/-- Carries / borrows rippling through runs of all-ones / all-zero limbs. -/
def gold_ripple (j : Std.U8) (t c : Std.U64) : Prop :=
  let j := j.val % 5
  let a := ofNat 4#usize (2^(64 * j) - 1)
  let b := ofNat 4#usize (1 + 2^(64 * j) * t.val)
  let z := ofNat 4#usize (2^(64 * j))
  addSpec a b c ∧ addSpec a (ofNat 4#usize 0) (mkU .U64 1) ∧ subSpec b a c ∧ subSpec z b c ∧
  subSpec z (ofNat 4#usize 0) (mkU .U64 (2^63)) ∧
  subModSpec (ofNat 4#usize 0) a z ∧ subModSpec a (ofNat 4#usize 0) (ofNat 4#usize (2^(64 * j))) ∧
  subModSpecialSpec (ofNat 4#usize 0) a (mkU .U64 (c.val % 2^63 + 1))

/-- `from_le_slice` / `from_be_slice` decode exactly the `8 * LIMBS`-byte slices
(little- / big-endian) and panic on any other length. -/
def gold_decode_any (s : Slice Std.U8) : Prop :=
  uint.encoding.Uint.from_le_slice 4#usize s =
    (if s.val.length = 32 then ok (ofNat 4#usize (leVal s.val)) else fail .panic) ∧
  uint.encoding.Uint.from_be_slice 4#usize s =
    (if s.val.length = 32 then ok (ofNat 4#usize (beVal s.val)) else fail .panic) ∧
  uint.encoding.Uint.from_le_slice 1#usize s =
    (if s.val.length = 8 then ok (ofNat 1#usize (leVal s.val)) else fail .panic) ∧
  uint.encoding.Uint.from_be_slice 2#usize s =
    (if s.val.length = 16 then ok (ofNat 2#usize (beVal s.val)) else fail .panic) ∧
  uint.encoding.Uint.from_le_slice 0#usize s =
    (if s.val.length = 0 then ok (ofNat 0#usize 0) else fail .panic)

def gold_decode32 (bs : Std.Array Std.U8 32#usize) : Prop :=
  uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice bs) = ok (ofNat 4#usize (leVal bs.val)) ∧
  uint.encoding.Uint.from_be_slice 4#usize (Array.to_slice bs) = ok (ofNat 4#usize (beVal bs.val)) ∧
  uint.encoding.Uint.from_be_slice 4#usize (Array.to_slice (⟨bs.val.reverse, by simp⟩ : Std.Array Std.U8 32#usize)) =
    uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice bs)

def gold_decode16 (bs : Std.Array Std.U8 16#usize) : Prop :=
  uint.encoding.Uint.from_le_slice 2#usize (Array.to_slice bs) = ok (ofNat 2#usize (leVal bs.val)) ∧
  uint.encoding.Uint.from_be_slice 2#usize (Array.to_slice bs) = ok (ofNat 2#usize (beVal bs.val))

def gold_decode8 (bs : Std.Array Std.U8 8#usize) : Prop :=
  uint.encoding.Uint.from_le_slice 1#usize (Array.to_slice bs) = ok (ofNat 1#usize (leVal bs.val)) ∧
  uint.encoding.Uint.from_be_slice 1#usize (Array.to_slice bs) = ok (ofNat 1#usize (beVal bs.val))

/-! ## Differential-testing probes -/

def diff_limb (x y c : Std.U64) :=
  (limb.add.Limb.carrying_add x y c, limb.add.Limb.overflowing_add x y, limb.sub.Limb.borrowing_sub x y c,
   limb.bit_and.Limb.bitand x y, limb.bit_or.Limb.bitor x y, limb.bit_xor.Limb.bitxor x y)
def diff_add4 (la lb : Std.Array Std.U64 4#usize) (c : Std.U64) :=
  (uint.add.Uint.carrying_add (⟨la⟩ : U 4#usize) ⟨lb⟩ c, uint.add.Uint.adc (⟨la⟩ : U 4#usize) ⟨lb⟩ c,
   uint.add.Uint.wrapping_add (⟨la⟩ : U 4#usize) ⟨lb⟩)
def diff_add1 (la lb : Std.Array Std.U64 1#usize) (c : Std.U64) :=
  uint.add.Uint.carrying_add (⟨la⟩ : U 1#usize) ⟨lb⟩ c
def diff_sub4 (la lb : Std.Array Std.U64 4#usize) (c : Std.U64) :=
  (uint.sub.Uint.borrowing_sub (⟨la⟩ : U 4#usize) ⟨lb⟩ c, uint.sub.Uint.sbb (⟨la⟩ : U 4#usize) ⟨lb⟩ c,
   uint.sub.Uint.wrapping_sub (⟨la⟩ : U 4#usize) ⟨lb⟩)
def diff_sub2 (la lb : Std.Array Std.U64 2#usize) (c : Std.U64) :=
  uint.sub.Uint.borrowing_sub (⟨la⟩ : U 2#usize) ⟨lb⟩ c
def diff_bits4 (la lb : Std.Array Std.U64 4#usize) (c : Std.U64) :=
  (uint.bit_and.Uint.bitand (⟨la⟩ : U 4#usize) ⟨lb⟩, uint.bit_and.Uint.wrapping_and (⟨la⟩ : U 4#usize) ⟨lb⟩,
   uint.bit_or.Uint.bitor (⟨la⟩ : U 4#usize) ⟨lb⟩, uint.bit_or.Uint.wrapping_or (⟨la⟩ : U 4#usize) ⟨lb⟩,
   uint.bit_xor.Uint.bitxor (⟨la⟩ : U 4#usize) ⟨lb⟩, uint.bit_xor.Uint.wrapping_xor (⟨la⟩ : U 4#usize) ⟨lb⟩,
   uint.bit_and.Uint.bitand_limb (⟨la⟩ : U 4#usize) c)
def diff_submod4 (la lb lp : Std.Array Std.U64 4#usize) (c : Std.U64) :=
  (uint.sub_mod.Uint.sub_mod (⟨la⟩ : U 4#usize) ⟨lb⟩ ⟨lp⟩, uint.sub_mod.Uint.sub_mod_special (⟨la⟩ : U 4#usize) ⟨lb⟩ c)
def diff_submod1 (la lb lp : Std.Array Std.U64 1#usize) (c : Std.U64) :=
  (uint.sub_mod.Uint.sub_mod (⟨la⟩ : U 1#usize) ⟨lb⟩ ⟨lp⟩, uint.sub_mod.Uint.sub_mod_special (⟨la⟩ : U 1#usize) ⟨lb⟩ c)
def diff_zero (la lb : Std.Array Std.U64 0#usize) (c : Std.U64) :=
  (uint.add.Uint.carrying_add (⟨la⟩ : U 0#usize) ⟨lb⟩ c, uint.sub.Uint.borrowing_sub (⟨la⟩ : U 0#usize) ⟨lb⟩ c,
   uint.sub_mod.Uint.sub_mod_special (⟨la⟩ : U 0#usize) ⟨lb⟩ c)
def diff_decode (bs : Std.Array Std.U8 32#usize) :=
  (uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice bs), uint.encoding.Uint.from_be_slice 4#usize (Array.to_slice bs))
def diff_decode_any (s : Slice Std.U8) :=
  (uint.encoding.Uint.from_le_slice 2#usize s, uint.encoding.Uint.from_be_slice 2#usize s)
def diff_new (la : Std.Array Std.U64 4#usize) := uint.Uint.new la

end Benchmark.V2.CryptoBigint.Uint.Gold
