import Benchmark.V2.Prelude
import TinysetFits64.Extraction

/-! Hidden gold specification for target `tinyset/fits64`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM tinyset RSGB

namespace Benchmark.V2.Tinyset.Fits64.Gold

/-! ## Reference model

Unsigned integers are stored as themselves; signed integers are stored with the
zig-zag encoding (`0, -1, 1, -2, … ↦ 0, 1, 2, 3, …`), so that small magnitudes
give small words. Decoding is only promised for words that came from the type. -/

def zz (v : Int) : Nat := if 0 ≤ v then (2 * v).toNat else (-2 * v - 1).toNat
def unzz (z : Nat) : Int := if z % 2 = 0 then (z / 2 : Nat) else -(((z + 1) / 2 : Nat) : Int)

/-! ## Unsigned types: identity embedding -/

def gold_u64 (x : Std.U64) : Prop :=
  U64.Insts.TinysetSet64Fits64.to_u64 x = ok x ∧ U64.Insts.TinysetSet64Fits64.from_u64 x = ok x
def gold_u32_to (x : Std.U32) : Prop :=
  U32.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = x.val ⦄
def gold_u16_to (x : Std.U16) : Prop :=
  U16.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = x.val ⦄
def gold_u8_to (x : Std.U8) : Prop :=
  U8.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = x.val ⦄
def gold_usize_to (x : Std.Usize) : Prop :=
  Usize.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = x.val ⦄

/-- `from_u64` inverts `to_u64` on the words of the type's image. -/
def gold_unsigned_from (w : Std.U64) : Prop :=
  (w.val < 2^32 → U32.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = w.val ⦄) ∧
  (w.val < 2^16 → U16.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = w.val ⦄) ∧
  (w.val < 2^8 → U8.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = w.val ⦄) ∧
  (w.val < 2^System.Platform.numBits → Usize.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = w.val ⦄)

/-- The `test_fits64` round trip for every unsigned type. -/
def gold_unsigned_roundtrip (a : Std.U32) (b : Std.U16) (c : Std.U8) (d : Std.Usize) : Prop :=
  (do let w ← U32.Insts.TinysetSet64Fits64.to_u64 a; U32.Insts.TinysetSet64Fits64.from_u64 w) = ok a ∧
  (do let w ← U16.Insts.TinysetSet64Fits64.to_u64 b; U16.Insts.TinysetSet64Fits64.from_u64 w) = ok b ∧
  (do let w ← U8.Insts.TinysetSet64Fits64.to_u64 c; U8.Insts.TinysetSet64Fits64.from_u64 w) = ok c ∧
  (do let w ← Usize.Insts.TinysetSet64Fits64.to_u64 d; Usize.Insts.TinysetSet64Fits64.from_u64 w) = ok d

/-! ## Signed types: zig-zag embedding -/

def gold_i8_to (x : Std.I8) : Prop :=
  I8.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = zz x.val ⦄
def gold_i16_to (x : Std.I16) : Prop :=
  I16.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = zz x.val ⦄
def gold_i32_to (x : Std.I32) : Prop :=
  I32.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = zz x.val ⦄
def gold_i64_to (x : Std.I64) : Prop :=
  I64.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = zz x.val ⦄
def gold_isize_to (x : Std.Isize) : Prop :=
  Isize.Insts.TinysetSet64Fits64.to_u64 x ⦃ w => w.val = zz x.val ⦄

/-- Decoding every word of the image of a `w`-bit signed type (i.e. `< 2^w`). -/
def gold_signed_from (w : Std.U64) : Prop :=
  (w.val < 2^8 → I8.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = unzz w.val ⦄) ∧
  (w.val < 2^16 → I16.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = unzz w.val ⦄) ∧
  (w.val < 2^32 → I32.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = unzz w.val ⦄) ∧
  I64.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = unzz w.val ⦄ ∧
  (w.val < 2^System.Platform.numBits → Isize.Insts.TinysetSet64Fits64.from_u64 w ⦃ x => x.val = unzz w.val ⦄)

/-- Smaller words for smaller words: the decoder applied to small words (`< 2^8`) agrees across widths. -/
def gold_signed_from_small (b : Std.U8) : Prop :=
  let w := mkU .U64 b.val
  (do let x8 ← I8.Insts.TinysetSet64Fits64.from_u64 w
      let x16 ← I16.Insts.TinysetSet64Fits64.from_u64 w
      let x32 ← I32.Insts.TinysetSet64Fits64.from_u64 w
      let x64 ← I64.Insts.TinysetSet64Fits64.from_u64 w
      ok (x8.val, x16.val, x32.val, x64.val)) ⦃ (a, b, c, d) => a = b ∧ b = c ∧ c = d ⦄

/-- The `test_fits64` round trip (both assertions) for every signed type. -/
def gold_signed_roundtrip (a : Std.I8) (b : Std.I16) (c : Std.I32) (d : Std.I64) (e : Std.Isize) : Prop :=
  (do let w ← I8.Insts.TinysetSet64Fits64.to_u64 a; I8.Insts.TinysetSet64Fits64.from_u64 w) = ok a ∧
  (do let w ← I16.Insts.TinysetSet64Fits64.to_u64 b; I16.Insts.TinysetSet64Fits64.from_u64 w) = ok b ∧
  (do let w ← I32.Insts.TinysetSet64Fits64.to_u64 c; I32.Insts.TinysetSet64Fits64.from_u64 w) = ok c ∧
  (do let w ← I64.Insts.TinysetSet64Fits64.to_u64 d; I64.Insts.TinysetSet64Fits64.from_u64 w) = ok d ∧
  (do let w ← Isize.Insts.TinysetSet64Fits64.to_u64 e; Isize.Insts.TinysetSet64Fits64.from_u64 w) = ok e

/-- Encoding is a bijection onto the words below `2^bits`: decoding then encoding is the identity there. -/
def gold_signed_roundtrip_inv (w : Std.U64) : Prop :=
  (w.val < 2^8 → (do let x ← I8.Insts.TinysetSet64Fits64.from_u64 w; I8.Insts.TinysetSet64Fits64.to_u64 x) = ok w) ∧
  (w.val < 2^16 → (do let x ← I16.Insts.TinysetSet64Fits64.from_u64 w; I16.Insts.TinysetSet64Fits64.to_u64 x) = ok w) ∧
  (w.val < 2^32 → (do let x ← I32.Insts.TinysetSet64Fits64.from_u64 w; I32.Insts.TinysetSet64Fits64.to_u64 x) = ok w) ∧
  (do let x ← I64.Insts.TinysetSet64Fits64.from_u64 w; I64.Insts.TinysetSet64Fits64.to_u64 x) = ok w ∧
  (do let x ← Isize.Insts.TinysetSet64Fits64.from_u64 w; Isize.Insts.TinysetSet64Fits64.to_u64 x) = ok w

/-- The value of an integer is preserved when converting between `i8` and `i64` encodings
(same number ↦ same word, independently of the type). -/
def gold_signed_width_independent (x : Std.I8) : Prop :=
  I16.Insts.TinysetSet64Fits64.to_u64 (mkI .I16 x.val) = I8.Insts.TinysetSet64Fits64.to_u64 x ∧
  I32.Insts.TinysetSet64Fits64.to_u64 (mkI .I32 x.val) = I8.Insts.TinysetSet64Fits64.to_u64 x ∧
  I64.Insts.TinysetSet64Fits64.to_u64 (mkI .I64 x.val) = I8.Insts.TinysetSet64Fits64.to_u64 x ∧
  Isize.Insts.TinysetSet64Fits64.to_u64 (mkI .Isize x.val) = I8.Insts.TinysetSet64Fits64.to_u64 x

/-! Differential-testing probes. -/

def diff_u64_to (x : Std.U64) := U64.Insts.TinysetSet64Fits64.to_u64 x
def diff_u64_from (x : Std.U64) := U64.Insts.TinysetSet64Fits64.from_u64 x
def diff_u32_to (x : Std.U32) := U32.Insts.TinysetSet64Fits64.to_u64 x
def diff_u32_from (x : Std.U64) := U32.Insts.TinysetSet64Fits64.from_u64 x
def diff_u16_to (x : Std.U16) := U16.Insts.TinysetSet64Fits64.to_u64 x
def diff_u16_from (x : Std.U64) := U16.Insts.TinysetSet64Fits64.from_u64 x
def diff_u8_to (x : Std.U8) := U8.Insts.TinysetSet64Fits64.to_u64 x
def diff_u8_from (x : Std.U64) := U8.Insts.TinysetSet64Fits64.from_u64 x
def diff_usize_to (x : Std.Usize) := Usize.Insts.TinysetSet64Fits64.to_u64 x
def diff_usize_from (x : Std.U64) := Usize.Insts.TinysetSet64Fits64.from_u64 x
def diff_i8_to (x : Std.I8) := I8.Insts.TinysetSet64Fits64.to_u64 x
def diff_i8_from (x : Std.U64) := I8.Insts.TinysetSet64Fits64.from_u64 x
def diff_i16_to (x : Std.I16) := I16.Insts.TinysetSet64Fits64.to_u64 x
def diff_i16_from (x : Std.U64) := I16.Insts.TinysetSet64Fits64.from_u64 x
def diff_i32_to (x : Std.I32) := I32.Insts.TinysetSet64Fits64.to_u64 x
def diff_i32_from (x : Std.U64) := I32.Insts.TinysetSet64Fits64.from_u64 x
def diff_i64_to (x : Std.I64) := I64.Insts.TinysetSet64Fits64.to_u64 x
def diff_i64_from (x : Std.U64) := I64.Insts.TinysetSet64Fits64.from_u64 x
def diff_isize_to (x : Std.Isize) := Isize.Insts.TinysetSet64Fits64.to_u64 x
def diff_isize_from (x : Std.U64) := Isize.Insts.TinysetSet64Fits64.from_u64 x

end Benchmark.V2.Tinyset.Fits64.Gold
