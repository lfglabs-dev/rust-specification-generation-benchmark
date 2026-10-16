import Benchmark.V2.Prelude
import ByteorderLiteUint.Extraction

/-! Hidden gold specification for target `byteorder_lite/uint`.

API: `read_uint`, `read_uint128`, `write_uint`, `write_uint128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`.

Contract (crate docs):
* `read_uint(buf, nbytes)` reads an unsigned integer of `nbytes` bytes from the
  first `nbytes` bytes of `buf`; panics iff `nbytes < 1 || nbytes > 8 ||
  buf.len() < nbytes` (`16` for `read_uint128`).
* `write_uint(buf, n, nbytes)` writes `n` as an `nbytes`-byte integer into the
  first `nbytes` bytes of `buf` (rest untouched); panics iff `n` is not
  representable in `nbytes` bytes (in particular for `nbytes = 0`), `nbytes > 8`
  (`16`), or `buf.len() < nbytes`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM byteorder_lite RSGB

namespace Benchmark.V2.ByteorderLite.Uint.Gold

/-- The `k` base-256 digits of `n`, most significant first. -/
def beDigits (k n : Nat) : List Nat := (List.range k).map fun i => n / 256 ^ (k - 1 - i) % 256

/-- The `k` base-256 digits of `n`, least significant first. -/
def leDigits (k n : Nat) : List Nat := (List.range k).map fun i => n / 256 ^ i % 256

/-- Value of a big-endian base-256 digit list. -/
def beValue (l : List Nat) : Nat := l.foldl (fun acc b => acc * 256 + b) 0

/-- Value of a little-endian base-256 digit list. -/
def leValue (l : List Nat) : Nat := l.foldr (fun b acc => b + 256 * acc) 0

def bytesOf (s : Slice Std.U8) : List Nat := s.val.map (·.val)

/-- The slice with contents `l` (inputs are sampled as lists). -/
def mkSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- Smallest positive number of bytes in which `n` is representable. -/
def minBytes (n : Nat) : Nat := ((List.range 17).filter fun k => decide (1 ≤ k ∧ n < 256 ^ k)).headD 17

/-- Exact contract of `read_uint{,128}` (`max` = 8 or 16), `nbytes = k`. -/
def readSpec {ty : UScalarTy} (max : Nat) (value : List Nat → Nat)
    (f : Slice Std.U8 → Std.Usize → RustM (UScalar ty)) (l : List Std.U8) (k : Nat) : Prop :=
  (1 ≤ k ∧ k ≤ max ∧ k ≤ l.length →
    f (mkSlice l) (mkU .Usize k) ⦃ r => r.val = value ((l.map (·.val)).take k) ⦄) ∧
  (¬ (1 ≤ k ∧ k ≤ max ∧ k ≤ l.length) → f (mkSlice l) (mkU .Usize k) = fail .panic)

/-- Exact contract of `write_uint{,128}` (`max` = 8 or 16), `nbytes = k`. -/
def writeSpec {ty : UScalarTy} (max : Nat) (enc : Nat → Nat → List Nat)
    (f : Slice Std.U8 → UScalar ty → Std.Usize → RustM (Slice Std.U8))
    (l : List Std.U8) (n : UScalar ty) (k : Nat) : Prop :=
  (1 ≤ k ∧ n.val < 256 ^ k ∧ k ≤ max ∧ k ≤ l.length →
    f (mkSlice l) n (mkU .Usize k) ⦃ s => bytesOf s = enc k n.val ++ (l.map (·.val)).drop k ⦄) ∧
  (¬ (1 ≤ k ∧ n.val < 256 ^ k ∧ k ≤ max ∧ k ≤ l.length) →
    (fun s => s.val) <$> f (mkSlice l) n (mkU .Usize k) = fail .panic)

/-- Writing with exactly the minimal width succeeds; one byte less panics. -/
def minimalWidth {ty : UScalarTy}
    (f : Slice Std.U8 → UScalar ty → Std.Usize → RustM (Slice Std.U8))
    (l : List Std.U8) (n : UScalar ty) : Prop :=
  (minBytes n.val ≤ l.length →
    ((fun s => (s.val.map (·.val)).length) <$> f (mkSlice l) n (mkU .Usize (minBytes n.val))) = ok l.length) ∧
  ((fun s => s.val) <$> f (mkSlice l) n (mkU .Usize (minBytes n.val - 1)) = fail .panic)

/-- Reading back what was written (same width) returns the value. -/
def roundTrip {ty : UScalarTy}
    (w : Slice Std.U8 → UScalar ty → Std.Usize → RustM (Slice Std.U8))
    (r : Slice Std.U8 → Std.Usize → RustM (UScalar ty))
    (l : List Std.U8) (n : UScalar ty) (k : Nat) : Prop :=
  1 ≤ k → n.val < 256 ^ k → k ≤ ty.numBits / 8 → k ≤ l.length →
    (do let s ← w (mkSlice l) n (mkU .Usize k); r s (mkU .Usize k)) ⦃ m => m = n ⦄

/-! ## read -/

def gold_be_read_uint (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 8 beValue BigEndian.Insts.Byteorder_liteByteOrder.read_uint buf nbytes.val
def gold_be_read_uint_small (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 8 beValue BigEndian.Insts.Byteorder_liteByteOrder.read_uint buf (nbytes.val % 11)
def gold_le_read_uint (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 8 leValue LittleEndian.Insts.Byteorder_liteByteOrder.read_uint buf nbytes.val
def gold_le_read_uint_small (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 8 leValue LittleEndian.Insts.Byteorder_liteByteOrder.read_uint buf (nbytes.val % 11)
def gold_be_read_uint128 (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 16 beValue BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf nbytes.val
def gold_be_read_uint128_small (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 16 beValue BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (nbytes.val % 19)
def gold_le_read_uint128 (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 16 leValue LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf nbytes.val
def gold_le_read_uint128_small (buf : List Std.U8) (nbytes : Std.U8) : Prop :=
  readSpec 16 leValue LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (nbytes.val % 19)

/-! ## write -/

def gold_be_write_uint (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  writeSpec 8 beDigits BigEndian.Insts.Byteorder_liteByteOrder.write_uint buf n nbytes.val
def gold_be_write_uint_small (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  writeSpec 8 beDigits BigEndian.Insts.Byteorder_liteByteOrder.write_uint buf n (nbytes.val % 11)
def gold_le_write_uint (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  writeSpec 8 leDigits LittleEndian.Insts.Byteorder_liteByteOrder.write_uint buf n nbytes.val
def gold_le_write_uint_small (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  writeSpec 8 leDigits LittleEndian.Insts.Byteorder_liteByteOrder.write_uint buf n (nbytes.val % 11)
def gold_be_write_uint128 (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  writeSpec 16 beDigits BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n nbytes.val
def gold_be_write_uint128_small (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  writeSpec 16 beDigits BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n (nbytes.val % 19)
def gold_le_write_uint128 (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  writeSpec 16 leDigits LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n nbytes.val
def gold_le_write_uint128_small (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  writeSpec 16 leDigits LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n (nbytes.val % 19)

/-! ## representability boundary -/

def gold_be_write_uint_minimal (buf : List Std.U8) (n : Std.U64) : Prop :=
  minimalWidth BigEndian.Insts.Byteorder_liteByteOrder.write_uint buf n
def gold_le_write_uint_minimal (buf : List Std.U8) (n : Std.U64) : Prop :=
  minimalWidth LittleEndian.Insts.Byteorder_liteByteOrder.write_uint buf n
def gold_be_write_uint128_minimal (buf : List Std.U8) (n : Std.U128) : Prop :=
  minimalWidth BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n
def gold_le_write_uint128_minimal (buf : List Std.U8) (n : Std.U128) : Prop :=
  minimalWidth LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n

/-! ## round trips (generalising the crate's quickcheck tests) -/

def gold_be_roundtrip_uint (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  roundTrip BigEndian.Insts.Byteorder_liteByteOrder.write_uint
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint buf (mkU .U64 (n.val % 256 ^ (nbytes.val % 9))) (nbytes.val % 9)
def gold_le_roundtrip_uint (buf : List Std.U8) (n : Std.U64) (nbytes : Std.U8) : Prop :=
  roundTrip LittleEndian.Insts.Byteorder_liteByteOrder.write_uint
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint buf (mkU .U64 (n.val % 256 ^ (nbytes.val % 9))) (nbytes.val % 9)
def gold_be_roundtrip_uint128 (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  roundTrip BigEndian.Insts.Byteorder_liteByteOrder.write_uint128
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (mkU .U128 (n.val % 256 ^ (nbytes.val % 17))) (nbytes.val % 17)
def gold_le_roundtrip_uint128 (buf : List Std.U8) (n : Std.U128) (nbytes : Std.U8) : Prop :=
  roundTrip LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (mkU .U128 (n.val % 256 ^ (nbytes.val % 17))) (nbytes.val % 17)

/-! Differential-testing probes. -/

def diff_be_read_uint (buf : Slice Std.U8) (nbytes : Std.U8) :=
  BigEndian.Insts.Byteorder_liteByteOrder.read_uint buf (mkU .Usize (nbytes.val % 20))
def diff_le_read_uint (buf : Slice Std.U8) (nbytes : Std.U8) :=
  LittleEndian.Insts.Byteorder_liteByteOrder.read_uint buf (mkU .Usize (nbytes.val % 20))
def diff_be_read_uint128 (buf : Slice Std.U8) (nbytes : Std.U8) :=
  BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (mkU .Usize (nbytes.val % 20))
def diff_le_read_uint128 (buf : Slice Std.U8) (nbytes : Std.U8) :=
  LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf (mkU .Usize (nbytes.val % 20))
def diff_be_write_uint (buf : Slice Std.U8) (n : Std.U64) (nbytes : Std.U8) :=
  (fun s => s.val) <$> BigEndian.Insts.Byteorder_liteByteOrder.write_uint buf n (mkU .Usize (nbytes.val % 20))
def diff_le_write_uint (buf : Slice Std.U8) (n : Std.U64) (nbytes : Std.U8) :=
  (fun s => s.val) <$> LittleEndian.Insts.Byteorder_liteByteOrder.write_uint buf n (mkU .Usize (nbytes.val % 20))
def diff_be_write_uint128 (buf : Slice Std.U8) (n : Std.U128) (nbytes : Std.U8) :=
  (fun s => s.val) <$> BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n (mkU .Usize (nbytes.val % 20))
def diff_le_write_uint128 (buf : Slice Std.U8) (n : Std.U128) (nbytes : Std.U8) :=
  (fun s => s.val) <$> LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 buf n (mkU .Usize (nbytes.val % 20))

end Benchmark.V2.ByteorderLite.Uint.Gold
