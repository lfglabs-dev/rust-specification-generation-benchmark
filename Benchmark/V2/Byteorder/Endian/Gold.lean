import Benchmark.V2.Prelude
import ByteorderEndian.Extraction

/-! Hidden gold specification for target `byteorder/endian`.

API: `read_u16/u32/u64/u128` and `write_u16/u32/u64/u128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`.

Contract (from the crate docs): `read_uN(buf)` reads an `N`-bit integer from the
first `N/8` bytes of `buf` (most / least significant byte first) and panics iff
`buf.len() < N/8`; `write_uN(buf, n)` overwrites exactly the first `N/8` bytes of
`buf` with the encoding of `n`, leaves the remaining bytes untouched, and panics
iff `buf.len() < N/8`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM byteorder RSGB

namespace Benchmark.V2.Byteorder.Endian.Gold

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

/-- Exact contract of a `read_uN` function of width `k` bytes. -/
def readSpec {ty : UScalarTy} (k : Nat) (value : List Nat → Nat)
    (f : Slice Std.U8 → RustM (UScalar ty)) (l : List Std.U8) : Prop :=
  (k ≤ l.length → f (mkSlice l) ⦃ r => r.val = value ((l.map (·.val)).take k) ⦄) ∧
  (l.length < k → f (mkSlice l) = fail .panic)

/-- Exact contract of a `write_uN` function of width `k` bytes. -/
def writeSpec {ty : UScalarTy} (k : Nat) (enc : Nat → List Nat)
    (f : Slice Std.U8 → UScalar ty → RustM (Slice Std.U8)) (l : List Std.U8) (n : UScalar ty) : Prop :=
  (k ≤ l.length → f (mkSlice l) n ⦃ s => bytesOf s = enc n.val ++ (l.map (·.val)).drop k ⦄) ∧
  (l.length < k → (fun s => s.val) <$> f (mkSlice l) n = fail .panic)

/-- Reading back what was written returns the written value (any buffer of sufficient length). -/
def roundTrip {ty : UScalarTy} (k : Nat)
    (w : Slice Std.U8 → UScalar ty → RustM (Slice Std.U8)) (r : Slice Std.U8 → RustM (UScalar ty))
    (l : List Std.U8) (n : UScalar ty) : Prop :=
  k ≤ l.length → (do let s ← w (mkSlice l) n; r s) ⦃ m => m = n ⦄

/-! ## Big endian -/

def gold_be_read_u16 (buf : List Std.U8) : Prop :=
  readSpec 2 beValue BigEndian.Insts.ByteorderByteOrder.read_u16 buf
def gold_be_read_u32 (buf : List Std.U8) : Prop :=
  readSpec 4 beValue BigEndian.Insts.ByteorderByteOrder.read_u32 buf
def gold_be_read_u64 (buf : List Std.U8) : Prop :=
  readSpec 8 beValue BigEndian.Insts.ByteorderByteOrder.read_u64 buf
def gold_be_read_u128 (buf : List Std.U8) : Prop :=
  readSpec 16 beValue BigEndian.Insts.ByteorderByteOrder.read_u128 buf

def gold_be_write_u16 (buf : List Std.U8) (n : Std.U16) : Prop :=
  writeSpec 2 (beDigits 2) BigEndian.Insts.ByteorderByteOrder.write_u16 buf n
def gold_be_write_u32 (buf : List Std.U8) (n : Std.U32) : Prop :=
  writeSpec 4 (beDigits 4) BigEndian.Insts.ByteorderByteOrder.write_u32 buf n
def gold_be_write_u64 (buf : List Std.U8) (n : Std.U64) : Prop :=
  writeSpec 8 (beDigits 8) BigEndian.Insts.ByteorderByteOrder.write_u64 buf n
def gold_be_write_u128 (buf : List Std.U8) (n : Std.U128) : Prop :=
  writeSpec 16 (beDigits 16) BigEndian.Insts.ByteorderByteOrder.write_u128 buf n

/-! ## Little endian -/

def gold_le_read_u16 (buf : List Std.U8) : Prop :=
  readSpec 2 leValue LittleEndian.Insts.ByteorderByteOrder.read_u16 buf
def gold_le_read_u32 (buf : List Std.U8) : Prop :=
  readSpec 4 leValue LittleEndian.Insts.ByteorderByteOrder.read_u32 buf
def gold_le_read_u64 (buf : List Std.U8) : Prop :=
  readSpec 8 leValue LittleEndian.Insts.ByteorderByteOrder.read_u64 buf
def gold_le_read_u128 (buf : List Std.U8) : Prop :=
  readSpec 16 leValue LittleEndian.Insts.ByteorderByteOrder.read_u128 buf

def gold_le_write_u16 (buf : List Std.U8) (n : Std.U16) : Prop :=
  writeSpec 2 (leDigits 2) LittleEndian.Insts.ByteorderByteOrder.write_u16 buf n
def gold_le_write_u32 (buf : List Std.U8) (n : Std.U32) : Prop :=
  writeSpec 4 (leDigits 4) LittleEndian.Insts.ByteorderByteOrder.write_u32 buf n
def gold_le_write_u64 (buf : List Std.U8) (n : Std.U64) : Prop :=
  writeSpec 8 (leDigits 8) LittleEndian.Insts.ByteorderByteOrder.write_u64 buf n
def gold_le_write_u128 (buf : List Std.U8) (n : Std.U128) : Prop :=
  writeSpec 16 (leDigits 16) LittleEndian.Insts.ByteorderByteOrder.write_u128 buf n

/-! ## Round trips (the crate's quickcheck properties, generalised to any buffer) -/

def gold_be_roundtrip_u16 (buf : List Std.U8) (n : Std.U16) : Prop :=
  roundTrip 2 BigEndian.Insts.ByteorderByteOrder.write_u16 BigEndian.Insts.ByteorderByteOrder.read_u16 buf n
def gold_be_roundtrip_u32 (buf : List Std.U8) (n : Std.U32) : Prop :=
  roundTrip 4 BigEndian.Insts.ByteorderByteOrder.write_u32 BigEndian.Insts.ByteorderByteOrder.read_u32 buf n
def gold_be_roundtrip_u64 (buf : List Std.U8) (n : Std.U64) : Prop :=
  roundTrip 8 BigEndian.Insts.ByteorderByteOrder.write_u64 BigEndian.Insts.ByteorderByteOrder.read_u64 buf n
def gold_be_roundtrip_u128 (buf : List Std.U8) (n : Std.U128) : Prop :=
  roundTrip 16 BigEndian.Insts.ByteorderByteOrder.write_u128 BigEndian.Insts.ByteorderByteOrder.read_u128 buf n
def gold_le_roundtrip_u16 (buf : List Std.U8) (n : Std.U16) : Prop :=
  roundTrip 2 LittleEndian.Insts.ByteorderByteOrder.write_u16 LittleEndian.Insts.ByteorderByteOrder.read_u16 buf n
def gold_le_roundtrip_u32 (buf : List Std.U8) (n : Std.U32) : Prop :=
  roundTrip 4 LittleEndian.Insts.ByteorderByteOrder.write_u32 LittleEndian.Insts.ByteorderByteOrder.read_u32 buf n
def gold_le_roundtrip_u64 (buf : List Std.U8) (n : Std.U64) : Prop :=
  roundTrip 8 LittleEndian.Insts.ByteorderByteOrder.write_u64 LittleEndian.Insts.ByteorderByteOrder.read_u64 buf n
def gold_le_roundtrip_u128 (buf : List Std.U8) (n : Std.U128) : Prop :=
  roundTrip 16 LittleEndian.Insts.ByteorderByteOrder.write_u128 LittleEndian.Insts.ByteorderByteOrder.read_u128 buf n

/-! Differential-testing probes. -/

def diff_be_read_u16 (buf : Slice Std.U8) := BigEndian.Insts.ByteorderByteOrder.read_u16 buf
def diff_be_read_u32 (buf : Slice Std.U8) := BigEndian.Insts.ByteorderByteOrder.read_u32 buf
def diff_be_read_u64 (buf : Slice Std.U8) := BigEndian.Insts.ByteorderByteOrder.read_u64 buf
def diff_be_read_u128 (buf : Slice Std.U8) := BigEndian.Insts.ByteorderByteOrder.read_u128 buf
def diff_le_read_u16 (buf : Slice Std.U8) := LittleEndian.Insts.ByteorderByteOrder.read_u16 buf
def diff_le_read_u32 (buf : Slice Std.U8) := LittleEndian.Insts.ByteorderByteOrder.read_u32 buf
def diff_le_read_u64 (buf : Slice Std.U8) := LittleEndian.Insts.ByteorderByteOrder.read_u64 buf
def diff_le_read_u128 (buf : Slice Std.U8) := LittleEndian.Insts.ByteorderByteOrder.read_u128 buf
def diff_be_write_u16 (buf : Slice Std.U8) (n : Std.U16) :=
  (fun s => s.val) <$> BigEndian.Insts.ByteorderByteOrder.write_u16 buf n
def diff_be_write_u32 (buf : Slice Std.U8) (n : Std.U32) :=
  (fun s => s.val) <$> BigEndian.Insts.ByteorderByteOrder.write_u32 buf n
def diff_be_write_u64 (buf : Slice Std.U8) (n : Std.U64) :=
  (fun s => s.val) <$> BigEndian.Insts.ByteorderByteOrder.write_u64 buf n
def diff_be_write_u128 (buf : Slice Std.U8) (n : Std.U128) :=
  (fun s => s.val) <$> BigEndian.Insts.ByteorderByteOrder.write_u128 buf n
def diff_le_write_u16 (buf : Slice Std.U8) (n : Std.U16) :=
  (fun s => s.val) <$> LittleEndian.Insts.ByteorderByteOrder.write_u16 buf n
def diff_le_write_u32 (buf : Slice Std.U8) (n : Std.U32) :=
  (fun s => s.val) <$> LittleEndian.Insts.ByteorderByteOrder.write_u32 buf n
def diff_le_write_u64 (buf : Slice Std.U8) (n : Std.U64) :=
  (fun s => s.val) <$> LittleEndian.Insts.ByteorderByteOrder.write_u64 buf n
def diff_le_write_u128 (buf : Slice Std.U8) (n : Std.U128) :=
  (fun s => s.val) <$> LittleEndian.Insts.ByteorderByteOrder.write_u128 buf n

end Benchmark.V2.Byteorder.Endian.Gold
