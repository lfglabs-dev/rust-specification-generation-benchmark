import Benchmark.V2.Prelude
import Crc32fastBaseline.Extraction

/-! Hidden gold specification for target `crc32fast/baseline`.

API: `baseline::update_slow(prev, buf)` and `baseline::update_fast_16(prev, buf)`.
Contract: both return the CRC-32 (IEEE 802.3 / zlib: reflected, polynomial
`0xEDB88320`, initial value and final xor `0xFFFFFFFF` folded into the
`!prev` / `!crc` convention) of `buf`, *continuing* from the checksum `prev` of
the data seen so far (`prev = 0` for a fresh hasher). Hence
`update(update(p, a), b) = update(p, a ++ b)`, `update(p, []) = p`, and the two
implementations agree. Neither ever panics. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM crc32fast RSGB

namespace RSGBGold.Crc32fast.Baseline

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- One reflected CRC-32 step (bitwise, no table). -/
def step (c : Nat) : Nat := if c % 2 = 1 then (c / 2) ^^^ 0xEDB88320 else c / 2

def crcByte (c : Nat) (b : Std.U8) : Nat := Nat.iterate step 8 (c ^^^ b.val)

/-- CRC-32 of `bs` continuing from the finished checksum `prev`. -/
def crc32 (prev : Nat) (bs : List Std.U8) : Nat :=
  (bs.foldl crcByte (prev ^^^ 0xFFFFFFFF)) ^^^ 0xFFFFFFFF

def slow (p : Std.U32) (l : List Std.U8) := baseline.update_slow p (toSlice l)
def fast (p : Std.U32) (l : List Std.U8) := baseline.update_fast_16 p (toSlice l)

def str (s : String) : List Std.U8 := s.toUTF8.toList.map (fun b => mkU .U8 b.toNat)

/-- Buffers of up to ~200 bytes (exercise the 64-byte and 16-byte block paths). -/
def long (a b c : List Std.U8) : List Std.U8 := a ++ b ++ c

end RSGBGold.Crc32fast.Baseline

namespace Benchmark.V2.Crc32fast.Baseline.Gold
open RSGBGold.Crc32fast.Baseline

/-! ## Exact value (CRC-32 continuing from `prev`) -/

def gold_slow_crc32 (p : Std.U32) (a : List Std.U8) : Prop :=
  slow p a ⦃ r => r.val = crc32 p.val a ⦄

def gold_slow_crc32_long (p : Std.U32) (a b c : List Std.U8) : Prop :=
  slow p (long a b c) ⦃ r => r.val = crc32 p.val (long a b c) ⦄

def gold_fast_crc32 (p : Std.U32) (a : List Std.U8) : Prop :=
  fast p a ⦃ r => r.val = crc32 p.val a ⦄

def gold_fast_crc32_long (p : Std.U32) (a b c : List Std.U8) : Prop :=
  fast p (long a b c) ⦃ r => r.val = crc32 p.val (long a b c) ⦄

/-- Fresh checksums (`prev = 0`) of standard check strings. -/
def gold_check_vectors : Prop :=
  slow 0#u32 (str "123456789") = ok 0xCBF43926#u32 ∧
  fast 0#u32 (str "123456789") = ok 0xCBF43926#u32 ∧
  slow 0#u32 (str "hello world") = ok 0x0D4A1185#u32 ∧
  fast 0#u32 (str "The quick brown fox jumps over the lazy dog") = ok 0x414FA339#u32 ∧
  fast 0#u32 (List.replicate 32 0#u8) = ok 0x190A55AD#u32 ∧
  fast 0#u32 (List.replicate 100 0xFF#u8) = slow 0#u32 (List.replicate 100 0xFF#u8)

/-! ## Algebraic laws -/

/-- The empty buffer leaves the checksum unchanged (any `prev`). -/
def gold_empty (p : Std.U32) : Prop :=
  slow p [] = ok p ∧ fast p [] = ok p

/-- Incremental hashing: continuing from `update(p, a)` equals hashing `a ++ b`. -/
def gold_slow_concat (p : Std.U32) (a b : List Std.U8) : Prop :=
  (do let x ← slow p a; slow x b) = slow p (a ++ b)

def gold_fast_concat (p : Std.U32) (a b c : List Std.U8) : Prop :=
  (do let x ← fast p (a ++ b); fast x c) = fast p (a ++ b ++ c)

/-- The fast and the slow implementation agree. -/
def gold_fast_eq_slow (p : Std.U32) (a b c : List Std.U8) : Prop :=
  fast p (long a b c) = slow p (long a b c) ∧ fast p a = slow p a

/-- Mixing: incremental fast/slow chains agree with one-shot hashing. -/
def gold_mixed_chain (p : Std.U32) (a b : List Std.U8) : Prop :=
  (do let x ← fast p (a ++ a); slow x b) = fast p (a ++ a ++ b)

/-! Differential-testing probes. -/

def diff_slow (p : Std.U32) (a : List Std.U8) := slow p a
def diff_fast (p : Std.U32) (a : List Std.U8) := fast p a
def diff_fast_long (p : Std.U32) (a b c : List Std.U8) := fast p (long a b c)
def diff_slow_long (p : Std.U32) (a b c : List Std.U8) := slow p (long a b c)

end Benchmark.V2.Crc32fast.Baseline.Gold
