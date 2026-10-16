import Benchmark.V2.Prelude
import NtTimeFileTime.Extraction

/-! Hidden gold specification for target `nt_time/file_time`.

API (`nt_time::FileTime`, a `u64` count of 100-ns intervals since
1601-01-01 00:00:00 UTC): `new`, `to_raw`, `to_be_bytes`, `to_le_bytes`,
`from_be_bytes`, `from_le_bytes`, `to_high_low`, `from_high_low`,
`to_unix_time_nanos`, `from_unix_time_secs`.

`from_unix_time_secs(secs)` returns `Err(Negative)` iff the time is before the NT
epoch (`secs < -11_644_473_600`), `Err(Overflow)` iff it is after
`FileTime::MAX` (`secs > 1_833_029_933_770`), and otherwise the exact tick count
`(secs + 11_644_473_600) * 10^7`; it never panics.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM nt_time RSGB

deriving instance DecidableEq for nt_time.error.FileTimeRangeErrorKind
deriving instance Repr for nt_time.error.FileTimeRangeErrorKind
deriving instance DecidableEq for core.result.Result
deriving instance Repr for core.result.Result

namespace Benchmark.V2.NtTime.FileTime.Gold

/-- Seconds between 1601-01-01 and 1970-01-01. -/
def unixOffsetSecs : Int := 11644473600

/-- The 8 base-256 digits of `n`, most significant first. -/
def beDigits (n : Nat) : List Nat := (List.range 8).map fun i => n / 256 ^ (7 - i) % 256

/-- The 8 base-256 digits of `n`, least significant first. -/
def leDigits (n : Nat) : List Nat := (List.range 8).map fun i => n / 256 ^ i % 256

def beValue (l : List Nat) : Nat := l.foldl (fun acc b => acc * 256 + b) 0
def leValue (l : List Nat) : Nat := l.foldr (fun b acc => b + 256 * acc) 0

/-- An 8-byte array built from a sampled list (truncated / zero-padded). -/
def mkArr8 (l : List Std.U8) : Std.Array Std.U8 8#usize :=
  if h : ((l ++ List.replicate 8 0#u8).take 8).length = (8#usize).val then ⟨_, h⟩
  else ⟨List.replicate 8 0#u8, by simp⟩

def arrNats (a : Std.Array Std.U8 8#usize) : List Nat := a.val.map (·.val)

/-- Reference model of `from_unix_time_secs`. -/
def fromUnixSecsModel (s : Int) : RustM (core.result.Result file_time.FileTime error.FileTimeRangeError) :=
  if s < -unixOffsetSecs then ok (.Err .Negative)
  else if (s + unixOffsetSecs) * 10000000 > 2 ^ 64 - 1 then ok (.Err .Overflow)
  else ok (.Ok (mkU .U64 ((s + unixOffsetSecs).toNat * 10000000)))

/-! ## raw value -/

def gold_new (x : Std.U64) : Prop := file_time.FileTime.new x = ok x
def gold_to_raw (x : Std.U64) : Prop := file_time.FileTime.to_raw x = ok x

/-! ## bytes -/

def gold_to_be_bytes (ft : Std.U64) : Prop :=
  file_time.FileTime.to_be_bytes ft ⦃ a => arrNats a = beDigits ft.val ⦄
def gold_to_le_bytes (ft : Std.U64) : Prop :=
  file_time.FileTime.to_le_bytes ft ⦃ a => arrNats a = leDigits ft.val ⦄
def gold_from_be_bytes (l : List Std.U8) : Prop :=
  file_time.FileTime.from_be_bytes (mkArr8 l) ⦃ ft => ft.val = beValue (arrNats (mkArr8 l)) ⦄
def gold_from_le_bytes (l : List Std.U8) : Prop :=
  file_time.FileTime.from_le_bytes (mkArr8 l) ⦃ ft => ft.val = leValue (arrNats (mkArr8 l)) ⦄
def gold_be_roundtrip (ft : Std.U64) : Prop :=
  (do let b ← file_time.FileTime.to_be_bytes ft; file_time.FileTime.from_be_bytes b) = ok ft
def gold_le_roundtrip (ft : Std.U64) : Prop :=
  (do let b ← file_time.FileTime.to_le_bytes ft; file_time.FileTime.from_le_bytes b) = ok ft
def gold_be_roundtrip_bytes (l : List Std.U8) : Prop :=
  (do let f ← file_time.FileTime.from_be_bytes (mkArr8 l); file_time.FileTime.to_be_bytes f)
    ⦃ a => a.val = (mkArr8 l).val ⦄
def gold_le_roundtrip_bytes (l : List Std.U8) : Prop :=
  (do let f ← file_time.FileTime.from_le_bytes (mkArr8 l); file_time.FileTime.to_le_bytes f)
    ⦃ a => a.val = (mkArr8 l).val ⦄
/-- The little-endian bytes are the big-endian bytes reversed. -/
def gold_le_is_reverse_be (ft : Std.U64) : Prop :=
  (do let b ← file_time.FileTime.to_be_bytes ft; let l ← file_time.FileTime.to_le_bytes ft; ok (b, l))
    ⦃ p => p.2.val = p.1.val.reverse ⦄

/-! ## high / low halves -/

def gold_to_high_low (ft : Std.U64) : Prop :=
  file_time.FileTime.to_high_low ft ⦃ p => p.1.val = ft.val / 2 ^ 32 ∧ p.2.val = ft.val % 2 ^ 32 ⦄
def gold_from_high_low (high low : Std.U32) : Prop :=
  file_time.FileTime.from_high_low high low ⦃ ft => ft.val = high.val * 2 ^ 32 + low.val ⦄
def gold_high_low_roundtrip (ft : Std.U64) : Prop :=
  (do let p ← file_time.FileTime.to_high_low ft; file_time.FileTime.from_high_low p.1 p.2) = ok ft
def gold_high_low_roundtrip' (high low : Std.U32) : Prop :=
  (do let ft ← file_time.FileTime.from_high_low high low; file_time.FileTime.to_high_low ft) = ok (high, low)

/-! ## Unix time -/

/-- Exact value, never panics (the range test of the crate follows). -/
def gold_to_unix_time_nanos (ft : Std.U64) : Prop :=
  file_time.unix_time.FileTime.to_unix_time_nanos ft ⦃ t => t.val = (ft.val : Int) * 100 - unixOffsetSecs * 1000000000 ⦄

def gold_from_unix_time_secs (secs : Std.I64) : Prop :=
  file_time.unix_time.FileTime.from_unix_time_secs secs = fromUnixSecsModel secs.val

/-- Exact behaviour around the lower boundary (NT epoch). -/
def gold_from_unix_time_secs_lo (d : Std.I8) : Prop :=
  file_time.unix_time.FileTime.from_unix_time_secs (mkI .I64 (-unixOffsetSecs + d.val)) =
    fromUnixSecsModel (-unixOffsetSecs + d.val)

/-- Exact behaviour around the upper boundary (`FileTime::MAX`). -/
def gold_from_unix_time_secs_hi (d : Std.I8) : Prop :=
  file_time.unix_time.FileTime.from_unix_time_secs (mkI .I64 (1833029933770 + d.val)) =
    fromUnixSecsModel (1833029933770 + d.val)

/-- Exact behaviour on small (|secs| < 2^31) timestamps around the Unix epoch. -/
def gold_from_unix_time_secs_small (s : Std.I32) : Prop :=
  file_time.unix_time.FileTime.from_unix_time_secs (mkI .I64 s.val) = fromUnixSecsModel s.val

/-- Converting in-range seconds then reading nanoseconds gives `secs * 10^9`. -/
def gold_secs_to_nanos (secs : Std.I64) : Prop :=
  -unixOffsetSecs ≤ secs.val → secs.val ≤ 1833029933770 →
    file_time.unix_time.FileTime.from_unix_time_secs secs =
      ok (.Ok (mkU .U64 ((secs.val + unixOffsetSecs).toNat * 10000000))) ∧
    file_time.unix_time.FileTime.to_unix_time_nanos (mkU .U64 ((secs.val + unixOffsetSecs).toNat * 10000000))
      ⦃ t => t.val = secs.val * 1000000000 ⦄

/-! Differential-testing probes. -/

def diff_new (x : Std.U64) := file_time.FileTime.new x
def diff_to_raw (x : Std.U64) := file_time.FileTime.to_raw x
def diff_to_be_bytes (x : Std.U64) := (fun a => a.val) <$> file_time.FileTime.to_be_bytes x
def diff_to_le_bytes (x : Std.U64) := (fun a => a.val) <$> file_time.FileTime.to_le_bytes x
def diff_from_be_bytes (x : Std.U64) (l : List Std.U8) := file_time.FileTime.from_be_bytes (mkArr8 (l ++ (beDigits x.val).map (mkU .U8)))
def diff_from_le_bytes (x : Std.U64) (l : List Std.U8) := file_time.FileTime.from_le_bytes (mkArr8 (l ++ (beDigits x.val).map (mkU .U8)))
def diff_to_high_low (x : Std.U64) := file_time.FileTime.to_high_low x
def diff_from_high_low (h l : Std.U32) := file_time.FileTime.from_high_low h l
def diff_to_unix_time_nanos (x : Std.U64) := file_time.unix_time.FileTime.to_unix_time_nanos x
def diff_from_unix_time_secs (s : Std.I64) := file_time.unix_time.FileTime.from_unix_time_secs s
def diff_from_unix_time_secs_lo (d : Std.I8) :=
  file_time.unix_time.FileTime.from_unix_time_secs (mkI .I64 (-unixOffsetSecs + d.val))
def diff_from_unix_time_secs_hi (d : Std.I8) :=
  file_time.unix_time.FileTime.from_unix_time_secs (mkI .I64 (1833029933770 + d.val))

end Benchmark.V2.NtTime.FileTime.Gold
